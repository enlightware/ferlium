// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

// Callgrind benchmark for the Wasm pipeline, reporting instruction counts and simulated cache
// behaviour per phase instead of the wall-clock times of `run.mjs`. Each optimization axis runs in
// its own Node process so that its standard library build is measured from the same state.
//
// The outer process builds the marker addon, drives one Valgrind child per axis and shard of the
// workload list, and reports; a child runs with `--worker` and owns the measured ranges.

import { execFileSync, spawn } from 'node:child_process';
import { createRequire } from 'node:module';
import { existsSync, mkdirSync, readFileSync, readdirSync, rmSync, statSync, writeFileSync } from 'node:fs';
import { availableParallelism } from 'node:os';
import { dirname, join } from 'node:path';
import { fileURLToPath } from 'node:url';

const here = dirname(fileURLToPath(import.meta.url));
const repoRoot = join(here, '..', '..');
const outRoot = join(repoRoot, 'target', 'wasm-callgrind');
const addonPath = join(outRoot, 'cgmark.node');
const addonSource = join(here, 'callgrind', 'cgmark.c');
const baselinePath = join(outRoot, 'baseline.json');

// V8 must not move work out of the measured thread, and its own tiering must not land inside a
// measured range: `--predictable` makes optimizing compilation synchronous and deterministic,
// while `--no-liftoff` with eager compilation builds every Wasm function with TurboFan during
// instantiation. Without those two the execute ranges would measure Liftoff code, or a lazy
// TurboFan compilation triggered by the first call.
const V8_FLAGS = ['--predictable', '--no-liftoff', '--no-wasm-lazy-compilation'];

const AXES = [
    { id: 'optimize:on', optimized: true },
    { id: 'optimize:off', optimized: false },
];

const DEFAULT_BATCH = 10;
const WASM_WARMUP_CALLS = 50;
// Interpreted linalg workloads dominate wall time by orders of magnitude. Keep the normal Wasm
// code-generation benchmark focused, and make the cross-engine comparison an explicit opt-in.
const DEFAULT_MIR_BATCH = 0;

// --- Worker: the process running under Callgrind ---

function runWorker(argv) {
    const optimized = argv[0] === 'on';
    const batch = Number(argv[1]);
    const mirBatch = Number(argv[2]);
    const names = argv.slice(3);
    const require = createRequire(import.meta.url);
    const cg = require(addonPath);
    if (!cg.runningOnValgrind()) {
        throw new Error('worker must run under Valgrind');
    }
    const runtime = require(join(repoRoot, 'target', 'wasm-profile', 'wasm_profile.js'));

    const range = (label, body) => {
        cg.zero();
        cg.toggleCollect();
        const result = body();
        cg.toggleCollect();
        cg.dump(label);
        return result;
    };

    // Warm V8's compiler machine code and Ferlium's incidental global machinery, then drop the
    // state it cached so that the measured build below is a complete one. The reset asserts that
    // no session still shares the standard library.
    //
    // The warmup compiles and runs a workload as well: the first compilation in a process costs
    // several times a later one, so without this a workload would measure differently depending on
    // how the shards happened to be cut. It uses the opposite optimization setting so that the
    // bytes about to be measured stay out of V8's compiled module cache.
    runtime.prepare_std(optimized);
    const warmup = new runtime.Workload(names[0], !optimized);
    warmup.instantiate();
    warmup.run();
    warmup.free();
    runtime.reset_std_cache();

    cg.startInstrumentation();
    range('phase=std_build', () => runtime.prepare_std(optimized));
    // Every later compilation depends on this being near zero: it is the same build again, now
    // served from the process cache that the measured build populated.
    range('phase=std_reuse', () => runtime.prepare_std(optimized));

    for (const name of names) {
        const phases = workloadPhases(name, mirBatch > 0);
        const workload = range(phases.compile, () => new runtime.Workload(name, optimized));
        try {
            // This is deterministic compile output rather than a Callgrind counter. Send it to the
            // outer process, which stores it alongside the compile range in the baseline.
            console.log(`wasm-module-bytes\t${name}\t${workload.code_bytes()}`);
            const expected = workload.expected();
            const check = (stage, produced) => {
                if (!Object.is(produced, expected)) {
                    throw new Error(`${name} produced ${produced} at ${stage}; expected ${expected}`);
                }
            };
            workload.instantiate();
            check('the first Wasm call', range(phases.wasmCold, () => workload.run()));
            // Enough calls to take V8 past tiering up the JS and wasm-bindgen glue around the
            // entry: landing that inside the batch has cost a measured range twice its steady
            // state. Interpreted calls need none of this, and are far too expensive to repeat.
            for (let warmup = 0; warmup < WASM_WARMUP_CALLS; warmup++) {
                check('Wasm warmup', workload.run());
            }
            const wasmResult = range(phases.wasmWarm, () => {
                let result;
                for (let call = 0; call < batch; call++) {
                    result = workload.run();
                }
                return result;
            });
            check('the measured Wasm batch', wasmResult);

            if (mirBatch > 0) {
                check('the first interpreted call', range(phases.mirCold, () => workload.run_mir()));
                const mirResult = range(phases.mirWarm, () => {
                    let result;
                    for (let call = 0; call < mirBatch; call++) {
                        result = workload.run_mir();
                    }
                    return result;
                });
                check('the measured interpreter batch', mirResult);
            }
        } finally {
            workload.free();
        }
    }
}

/// The measured ranges of one workload, named identically by the worker and the report.
function workloadPhases(name, withMir) {
    const phases = {
        compile: `phase=compile,workload=${name}`,
        wasmCold: `phase=execute_cold,engine=wasm,workload=${name}`,
        wasmWarm: `phase=execute,engine=wasm,workload=${name}`,
    };
    if (withMir) {
        phases.mirCold = `phase=execute_cold,engine=mir,workload=${name}`;
        phases.mirWarm = `phase=execute,engine=mir,workload=${name}`;
    }
    return phases;
}

// --- Callgrind output parsing ---

/// Sum the event counts of one dump, keyed by the phase label of its client request.
function readDumps(directory) {
    const dumps = new Map();
    for (const file of readdirSync(directory)) {
        const text = readFileSync(join(directory, file), 'utf8');
        const label = /^desc: Trigger: Client Request: (.*)$/m.exec(text);
        const events = /^events: (.*)$/m.exec(text);
        const summary = /^summary: (.*)$/m.exec(text);
        if (!label || !events || !summary) {
            continue; // The termination dump carries no range of ours.
        }
        dumps.set(label[1].trim(), metricsOf(events[1].trim().split(/\s+/), summary[1].trim().split(/\s+/)));
    }
    return dumps;
}

function metricsOf(events, counts) {
    const count = (event) => {
        const index = events.indexOf(event);
        // Callgrind omits trailing zeroes from some summaries.
        return index < 0 ? 0 : Number(counts[index] ?? 0);
    };
    const instructions = count('Ir');
    const accesses = instructions + count('Dr') + count('Dw');
    const l1Misses = count('I1mr') + count('D1mr') + count('D1mw');
    const ramHits = count('ILmr') + count('DLmr') + count('DLmw');
    const l1Hits = accesses - l1Misses;
    const llHits = l1Misses - ramHits;
    return {
        'Instructions': instructions,
        'L1 Hits': l1Hits,
        'LL Hits': llHits,
        'RAM Hits': ramHits,
        'Total read+write': accesses,
        'Estimated Cycles': l1Hits + 5 * llHits + 35 * ramHits,
    };
}

const METRICS = ['Instructions', 'L1 Hits', 'LL Hits', 'RAM Hits', 'Total read+write', 'Estimated Cycles'];
const WASM_BYTES = 'Wasm Bytes';

function scale(metrics, divisor) {
    return Object.fromEntries(METRICS.map((metric) => [metric, Math.round(metrics[metric] / divisor)]));
}

// --- Reporting ---

/// Gungraun's `new|old (percent) [factor]` columns, so both benchmarks read the same way.
function formatRow(label, current, previous) {
    const head = `  ${label}:`;
    const value = String(current);
    const padded = head + ' '.repeat(Math.max(1, 43 - head.length - value.length)) + value;
    if (previous === undefined) {
        return `${padded}|N/A`.padEnd(65) + '(*********)';
    }
    const diff = `${padded}|${previous}`.padEnd(65);
    if (current === previous) {
        return `${diff}(No change)`;
    }
    const percent = ((current - previous) / previous) * 100;
    const factor = current > previous ? current / previous : -(previous / current);
    return `${diff}(${signed(percent)}%) [${signed(factor)}x]`;
}

function signed(value) {
    const text = Math.abs(value).toPrecision(6);
    return `${value < 0 ? '-' : '+'}${text}`;
}

function report(results, baseline, options) {
    // Dumps are keyed by label, so the reading order is the directory's; name the phases in the
    // order they were measured instead.
    const phases = ['phase=std_build', ...options.selected.flatMap(
        (name) => Object.values(workloadPhases(name, options.mirBatch > 0)),
    )];
    for (const phase of phases) {
        for (const axis of options.axes) {
            const metrics = results.get(axis.id).get(phase);
            if (!metrics) {
                continue;
            }
            const previous = baseline?.[axis.id]?.[phase];
            console.log(`wasm::${phase} ${axis.id}`);
            const metricsToReport = metrics[WASM_BYTES] === undefined
                ? METRICS
                : [...METRICS, WASM_BYTES];
            for (const metric of metricsToReport) {
                console.log(formatRow(metric, metrics[metric], previous?.[metric]));
            }
        }
    }

    if (!results.has('optimize:off')) {
        reportTrailer(results, options);
        return;
    }
    console.log('\nOptimization effect (optimize:on against optimize:off, Estimated Cycles)');
    const width = Math.max(...phases.map((phase) => phase.length)) + 2;
    console.log(`  ${'phase'.padEnd(width)}${'on'.padStart(14)}${'off'.padStart(14)}${'change'.padStart(13)}`);
    for (const phase of phases) {
        const on = results.get('optimize:on').get(phase)?.['Estimated Cycles'];
        const off = results.get('optimize:off').get(phase)?.['Estimated Cycles'];
        if (on === undefined || off === undefined) {
            continue;
        }
        const change = off === 0 ? '' : `${signed(((on - off) / off) * 100)}%`;
        console.log(`  ${phase.padEnd(width)}${String(on).padStart(14)}${String(off).padStart(14)}${change.padStart(13)}`);
    }

    reportModuleSizes(results, options.selected);

    reportTrailer(results, options);
}

function reportTrailer(results, options) {
    if (options.mirBatch > 0) {
        for (const axis of options.axes) {
            reportEngines(results.get(axis.id), axis.id, options);
        }
    }
    const batches = options.mirBatch > 0
        ? `${options.batch} Wasm and ${options.mirBatch} interpreter call(s)`
        : `${options.batch} call(s)`;
    console.log(`\nwarm phases are per invocation over ${batches}; cold phases are the first call.`);
}

function reportModuleSizes(results, selected) {
    console.log('\nGenerated Wasm module size (optimize:on against optimize:off)');
    const width = Math.max(...selected.map((name) => name.length)) + 2;
    console.log(`  ${'workload'.padEnd(width)}${'on'.padStart(14)}${'off'.padStart(14)}${'change'.padStart(13)}`);
    for (const name of selected) {
        const phase = workloadPhases(name, false).compile;
        const on = results.get('optimize:on').get(phase)?.[WASM_BYTES];
        const off = results.get('optimize:off').get(phase)?.[WASM_BYTES];
        if (on === undefined || off === undefined) {
            continue;
        }
        const change = off === 0 ? '' : `${signed(((on - off) / off) * 100)}%`;
        console.log(`  ${name.padEnd(width)}${String(on).padStart(14)}${String(off).padStart(14)}${change.padStart(13)}`);
    }
}

/// Physical MIR interpretation against generated Wasm, on identical compiled artifacts.
function reportEngines(dumps, axis, options) {
    console.log(`\nEngine effect for ${axis} (Instructions)`);
    const columns = ['wasm cold', 'wasm warm', 'mir cold', 'mir warm', 'mir/wasm cold', 'mir/wasm warm'];
    console.log(`  ${'workload'.padEnd(20)}${columns.map((name) => name.padStart(15)).join('')}`);
    for (const name of options.selected) {
        const phases = workloadPhases(name, true);
        const instructions = (phase) => dumps.get(phase).Instructions;
        const wasmCold = instructions(phases.wasmCold);
        const wasmWarm = instructions(phases.wasmWarm);
        const mirCold = instructions(phases.mirCold);
        const mirWarm = instructions(phases.mirWarm);
        const values = [wasmCold, wasmWarm, mirCold, mirWarm]
            .map((value) => String(value).padStart(15));
        const ratios = [mirCold / wasmCold, mirWarm / wasmWarm]
            .map((ratio) => `${ratio.toFixed(1)}x`.padStart(15));
        console.log(`  ${name.padEnd(20)}${values.join('')}${ratios.join('')}`);
    }
}

// --- Outer process ---

function buildAddon(valgrind) {
    const include = process.env.VALGRIND_INCLUDE || valgrindIncludeFor(valgrind);
    const headers = [join(include, 'valgrind.h'), join(include, 'callgrind.h')];
    const missing = headers.filter((header) => !existsSync(header));
    if (missing.length > 0) {
        throw new Error(
            `Callgrind headers not found: ${missing.join(', ')}. Install Valgrind's development ` +
            'headers or set VALGRIND_INCLUDE to the directory holding valgrind.h and callgrind.h.',
        );
    }
    if (existsSync(addonPath) && statSync(addonPath).mtimeMs > statSync(addonSource).mtimeMs) {
        return;
    }
    const nodeInclude = join(process.execPath, '..', '..', 'include', 'node');
    execFileSync('cc', [
        '-O2', '-fPIC', '-shared', '-o', addonPath, addonSource,
        `-I${nodeInclude}`, `-I${include}`,
    ], { stdio: 'inherit' });
}

/// An uninstalled `vg-in-place` tree keeps the two headers in separate directories.
function valgrindIncludeFor(valgrind) {
    const tree = dirname(valgrind);
    if (existsSync(join(tree, 'include', 'valgrind.h'))) {
        const staged = join(outRoot, 'include');
        mkdirSync(staged, { recursive: true });
        for (const [header, source] of [
            ['valgrind.h', join(tree, 'include', 'valgrind.h')],
            ['callgrind.h', join(tree, 'callgrind', 'callgrind.h')],
        ]) {
            writeFileSync(join(staged, header), readFileSync(source));
        }
        return staged;
    }
    return '/usr/include/valgrind';
}

/// One Valgrind process: one axis, one shard of the workload list.
function runShard(valgrind, axis, shard, options, names) {
    const directory = join(outRoot, `${axis.id.replace(':', '-')}-${shard}`);
    rmSync(directory, { recursive: true, force: true });
    mkdirSync(directory, { recursive: true });
    const child = spawn(valgrind, [
        '--tool=callgrind',
        '--instr-atstart=no',
        '--collect-atstart=no',
        '--cache-sim=yes',
        `--callgrind-out-file=${join(directory, 'cg.out.%p.%n')}`,
        process.execPath,
        ...V8_FLAGS,
        fileURLToPath(import.meta.url),
        '--worker',
        axis.optimized ? 'on' : 'off',
        String(options.batch),
        String(options.mirBatch),
        ...names,
    ], { stdio: ['ignore', 'pipe', 'pipe'] });
    let output = '';
    child.stdout.on('data', (chunk) => { output += chunk; });
    child.stderr.on('data', (chunk) => { output += chunk; });
    return new Promise((resolve, reject) => {
        child.on('error', reject);
        child.on('close', (status) => {
            if (status !== 0) {
                reject(new Error(`${axis.id} shard ${shard} failed with status ${status}\n${output}`));
                return;
            }
            const moduleBytes = new Map(
                [...output.matchAll(/^wasm-module-bytes\t([^\t]+)\t(\d+)$/gm)]
                    .map((match) => [match[1], Number(match[2])]),
            );
            if (moduleBytes.size !== names.length || names.some((name) => !moduleBytes.has(name))) {
                reject(new Error(`${axis.id} shard ${shard} did not report every Wasm module size\n${output}`));
                return;
            }
            console.log(`  done: ${axis.id} [${names.join(' ')}]`);
            resolve({ axis: axis.id, dumps: readDumps(directory), moduleBytes });
        });
    });
}

function shardsOf(names, count) {
    // Produce exactly `count` balanced shards when enough workloads exist. Fixed-size chunks would
    // turn twelve workloads and eight available slots into only six two-workload shards, leaving
    // both cores and parallelism unused.
    count = Math.min(count, names.length);
    const baseSize = Math.floor(names.length / count);
    const largerShards = names.length % count;
    const shards = [];
    let start = 0;
    for (let shard = 0; shard < count; shard++) {
        const size = baseSize + Number(shard < largerShards);
        shards.push(names.slice(start, start + size));
        start += size;
    }
    return shards;
}

/// Merge the shards of one axis, keeping the standard library ranges of the first.
function mergeShards(shards) {
    const merged = new Map();
    const stdBuilds = [];
    for (const { dumps, moduleBytes } of shards) {
        const stdBuild = dumps.get('phase=std_build');
        const stdReuse = dumps.get('phase=std_reuse');
        if (!stdBuild || !stdReuse) {
            throw new Error('a shard produced no standard library ranges');
        }
        stdBuilds.push(stdBuild.Instructions);
        if (stdReuse.Instructions * 100 > stdBuild.Instructions) {
            throw new Error(
                'the standard library was rebuilt instead of reused ' +
                `(${stdReuse.Instructions} against ${stdBuild.Instructions} instructions)`,
            );
        }
        dumps.delete('phase=std_reuse');
        for (const [name, bytes] of moduleBytes) {
            const phase = workloadPhases(name, false).compile;
            const metrics = dumps.get(phase);
            if (!metrics) {
                throw new Error(`a shard produced no compile range for ${name}`);
            }
            metrics[WASM_BYTES] = bytes;
        }
        for (const [phase, metrics] of dumps) {
            if (phase !== 'phase=std_build' || !merged.has(phase)) {
                merged.set(phase, metrics);
            }
        }
    }
    // Shards repeat the same standard library build in separate processes, which makes them a free
    // check that a repeated measurement lands on the same counts.
    const spread = (Math.max(...stdBuilds) - Math.min(...stdBuilds)) / Math.min(...stdBuilds);
    if (spread > 0.01) {
        throw new Error(`standard library builds disagree across shards by ${(spread * 100).toFixed(2)}%`);
    }
    return merged;
}

async function main() {
    const require = createRequire(import.meta.url);
    const runtime = require(join(repoRoot, 'target', 'wasm-profile', 'wasm_profile.js'));
    const available = runtime.workload_names().split('\n');

    const args = process.argv.slice(2);
    if (args.includes('--list')) {
        console.log(available.join('\n'));
        return;
    }
    const count = (flag, fallback, least = 1) => {
        const arg = args.find((value) => value.startsWith(`--${flag}=`));
        const value = arg === undefined ? fallback : Number(arg.slice(flag.length + 3));
        if (!Number.isInteger(value) || value < least) {
            throw new Error(`--${flag} takes an integer of at least ${least}, not ${JSON.stringify(value)}`);
        }
        return value;
    };
    const batch = count('batch', DEFAULT_BATCH);
    // One interpreted call costs orders of magnitude more than a Wasm one, so it is its own,
    // opt-in batch. --no-mir remains a convenient explicit spelling for scripts.
    const mirBatch = args.includes('--no-mir') ? 0 : count('mir-batch', DEFAULT_MIR_BATCH, 0);
    // The unoptimized axis is only a reference point; skipping it halves the processes to run,
    // leaving room for a concurrent run of another checkout.
    const axes = args.includes('--optimized-only') ? AXES.filter((axis) => axis.optimized) : AXES;
    const names = args.filter((arg) => !arg.startsWith('--'));
    const selected = names.length === 0 ? available : names;
    for (const name of selected) {
        if (!available.includes(name)) {
            throw new Error(`unknown workload ${JSON.stringify(name)}; use --list to show valid names`);
        }
    }

    const valgrind = process.env.VALGRIND ?? 'valgrind';
    mkdirSync(outRoot, { recursive: true });
    buildAddon(valgrind);

    const version = execFileSync(valgrind, ['--version'], { encoding: 'utf8' }).trim();
    console.log(`Node ${process.version} ${V8_FLAGS.join(' ')}, ${version}, ${process.arch}`);
    console.log('Estimated Cycles = L1 Hits + 5 * LL Hits + 35 * RAM Hits.');

    // Every process pays for its own standard library build, so sharding trades total work for
    // wall time. That trade is only sound because Callgrind counts the simulated program: what
    // else runs on the machine cannot move the numbers.
    const jobs = count('jobs', Math.max(1, Math.round(Number(process.env.BENCH_JOBS ?? availableParallelism() / 2))));
    // Shard as if both axes ran, even when one does: the runtime code a workload executes depends on
    // what ran before it in the same process, so only equal shardings give comparable counts.
    const shards = shardsOf(selected, Math.max(1, Math.min(Math.floor(jobs / AXES.length), selected.length)));
    console.log(`${axes.length} axes x ${shards.length} shard(s) of ${selected.length} workload(s), ${jobs} at a time\n`);

    const options = { axes, batch, mirBatch, selected };
    const started = Date.now();
    const finished = await inParallel(jobs, axes.flatMap(
        (axis) => shards.map((names, shard) => () => runShard(valgrind, axis, shard, options, names)),
    ));
    console.log(`measured in ${((Date.now() - started) / 1000).toFixed(0)}s\n`);

    const results = new Map(axes.map(
        (axis) => [axis.id, mergeShards(finished.filter((shard) => shard.axis === axis.id))],
    ));
    validate(results, axes, selected, batch, mirBatch);

    // Counts only mean the same thing under the same engine, tool and batch sizes.
    const run = { node: process.version, valgrind: version, arch: process.arch, batch, mirBatch };
    const baseline = existsSync(baselinePath) ? JSON.parse(readFileSync(baselinePath, 'utf8')) : undefined;
    const differs = baseline && Object.keys(run).filter((key) => baseline[key] !== run[key]);
    if (differs?.length > 0) {
        console.log(`baseline ignored: it was recorded with a different ${differs.join(', ')}\n`);
    }
    const previous = baseline && differs.length === 0 ? baseline.results : undefined;
    report(results, previous, options);
    // Keep the phases this run did not select, so that a subset run leaves their history intact.
    const kept = structuredClone(previous ?? {});
    for (const [axis, phases] of results) {
        kept[axis] = { ...kept[axis], ...Object.fromEntries(phases) };
    }
    writeFileSync(baselinePath, JSON.stringify({ ...run, results: kept }, null, 1));
}

/// Run at most `limit` Valgrind processes at once.
async function inParallel(limit, tasks) {
    const pending = [...tasks].reverse();
    const results = [];
    const workers = Array.from({ length: Math.min(limit, tasks.length) }, async () => {
        for (let task = pending.pop(); task !== undefined; task = pending.pop()) {
            results.push(await task());
        }
    });
    await Promise.all(workers);
    return results;
}

/// Fail loudly rather than report a range that measured nothing.
function validate(results, axes, selected, batch, mirBatch) {
    for (const axis of axes) {
        const dumps = results.get(axis.id);
        if (!dumps.get('phase=std_build')?.Instructions) {
            throw new Error(`${axis.id} collected nothing for the standard library build`);
        }
        for (const name of selected) {
            const phases = workloadPhases(name, mirBatch > 0);
            for (const phase of Object.values(phases)) {
                if (!dumps.get(phase)?.Instructions) {
                    throw new Error(`${axis.id} collected nothing for ${phase}`);
                }
            }
            if (!dumps.get(phases.compile)?.[WASM_BYTES]) {
                throw new Error(`${axis.id} reported no Wasm module size for ${name}`);
            }
            dumps.set(phases.wasmWarm, scale(dumps.get(phases.wasmWarm), batch));
            if (mirBatch > 0) {
                dumps.set(phases.mirWarm, scale(dumps.get(phases.mirWarm), mirBatch));
            }
        }
    }
}

if (process.argv[2] === '--worker') {
    runWorker(process.argv.slice(3));
} else {
    main().catch((error) => {
        console.error(error.message);
        process.exit(1);
    });
}
