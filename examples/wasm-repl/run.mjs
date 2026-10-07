// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

import { readFileSync, writeFileSync, mkdirSync } from 'node:fs';
import { homedir } from 'node:os';
import { join } from 'node:path';
import { terminalInterface } from './terminal.mjs';
import runtime from '../../target/wasm-repl/wasm_repl.js';

const defaultFuel = runtime.default_fuel_limit();

const help = `Ferlium Wasm REPL
Usage: node examples/wasm-repl/run.mjs [options] [file]
  -e, --eval SOURCE    Run one submission
  --session           Read submissions and commands line by line from stdin
  --json              Emit JSON lines (without prompts)
  --wasm              Inspect the complete last module after execution
  --mir               Inspect semantic MIR with current optimization after execution
  --physical-mir      Inspect physical MIR after execution
  --fuel N|off        Set execution fuel (default: ${defaultFuel})
  --opt on|off        Select MIR optimization (default: on)
  --allow-experimental

Commands:
  \\help               Show this help
  \\wasm               Show Wasm for the complete last compiled module
  \\mir [MODULE] [raw]          Show semantic MIR with current optimization, or raw MIR
  \\physical-mir [MODULE] [raw] Show physical MIR with current optimization, or raw MIR
  \\module [MODULE]    Show the current or named module (HIR)
  \\function FN [MOD]  Show a function by name/index or MODULE::FN (HIR)
  \\history            List compiled submissions
  \\opt [on|off]       Show or set MIR optimization
  \\run                Run the last successfully compiled expression again
  \\fuel [N|off]       Show or set execution fuel
  \\load FILE          Compile and run a file as a submission
  \\reset              Clear the session
  \\quit               Exit

Without a file or --eval, piped stdin is one complete source submission.
Use --session to script a persistent REPL. Top-level local variables do not
persist between submissions; public module definitions do, as in the native REPL.`;

const args = process.argv.slice(2);
let json = false, sessionMode = false, experimental = false, fuel = defaultFuel, optimized = true;
let expression, file, inspection;
class UsageError extends Error {}

function markFailure(code) {
    process.exitCode = Math.max(process.exitCode ?? 0, code);
}

function readSource(path) {
    try { return readFileSync(path, 'utf8'); }
    catch (error) { throw new UsageError(error.message); }
}

function parseOptimization(value) {
    if (!['on', 'yes', 'off', 'no'].includes(value)) {
        throw new UsageError(`Unknown optimization setting "${value}".`);
    }
    return ['on', 'yes'].includes(value);
}

function parseFuel(value) {
    if (['off', 'none', 'unlimited'].includes(value)) return null;
    if (!/^\d+$/.test(value ?? '') || Number(value) > 0xffffffff) {
        throw new UsageError('fuel must be an integer between 0 and 4294967295, or off');
    }
    return Number(value);
}
try {
    for (let i = 0; i < args.length; i++) {
        const arg = args[i];
        switch (arg) {
            case '-h': case '--help': console.log(help); process.exit(0); break;
            case '--json': json = true; break;
            case '--session': sessionMode = true; break;
            case '--allow-experimental': experimental = true; break;
            case '--fuel': fuel = parseFuel(args[++i]); break;
            case '--opt': optimized = parseOptimization(args[++i]); break;
            case '-e': case '--eval':
                expression = args[++i];
                if (expression === undefined) throw new Error(`${arg} requires source`);
                break;
            case '--wasm': inspection = 'wasm'; break;
            case '--mir': inspection = 'mir'; break;
            case '--physical-mir': inspection = 'physical-mir'; break;
            default:
                if (arg.startsWith('-') || file !== undefined) throw new Error(`unexpected argument: ${arg}`);
                file = arg;
        }
    }
    if (file !== undefined && expression !== undefined) throw new Error('choose a file or --eval');
    if (sessionMode && (file !== undefined || expression !== undefined)) throw new Error('--session reads stdin');
} catch (error) {
    console.error(error.message);
    process.exit(1);
}

let repl, counter = 0, compiled = false, runtimeUsable = true;
const sources = new Map();
function reset() {
    repl?.free();
    repl = new runtime.Repl();
    repl.set_allow_experimental(experimental);
    repl.set_optimized(optimized);
    if (fuel === null) repl.disable_fuel(); else repl.set_fuel(fuel);
    counter = 0;
    compiled = false;
    sources.clear();
}
reset();

function emit(event) {
    if (json) { console.log(JSON.stringify(event)); return; }
    if (event.kind === 'diagnostic') {
        const source = sources.get(event.file) ?? '';
        const before = source.slice(0, event.from);
        const line = before.split('\n').length;
        const column = before.length - before.lastIndexOf('\n');
        console.error(`${event.file}:${line}:${column}: ${event.severity}: ${event.text}`);
        if (source) {
            console.error(source.split('\n')[line - 1]);
            console.error(`${' '.repeat(column - 1)}^`);
        }
    } else if (event.kind === 'error') console.error(event.text);
    else console.log(event.text);
}

function execute() {
    if (!compiled) throw new Error('no successfully compiled submission');
    let result;
    try {
        result = repl.run();
        for (const text of repl.take_output()) emit({ kind: 'print', text });
        if (result) {
            const error = result.error_content();
            try {
                emit({ kind: error ? 'error' : 'result', text: result.text_message() });
                if (error) markFailure(2);
            } finally { error?.free(); }
        }
    } finally { result?.free(); }
}

function inspect(kind, raw = false, module) {
    if (!compiled && !module) throw new Error('no successfully compiled submission');
    if (kind === 'wasm') {
        const artifact = repl.wasm_text();
        try { emit({ kind: 'inspection', format: kind, text: artifact.text }); }
        finally { artifact.free(); }
    } else {
        const text = kind === 'physical-mir' ? repl.physical_mir_text(raw, module)
            : repl.mir_text(optimized && !raw, module);
        emit({ kind: 'inspection', format: kind, text });
    }
}

function submit(source) {
    if (!source.trim()) return;
    const name = `repl${counter++}`;
    sources.set(name, source);
    const report = repl.compile(source);
    const diagnostics = report.diagnostics;
    try {
        for (const diagnostic of diagnostics) {
            emit({ kind: 'diagnostic', file: diagnostic.file, from: diagnostic.from,
                to: diagnostic.to, severity: diagnostic.severity === runtime.DiagnosticSeverity.Warning
                    ? 'warning' : 'error', text: diagnostic.text });
        }
        if (!report.succeeded) { markFailure(1); return; }
        compiled = true;
        execute();
        if (inspection) inspect(inspection);
    } finally {
        for (const diagnostic of diagnostics) diagnostic.free();
        report.free();
    }
}

function command(line) {
    const match = /^\\(\S+)\s*(.*)$/.exec(line.trim());
    if (!match) throw new UsageError('empty command; use \\help');
    const [, name, argument] = match;
    switch (name) {
        case 'help': emit({ kind: 'info', text: help }); break;
        case 'wasm':
            if (argument) throw new UsageError(`\\${name} takes no arguments`);
            inspect(name); break;
        case 'mir': case 'physical-mir': {
            const args = argument ? argument.split(/\s+/) : [];
            const modules = args.filter(arg => arg !== 'raw');
            if (modules.length > 1 || args.filter(arg => arg === 'raw').length > 1)
                throw new UsageError(`Usage: \\${name} [MODULE] [raw]`);
            inspect(name, args.includes('raw'), modules[0]); break;
        }
        case 'module':
            if (argument.split(/\s+/).length > 1) throw new UsageError('Usage: \\module [MODULE]');
            emit({ kind: 'inspection', format: 'hir', text: repl.module_text(argument || undefined) }); break;
        case 'function': {
            const [fn, module, extra] = argument.split(/\s+/);
            if (!fn) throw new UsageError('Function id or name is required.');
            if (extra) throw new UsageError('Usage: \\function FN_NAME_OR_INDEX [MOD_NAME]');
            emit({ kind: 'inspection', format: 'hir', text: repl.function_text(fn, module) }); break;
        }
        case 'history': emit({ kind: 'info', text: repl.history_text() }); break;
        case 'opt':
            if (argument) {
                optimized = parseOptimization(argument);
                repl.set_optimized(optimized);
            }
            emit({ kind: 'info', text: `MIR optimization: ${optimized ? 'on' : 'off'}` }); break;
        case 'run': execute(); break;
        case 'load':
            if (!argument) throw new UsageError('Usage: \\load FILE');
            submit(readSource(argument)); break;
        case 'fuel':
            if (argument) {
                fuel = parseFuel(argument);
                if (fuel === null) repl.disable_fuel(); else repl.set_fuel(fuel);
            }
            emit({ kind: 'info', text: fuel === null && argument
                ? 'Execution fuel limit disabled.' : `Execution fuel limit: ${fuel ?? 'off'}` }); break;
        case 'reset': reset(); emit({ kind: 'info', text: 'Session reset.' }); break;
        case 'quit': return false;
        default: throw new UsageError(`unknown command: \\${name}; use \\help`);
    }
    return true;
}

function reportFailure(error) {
    // Rust panics and engine traps can leave the runtime unusable, including its destructors.
    runtimeUsable = !(error instanceof WebAssembly.RuntimeError || error instanceof RangeError);
    if (runtimeUsable) {
        for (const text of repl.take_output()) emit({ kind: 'print', text });
    }
    emit({ kind: 'error', text: String(error?.message ?? error) });
    markFailure(error instanceof UsageError ? 1 : 2);
    return runtimeUsable;
}

async function terminal() {
    const interactive = Boolean(process.stdin.isTTY && !json);
    const historyDirectory = join(process.env.XDG_STATE_HOME ?? join(homedir(), '.local', 'state'), 'ferlium');
    const historyFile = join(historyDirectory, 'wasm-repl-history.json');
    let history = [];
    if (interactive) {
        try {
            const saved = JSON.parse(readFileSync(historyFile, 'utf8'));
            if (Array.isArray(saved) && saved.every(entry => typeof entry === 'string')) history = saved;
        } catch { /* First session. */ }
        emit({ kind: 'info', text: 'Ferlium Wasm REPL - Type \\help for help.' });
    }
    const rl = terminalInterface({ input: process.stdin, output: process.stdout, terminal: interactive,
        history, historySize: 256, removeHistoryDuplicates: true });
    rl.on('history', entries => {
        try {
            mkdirSync(historyDirectory, { recursive: true });
            writeFileSync(historyFile, JSON.stringify(entries));
        } catch { /* History is optional. */ }
    });
    const prompt = () => {
        if (interactive) { rl.setPrompt(`repl${counter} >> `); rl.prompt(); }
    };
    rl.on('SIGINT', () => rl.close());
    prompt();
    try {
        for await (const input of rl) {
            const line = input.replace(/\r\n?/g, '\n');
            try {
                if (line.trim().startsWith('\\')) { if (!command(line)) break; }
                else submit(line);
            } catch (error) { if (!reportFailure(error)) break; }
            prompt();
        }
    } finally { rl.close(); }
}

try {
    if (expression !== undefined) submit(expression);
    else if (file !== undefined) submit(readSource(file));
    else if (!process.stdin.isTTY && !sessionMode) submit(readSource(0));
    else await terminal();
} catch (error) { reportFailure(error); }
finally { if (runtimeUsable) repl.free(); }
