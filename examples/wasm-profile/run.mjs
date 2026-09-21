// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

import { performance } from 'node:perf_hooks';
import runtime from '../../target/wasm-profile/wasm_profile.js';

const { Workload, workload_names: workloadNames } = runtime;

const available = workloadNames().split('\n');
const requested = process.argv.slice(2);
if (requested.includes('--list')) {
    console.log(available.join('\n'));
    process.exit(0);
}
const selected = requested.length === 0 ? available : requested;
for (const name of selected) {
    if (!available.includes(name)) {
        throw new Error(`unknown workload ${JSON.stringify(name)}; use --list to show valid names`);
    }
}

console.log('workload                 compile    instantiate        cold      warmed       bytes  result');
for (const name of selected) {
    let start = performance.now();
    const workload = new Workload(name);
    const compilation = performance.now() - start;
    try {
        start = performance.now();
        workload.instantiate();
        const instantiation = performance.now() - start;

        start = performance.now();
        const result = workload.run();
        const cold = performance.now() - start;
        const expected = workload.expected();
        if (!Object.is(result, expected)) {
            throw new Error(`${name} produced ${result}; expected ${expected}`);
        }

        for (let warmup = 0; warmup < 3; warmup++) {
            const warmed = workload.run();
            if (!Object.is(warmed, expected)) {
                throw new Error(`${name} changed result during warmup: ${expected} -> ${warmed}`);
            }
        }

        const samples = [];
        for (let sample = 0; sample < 7; sample++) {
            start = performance.now();
            const result = workload.run();
            samples.push(performance.now() - start);
            if (!Object.is(result, expected)) {
                throw new Error(`${name} changed result while sampling: ${expected} -> ${result}`);
            }
        }
        samples.sort((a, b) => a - b);
        console.log(
            `${name.padEnd(22)} ${compilation.toFixed(3).padStart(9)} ms` +
            ` ${instantiation.toFixed(3).padStart(11)} ms` +
            ` ${cold.toFixed(3).padStart(9)} ms` +
            ` ${samples[3].toFixed(3).padStart(9)} ms` +
            ` ${String(workload.code_bytes()).padStart(11)}  ${expected}`,
        );
    } finally {
        workload.free();
    }
}
