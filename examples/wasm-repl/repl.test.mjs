// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

import { test } from 'node:test';
import { PassThrough } from 'node:stream';
import { once } from 'node:events';
import { bracketedPaste, terminalInterface } from './terminal.mjs';
import runtime from '../../target/wasm-repl/wasm_repl.js';
import assert from 'node:assert/strict';
import { spawnSync } from 'node:child_process';
import { fileURLToPath } from 'node:url';
import { mkdtempSync, writeFileSync, rmSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';

const driver = fileURLToPath(new URL('./run.mjs', import.meta.url));
function run(args, input = '') {
    const result = spawnSync(process.execPath, [driver, ...args], { input, encoding: 'utf8', timeout: 30000 });
    assert.ifError(result.error);
    return result;
}
function events(input, args = []) {
    const result = run(['--session', '--json', ...args], input);
    return { ...result, events: result.stdout.trim().split('\n').filter(Boolean).map(JSON.parse) };
}

test('stdin is a complete source; output is quiet by default', () => {
    const result = run([], 'fn twice(x: int) -> int {\n x * 2\n}\ntwice(21)\n');
    assert.equal(result.status, 0, result.stderr);
    assert.equal(result.stdout, '42: int\n');
});

test('definitions persist, shadowing prefers newest, earlier callers keep their bindings', () => {
    const result = events('pub fn answer() -> int { 1 }\npub fn old() -> int { answer() }\npub fn answer() -> int { 42 }\n(answer(), old())\n');
    assert.equal(result.status, 0, result.stderr);
    assert.deepEqual(result.events.filter(e => e.kind === 'result').map(e => e.text), ['(42, 1): (int, int)']);
});

test('multiline submissions, generic functions, printing, and aggregate results', () => {
    const result = events('pub fn identity<T>(x: T) -> T { x }\nprint("hello <&> 😀"); identity([1, 2, 3])\n');
    assert.equal(result.status, 0, result.stderr);
    assert.deepEqual(result.events, [
        { kind: 'print', text: 'hello <&> 😀' },
        { kind: 'result', text: '[1, 2, 3]: [int]' },
    ]);
});

test('inspection includes uncalled private functions and does not rerun print', () => {
    const result = events('fn unused(x: int) -> int { x + 100 }\nprint("once"); 42\n\\wasm\n\\mir raw\n\\physical-mir\n');
    assert.equal(result.status, 0, result.stderr);
    assert.equal(result.events.filter(e => e.kind === 'print').length, 1);
    // Inspect the latest submitted module, then separately a definitions-only module.
    assert.equal(result.events.filter(e => e.kind === 'inspection').length, 3);
    const definitions = events('fn unused(x: int) -> int { x + 100 }\n\\wasm\n');
    assert.equal(definitions.status, 0, definitions.stderr);
    assert.match(definitions.events[0].text, /repl0::unused/);
});

test('compilation failure preserves previous definitions and inspection', () => {
    const result = events('pub fn answer() -> int { 42 }\nfn broken() -> bool { 1 }\n\\wasm\nanswer()\n');
    assert.equal(result.status, 1);
    assert.ok(result.events.some(e => e.kind === 'diagnostic' && e.severity === 'error'));
    assert.match(result.events.find(e => e.kind === 'inspection').text, /repl0::answer/);
    assert.equal(result.events.at(-1).text, '42: int');
});

test('fuel exhaustion and runtime failures allow later submissions', () => {
    const result = events('loop {}\n[1][9]\n42\n', ['--fuel', '100']);
    assert.equal(result.status, 2);
    assert.ok(result.events.some(e => e.kind === 'error' && /fuel/i.test(e.text)));
    assert.ok(result.events.some(e => e.kind === 'error' && /bound/i.test(e.text)));
    assert.equal(result.events.at(-1).text, '42: int');
});

test('warnings are nonfatal and positions use UTF-16', () => {
    const result = events('pub fn f() -> int { return 1; }\nf()\n');
    assert.equal(result.status, 0, result.stderr);
    assert.ok(result.events.some(e => e.kind === 'diagnostic' && e.severity === 'warning'));
    assert.equal(result.events.at(-1).text, '1: int');
    const failure = events('"😀" + 1\n');
    assert.equal(failure.status, 1);
    assert.ok(failure.events.some(e => e.kind === 'diagnostic' && e.from === 7 && e.to === 8));
});

test('reset, rerun and invalid options', () => {
    const result = events('40 + 2\n\\run\n\\reset\n\\wasm\n');
    assert.equal(result.status, 2);
    assert.equal(result.events.filter(e => e.kind === 'result').length, 2);
    assert.match(result.events.at(-1).text, /no successfully compiled/);
    assert.equal(run(['--fuel', '-1']).status, 1);
});

test('file input, load command and explicit command-line inspection', () => {
    const directory = mkdtempSync(join(tmpdir(), 'ferlium-repl-'));
    try {
        const path = join(directory, 'a program.fer');
        writeFileSync(path, 'pub fn answer() -> int { 42 }\nanswer()\n');
        const file = run(['--json', '--wasm', path]);
        assert.equal(file.status, 0, file.stderr);
        const output = file.stdout.trim().split('\n').map(JSON.parse);
        assert.equal(output[0].text, '42: int');
        assert.match(output[1].text, /repl0::answer/);
        const loaded = events(`\\load ${path}\nanswer()\n`);
        assert.equal(loaded.status, 0, loaded.stderr);
        assert.equal(loaded.events.filter(e => e.kind === 'result').length, 2);
    } finally { rmSync(directory, { recursive: true }); }
});

test('native inspection commands and fuel/optimization aliases', () => {
    const result = events('\\module\nfn private(x: int) -> int { x + 1 }\n\\module\n\\function private\n\\function repl0::private\n\\function private repl0\n\\function 0 repl0\n\\history\n\\fuel none\n\\fuel\n\\fuel unlimited\n\\fuel 200\n\\opt no\n40 + 2\n\\opt yes\n40 + 2\n\\physical-mir raw\n');
    assert.equal(result.status, 0, result.stderr);
    const inspected = result.events.filter(e => e.kind === 'inspection');
    assert.match(inspected[0].text, /string_len/);
    assert.match(inspected[1].text, /private/);
    assert.equal(inspected[2].text, inspected[3].text);
    assert.equal(inspected[2].text, inspected[4].text);
    assert.equal(inspected[2].text, inspected[5].text);
    const information = result.events.filter(e => e.kind === 'info').map(e => e.text);
    assert.match(information[0], /repl0:/);
    assert.deepEqual(information.slice(1), [
        'Execution fuel limit disabled.', 'Execution fuel limit: off',
        'Execution fuel limit disabled.', 'Execution fuel limit: 200',
        'MIR optimization: off', 'MIR optimization: on',
    ]);
    assert.equal(result.events.filter(e => e.kind === 'result').at(-1).text, '42: int');
});

test('optimization off applies to execution and inspection without changing results', () => {
    const result = events('pub fn twice(x: int) -> int { x * 2 }\n\\opt off\ntwice(21)\n\\wasm\n\\mir\n\\physical-mir\n\\opt on\n\\run\n');
    assert.equal(result.status, 0, result.stderr);
    assert.deepEqual(result.events.filter(e => e.kind === 'result').map(e => e.text), ['42: int', '42: int']);
    assert.equal(result.events.filter(e => e.kind === 'inspection').length, 3);
});

test('optimization changes generated physical code, not just the status message', () => {
    const result = events([
        'pub fn sum(x: int) -> int { let pair = (x, x + 1); pair.0 + pair.1 }',
        '\\opt off', '\\wasm', '\\physical-mir',
        '\\opt on', '\\wasm', '\\physical-mir',
    ].join('\n') + '\n');
    assert.equal(result.status, 0, result.stderr);
    const inspected = result.events.filter(e => e.kind === 'inspection');
    assert.notEqual(inspected[1].text, inspected[3].text);
});

test('usage failures exit with 1; inspection failures exit with 2', () => {
    for (const command of ['\\unknown', '\\opt invalid', '\\fuel invalid', '\\function',
        '\\function a b c', '\\module a b', '\\load', '\\load /missing/ferlium-file']) {
        assert.equal(events(command + '\n').status, 1, command);
    }
    assert.equal(events('\\wasm\n').status, 2);
    assert.equal(run(['/missing/ferlium-file']).status, 1);
    assert.equal(run(['--opt', 'invalid']).status, 1);
});

test('later compilation and usage failures preserve earlier execution failure status', () => {
    for (const input of ['[1][9]\nfn broken() -> bool { 1 }\n42\n',
        '[1][9]\n\\unknown\n42\n']) {
        assert.equal(events(input).status, 2);
    }
});

test('file source beginning with a backslash is compiled as source', () => {
    const directory = mkdtempSync(join(tmpdir(), 'ferlium-repl-'));
    try {
        const path = join(directory, 'source.fer');
        writeFileSync(path, '\\quit\n');
        const result = events(`\\load ${path}\n42\n`);
        assert.equal(result.status, 1);
        assert.equal(result.events.at(-1).text, '42: int');
        assert.equal(result.events.filter(e => e.kind === 'diagnostic').length, 1);
    } finally { rmSync(directory, { recursive: true }); }
});

test('fuel defaults are exported by Rust and CLI optimization can be disabled', () => {
    const result = events('\\fuel\n\\fuel none\n\\reset\n\\fuel\n');
    assert.equal(result.status, 0, result.stderr);
    assert.equal(result.events[0].text, `Execution fuel limit: ${runtime.default_fuel_limit()}`);
    assert.equal(result.events.at(-1).text, 'Execution fuel limit: off');
    const evaluation = run(['--opt', 'off', '--eval', '40 + 2']);
    assert.equal(evaluation.status, 0, evaluation.stderr);
    assert.equal(evaluation.stdout, '42: int\n');
});

test('bracketed paste preserves source across every delimiter split', () => {
    const source = 'fn answer() -> int {\r\n 42\r\n}';
    const stream = 'before\x1b[200~' + source + '\x1b[201~after';
    for (let split = 0; split <= stream.length; split++) {
        let input = '';
        const pasted = [];
        const consume = bracketedPaste(text => { input += text; }, text => pasted.push(text));
        consume(stream.slice(0, split));
        consume(stream.slice(split));
        assert.equal(input, 'beforeafter');
        assert.deepEqual(pasted, [source.replace(/\r\n/g, '\n')]);
    }
});

test('terminal paste waits for Enter and keeps multiline source in one submission', async () => {
    const input = new PassThrough();
    const output = new PassThrough();
    output.columns = 80;
    const rawModes = [];
    input.setRawMode = enabled => rawModes.push(enabled);
    const previousTerm = process.env.TERM;
    process.env.TERM = 'xterm';
    const rl = terminalInterface({ input, output, terminal: true });
    if (previousTerm === undefined) delete process.env.TERM;
    else process.env.TERM = previousTerm;
    const submissions = [];
    rl.on('line', line => submissions.push(line));
    try {
        input.write('1 + ');
        input.write('\x1b[200~(\r\n 2\r\n)\x1b[201~');
        await new Promise(resolve => setImmediate(resolve));
        assert.deepEqual(submissions, []);
        assert.equal(rl.line, '1 + (\n 2\n)');
        const submitted = once(rl, 'line');
        input.write('\r');
        await submitted;
        assert.deepEqual(submissions.map(line => line.replace(/\r\n?/g, '\n')), ['1 + (\n 2\n)']);
        input.write('\x1b[A');
        const recalled = once(rl, 'line');
        input.write('\r');
        await recalled;
        assert.equal(submissions[1].replace(/\r\n?/g, '\n'), '1 + (\n 2\n)');
    } finally { rl.close(); }
    assert.deepEqual(rawModes, [true, false]);
});

test('MIR inspection selects earlier modules without changing the current submission', () => {
    const result = events([
        'pub fn earlier(x: int) -> int { x + 1 }',
        'pub fn latest(x: int) -> int { x * 2 }',
        '\\mir repl0 raw', '\\physical-mir raw repl0',
        '\\mir', '\\physical-mir',
        '\\mir missing', '\\mir repl0 repl1', '\\mir raw raw',
        '\\module', 'fn broken() -> bool { 1 }', '\\mir repl2', '\\physical-mir repl2', 'latest(21)',
    ].join('\n') + '\n');
    assert.equal(result.status, 2);
    const inspected = result.events.filter(e => e.kind === 'inspection');
    assert.match(inspected[0].text, /earlier/);
    assert.doesNotMatch(inspected[0].text, /latest/);
    assert.match(inspected[1].text, /earlier/);
    assert.match(inspected[2].text, /latest/);
    assert.match(inspected[3].text, /latest/);
    assert.match(inspected[4].text, /latest/);
    assert.ok(result.events.some(e => e.kind === 'error' && /Module missing not found/.test(e.text)));
    assert.equal(result.events.at(-1).text, '42: int');
});
