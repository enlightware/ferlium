// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

import { createInterface } from 'node:readline';
import { PassThrough } from 'node:stream';
import { StringDecoder } from 'node:string_decoder';

// Keep paste delimiters and pasted newlines out of readline's keypress parser.
export function bracketedPaste(onInput, onPaste) {
    let pending = '';
    let pasted = null;
    return chunk => {
        pending += chunk;
        while (pending) {
            const marker = pasted === null ? '\x1b[200~' : '\x1b[201~';
            const index = pending.indexOf(marker);
            if (index >= 0) {
                const text = pending.slice(0, index);
                pending = pending.slice(index + marker.length);
                if (pasted === null) { onInput(text); pasted = ''; }
                else { onPaste((pasted + text).replace(/\r\n?/g, '\n')); pasted = null; }
            } else {
                let retained = 0;
                for (let length = 1; length < marker.length; length++) {
                    if (pending.endsWith(marker.slice(0, length))) retained = length;
                }
                const text = pending.slice(0, pending.length - retained);
                if (pasted === null) onInput(text);
                else pasted += text;
                pending = pending.slice(pending.length - retained);
                break;
            }
        }
    };
}

export function terminalInterface(options) {
    if (!options.terminal) return createInterface(options);
    const source = options.input;
    const input = new PassThrough();
    input.isTTY = true;
    input.setRawMode = enabled => source.setRawMode(enabled);
    const rl = createInterface({ ...options, input });
    const decoder = new StringDecoder('utf8');
    const consume = bracketedPaste(text => input.write(text), text => {
        rl.line = rl.line.slice(0, rl.cursor) + text + rl.line.slice(rl.cursor);
        const cursor = rl.cursor + text.length;
        // An edit inside the buffer also updates Node's multiline history state.
        // Assigning line alone leaves that state stale on Node 24.
        rl.cursor = 0;
        rl.write(' ');
        rl.write(null, { ctrl: true, name: 'h' });
        rl.cursor = cursor;
        rl.prompt(true);
    });
    const onData = chunk => consume(decoder.write(chunk));
    const onEnd = () => { consume(decoder.end()); input.end(); };
    source.on('data', onData);
    source.once('end', onEnd);
    source.resume();
    options.output.write('\x1b[?2004h');
    rl.once('close', () => {
        source.off('data', onData);
        source.off('end', onEnd);
        source.pause();
        options.output.write('\x1b[?2004l');
    });
    return rl;
}
