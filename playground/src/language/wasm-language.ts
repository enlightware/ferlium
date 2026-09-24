// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

import { LanguageSupport, StreamLanguage } from "@codemirror/language";

const definitionKeywords = new Set([
	"module", "func", "param", "result", "local", "type", "import", "export", "memory", "table",
	"elem", "global", "mut", "data", "start",
]);
const controlKeywords = new Set([
	"block", "loop", "if", "then", "else", "end", "br", "br_if", "br_table", "return", "call",
	"call_indirect", "return_call", "return_call_indirect", "unreachable", "nop", "select", "drop",
]);
const valueTypes = new Set(["i32", "i64", "f32", "f64", "v128", "funcref", "externref"]);

type WasmTokenizerState = {
	/// Nesting depth of `(; ... ;)` block comments, which may span lines.
	commentDepth: number;
};

/**
 * A small tokenizer for the flat Wasm text format printed by the backend inspection view.
 */
export const wasmLanguage = StreamLanguage.define({
	name: "Wasm text",
	startState(): WasmTokenizerState {
		return { commentDepth: 0 };
	},
	token(stream, state) {
		if (state.commentDepth > 0) {
			while (!stream.eol()) {
				if (stream.match("(;")) {
					state.commentDepth += 1;
				} else if (stream.match(";)")) {
					state.commentDepth -= 1;
					if (state.commentDepth === 0) {
						break;
					}
				} else {
					stream.next();
				}
			}
			return "blockComment";
		}
		if (stream.eatSpace()) {
			return null;
		}
		if (stream.match(";;")) {
			stream.skipToEnd();
			return "lineComment";
		}
		if (stream.match("(;")) {
			state.commentDepth = 1;
			return "blockComment";
		}
		if (stream.match(/"(?:[^"\\]|\\.)*"/)) {
			return "string";
		}
		// Identifiers are either plain or quoted, the latter holding names such as `$"ide::f"`.
		if (stream.match(/\$"(?:[^"\\]|\\.)*"/) || stream.match(/\$[^\s()"]+/)) {
			return "variableName";
		}
		// Custom annotations, such as the host data sections listed after the module.
		if (stream.match(/@[A-Za-z0-9_.]+/)) {
			return "meta";
		}
		if (stream.match(/[()]/)) {
			return "punctuation";
		}
		if (stream.match(/[-+]?(?:0x[0-9a-fA-F_.p+-]+|[0-9][0-9_]*(?:\.[0-9_]*)?(?:[eE][-+]?[0-9]+)?|inf|nan(?::0x[0-9a-fA-F]+)?)(?=[\s()]|$)/)) {
			return "number";
		}
		const word = stream.match(/[A-Za-z_][A-Za-z0-9_.=/]*/);
		if (!Array.isArray(word)) {
			stream.next();
			return null;
		}
		const text = word[0];
		if (/^(?:offset|align)=/.test(text)) {
			return "modifier";
		}
		if (definitionKeywords.has(text)) {
			return "definitionKeyword";
		}
		if (controlKeywords.has(text)) {
			return "controlKeyword";
		}
		if (valueTypes.has(text)) {
			return "typeName";
		}
		if (text.includes(".")) {
			return "keyword";
		}
		return "variableName";
	},
});

export function wasmLanguageExtension() {
	return new LanguageSupport(wasmLanguage);
}
