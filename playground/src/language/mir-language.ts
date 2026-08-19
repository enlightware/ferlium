// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
import { LanguageSupport, StreamLanguage } from "@codemirror/language";

const definitionKeywords = new Set(["fn", "let", "ref", "mut"]);
const controlKeywords = new Set([
	"br", "condbr", "invoke", "ret", "yield", "propagate_error", "failure_during_cleanup",
]);
const operationKeywords = new Set([
	"alloca", "alloca_place", "call", "project", "end_project", "comp_eq", "load",
	"subfield", "dict_entry", "subscript_member", "build_subscript", "variant", "build_array",
	"extract_tag", "store", "clear", "memcpy", "move", "stack_save", "stack_restore",
	"check_call_depth", "check_fuel", "drop", "clone", "build_closure", "clone_closure_env",
	"drop_closure_env",
]);
const contextualKeywords = new Set([
	"arg", "owned", "extra", "using", "from", "to", "via", "capturing", "error",
]);
const primitiveTypes = new Set(["bool", "char", "float", "int", "never", "string", "unit"]);

type MirTokenizerState = {
	nextTokenIsFunctionName: boolean;
	/// Set between a defining `%rN` and its `=`, where the text is a role annotation rather than
	/// MIR syntax. `%r0: fn = ...` must not put the tokenizer into function-name mode, and a role
	/// word like `stack` names a pseudo-type, not a variable.
	inRoleAnnotation: boolean;
};

/**
 * Advance the stream over one callable name, which can carry `::` path segments, `<...>` type
 * arguments, `[...]` specialization arguments and `#tag:hash` suffixes, all of which may contain
 * spaces, parentheses and `->` arrows.
 *
 * A name is followed either by its argument list (`call`, `fn`, `build_closure`) or, where the
 * callee is only referenced (`drop ... via <callee>`), by a space or the end of the line.
 */
function skipCallableName(stream: { string: string; pos: number }): boolean {
	const start = stream.pos;
	let squareDepth = 0;
	let angleDepth = 0;
	for (let position = start; position < stream.string.length; position += 1) {
		const character = stream.string[position];
		if (character === "[") {
			squareDepth += 1;
		} else if (character === "]") {
			squareDepth = Math.max(0, squareDepth - 1);
		} else if (character === "<") {
			angleDepth += 1;
		} else if (character === ">" && stream.string[position - 1] !== "-") {
			angleDepth = Math.max(0, angleDepth - 1);
		} else if (
			squareDepth === 0
			&& angleDepth === 0
			&& (character === "(" || character === " " || character === "\t" || character === ",")
		) {
			stream.pos = position;
			return position > start;
		}
	}
	stream.pos = stream.string.length;
	return stream.pos > start;
}

/**
 * Advance over an identifier with a balanced parenthesized payload as one opaque name. MIR uses
 * this shape for symbolic operands such as dictionaries and subscripts. Their readable identities
 * may contain types, but that type-shaped text is part of the name rather than a type annotation
 * at the use site. Keeping the rule structural also covers future symbolic operand kinds.
 */
function skipOpaqueParenthesizedName(stream: { string: string; pos: number }): boolean {
	const prefix = /^[A-Za-z_][A-Za-z0-9_]*\(/.exec(stream.string.slice(stream.pos))?.[0];
	if (prefix === undefined) {
		return false;
	}
	let depth = 1;
	for (let position = stream.pos + prefix.length; position < stream.string.length; position += 1) {
		const character = stream.string[position];
		if (character === "(") {
			depth += 1;
		} else if (character === ")") {
			depth -= 1;
			if (depth === 0) {
				stream.pos = position + 1;
				return true;
			}
		}
	}
	return false;
}

/**
 * A deliberately small tokenizer for rendered MIR.
 *
 * MIR is an inspection view, so this favors clear, stable token classes over a full grammar. The
 * returned semantic tags reuse the source-language tags where MIR has an equivalent form, and
 * therefore follow its existing light color convention.
 */
export const mirLanguage = StreamLanguage.define({
	name: "Ferlium MIR",
	startState(): MirTokenizerState {
		return { nextTokenIsFunctionName: false, inRoleAnnotation: false };
	},
	blankLine(state) {
		state.nextTokenIsFunctionName = false;
		state.inRoleAnnotation = false;
	},
	token(stream, state) {
		if (stream.eatSpace()) {
			return null;
		}
		if (state.nextTokenIsFunctionName) {
			state.nextTokenIsFunctionName = false;
			if (skipCallableName(stream)) {
				return "variableName";
			}
		}
		if (stream.match("//")) {
			stream.skipToEnd();
			return "lineComment";
		}
		if (stream.match(/"(?:[^"\\]|\\.)*"/)) {
			return "string";
		}
		if (stream.match(/#[A-Za-z_]+:[0-9a-f]+/) || stream.match(/#[A-Za-z_]+:(?=\[)/)) {
			return "meta";
		}
		if (stream.match(/@(?:arg|extra|ret)\b/)) {
			return "modifier";
		}
		const register = stream.match(/%r[0-9]+(?=:)/);
		if (Array.isArray(register)) {
			state.inRoleAnnotation = true;
			return "variableName";
		}
		if (stream.match(/%[pr][0-9]+/) || stream.match(/@c[0-9]+/)) {
			return "variableName";
		}
		if (stream.match(/b[0-9]+\b/)) {
			return "labelName";
		}
		if (stream.match(/-?[0-9]+(?:\.[0-9]+)?/)) {
			return "number";
		}
		if (skipOpaqueParenthesizedName(stream)) {
			return "variableName";
		}
		if (stream.match("=")) {
			state.inRoleAnnotation = false;
			return "punctuation";
		}
		// `*` only ever appears in a role annotation, where it is the pointer marker of `*int` or
		// the double indirection of an `alloca_place` slot's `**int`.
		if (stream.match(/->|::|[*()[\]{},:<>]/)) {
			return "punctuation";
		}
		const word = stream.match(/[A-Za-z_][A-Za-z0-9_]*/);
		if (!Array.isArray(word)) {
			stream.next();
			return null;
		}
		const text = word[0];
		if (state.inRoleAnnotation) {
			// `open` qualifies the yielded place of a `project`; everything else in this position
			// is a type name or a pseudo-type such as `stack`.
			return text === "open" ? "modifier" : "typeName";
		}
		if (definitionKeywords.has(text)) {
			if (text === "fn") {
				state.nextTokenIsFunctionName = true;
			}
			return "definitionKeyword";
		}
		if (controlKeywords.has(text)) {
			return "controlKeyword";
		}
		if (operationKeywords.has(text)) {
			if (text === "call" || text === "build_closure") {
				state.nextTokenIsFunctionName = true;
			}
			return "keyword";
		}
		if (contextualKeywords.has(text)) {
			// `via` introduces the callee of a drop or clone, which is a bare name with no argument
			// list of its own.
			if (text === "via") {
				state.nextTokenIsFunctionName = true;
			}
			return "modifier";
		}
		if (text === "true" || text === "false") {
			return "bool";
		}
		if (primitiveTypes.has(text) || /^[A-Z]/.test(text)) {
			return "typeName";
		}
		return "variableName";
	},
});

export function mirLanguageExtension() {
	return new LanguageSupport(mirLanguage);
}
