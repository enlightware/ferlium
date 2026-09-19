// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

import { highlightTree, classHighlighter } from "@lezer/highlight";
import { describe, expect, it } from "vitest";
import { wasmLanguage } from "./wasm-language";

function highlightedTokens(source: string): Array<[string, string]> {
	const tokens: Array<[string, string]> = [];
	highlightTree(wasmLanguage.parser.parse(source), classHighlighter, (from, to, classes) => {
		tokens.push([source.slice(from, to), classes]);
	});
	return tokens;
}

describe("Wasm language highlighting", () => {
	it("highlights definitions, quoted names and instructions", () => {
		const tokens = highlightedTokens(
			"(func $\"ide::triple\" (;3;) (type 2) (param i32) (result i32)\n"
			+ "  local.get 0\n  i32.const 3\n  i32.mul\n  call $\"ide::helper\" ;; tail\n)",
		);
		expect(tokens).toContainEqual(["func", "tok-keyword"]);
		expect(tokens).toContainEqual(["$\"ide::triple\"", "tok-variableName"]);
		expect(tokens).toContainEqual(["(;3;)", "tok-comment"]);
		expect(tokens).toContainEqual(["i32", "tok-typeName"]);
		expect(tokens).toContainEqual(["i32.mul", "tok-keyword"]);
		expect(tokens).toContainEqual(["3", "tok-number"]);
		expect(tokens).toContainEqual([";; tail", "tok-comment"]);
	});
});
