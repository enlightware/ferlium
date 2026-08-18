// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
import { highlightTree, classHighlighter } from "@lezer/highlight";
import { describe, expect, it } from "vitest";
import { mirLanguage } from "./mir-language";

function highlightedTokens(source: string): Array<[string, string]> {
	const tokens: Array<[string, string]> = [];
	highlightTree(mirLanguage.parser.parse(source), classHighlighter, (from, to, classes) => {
		tokens.push([source.slice(from, to), classes]);
	});
	return tokens;
}

describe("MIR language highlighting", () => {
	it("assigns source-style semantic tags to real MIR forms", () => {
		const source = [
			"// comment",
			"fn std::map#spec:[(int) -> int](%p0: @arg let int, %p1: @ret bool):",
			"  @c0: int = 42",
			"  b0:",
			"    %r0 = alloca int",
			"    store @c0 to %r0",
			"    condbr %r0, b1, b2",
			"  b1:",
			"    call std::Num<std::int>::from_int#impl:25eabc6b(%r0)",
			"    call std::Value<[int]>::drop#impl:4499dda8#spec:[int](%r0)",
			"    call std::Value<std::Buffer<std::int>>::clone#impl:62cf4a1c(%r0)",
			"    call std::Value<std::Buffer<std::int>>::eq#impl:62cf4a1c(%r0)",
			"    call std::clone(%r0)",
			"    call std::map#spec:[(int) -> int](%r0)",
			"    invoke call std::Value<[int]>::drop#impl:4499dda8(%r0) -> b2 error b3",
			"    comp_eq %r0 true",
			"    br b3",
		].join("\n");

		const tokens = highlightedTokens(source);
		expect(tokens).toEqual(expect.arrayContaining([
			["// comment", "tok-comment"],
			["fn", "tok-keyword"],
			["std::map#spec:[(int) -> int]", "tok-variableName"],
			["@arg", "tok-keyword"],
			["int", "tok-typeName"],
			["42", "tok-number"],
			["b0", "tok-labelName"],
			["%r0", "tok-variableName"],
			["alloca", "tok-keyword"],
			["condbr", "tok-keyword"],
			["std::Num<std::int>::from_int#impl:25eabc6b", "tok-variableName"],
			["std::Value<[int]>::drop#impl:4499dda8#spec:[int]", "tok-variableName"],
			["std::Value<std::Buffer<std::int>>::clone#impl:62cf4a1c", "tok-variableName"],
			["std::Value<std::Buffer<std::int>>::eq#impl:62cf4a1c", "tok-variableName"],
			["std::Value<[int]>::drop#impl:4499dda8", "tok-variableName"],
			["std::map#spec:[(int) -> int]", "tok-variableName"],
			["true", "tok-bool"],
			["b3", "tok-labelName"],
		]));
		expect(tokens.filter(([token, classes]) => (
			token === "std::map#spec:[(int) -> int]" && classes === "tok-variableName"
		))).toHaveLength(2);
	});
});
