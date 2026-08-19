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

	it("highlights role annotations as types, not as MIR keywords", () => {
		const source = [
			"    %r0: *int = alloca int",
			"    %r1: **int = alloca_place int",
			"    %r2: *int = load %r1",
			"    %r3: stack = stack_save",
			"    %r4: open *string = project <test>::cell::ref_mut#subscript:f3d0ec43(%p0)",
			"    %r5: (int) -> int = build_closure <test>::$lambda$1(%r3)",
		].join("\n");

		const tokens = highlightedTokens(source);
		expect(tokens).toEqual(expect.arrayContaining([
			["%r0", "tok-variableName"],
			["*", "tok-punctuation"],
			["int", "tok-typeName"],
			["alloca", "tok-keyword"],
			["alloca_place", "tok-keyword"],
			["load", "tok-keyword"],
			// A pseudo-type, and the qualifier of a yielded place: neither is a variable.
			["stack", "tok-typeName"],
			["open", "tok-keyword"],
			["string", "tok-typeName"],
		]));
		// `build_closure` still takes the callee that follows it, and the annotation before the
		// `=` must not have consumed that state.
		expect(tokens).toEqual(expect.arrayContaining([
			["<test>::$lambda$1", "tok-variableName"],
		]));
	});

	it("highlights a referenced callee as a single name", () => {
		const source = [
			"    drop string %r1 via std::Value<std::string>::drop#impl:1d429675",
			"    clone Probe %p0 to %p1 via <test>::std::Value<<test>::Probe>::clone#impl:a879cee3",
			"    invoke drop () -> int %r1 via <test>::$_ferlium_function_value_drop -> b1 error b2",
			"    drop A %r0 via %r4",
			"    %r4 = build_closure <test>::$lambda$1(%r3, dict(<test>::std::Value<(std::int,)>))",
		].join("\n");

		const tokens = highlightedTokens(source);
		expect(tokens).toEqual(expect.arrayContaining([
			["via", "tok-keyword"],
			["std::Value<std::string>::drop#impl:1d429675", "tok-variableName"],
			["<test>::std::Value<<test>::Probe>::clone#impl:a879cee3", "tok-variableName"],
			["<test>::$_ferlium_function_value_drop", "tok-variableName"],
			["%r4", "tok-variableName"],
			["b1", "tok-labelName"],
			["<test>::$lambda$1", "tok-variableName"],
		]));
	});
});
