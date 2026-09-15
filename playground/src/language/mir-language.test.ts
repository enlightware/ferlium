// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

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
	it.each([
		"runtime_alloc int size 8 align 8",
		"runtime_dealloc %r0",
		"address_offset %r0 by 8",
		"address_offset_place %r0 by 8",
		"move_bytes int %r0 to %r1 size 8",
		"variant_payload from %r0",
		"build_dictionary dict(m0:i0) %p0",
		"build_subscript_evidence subscript(m0:s0) capturing (%p0)",
		"clone_subscript_env %r0",
		"drop_subscript_env %r0",
		"borrow_subscript_member mut from %r0",
		"extract_payload_indirection %r0",
		"is_initialized %r0",
		"replace %r0 to %r1 using %p0",
		"switch_variant %r0 [0 => b1, 1 => b2] default b3",
		'invariant_failure "invalid variant tag"',
	])("highlights the instruction in %s", (source) => {
		expect(highlightedTokens(source)[0]).toEqual([source.split(" ")[0], "tok-keyword"]);
	});

	it("highlights physical layout and hidden-evidence qualifiers", () => {
		const tokens = highlightedTokens([
			"%r0: *int = runtime_alloc int size 8 align 8",
			"%r1: *int = address_offset %r0 by 8",
			"%r2 = variant Some storage via %p0 layout via %p1",
			"clone T %r0 to %r1 via %r3 with (%p0, %p1)",
			"switch_variant %r4 [0 => b1] default b2",
		].join("\n"));
		for (const keyword of ["size", "align", "by", "storage", "layout", "with", "default"]) {
			expect(tokens).toContainEqual([keyword, "tok-keyword"]);
		}
		expect(tokens).toContainEqual(["=>", "tok-punctuation"]);
		expect(tokens).toContainEqual(["b2", "tok-labelName"]);
	});

	it.each([
		"cell",
		"<test>::cell::ref_mut#subscript:f3d0ec43",
		"std::cell#spec:[(int) -> int]",
		"%r1",
	])("highlights project callee %s separately from its arguments", (callee) => {
		const tokens = highlightedTokens(`%r0: open *int = project ${callee}(%p0, %p1)`);
		expect(tokens).toContainEqual(["project", "tok-keyword"]);
		expect(tokens).toContainEqual([callee, "tok-variableName"]);
		expect(tokens).toContainEqual(["(", "tok-punctuation"]);
		expect(tokens).toContainEqual(["%p0", "tok-variableName"]);
		expect(tokens).toContainEqual(["%p1", "tok-variableName"]);
	});

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

	it("highlights symbolic evidence operands as single names", () => {
		const subscript = "subscript(ide::{ x: std::int, y: std::int }.y)";
		const dictionary = "dict(std::Num<std::int>)";
		const nestedDictionary = "dict(std::Value<(std::int) -> std::int>)";
		const source = `    call ide::l2(${subscript}, ${dictionary}, ${nestedDictionary}, %r0)`;

		const tokens = highlightedTokens(source);
		expect(tokens).toContainEqual([subscript, "tok-variableName"]);
		expect(tokens).toContainEqual([dictionary, "tok-variableName"]);
		expect(tokens).toContainEqual([nestedDictionary, "tok-variableName"]);
		expect(tokens).not.toContainEqual(["int", "tok-typeName"]);
	});
});
