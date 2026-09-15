// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

import { ExternalTokenizer, type InputStream } from "@lezer/lr";
import { Identifier, LoopLabel } from "./language.grammar.terms";

interface Scalar {
	value: string;
	width: number;
}

const unicodeLetter = /^\p{L}$/u;
const unicodeDecimalDigit = /^\p{Nd}$/u;

function scalarAt(input: InputStream, offset: number): Scalar | null {
	const first = input.peek(offset);
	if (first < 0) return null;
	if (first >= 0xd800 && first <= 0xdbff) {
		const second = input.peek(offset + 1);
		if (second >= 0xdc00 && second <= 0xdfff) {
			return {
				value: String.fromCodePoint(
					((first - 0xd800) << 10) + second - 0xdc00 + 0x10000,
				),
				width: 2,
			};
		}
	}
	return { value: String.fromCharCode(first), width: 1 };
}

function isIdentifierStart(scalar: Scalar): boolean {
	return scalar.value === "_" || unicodeLetter.test(scalar.value);
}

function isIdentifierContinue(scalar: Scalar): boolean {
	return isIdentifierStart(scalar) || unicodeDecimalDigit.test(scalar.value);
}

function hasAsciiWord(input: InputStream, word: string): boolean {
	for (let i = 0; i < word.length; i++) {
		if (input.peek(i) !== word.charCodeAt(i)) return false;
	}
	const next = scalarAt(input, word.length);
	return next === null || !isIdentifierContinue(next);
}

export const unicodeIdentifiers = new ExternalTokenizer((input) => {
	let offset = 0;
	let token = Identifier;

	if (input.next === 39) {
		token = LoopLabel;
		offset = 1;
	} else if (input.next === 114 && input.peek(1) === 35) {
		offset = 2;
	} else if (input.next === 102 && input.peek(1) === 34) {
		// Let the built-in string token consume formatted strings.
		return;
	} else if (hasAsciiWord(input, "true") || hasAsciiWord(input, "false")) {
		// The grammar gives boolean literals their own token.
		return;
	}

	let scalar = scalarAt(input, offset);
	if (scalar === null || !isIdentifierStart(scalar)) return;
	offset += scalar.width;
	while ((scalar = scalarAt(input, offset)) !== null && isIdentifierContinue(scalar)) {
		offset += scalar.width;
	}

	input.advance(offset);
	input.acceptToken(token);
});
