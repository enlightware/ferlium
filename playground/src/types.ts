// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

/**
 * Return [[value]], throw if null.
 * @param value - Value of type T | null
 * @param message - An optional user message to send with the exception
 * @return value of type T or throw if value is null
 */
export function nonnull<T>(value: T | null, message: string | null = null): T {
	const userMessage = message !== null ? message : 'value is null';
	if (value === null) {
		throw new TypeError(`nonnull: ${userMessage}`);
	}
	return value;
}

/**
 * Return [[value]], throw if undefined.
 * @param value - Value of type T | undefined
 * @param message - An optional user message to send with the exception
 * @return value of type T or throw if value is undefined
 */
export function defined<T>(value: T | undefined, message: string | null = null): T {
	const userMessage = message !== null ? message : 'value is undefined';
	if (value === undefined) {
		throw new TypeError(`defined: ${userMessage}`);
	}
	return value;
}

export const executionModes = [
	{ value: "hir", label: "HIR" },
	{ value: "mir", label: "raw MIR" },
	{ value: "optimized-mir", label: "opt. MIR" },
	{ value: "physical-mir", label: "phy. MIR" },
	{ value: "wasm", label: "Wasm" },
] as const;

export type ExecutionMode = typeof executionModes[number]["value"];

export interface SourceRange {
	from: number;
	to: number;
}

export interface IrText {
	text: string;
	source_map: Array<SourceMapEntry>;
}

export interface SourceMapEntry extends SourceRange {
	source_from: number;
	source_to: number;
}

/** Whether two editor ranges intersect, treating a cursor as a point in the other range. */
export function rangesOverlap(left: SourceRange, right: SourceRange): boolean {
	if (left.from === left.to) {
		return right.from <= left.from && left.from <= right.to;
	}
	if (right.from === right.to) {
		return left.from <= right.from && right.from <= left.to;
	}
	return left.from < right.to && right.from < left.to;
}
