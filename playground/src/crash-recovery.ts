// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

// A Rust panic aborts the Rust instance mid-call, leaving it unusable. Its panic hook dispatches
// `panicEvent` first, upon which the playground reloads the page to get a fresh instance, carrying
// its state across. Engine traps, such as a stack overflow, abort it without a panic, so the places
// where exceptions end up report them as the same event.

import type { ExecutionMode } from "./types";

/** Playground state carried across the reload that replaces a crashed Rust instance. */
export interface CrashState {
	code: string;
	executionMode: ExecutionMode;
	annotationMode: string;
	message: string;
	/** Whether to compile the restored code; false when doing so crashed again after a reload. */
	compile: boolean;
}

const crashStateKey = "ferlium-playground-crash-state";

/** Dispatched on the window by the panic hook of script-api, with the message as detail. */
export const panicEvent = "ferlium-panic";

/** If `error` is an engine trap that aborted the Rust instance, report it as a panic. */
export function reportEngineTrap(error: unknown) {
	// Firefox reports engine stack overflows as a non-standard InternalError.
	if (error instanceof WebAssembly.RuntimeError || error instanceof RangeError
		|| (error instanceof Error && error.name === "InternalError")) {
		window.dispatchEvent(new CustomEvent(panicEvent, { detail: String(error) }));
	}
}

/** Save the state for the next page load; returns whether it could be saved. */
export function saveCrashState(state: CrashState): boolean {
	try {
		sessionStorage.setItem(crashStateKey, JSON.stringify(state));
		return true;
	} catch {
		return false;
	}
}

/** Take the state saved before the reload, if this page load replaces a crashed instance. */
export function takeCrashState(): CrashState | undefined {
	try {
		const state = sessionStorage.getItem(crashStateKey);
		sessionStorage.removeItem(crashStateKey);
		return state === null ? undefined : JSON.parse(state) as CrashState;
	} catch {
		return undefined;
	}
}

export function reloadPage() {
	window.location.reload();
}
