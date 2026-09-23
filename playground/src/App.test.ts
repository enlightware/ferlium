// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

import { mount, type VueWrapper } from "@vue/test-utils";
import { afterEach, describe, expect, it, vi } from "vitest";

const compiler = vi.hoisted(() => {
	let source = "";
	return {
		source: () => source,
		compile: vi.fn((newSource: string) => {
			source = newSource;
			return { succeeded: true, diagnostics: [] };
		}),
		mirText: vi.fn(() => ({ text: `MIR of ${source}`, source_map: [] })),
		physicalMirText: vi.fn(() => ({ text: `Physical MIR of ${source}`, source_map: [] })),
		wasmText: vi.fn(() => ({ text: `Wasm of ${source}`, source_map: [] })),
		runHir: vi.fn(),
		runMir: vi.fn(),
		runPhysicalMir: vi.fn(() => ({
			html_message: () => "42: int",
			error_data: () => undefined,
		})),
	};
});

vi.mock("./compiler-api", () => ({
	DiagnosticSeverity: { Error: 0, Warning: 1 },
	PlaygroundCompiler: class {
		set_allow_experimental() {}
		compile(source: string) {
			return compiler.compile(source);
		}
		get_annotations() { return []; }
		get_light_annotations() { return []; }
		run_expr() { return compiler.runHir(); }
		run_expr_mir(optimized: boolean) { return compiler.runMir(optimized); }
		run_expr_physical_mir() { return compiler.runPhysicalMir(); }
		mir_text() { return compiler.mirText(); }
		physical_mir_text() { return compiler.physicalMirText(); }
		wasm_text() { return compiler.wasmText(); }
	},
}));

vi.mock("./crash-recovery", async importOriginal => ({
	...await importOriginal<typeof import("./crash-recovery")>(),
	reloadPage: vi.fn(),
}));

vi.mock("./annotation-extension", () => ({
	renderAnnotationsPlugin: [],
	setAnnotations: vi.fn(),
}));

vi.mock("./language/language-extension", () => ({
	languageExtension: () => [],
}));

vi.mock("./position-panel-extension", () => ({
	positionPanel: () => [],
}));

import App from "./App.vue";
import { panicEvent, reloadPage, type CrashState } from "./crash-recovery";

const crashStateKey = "ferlium-playground-crash-state";

function savedCrashState(): CrashState {
	return JSON.parse(sessionStorage.getItem(crashStateKey) ?? "null") as CrashState;
}

/** Simulate a Rust panic: the panic hook dispatches the event, then the instance traps. */
function panic(message: string): never {
	window.dispatchEvent(new CustomEvent(panicEvent, { detail: message }));
	throw new WebAssembly.RuntimeError("unreachable");
}

function editorText(): string | undefined {
	return document.body.querySelector(".source-pane .cm-content")?.textContent ?? undefined;
}

/** The toolbar exposes the execution mode, the code sample and the annotation mode, in that order. */
function selects(wrapper: VueWrapper) {
	const [executionMode, sample] = wrapper.findAll("select");
	return { executionMode: executionMode!, sample: sample! };
}

function irText(): string | undefined {
	return document.body.querySelector(".ir-panel .cm-content")?.textContent ?? undefined;
}

describe("App", () => {
	let wrapper: VueWrapper | undefined;

	afterEach(() => {
		sessionStorage.clear();
		vi.mocked(reloadPage).mockClear();
		wrapper?.unmount();
		wrapper = undefined;
		document.body.replaceChildren();
	});

	function mountApp(): VueWrapper {
		wrapper = mount(App, { attachTo: document.body });
		return wrapper;
	}

	it("shows no IR pane while the HIR interpreter is selected", async () => {
		const app = mountApp();
		await selects(app).sample.setValue("Factorial");
		await vi.waitFor(() => {
			expect(compiler.compile).toHaveBeenCalledWith(expect.stringContaining("fn factorial"));
		});
		expect(compiler.mirText).not.toHaveBeenCalled();
		expect(document.body.querySelector(".ir-panel")).toBe(null);
	});

	it("keeps the MIR pane visible while the source has no MIR to show", async () => {
		const app = mountApp();
		// The source is still empty, so no MIR exists yet: the pane must be there all the same, so
		// that it does not appear and disappear as the source alternates between valid and invalid.
		await selects(app).executionMode.setValue("raw MIR");
		await vi.waitFor(() => {
			expect(document.body.querySelector(".ir-panel")).not.toBe(null);
		});
		expect(irText()).toBe("");
	});

	it("refreshes the MIR when the source comes from the code sample selector", async () => {
		const app = mountApp();
		await selects(app).executionMode.setValue("raw MIR");
		await selects(app).sample.setValue("Factorial");
		await vi.waitFor(() => {
			expect(irText()).toContain("fn factorial");
		});

		await selects(app).sample.setValue("Is even");
		await vi.waitFor(() => {
			expect(irText()).toContain("fn is_even");
		});
	});

	it("inspects and executes physical MIR without falling back", async () => {
		const app = mountApp();
		expect(selects(app).executionMode.findAll("option:not([disabled])").map(option => option.text()))
			.toEqual(["HIR", "raw MIR", "opt. MIR", "phy. MIR", "Wasm"]);
		await selects(app).executionMode.setValue("phy. MIR");
		await selects(app).sample.setValue("Factorial");
		await vi.waitFor(() => expect(irText()).toContain("Physical MIR of fn factorial"));
		await app.get(".execution-controls button").trigger("click");
		expect(compiler.runPhysicalMir).toHaveBeenCalledOnce();
		expect(compiler.runHir).not.toHaveBeenCalled();
		expect(compiler.runMir).not.toHaveBeenCalled();
		expect(app.text()).toContain("42: int");
		await selects(app).executionMode.setValue("opt. MIR");
		await vi.waitFor(() => expect(irText()).not.toContain("Physical MIR"));
		await app.get(".execution-controls button").trigger("click");
		expect(compiler.runMir).toHaveBeenCalledWith(true);
	});

	it("inspects Wasm without executing any interpreter", async () => {
		for (const run of [compiler.runHir, compiler.runMir, compiler.runPhysicalMir]) {
			run.mockClear();
		}
		const app = mountApp();
		await selects(app).executionMode.setValue("Wasm");
		await selects(app).sample.setValue("Factorial");
		await vi.waitFor(() => expect(irText()).toContain("Wasm of fn factorial"));
		await app.get(".execution-controls button").trigger("click");
		expect(compiler.runHir).not.toHaveBeenCalled();
		expect(compiler.runMir).not.toHaveBeenCalled();
		expect(compiler.runPhysicalMir).not.toHaveBeenCalled();
		expect(app.text()).toContain("Wasm execution is not available in the playground yet");
	});

	it("shows Wasm generation errors in the IR pane", async () => {
		const app = mountApp();
		compiler.wasmText.mockImplementationOnce(() => { throw "unsupported Wasm storage type"; });
		await selects(app).executionMode.setValue("Wasm");
		await selects(app).sample.setValue("Factorial");
		await vi.waitFor(() => expect(irText()).toContain("Unable to generate Wasm: unsupported Wasm storage type"));
	});

	it("shows physical preparation errors in the IR pane", async () => {
		const app = mountApp();
		// wasm-bindgen propagates Result::Err(String) as a bare JavaScript string.
		compiler.physicalMirText.mockImplementationOnce(() => { throw "unsupported native ABI"; });
		await selects(app).executionMode.setValue("phy. MIR");
		await selects(app).sample.setValue("Factorial");
		await vi.waitFor(() => expect(irText()).toContain("Unable to prepare MIR: unsupported native ABI"));
	});

	it("reloads with the playground state when the Rust instance crashes", async () => {
		const app = mountApp();
		await selects(app).executionMode.setValue("opt. MIR");
		await selects(app).sample.setValue("Factorial");
		compiler.runMir.mockImplementationOnce(() => panic("panicked at src/lib.rs:1:1:\nboom"));
		await app.get(".execution-controls button").trigger("click");
		expect(reloadPage).toHaveBeenCalledOnce();
		expect(savedCrashState()).toEqual({
			code: expect.stringContaining("fn factorial"),
			executionMode: "optimized-mir",
			annotationMode: "light",
			message: "The compiler crashed and the playground was reloaded: panicked at src/lib.rs:1:1:\nboom",
			compile: true,
		});
	});

	it("reloads with the playground state when the engine traps without a panic", async () => {
		const app = mountApp();
		compiler.compile.mockImplementationOnce(() => { throw new RangeError("Maximum call stack size exceeded"); });
		await selects(app).sample.setValue("Factorial");
		expect(reloadPage).toHaveBeenCalledOnce();
		expect(savedCrashState()).toMatchObject({
			code: expect.stringContaining("fn factorial"),
			message: "The compiler crashed and the playground was reloaded: RangeError: Maximum call stack size exceeded",
			compile: true,
		});
	});

	it("reloads when IR generation traps", async () => {
		const app = mountApp();
		compiler.wasmText.mockImplementationOnce(() => { throw new RangeError("Maximum call stack size exceeded"); });
		await selects(app).executionMode.setValue("Wasm");
		await selects(app).sample.setValue("Factorial");
		await vi.waitFor(() => expect(reloadPage).toHaveBeenCalledOnce());
		expect(savedCrashState()).toMatchObject({ executionMode: "wasm", compile: true });
	});

	it("restores the playground state after a crash", async () => {
		sessionStorage.setItem(crashStateKey, JSON.stringify({
			code: "fn restored() {}",
			executionMode: "physical-mir",
			annotationMode: "full",
			message: "The compiler crashed and the playground was reloaded: boom",
			compile: true,
		}));
		const app = mountApp();
		expect(editorText()).toBe("fn restored() {}");
		expect(compiler.compile).toHaveBeenLastCalledWith("fn restored() {}");
		expect(selects(app).executionMode.element.value).toBe("phy. MIR");
		await vi.waitFor(() => expect(irText()).toContain("Physical MIR of fn restored"));
		expect(app.text()).toContain("The compiler crashed and the playground was reloaded: boom");
		expect(sessionStorage.getItem(crashStateKey)).toBe(null);
	});

	it("defers compiling restored code whose compilation crashed again", () => {
		sessionStorage.setItem(crashStateKey, JSON.stringify({
			code: "fn crashing() {}",
			executionMode: "hir",
			annotationMode: "light",
			message: "boom",
			compile: true,
		}));
		compiler.compile.mockImplementationOnce(() => panic("boom"));
		mountApp();
		expect(reloadPage).toHaveBeenCalledOnce();
		expect(savedCrashState()).toMatchObject({ code: "fn crashing() {}", compile: false });

		wrapper?.unmount();
		document.body.replaceChildren();
		compiler.compile.mockClear();
		const app = mountApp();
		expect(editorText()).toBe("fn crashing() {}");
		expect(compiler.compile).not.toHaveBeenCalled();
		expect(app.text()).toContain("it will be compiled at the next edit");
	});
});
