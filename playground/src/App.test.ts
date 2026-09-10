// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
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
	},
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
			.toEqual(["HIR", "raw MIR", "opt. MIR", "phy. MIR"]);
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

	it("shows physical preparation errors in the IR pane", async () => {
		const app = mountApp();
		// wasm-bindgen propagates Result::Err(String) as a bare JavaScript string.
		compiler.physicalMirText.mockImplementationOnce(() => { throw "unsupported native ABI"; });
		await selects(app).executionMode.setValue("phy. MIR");
		await selects(app).sample.setValue("Factorial");
		await vi.waitFor(() => expect(irText()).toContain("Unable to prepare MIR: unsupported native ABI"));
	});
});
