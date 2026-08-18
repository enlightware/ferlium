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
		run_expr() { return undefined; }
		run_expr_mir() { return undefined; }
		mir_text() { return compiler.mirText(); }
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
		await selects(app).executionMode.setValue("MIR");
		await vi.waitFor(() => {
			expect(document.body.querySelector(".ir-panel")).not.toBe(null);
		});
		expect(irText()).toBe("");
	});

	it("refreshes the MIR when the source comes from the code sample selector", async () => {
		const app = mountApp();
		await selects(app).executionMode.setValue("MIR");
		await selects(app).sample.setValue("Factorial");
		await vi.waitFor(() => {
			expect(irText()).toContain("fn factorial");
		});

		await selects(app).sample.setValue("Is even");
		await vi.waitFor(() => {
			expect(irText()).toContain("fn is_even");
		});
	});
});
