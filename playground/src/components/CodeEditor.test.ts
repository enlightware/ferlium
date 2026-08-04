// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
import { mount, type VueWrapper } from "@vue/test-utils";
import { afterEach, beforeEach, describe, expect, it, vi } from "vitest";

const compiler = vi.hoisted(() => ({
	compile: vi.fn(),
	getAnnotations: vi.fn(() => []),
	getLightAnnotations: vi.fn(() => []),
	runExpr: vi.fn(),
}));

vi.mock("../compiler-api", () => ({
	DiagnosticSeverity: {
		Error: 0,
		Warning: 1,
	},
	PlaygroundCompiler: class {
		set_allow_experimental() {}
		compile(source: string) {
			return compiler.compile(source);
		}
		get_annotations() {
			return compiler.getAnnotations();
		}
		get_light_annotations() {
			return compiler.getLightAnnotations();
		}
		run_expr() {
			return compiler.runExpr();
		}
	},
}));

vi.mock("../annotation-extension", () => ({
	renderAnnotationsPlugin: [],
	setAnnotations: vi.fn(),
}));

vi.mock("../language/language-extension", () => ({
	languageExtension: () => [],
}));

vi.mock("../position-panel-extension", () => ({
	positionPanel: () => [],
}));

import CodeEditor from "./CodeEditor.vue";

type ExposedCodeEditor = {
	setText(source: string): void;
	runCode(): unknown;
};

function editor(wrapper: VueWrapper): ExposedCodeEditor {
	return wrapper.vm as unknown as ExposedCodeEditor;
}

describe("CodeEditor", () => {
	let wrapper: VueWrapper | undefined;

	beforeEach(() => {
		compiler.compile.mockReset();
		compiler.getAnnotations.mockClear();
		compiler.getLightAnnotations.mockClear();
		compiler.runExpr.mockReset();
	});

	afterEach(() => {
		wrapper?.unmount();
		wrapper = undefined;
		document.body.replaceChildren();
	});

	it("keeps warning-only compilations runnable and displays a warning", async () => {
		const source = "fn value() -> int { return 1; 999 }";
		const from = source.indexOf("999");
		compiler.compile.mockReturnValue({
			succeeded: true,
			diagnostics: [{
				file: "<ide>",
				from,
				to: from + 3,
				severity: 1,
				text: "unreachable code",
			}],
		});
		const result = { error_data: () => undefined };
		compiler.runExpr.mockReturnValue(result);

		const mounted = mount(CodeEditor, {
			attachTo: document.body,
			props: { annotationMode: "none" },
		});
		wrapper = mounted;
		editor(mounted).setText(source);

		await vi.waitFor(() => {
			expect(mounted.find(".cm-lintRange-warning").exists()).toBe(true);
		});
		expect(mounted.find(".cm-lintRange-error").exists()).toBe(false);
		expect(mounted.emitted("setRunAvailability")?.at(-1)).toEqual([true]);
		expect(editor(mounted).runCode()).toBe(result);
	});

	it("displays multiple diagnostics from one compilation", async () => {
		const source = "fn value(x) { if x == 0 { loop {}; 1 } else { loop {}; 2 } }";
		const first = source.indexOf("1");
		const second = source.indexOf("2");
		compiler.compile.mockReturnValue({
			succeeded: true,
			diagnostics: [
				{
					file: "<ide>",
					from: first,
					to: first + 1,
					severity: 1,
					text: "unreachable code",
				},
				{
					file: "<ide>",
					from: second,
					to: second + 1,
					severity: 1,
					text: "unreachable code",
				},
			],
		});

		const mounted = mount(CodeEditor, {
			attachTo: document.body,
			props: { annotationMode: "none" },
		});
		wrapper = mounted;
		editor(mounted).setText(source);

		await vi.waitFor(() => {
			expect(mounted.findAll(".cm-lintRange-warning")).toHaveLength(2);
		});
	});

	it("disables execution and displays an error after failed compilation", async () => {
		const source = "fn value() -> bool { 1 }";
		const from = source.indexOf("1");
		compiler.compile.mockReturnValue({
			succeeded: false,
			diagnostics: [{
				file: "<ide>",
				from,
				to: from + 1,
				severity: 0,
				text: "expected bool, found int",
			}],
		});

		const mounted = mount(CodeEditor, {
			attachTo: document.body,
			props: { annotationMode: "none" },
		});
		wrapper = mounted;
		editor(mounted).setText(source);

		await vi.waitFor(() => {
			expect(mounted.find(".cm-lintRange-error").exists()).toBe(true);
		});
		expect(mounted.find(".cm-lintRange-warning").exists()).toBe(false);
		expect(mounted.emitted("setRunAvailability")?.at(-1)).toEqual([false]);
	});
});
