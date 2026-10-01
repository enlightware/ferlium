// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

import { mount, type VueWrapper } from "@vue/test-utils";
import { afterEach, describe, expect, it, vi } from "vitest";
import { EditorView } from "@codemirror/view";
import IrViewer from "./IrViewer.vue";

describe("IrViewer", () => {
	let wrapper: VueWrapper | undefined;

	afterEach(() => {
		wrapper?.unmount();
		wrapper = undefined;
		document.body.replaceChildren();
	});

	it("highlights MIR ranges associated with the selected source", async () => {
		wrapper = mount(IrViewer, {
			attachTo: document.body,
			props: {
				title: "MIR",
				ir: {
					text: "fn @expr():\n  b0:\n    ret",
					source_map: [{ from: 20, to: 23, source_from: 0, source_to: 6, inline_depth: 0 }],
				},
				sourceSelection: [{ from: 1, to: 2 }],
			},
		});

		await vi.waitFor(() => {
			expect(wrapper?.find(".cm-source-linked").exists()).toBe(true);
		});
	});

	it("selects every source range of code linked to several", async () => {
		const mounted = mount(IrViewer, {
			attachTo: document.body,
			props: {
				title: "Wasm",
				ir: {
					text: "local.get 0\nlocal.tee 1\nreturn",
					source_map: [
						{ from: 0, to: 23, source_from: 0, source_to: 5, inline_depth: 0 },
						{ from: 12, to: 23, source_from: 10, source_to: 15, inline_depth: 0 },
						{ from: 12, to: 23, source_from: 10, source_to: 15, inline_depth: 0 },
						{ from: 0, to: 23, source_from: 20, source_to: 30, inline_depth: 1 },
					],
				},
			},
		});
		wrapper = mounted;
		const view = EditorView.findFromDOM(mounted.element as HTMLElement);
		expect(view).not.toBeNull();
		view?.dispatch({ selection: { anchor: 14 } });

		expect(mounted.emitted("sourceSelected")?.at(-1)).toEqual([[
			{ from: 0, to: 5 },
			{ from: 10, to: 15 },
		]]);
	});

	it("selects the call site of code inlined from another source", async () => {
		const mounted = mount(IrViewer, {
			attachTo: document.body,
			props: {
				title: "Wasm",
				ir: {
					text: "local.get 0\ni32.mul",
					source_map: [
						{ from: 12, to: 19, source_from: 20, source_to: 30, inline_depth: 2 },
						{ from: 12, to: 19, source_from: 5, source_to: 9, inline_depth: 1 },
					],
				},
			},
		});
		wrapper = mounted;
		const view = EditorView.findFromDOM(mounted.element as HTMLElement);
		view?.dispatch({ selection: { anchor: 14 } });

		expect(mounted.emitted("sourceSelected")?.at(-1)).toEqual([[{ from: 5, to: 9 }]]);
	});

	it("selects the nearest source of each piece of code", async () => {
		const mounted = mount(IrViewer, {
			attachTo: document.body,
			props: {
				title: "Wasm",
				ir: {
					text: "local.get 0\ni32.mul",
					source_map: [
						{ from: 0, to: 11, source_from: 0, source_to: 3, inline_depth: 0 },
						{ from: 12, to: 19, source_from: 5, source_to: 9, inline_depth: 1 },
					],
				},
			},
		});
		wrapper = mounted;
		const view = EditorView.findFromDOM(mounted.element as HTMLElement);
		view?.dispatch({ selection: { anchor: 0, head: 19 } });

		expect(mounted.emitted("sourceSelected")?.at(-1)).toEqual([[
			{ from: 0, to: 3 },
			{ from: 5, to: 9 },
		]]);
	});

	it("selects the nearest source when a call site spans more code", async () => {
		const mounted = mount(IrViewer, {
			attachTo: document.body,
			props: {
				title: "Wasm",
				ir: {
					text: "local.get 0\ni32.mul",
					source_map: [
						{ from: 0, to: 11, source_from: 0, source_to: 3, inline_depth: 0 },
						{ from: 0, to: 19, source_from: 5, source_to: 9, inline_depth: 1 },
					],
				},
			},
		});
		wrapper = mounted;
		const view = EditorView.findFromDOM(mounted.element as HTMLElement);
		view?.dispatch({ selection: { anchor: 5 } });
		expect(mounted.emitted("sourceSelected")?.at(-1)).toEqual([[{ from: 0, to: 3 }]]);

		// Beyond the code's own source, only the call site remains.
		view?.dispatch({ selection: { anchor: 5, head: 15 } });
		expect(mounted.emitted("sourceSelected")?.at(-1)).toEqual([[
			{ from: 0, to: 3 },
			{ from: 5, to: 9 },
		]]);
	});

	it("marks code inlined at a selected call site faintly", async () => {
		wrapper = mount(IrViewer, {
			attachTo: document.body,
			props: {
				title: "Wasm",
				ir: {
					text: "local.get 0\ni32.mul",
					source_map: [
						{ from: 12, to: 19, source_from: 5, source_to: 9, inline_depth: 1 },
					],
				},
				sourceSelection: [{ from: 6, to: 6 }],
			},
		});

		await vi.waitFor(() => {
			expect(wrapper?.find(".cm-source-inlined").exists()).toBe(true);
		});
		expect(wrapper?.find(".cm-source-linked").exists()).toBe(false);
	});
});
