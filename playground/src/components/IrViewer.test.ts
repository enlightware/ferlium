import { mount, type VueWrapper } from "@vue/test-utils";
import { afterEach, describe, expect, it, vi } from "vitest";
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
					source_map: [{ from: 20, to: 23, source_from: 0, source_to: 6 }],
				},
				sourceSelection: { from: 1, to: 2 },
			},
		});

		await vi.waitFor(() => {
			expect(wrapper?.find(".cm-source-linked").exists()).toBe(true);
		});
	});
});
