import { vi } from "vitest";

class ResizeObserver {
	disconnect() {}
	observe() {}
	unobserve() {}
}

vi.stubGlobal("ResizeObserver", ResizeObserver);

if (typeof Range.prototype.getClientRects !== "function") {
	Range.prototype.getClientRects = () => ({
		length: 0,
		item: () => null,
		[Symbol.iterator]: function* () {},
	});
}

if (typeof Range.prototype.getBoundingClientRect !== "function") {
	Range.prototype.getBoundingClientRect = () => new DOMRect();
}
