<script setup lang="ts">
import { onBeforeUnmount, onMounted, ref, watch } from "vue";
import { Decoration, EditorView, type DecorationSet, type ViewUpdate } from "@codemirror/view";
import { Compartment, StateEffect, StateField } from "@codemirror/state";
import { basicSetup } from "codemirror";
import { rangesOverlap, type IrText, type SourceMapEntry, type SourceRange } from "../types";
import { mirLanguageExtension } from "../language/mir-language";
import { wasmLanguageExtension } from "../language/wasm-language";

const props = defineProps<{
	/** The rendered IR, or `undefined` when the current source has none to show. */
	ir?: IrText,
	title: string,
	/** The selected source ranges, several with multiple selections. */
	sourceSelection?: Array<SourceRange>,
	/** The syntax of the rendered IR. */
	language?: "mir" | "wasm",
}>();

const emit = defineEmits<{
	sourceSelected: [ranges: Array<SourceRange>],
}>();

const viewer = ref<HTMLElement>();
const view = ref<EditorView>();
const languageCompartment = new Compartment();

function languageExtension() {
	return props.language === "wasm" ? wasmLanguageExtension() : mirLanguageExtension();
}

const setHighlights = StateEffect.define<DecorationSet>();
const highlights = StateField.define<DecorationSet>({
	create: () => Decoration.none,
	update(value, transaction) {
		for (const effect of transaction.effects) {
			if (effect.is(setHighlights)) {
				return effect.value;
			}
		}
		return value.map(transaction.changes);
	},
	provide: field => EditorView.decorations.from(field),
});

const editorTheme = EditorView.theme({
	"&.cm-editor": { height: "100%" },
	".cm-scroller": { overflow: "auto", fontFamily: "'JuliaMono', monospace" },
	".cm-source-linked": { backgroundColor: "#fff0a8" },
	".cm-source-inlined": { backgroundColor: "#fff8d6" },
});

function sourceRange(entry: SourceMapEntry): SourceRange {
	return { from: entry.source_from, to: entry.source_to };
}

function irText(): string {
	return props.ir?.text ?? "";
}

function sourceMap(): Array<SourceMapEntry> {
	return props.ir?.source_map ?? [];
}

function refreshHighlights() {
	if (!view.value) {
		return;
	}
	const selection = props.sourceSelection;
	// Code whose own source is selected is marked strongly; code inlined at a selected call site,
	// faintly. A range linked both ways is marked strongly.
	const depths = new Map<string, { from: number, to: number, inlined: boolean }>();
	const selected = selection === undefined
		? []
		: sourceMap().filter(entry => selection.some(range => rangesOverlap(range, sourceRange(entry))));
	for (const entry of selected) {
		const key = `${entry.from}:${entry.to}`;
		const inlined = entry.inline_depth > 0 && (depths.get(key)?.inlined ?? true);
		depths.set(key, { from: entry.from, to: entry.to, inlined });
	}
	const decorations = [...depths.values()].map(({ from, to, inlined }) =>
		Decoration.mark({ class: inlined ? "cm-source-inlined" : "cm-source-linked" }).range(from, to));
	view.value.dispatch({ effects: setHighlights.of(Decoration.set(decorations, true)) });
}

function replaceText() {
	if (!view.value) {
		return;
	}
	const current = view.value.state.doc;
	view.value.dispatch({ changes: { from: 0, to: current.length, insert: irText() } });
	refreshHighlights();
}

/**
 * The `links` overlapping `selection` that are the innermost somewhere within it. Links of one
 * piece of code need not share its range, as a call site's link may span the code of several
 * operations, so the selection is swept from boundary to boundary and each piece is decided alone.
 */
function innermostLinks(selection: SourceRange, links: Array<SourceMapEntry>): Array<SourceMapEntry> {
	if (selection.from === selection.to) {
		const depth = Math.min(...links.map(link => link.inline_depth));
		return links.filter(link => link.inline_depth === depth);
	}
	const events = links.flatMap(link => {
		const from = Math.max(link.from, selection.from);
		const to = Math.min(link.to, selection.to);
		return from < to ? [{ position: from, link, start: true }, { position: to, link, start: false }] : [];
	}).sort((left, right) => left.position - right.position || Number(left.start) - Number(right.start));
	// The links covering the current piece by depth, with those not yet kept: each is kept at most
	// once, so beyond sorting, each boundary costs only a scan of the active depths, which inline
	// chains keep few.
	const active = new Map<number, { count: number, pending: Set<SourceMapEntry> }>();
	const kept = new Set<SourceMapEntry>();
	for (const [index, { position, link, start }] of events.entries()) {
		const depth = link.inline_depth;
		if (start) {
			const group = active.get(depth) ?? { count: 0, pending: new Set() };
			group.count += 1;
			if (!kept.has(link)) {
				group.pending.add(link);
			}
			active.set(depth, group);
		} else {
			const group = active.get(depth)!;
			group.count -= 1;
			group.pending.delete(link);
			if (group.count === 0) {
				active.delete(depth);
			}
		}
		if (events[index + 1]?.position === position || active.size === 0) {
			continue;
		}
		const innermost = active.get(Math.min(...active.keys()))!;
		for (const pending of innermost.pending) {
			kept.add(pending);
		}
		innermost.pending.clear();
	}
	return links.filter(link => kept.has(link));
}

function processUpdate(update: ViewUpdate) {
	if (!update.selectionSet) {
		return;
	}
	// Code may do the work of several source expressions, with one entry for each. Code inlined
	// from elsewhere also links to its call sites: for each piece of code, the innermost links found
	// are selected, which for code inlined from another source are its call sites in this one.
	const selection = update.state.selection.main;
	const selected = sourceMap().filter(entry => rangesOverlap(selection, entry));
	const ranges: Array<SourceRange> = [];
	for (const entry of innermostLinks(selection, selected)) {
		const range = sourceRange(entry);
		if (!ranges.some(other => other.from === range.from && other.to === range.to)) {
			ranges.push(range);
		}
	}
	if (ranges.length > 0) {
		emit("sourceSelected", ranges);
	}
}

watch(() => props.ir, replaceText);
watch(() => props.language, () => {
	view.value?.dispatch({ effects: languageCompartment.reconfigure(languageExtension()) });
});
watch(() => props.sourceSelection, refreshHighlights, { deep: true });

onMounted(() => {
	view.value = new EditorView({
		doc: irText(),
		extensions: [
			basicSetup,
			languageCompartment.of(languageExtension()),
			EditorView.editable.of(false),
			highlights,
			EditorView.updateListener.of(processUpdate),
			editorTheme,
		],
		parent: viewer.value,
	});
	refreshHighlights();
});

onBeforeUnmount(() => view.value?.destroy());
</script>

<template>
	<section class="ir-panel">
		<header>{{ title }}</header>
		<div ref="viewer" />
	</section>
</template>

<style scoped>
.ir-panel {
	display: flex;
	min-width: 0;
	min-height: 0;
	flex: 1;
	flex-direction: column;
	border-left: 1px solid #e9ecef;
}

header {
	padding: 5px 8px;
	font-size: 0.875rem;
	color: #555;
	background-color: #f8f9fa;
	border-bottom: 1px solid #e9ecef;
}

.ir-panel > div {
	min-height: 0;
	flex: 1;
}
</style>
