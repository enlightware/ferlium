<script setup lang="ts">
import { onBeforeUnmount, onMounted, ref, watch } from "vue";
import { Decoration, EditorView, type DecorationSet, type ViewUpdate } from "@codemirror/view";
import { StateEffect, StateField } from "@codemirror/state";
import { basicSetup } from "codemirror";
import { rangesOverlap, type IrText, type SourceMapEntry, type SourceRange } from "../types";

const props = defineProps<{
	ir: IrText,
	title: string,
	sourceSelection?: SourceRange,
}>();

const emit = defineEmits<{
	sourceSelected: [range: SourceRange],
}>();

const viewer = ref<HTMLElement>();
const view = ref<EditorView>();

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
});

function sourceRange(entry: SourceMapEntry): SourceRange {
	return { from: entry.source_from, to: entry.source_to };
}

function refreshHighlights() {
	if (!view.value) {
		return;
	}
	const selection = props.sourceSelection;
	const decorations = selection === undefined
		? []
		: props.ir.source_map
			.filter(entry => rangesOverlap(selection, sourceRange(entry)))
			.map(entry => Decoration.mark({ class: "cm-source-linked" }).range(entry.from, entry.to));
	view.value.dispatch({ effects: setHighlights.of(Decoration.set(decorations, true)) });
}

function replaceText() {
	if (!view.value) {
		return;
	}
	const current = view.value.state.doc;
	view.value.dispatch({ changes: { from: 0, to: current.length, insert: props.ir.text } });
	refreshHighlights();
}

function processUpdate(update: ViewUpdate) {
	if (!update.selectionSet) {
		return;
	}
	const selection = update.state.selection.main;
	const entry = props.ir.source_map.find(entry => rangesOverlap(selection, entry));
	if (entry !== undefined) {
		emit("sourceSelected", sourceRange(entry));
	}
}

watch(() => props.ir, replaceText);
watch(() => props.sourceSelection, refreshHighlights, { deep: true });

onMounted(() => {
	view.value = new EditorView({
		doc: props.ir.text,
		extensions: [
			basicSetup,
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
