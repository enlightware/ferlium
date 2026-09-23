<script setup lang="ts">

import { ref, onMounted, watch } from "vue";
import { DiagnosticSeverity, PlaygroundCompiler as Compiler, ErrorData } from "../compiler-api";
import type { ExecutionMode, IrText, SourceRange } from "../types";

import { EditorView, keymap, ViewUpdate, scrollPastEnd } from "@codemirror/view";
import { indentWithTab } from "@codemirror/commands";
import { indentUnit } from "@codemirror/language";
import { linter, lintGutter, type Diagnostic } from "@codemirror/lint";
import { basicSetup } from "codemirror";
import { renderAnnotationsPlugin, setAnnotations } from "../annotation-extension";
import { languageExtension } from "../language/language-extension";
import { positionPanel } from "../position-panel-extension";
import { reportEngineTrap } from "../crash-recovery";

const editor = ref<HTMLElement>();
const view = ref<EditorView>();
const diagnostics: Diagnostic[] = [];

const compiler = new Compiler();
compiler.set_allow_experimental(true);

type AnnotationMode = "none" | "light" | "full";

const props = withDefaults(defineProps<{
	annotationMode: AnnotationMode,
	executionMode?: ExecutionMode,
}>(), {
	executionMode: "hir",
});

const emit = defineEmits<{
	runCode: [],
	setRunAvailability: [status: boolean],
	irChanged: [ir: IrText | undefined],
	sourceSelection: [range: SourceRange],
}>();

const myKeymap = keymap.of([
	{
		key: "Ctrl-Enter",
		mac: "Cmd-Enter",
		run: () => { emit("runCode"); return true; },
	},
]);

let forceLint = false;
let annotationsAvailable = false;
let skipCompilation = false;

function linterNeedsRefresh() {
	if (forceLint) {
		forceLint = false;
		return true;
	}
	return false;
}

const editorTheme = EditorView.theme({
	"&.cm-editor": {height: "100%"},
	".cm-scroller": {overflow: "auto", fontFamily: "'JuliaMono', monospace"},
	".cursor-panel": {textAlign: "right", paddingRight: "4px"}
});

const extensions = [
	myKeymap,
	basicSetup,
	languageExtension(),
	positionPanel(),
	keymap.of([indentWithTab]),
	indentUnit.of("\t"),
	scrollPastEnd(),
	EditorView.lineWrapping,
	renderAnnotationsPlugin,
	EditorView.updateListener.of(processUpdate),
	linter(() => diagnostics, { delay: 0, needsRefresh: linterNeedsRefresh }),
	lintGutter(),
	editorTheme,
	EditorView.exceptionSink.of(error => {
		reportEngineTrap(error);
		console.error(error);
	}),
];

function fillDiagnostics(diagnosticData: ErrorData[]) {
	diagnostics.length = 0;
	for (const data of diagnosticData) {
		if (data.file != "<ide>") {
			continue;
		}
		diagnostics.push({
			from: data.from,
			to: data.to,
			severity: data.severity === DiagnosticSeverity.Warning ? "warning" : "error",
			message: data.text,
		});
	}
}

function processUpdate(update: ViewUpdate) {
	const text = update.state.doc.toString();
	const view = update.view;
	if (update.selectionSet) {
		const selection = update.state.selection.main;
		emit("sourceSelection", { from: selection.from, to: selection.to });
	}
	if (update.docChanged) {
		const report = skipCompilation ? undefined : compiler.compile(text);
		fillDiagnostics(report?.diagnostics ?? []);
		if (!report?.succeeded) {
			annotationsAvailable = false;
			setAnnotations(view, []);
			emit("setRunAvailability", false);
			emit("irChanged", undefined);
		} else {
			annotationsAvailable = true;
			refreshAnnotations();
			emit("setRunAvailability", true);
			refreshIr();
		}
	}
}

function refreshAnnotations() {
	if (!view.value) {
		return;
	}
	if (!annotationsAvailable) {
		setAnnotations(view.value, []);
		return;
	}
	switch (props.annotationMode) {
		case "none":
			setAnnotations(view.value, []);
			break;
		case "light":
			setAnnotations(view.value, compiler.get_light_annotations());
			break;
		case "full":
			setAnnotations(view.value, compiler.get_annotations());
			break;
	}
}

function refreshIr() {
	if (!annotationsAvailable || props.executionMode === "hir") {
		emit("irChanged", undefined);
		return;
	}
	try {
		const ir = (props.executionMode === "wasm"
			? compiler.wasm_text()
			: props.executionMode === "physical-mir"
				? compiler.physical_mir_text()
				: compiler.mir_text(props.executionMode === "optimized-mir")) as IrText;
		emit("irChanged", ir.text === "" ? undefined : ir);
	} catch (error) {
		reportEngineTrap(error);
		emit("irChanged", props.executionMode === "wasm"
			? { text: `Unable to generate Wasm: ${String(error)}`, source_map: [] }
			: props.executionMode === "physical-mir"
				? { text: `Unable to prepare MIR: ${String(error)}`, source_map: [] }
				: undefined);
	}
}

watch(() => props.annotationMode, refreshAnnotations);
watch(() => props.executionMode, refreshIr);

/** Replace the source; without `compile`, it stays uncompiled until the next edit. */
const setText = (newText: string, compile = true) => {
	if (view.value) {
		const text = view.value.state.doc.toString();
		skipCompilation = !compile;
		try {
			view.value.dispatch({changes: {from: 0, to: text.length, insert: newText}});
		} finally {
			skipCompilation = false;
		}
	}
};

const getText = () => view.value?.state.doc.toString() ?? "";

const runCode = (executionMode: ExecutionMode = props.executionMode) => {
	try {
		const result = executionMode === "hir"
			? compiler.run_expr()
			: executionMode === "physical-mir"
				? compiler.run_expr_physical_mir()
				: executionMode === "wasm"
					? compiler.run_expr_wasm()
					: compiler.run_expr_mir(executionMode === "optimized-mir");
		const errorData = result?.error_data();
		if (errorData !== undefined && view.value) {
			fillDiagnostics([errorData]);
			forceLint = true;
			view.value.dispatch({});
		}
		return result;
	} catch (e) {
		reportEngineTrap(e);
		// eslint-disable-next-line @typescript-eslint/no-explicit-any
		return `The compiler crashed, reload the page! Error: ${(e as any).toString()}`;
	}
}

const selectRange = (range: SourceRange) => {
	view.value?.dispatch({
		selection: { anchor: range.from, head: range.to },
		scrollIntoView: true,
	});
};

defineExpose({
	setText,
	getText,
	runCode,
	selectRange,
});


onMounted(() => {
	view.value = new EditorView({
		doc: "",
		extensions,
		parent: editor.value,
	});
});
</script>

<template>
	<div ref="editor" />
</template>

<style scoped>
div {
	flex-grow: 1;
	min-height: 0;
	overflow-y: auto;
}
</style>
