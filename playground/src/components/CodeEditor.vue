<script setup lang="ts">

import { ref, onMounted, watch } from "vue";
import { DiagnosticSeverity, PlaygroundCompiler as Compiler, ErrorData } from "../compiler-api";
import type { IrText, SourceRange } from "../types";

import { EditorView, keymap, ViewUpdate, scrollPastEnd } from "@codemirror/view";
import { indentWithTab } from "@codemirror/commands";
import { indentUnit } from "@codemirror/language";
import { linter, lintGutter, type Diagnostic } from "@codemirror/lint";
import { basicSetup } from "codemirror";
import { renderAnnotationsPlugin, setAnnotations } from "../annotation-extension";
import { languageExtension } from "../language/language-extension";
import { positionPanel } from "../position-panel-extension";

const editor = ref<HTMLElement>();
const view = ref<EditorView>();
const diagnostics: Diagnostic[] = [];

const compiler = new Compiler();
compiler.set_allow_experimental(true);

type AnnotationMode = "none" | "light" | "full";
type ExecutionMode = "hir" | "mir" | "optimized-mir";

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
		const report = compiler.compile(text);
		fillDiagnostics(report.diagnostics);
		if (!report.succeeded) {
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
		const ir = compiler.mir_text(props.executionMode === "optimized-mir") as IrText;
		emit("irChanged", ir.text === "" ? undefined : ir);
	} catch {
		emit("irChanged", undefined);
	}
}

watch(() => props.annotationMode, refreshAnnotations);
watch(() => props.executionMode, refreshIr);

const setText = (newText: string) => {
	if (view.value) {
		const text = view.value.state.doc.toString();
		view.value.dispatch({changes: {from: 0, to: text.length, insert: newText}});
	}
};

const runCode = (executionMode: ExecutionMode = props.executionMode) => {
	try {
		const result = executionMode === "hir"
			? compiler.run_expr()
			: compiler.run_expr_mir(executionMode === "optimized-mir");
		const errorData = result?.error_data();
		if (errorData !== undefined && view.value) {
			fillDiagnostics([errorData]);
			forceLint = true;
			view.value.dispatch({});
		}
		return result;
	} catch (e) {
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
