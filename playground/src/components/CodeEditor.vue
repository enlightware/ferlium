<script setup lang="ts">

import { ref, onMounted } from "vue";
import { Compiler, ErrorData } from "script-api";

import { EditorView, keymap, ViewUpdate, scrollPastEnd } from "@codemirror/view";
import { indentWithTab } from "@codemirror/commands";
import { indentUnit } from "@codemirror/language";
import { linter, type Diagnostic } from "@codemirror/lint";
import { basicSetup } from "codemirror";
import { renderAnnotationsPlugin, setAnnotations } from "../annotation-extension";
import { languageExtension } from "../language/language-extension";
import { positionPanel } from "../position-panel-extension";

const editor = ref<HTMLElement>();
const view = ref<EditorView>();
const diagnostics: Diagnostic[] = [];

const compiler = new Compiler();

const emit = defineEmits<{
	runCode: [],
	setRunAvailability: [status: boolean],
}>();

const myKeymap = keymap.of([
	{
		key: "Ctrl-Enter",
		mac: "Cmd-Enter",
		run: () => { emit("runCode"); return true; },
	},
]);

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
	linter(() => diagnostics, { delay: 0 }),
	EditorView.theme({
		"&.cm-editor": {height: "100%"},
		".cm-scroller": {overflow: "auto", fontFamily: "'JuliaMono', monospace"},
		".cursor-panel": {textAlign: "right", paddingRight: "4px"}
	}),
];

function fillDiagnostics(errorData: ErrorData[]){
	diagnostics.length = 0;
	for (const data of errorData) {
		if (data.file != "<playground>") {
			continue;
		}
		diagnostics.push({
			from: data.from,
			to: data.to,
			severity: "error",
			message: data.text,
		});
	}
}

function processUpdate(update: ViewUpdate) {
	const text = update.state.doc.toString();
	const view = update.view;
	if (update.docChanged) {
		const errorData = compiler.compile("<playground>", text);
		if (errorData !== undefined) {
			fillDiagnostics(errorData);
			setAnnotations(view, []);
			emit("setRunAvailability", false);
		} else {
			diagnostics.length = 0;
			setAnnotations(view, compiler.get_annotations());
			emit("setRunAvailability", true);
		}
	}
}



const setText = (newText: string) => {
	if (view.value) {
		const text = view.value.state.doc.toString();
		view.value.dispatch({changes: {from: 0, to: text.length, insert: newText}});
	}
};

const runCode = () => {
	try {
		return compiler.run_expr_to_html();
	} catch (e) {
		// eslint-disable-next-line @typescript-eslint/no-explicit-any
		return `The compiler crashed, reload the page! Error: ${(e as any).toString()}`;
	}
}

defineExpose({
	setText,
	runCode,
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
	overflow-y: auto;
}
</style>
