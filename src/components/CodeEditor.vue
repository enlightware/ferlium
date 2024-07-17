<script setup lang="ts">

import { ref, onMounted } from 'vue';
import { Compiler, ErrorData } from 'script-api';

import { EditorView,keymap, ViewUpdate, scrollPastEnd } from '@codemirror/view';
import { indentWithTab } from "@codemirror/commands";
import { indentUnit } from "@codemirror/language";
import { linter, type Diagnostic } from "@codemirror/lint";
import { basicSetup } from 'codemirror';
import { renderAnnotationsPlugin, setAnnotations } from '../annotation-extension';
import { languageExtension } from "../language/language-extension";

const editor = ref<HTMLElement>();
const view = ref<EditorView>();
const diagnostics: Diagnostic[] = [];

const compiler = new Compiler();

function fillDiagnostics(errorData: ErrorData[]){
	diagnostics.length = 0;
	for (const data of errorData){
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
		const errorData = compiler.compile(text);
		if (errorData !== undefined) {
			fillDiagnostics(errorData);
			setAnnotations(view, []);
		} else {
			diagnostics.length = 0;
			setAnnotations(view, compiler.get_annotations());
		}
	}
}

const setText = (newText: string) => {
	if (view.value) {
		const text = view.value.state.doc.toString();
		view.value.dispatch({changes: {from: 0, to: text.length, insert: newText}});
	}
};

defineExpose({
	setText
});

onMounted(() => {
	view.value = new EditorView({
		doc: "",
		extensions: [
			basicSetup,
			languageExtension(),
			keymap.of([indentWithTab]),
			indentUnit.of("\t"),
			scrollPastEnd(),
			renderAnnotationsPlugin,
			EditorView.updateListener.of(processUpdate),
			linter(() => diagnostics, { delay: 0 }),
			EditorView.theme({
				"&.cm-editor": {height: "100%"},
				".cm-scroller": {overflow: "auto", fontFamily: "'JuliaMono', monospace"}
			}),
		],
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
