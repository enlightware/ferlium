<script setup lang="ts">

import { ref, onMounted, type Ref } from 'vue';
import { Compiler } from 'script-api';

import { EditorView,keymap, ViewUpdate, scrollPastEnd } from '@codemirror/view';
import { indentWithTab } from "@codemirror/commands";
import { indentUnit } from "@codemirror/language";
//import { lintGutter } from "@codemirror/lint";
import { basicSetup } from 'codemirror';
import { nonnull } from '../types';
import { renderErrorDataPlugin, setErrorUnderlines } from '../error-underline-extension';
import { renderAnnotationsPlugin, setAnnotations } from '../annotation-extension';

const editor: Ref<null | HTMLElement> = ref(null);
const compiler = new Compiler();

function processUpdate(update: ViewUpdate){
	const text = update.state.doc.toString();
	const view = update.view;
	// const newText = processText(text);
	// if (newText !== text) {
	// 	view.dispatch({changes: {from: 0, to: newText.length, insert: newText}});
	// }
	if (update.docChanged) {
		const errorData = compiler.compile(text);
		if (errorData !== undefined) {
			setErrorUnderlines(view, errorData);
			setAnnotations(view, []);
		} else {
			setErrorUnderlines(view, []);
			setAnnotations(view, compiler.get_annotations());
		}
	}
}

onMounted(() => {
	new EditorView({
		doc: "",
		extensions: [
			basicSetup,
			keymap.of([indentWithTab]),
			indentUnit.of("\t"),
			scrollPastEnd(),
			//lintGutter(),
			renderErrorDataPlugin,
			renderAnnotationsPlugin,
			EditorView.updateListener.of(processUpdate),
			EditorView.theme({
				"&.cm-editor": {height: "100%"},
				".cm-scroller": {overflow: "auto"}
			}),
		],
		parent: nonnull(editor.value),
	});
});

</script>

<template>
	<div ref="editor" />
</template>

<style scoped>
div {
	height: 100%;
	width: 100%;
	border: 1px solid black;
}
</style>
