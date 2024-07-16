<script setup lang="ts">

import { ref, onMounted, type Ref } from 'vue';
import { Compiler } from 'script-api';

import { EditorView, ViewUpdate } from '@codemirror/view';
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
			renderErrorDataPlugin,
			renderAnnotationsPlugin,
			EditorView.updateListener.of(processUpdate)
		],
		parent: nonnull(editor.value),
	});
});

</script>

<template>
	<div ref="editor" />
</template>

<style scoped>
</style>
