<script setup lang="ts">

import { ref, onMounted, type Ref } from 'vue';
import { replace_text } from 'script-api';

import { javascript } from '@codemirror/lang-javascript';
import { EditorView } from '@codemirror/view';
import { basicSetup } from 'codemirror';
import { nonnull } from '../types';

const editor: Ref<null | HTMLElement> = ref(null);

onMounted(() => {
	const viewPtr: unknown[] = [null];
	viewPtr[0] = new EditorView({
		doc: "",
		extensions: [
			basicSetup,
			javascript(),
			EditorView.updateListener.of(({ state }) => {
				const text = state.doc.toString();
				const newText = processText(text);
				const view = (viewPtr[0] as EditorView);
				if (newText !== text) {
					view.dispatch({changes: {from: 0, to: newText.length, insert: newText}});
				}
			})
		],
		parent: nonnull(editor.value),
	});
});

function processText(text: string) {
	// Function is called on every keystroke to process the text.
	return replace_text(text, 'foo', 'bar');
}
</script>

<template>
	<div ref="editor" />
</template>

<style scoped>
div {
	font-family: monospace;
}
</style>
