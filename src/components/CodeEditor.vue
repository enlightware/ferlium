<script setup lang="ts">

import { ref, onMounted, type Ref } from 'vue';
import { replace_text } from 'script-api';

import { javascript } from '@codemirror/lang-javascript';
import { EditorView } from '@codemirror/view';
import { basicSetup } from 'codemirror';
import { nonnull } from '../types';
import { setErrorUnderlines } from '../error-underline-extension';
import { renderTypeHintPlugin, setTypeHints } from '../type-hint-extension';

const editor: Ref<null | HTMLElement> = ref(null);

onMounted(() => {
	const viewPtr: unknown[] = [null];
	viewPtr[0] = new EditorView({
		doc: "",
		extensions: [
			basicSetup,
			javascript(),
			renderTypeHintPlugin,
			EditorView.updateListener.of((update) => {
				const text = update.state.doc.toString();
				const view = (viewPtr[0] as EditorView);
				const newText = processText(text);
				if (newText !== text) {
					view.dispatch({changes: {from: 0, to: newText.length, insert: newText}});
				}
				if (update.docChanged) {
					const errors = findErrors(text);
					setErrorUnderlines(view, errors);
					if (text.length > 5) {
						setTypeHints(view, [{ pos: 5, hint: "tada"}]);
					} else {
						setTypeHints(view, []);
					}
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

function findErrors(text: string) {
	const target = "bar";
	const result: [number, number][] = [];
	let index = text.indexOf(target);

	while (index !== -1) {
		result.push([index, index + target.length]);
		index = text.indexOf(target, index + 1);
	}

	return result;
}

</script>

<template>
	<div ref="editor" />
</template>

<style scoped>
</style>
