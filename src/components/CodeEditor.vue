<script setup lang="ts">

import { ref, onMounted, type Ref } from 'vue';
import { Compiler } from 'script-api';

// import { javascript } from '@codemirror/lang-javascript';
import { EditorView } from '@codemirror/view';
import { basicSetup } from 'codemirror';
import { nonnull } from '../types';
import { renderErrorDataPlugin, setErrorUnderlines } from '../error-underline-extension';
import { renderAnnotationsPlugin, setAnnotations } from '../annotation-extension';

const editor: Ref<null | HTMLElement> = ref(null);
const compiler = new Compiler();

onMounted(() => {
	const viewPtr: unknown[] = [null];
	viewPtr[0] = new EditorView({
		doc: "",
		extensions: [
			basicSetup,
			// javascript(),
			renderErrorDataPlugin,
			renderAnnotationsPlugin,
			EditorView.updateListener.of((update) => {
				const text = update.state.doc.toString();
				const view = (viewPtr[0] as EditorView);
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
			})
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
