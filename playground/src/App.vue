<script setup lang="ts">
import { ref } from 'vue';
import CodeEditor from './components/CodeEditor.vue';
import DropdownSelect from './components/DropdownSelect.vue';
import SimpleButton from './components/SimpleButton.vue';
import FlatLinkButton from './components/FlatLinkButton.vue';
import ConsoleOutput from './components/ConsoleOutput.vue';
import { demoCodes } from './demo-codes';
import { defined } from './types';
import { onMounted } from 'vue';

const demoTitles = demoCodes.map(([title, _]) => title);
const annotationModes = ["none", "light", "full"] as const;
type AnnotationMode = typeof annotationModes[number];
const annotationOptionTitles = [
	"Hide type annotations.",
	"Show simplified type annotations.",
	"Show full type annotations.",
];
const editor = ref<typeof CodeEditor>();
const console = ref<typeof ConsoleOutput>();
const runOutput = ref("Press Run or Ctrl/Cmd+Enter to execute the code.");
const isRunDisabled = ref(false);
const annotationMode = ref<AnnotationMode>("light");

function updateEditor(data: { value: string, index: number }) {
	if (editor.value) {
		editor.value.setText(demoCodes[data.index]?.[1] ?? '');
	}
};

function updateAnnotationMode(data: { value: string, index: number }) {
	annotationMode.value = annotationModes[data.index] ?? "light";
}

function runCode() {
	if (editor.value && !isRunDisabled.value) {
		const result = editor.value.runCode();
		if (result !== undefined) {
			runOutput.value = result.html_message();
		} else {
			runOutput.value = "<span class=\"warning\">No expression to run</span>";
		}
		defined(console.value).highlight();
	}
}

function setRunAvailability(status: boolean) {
	isRunDisabled.value = !status;
}

onMounted(() => {
	const queryString = window.location.search;
	const urlParams = new URLSearchParams(queryString);
	const code = urlParams.get('code');
	if (code !== null) {
		defined(editor.value).setText(code);
	}
});
</script>

<template>
	<div class="toolbar">
		<SimpleButton
			:disabled="isRunDisabled"
			@click="runCode"
		>
			Run
		</SimpleButton>
		<div class="revision" />
		<div class="demo-controls">
			<DropdownSelect
				:items="demoTitles"
				placeholder="Select a code sample"
				@selection-changed="updateEditor"
			/>
			<DropdownSelect
				:items="[...annotationModes]"
				:item-titles="annotationOptionTitles"
				:initial-index="1"
				placeholder="annotation"
				@selection-changed="updateAnnotationMode"
			/>
			<FlatLinkButton
				href="https://enlightware.github.io/ferlium/book/"
				title="Open documentation"
			>
				🕮
			</FlatLinkButton>
		</div>
	</div>
	<CodeEditor
		ref="editor"
		:annotation-mode="annotationMode"
		@run-code="runCode()"
		@set-run-availability="setRunAvailability"
	/>
	<ConsoleOutput
		ref="console"
		:text="runOutput"
	/>
</template>

<style scoped>
.toolbar {
	display: flex;
	justify-content: space-between;
	align-items: center;
	padding: 10px;
	background-color: #f8f9fa;
	border-bottom: 1px solid #e9ecef;
}
.revision {
	color: gray;
}

.demo-controls {
	display: flex;
	align-items: center;
	gap: 8px;
}
</style>
