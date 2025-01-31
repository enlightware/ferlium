<script setup lang="ts">
import { ref } from 'vue';
import CodeEditor from './components/CodeEditor.vue';
import DropdownSelect from './components/DropdownSelect.vue';
import SimpleButton from './components/SimpleButton.vue';
import ConsoleOutput from './components/ConsoleOutput.vue';
import { demoCodes } from './demo-codes';
import { defined } from './types';
import { onMounted } from 'vue';

const demoTitles = demoCodes.map(([title, _]) => title);
const editor = ref<typeof CodeEditor>();
const console = ref<typeof ConsoleOutput>();
const runOutput = ref("Press Run or Ctrl/Cmd+Enter to execute the code.");
const isRunDisabled = ref(false);

function updateEditor(data: { value: string, index: number }) {
	if (editor.value) {
		editor.value.setText(demoCodes[data.index]?.[1] ?? '');
	}
};

function runCode() {
	if (editor.value && !isRunDisabled.value) {
		runOutput.value = editor.value.runCode();
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
		<DropdownSelect
			:items="demoTitles"
			@selection-changed="updateEditor"
		/>
	</div>
	<CodeEditor
		ref="editor"
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
</style>
