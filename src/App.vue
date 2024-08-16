<script setup lang="ts">
import { ref } from 'vue';
import CodeEditor from './components/CodeEditor.vue';
import DropdownSelect from './components/DropdownSelect.vue';
import SimpleButton from './components/SimpleButton.vue';
import ConsoleOutput from './components/ConsoleOutput.vue';
import { demoCodes } from './demo-codes';

const editor = ref<typeof CodeEditor>();
const runOutput = ref("Press Run or Ctrl/Cmd+Enter to execute the code.");
const isRunDisabled = ref(false);

function updateEditor(data: { value: string, index: number }) {
	if (editor.value) {
		editor.value.setText(demoCodes[data.index]);
	}
};

function runCode() {
	if (editor.value) {
		runOutput.value = editor.value.runCode();
	}
}

function setRunAvailability(status: boolean) {
	isRunDisabled.value = !status;
}
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
			:items="['Empty', 'Factorial', 'Is even', 'Polymorphic let (function)', 'Polymorphic let (value)', 'Quicksort', 'String']"
			@selection-changed="updateEditor"
		/>
	</div>
	<CodeEditor
		ref="editor"
		@run-code="runCode()"
		@set-run-availability="setRunAvailability"
	/>
	<ConsoleOutput :text="runOutput" />
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
