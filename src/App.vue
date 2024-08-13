<script setup lang="ts">
import { ref } from 'vue';
import CodeEditor from './components/CodeEditor.vue';
import DropdownSelect from './components/DropdownSelect.vue';
import SimpleButton from './components/SimpleButton.vue';
import ConsoleOutput from './components/ConsoleOutput.vue';
import { demoCodes } from './demo-codes';

const editor = ref<typeof CodeEditor>();
const runOutput = ref("Press Run or Ctrl/Cmd+Enter to execute the code.");

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
</script>

<template>
	<div class="toolbar">
		<SimpleButton @click="runCode">
			Run
		</SimpleButton>
		<DropdownSelect
			:items="['Empty', 'Factorial', 'Is even', 'Polymorphic let (function)', 'Polymorphic let (value)', 'Quicksort']"
			@selection-changed="updateEditor"
		/>
	</div>
	<CodeEditor
		ref="editor"
		@run-code="runCode()"
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
