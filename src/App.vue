<script setup lang="ts">
import { ref } from 'vue';
import CodeEditor from './components/CodeEditor.vue';
import DropdownSelect from './components/DropdownSelect.vue';
import { demoCodes } from './demo-codes';

const editor = ref<typeof CodeEditor>();

function updateEditor(data: { value: string, index: number }) {
	if (editor.value) {
		editor.value.setText(demoCodes[data.index]);
	}
};
</script>

<template>
	<DropdownSelect
		:items="['Empty', 'Factorial', 'Is even', 'Polymorphic let']"
		@selection-changed="updateEditor"
	/>
	<CodeEditor ref="editor" />
</template>

<style scoped>
</style>
