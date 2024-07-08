<script setup lang="ts">
import { ref } from 'vue';
import { replace_text } from 'script-api';

const inputText = ref('');

function processText() {
	// Function is called on every keystroke to process the text.
	inputText.value = replace_text(inputText.value, 'foo', 'bar');
}
</script>

<template>
	<textarea
		v-model="inputText"
		placeholder="Type here..."
		@input="processText"
	/>
</template>

<style scoped>
textarea {
	font-family: monospace;
}
</style>