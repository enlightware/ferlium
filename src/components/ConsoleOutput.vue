<script setup lang="ts">
defineProps<{
	text: string
}>();
</script>

<template>
	<!-- eslint-disable-next-line vue/no-v-html -->
	<div v-html="text" />
</template>

<style scoped>
div {
	resize: none;
	font-family: JuliaMono, monospace;
	background-color: #1e1e1e;
	color: #dcdcdc;
	padding: 4px;
	white-space: pre-wrap; /* Maintains whitespace formatting */
	border: 1px solid #333;
}
div :deep(.warning) {
	color: #ffe786;
}
div :deep(.error) {
	color: #ff9898;
}
</style>