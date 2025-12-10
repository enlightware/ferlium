<script setup lang="ts">
import { ref } from 'vue';

defineProps<{
	text: string
}>();

const highlightableRef = ref<HTMLElement>();

const highlight = () => {
	const element = highlightableRef.value;
	if (element) {
		element.classList.add('highlight');
		setTimeout(() => {
			element.classList.remove('highlight');
		}, 500);
	}
};

defineExpose({
	highlight
});
</script>

<template>
	<!-- eslint-disable vue/no-v-html -->
	<div
		ref="highlightableRef"
		v-html="text"
	/>
</template>

<style scoped>
div {
	resize: none;
	font-family: JuliaMono, monospace;
	background-color: black;
	color: #dcdcdc;
	padding: 4px;
	white-space: pre-wrap; /* Maintains whitespace formatting */
	border: 1px solid #333;
	min-height: calc(2em + 8px);
	max-height: 30%;
	overflow: auto;
	flex-shrink: 0;
}
div :deep(.warning) {
	color: #ffe786;
}
div :deep(.error) {
	color: #ff9898;
}

.highlight {
	animation: highlightAnimation 0.5s ease;
}

@keyframes highlightAnimation {
	0% {
		background-color: white; /* Highlight color */
	}
	100% {
		background-color: black;
	}
}
</style>