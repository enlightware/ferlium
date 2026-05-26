<script setup lang="ts">
import { ref } from 'vue';

const highlightableRef = ref<HTMLElement>();

function appendNewlineIfNeeded(element: HTMLElement) {
	if (element.childNodes.length > 0) {
		element.appendChild(document.createTextNode("\n"));
	}
}

const clear = () => {
	const element = highlightableRef.value;
	if (element) {
		element.innerHTML = "";
	}
};

const appendHtml = (html: string) => {
	const element = highlightableRef.value;
	if (element) {
		appendNewlineIfNeeded(element);
		element.insertAdjacentHTML("beforeend", html);
	}
};

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
	appendHtml,
	clear,
	highlight
});
</script>

<template>
	<!-- eslint-disable vue/no-v-html -->
	<div
		id="console-output"
		ref="highlightableRef"
	>
		Press Run or Ctrl/Cmd+Enter to execute the code.
	</div>
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