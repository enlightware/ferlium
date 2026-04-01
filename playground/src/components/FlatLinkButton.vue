<script setup lang="ts">

const props = defineProps<{
	href: string,
	title: string
}>();

function openLink() {
	window.open(props.href, "_blank", "noopener,noreferrer");
}
</script>

<template>
	<button
		class="book-link-button"
		type="button"
		aria-label=""
		:title="title"
		@click="openLink"
	>
		<slot />
	</button>
</template>

<style scoped>
.book-link-button {
	border: none;
	background: transparent;
	color: #4a4a4a;
	font-size: 24px;
	line-height: 1;
	cursor: pointer;
}

.book-link-button:hover {
	color: #000000;
}
</style>
