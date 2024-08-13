<script setup lang="ts">
const emit = defineEmits<{
	click: [event: Event]
}>();
</script>

<template>
	<button @click="emit('click', $event)">
		<slot /> <!-- Allows content to be inserted inside the button -->
	</button>
</template>

<style scoped>
button {
	padding: 6px 16px;
	border: none;
	border-radius: 5px;
	background-color: #007BFF;
	color: white;
	cursor: pointer;
}
button:hover {
	background-color: #0056b3;
}
</style>