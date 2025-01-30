<script setup lang="ts">
import { ref } from 'vue';

const props = defineProps<{
	items: string[]
}>();

interface Selection {
	value: string;
	index: number;
}

const emit = defineEmits<{
	selectionChanged: [value: Selection]
}>();

const selected = ref('');

const handleChange = () => {
	const index = props.items.indexOf(selected.value);
	emit('selectionChanged', { value: selected.value, index });
};
</script>

<template>
	<select
		v-model="selected"
		@change="handleChange"
	>
		<option
			disabled
			value=""
		>
			Please select one
		</option>
		<option
			v-for="(item, index) in items"
			:key="index"
			:value="item"
		>
			{{ item }}
		</option>
	</select>
</template>

<style scoped>
select {
	max-width: 200px;
}
</style>