<script setup lang="ts">
import { computed, ref } from 'vue';

const props = withDefaults(defineProps<{
	items: string[],
	itemTitles?: string[],
	initialIndex?: number,
	placeholder?: string,
}>(), {
	itemTitles: () => [],
	initialIndex: -1,
	placeholder: 'Select',
});

interface Selection {
	value: string;
	index: number;
}

const emit = defineEmits<{
	selectionChanged: [value: Selection]
}>();

const selected = ref(props.initialIndex >= 0 ? props.items[props.initialIndex] ?? '' : '');
const selectedTitle = computed(() => props.itemTitles[props.items.indexOf(selected.value)] ?? '');

const handleChange = () => {
	const index = props.items.indexOf(selected.value);
	emit('selectionChanged', { value: selected.value, index });
};
</script>

<template>
	<select
		v-model="selected"
		:title="selectedTitle"
		@change="handleChange"
	>
		<option
			disabled
			value=""
		>
			{{ placeholder }}
		</option>
		<option
			v-for="(item, index) in items"
			:key="index"
			:title="itemTitles[index] ?? ''"
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
