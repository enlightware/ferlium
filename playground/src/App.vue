<script setup lang="ts">
import { computed, ref } from 'vue';
import CodeEditor from './components/CodeEditor.vue';
import IrViewer from './components/IrViewer.vue';
import DropdownSelect from './components/DropdownSelect.vue';
import SimpleButton from './components/SimpleButton.vue';
import FlatLinkButton from './components/FlatLinkButton.vue';
import ConsoleOutput from './components/ConsoleOutput.vue';
import { demoCodes } from './demo-codes';
import { defined, executionModes } from './types';
import { onMounted, onUnmounted } from 'vue';
import { panicEvent, reloadPage, saveCrashState, takeCrashState } from './crash-recovery';
import type { ExecutionMode, IrText, SourceRange } from './types';

const demoTitles = demoCodes.map(([title, _]) => title);
const annotationModes = ["none", "light", "full"] as const;
type AnnotationMode = typeof annotationModes[number];
const annotationOptionTitles = [
	"Hide type annotations.",
	"Show simplified type annotations.",
	"Show full type annotations.",
];
// Set when this page load replaces a Rust instance that crashed.
const restoredState = takeCrashState();
const editor = ref<typeof CodeEditor>();
const console = ref<typeof ConsoleOutput>();
const isRunDisabled = ref(false);
const annotationMode = ref<AnnotationMode>(
	annotationModes.find(mode => mode === restoredState?.annotationMode) ?? "light"
);
const executionMode = ref<ExecutionMode>(
	executionModes.find(mode => mode.value === restoredState?.executionMode)?.value ?? "hir"
);
// Whether the restored code is being compiled, so a crash doing so must not reload in a loop.
let isRestoring = false;
// Set once the reload is triggered: a panic is followed by the trap it causes, which must not
// overwrite the saved panic message.
let isReloading = false;
const ir = ref<IrText>();
const sourceSelection = ref<SourceRange>();
const irTitle = computed(() => defined(executionModes.find(mode => mode.value === executionMode.value)).label);
// The pane follows the selected execution mode, not the availability of its content: a transiently
// broken source while typing must not make the layout jump.
const isIrVisible = computed(() => executionMode.value !== "hir");
const workbench = ref<HTMLElement>();
const sourcePaneWidth = ref(50);
const sourcePaneStyle = computed(() => ({ "--source-pane-width": `${sourcePaneWidth.value}%` }));

function updateEditor(data: { value: string, index: number }) {
	if (editor.value) {
		editor.value.setText(demoCodes[data.index]?.[1] ?? '');
	}
};

function updateAnnotationMode(data: { value: string, index: number }) {
	annotationMode.value = annotationModes[data.index] ?? "light";
}

function updateExecutionMode(data: { value: string, index: number }) {
	executionMode.value = executionModes[data.index]?.value ?? "hir";
}

function updateIr(newIr: IrText | undefined) {
	ir.value = newIr;
}

function updateSourceSelection(range: SourceRange) {
	sourceSelection.value = range;
}

function selectSource(range: SourceRange) {
	defined(editor.value).selectRange(range);
}

function startResize(event: PointerEvent) {
	const handle = event.currentTarget as HTMLElement;
	const updateWidth = (moveEvent: PointerEvent) => {
		const bounds = defined(workbench.value).getBoundingClientRect();
		const percentage = (moveEvent.clientX - bounds.left) / bounds.width * 100;
		sourcePaneWidth.value = Math.min(75, Math.max(25, percentage));
	};
	const stopResize = () => {
		handle.removeEventListener("pointermove", updateWidth);
		handle.removeEventListener("pointerup", stopResize);
		handle.removeEventListener("lostpointercapture", stopResize);
		if (handle.hasPointerCapture(event.pointerId)) {
			handle.releasePointerCapture(event.pointerId);
		}
	};
	event.preventDefault();
	handle.setPointerCapture(event.pointerId);
	handle.addEventListener("pointermove", updateWidth);
	handle.addEventListener("pointerup", stopResize);
	handle.addEventListener("lostpointercapture", stopResize);
}

function escapeHtml(text: string): string {
	return text.replace(/[&<>"']/g, char => ({
		"&": "&amp;",
		"<": "&lt;",
		">": "&gt;",
		'"': "&quot;",
		"'": "&#39;",
	})[char] ?? char);
}

function runCode() {
	if (editor.value && !isRunDisabled.value) {
		const consoleOutput = defined(console.value);
		consoleOutput.clear();
		const startedAt = performance.now();
		const result = editor.value.runCode(executionMode.value);
		const duration = performance.now() - startedAt;
		if (result !== undefined) {
			consoleOutput.appendHtml(typeof result === "string"
				? `<span class="error">${escapeHtml(result)}</span>`
				: result.html_message());
		} else {
			consoleOutput.appendHtml("<span class=\"warning\">No expression to run</span>");
		}
		consoleOutput.appendHtml(`<span class="duration">end-to-end ${duration.toFixed(1)} ms</span>`);
		consoleOutput.highlight();
	}
}

function setRunAvailability(status: boolean) {
	isRunDisabled.value = !status;
}

/**
 * Reload the page to replace the Rust instance that is panicking, keeping the playground state.
 * This runs within the panic hook, so it must not call into Rust.
 */
function recoverFromPanic(event: Event) {
	if (isReloading) {
		return;
	}
	const panic = String((event as CustomEvent).detail);
	const saved = saveCrashState({
		code: defined(editor.value).getText(),
		executionMode: executionMode.value,
		annotationMode: annotationMode.value,
		message: `The compiler crashed and the playground was reloaded: ${panic}`,
		compile: !isRestoring,
	});
	if (saved) {
		isReloading = true;
		reloadPage();
	} else {
		const consoleOutput = defined(console.value);
		consoleOutput.appendHtml(`<span class="error">${escapeHtml(
			`The compiler crashed and the playground state could not be saved, reload the page! ${panic}`
		)}</span>`);
	}
}

onUnmounted(() => window.removeEventListener(panicEvent, recoverFromPanic));

onMounted(() => {
	window.addEventListener(panicEvent, recoverFromPanic);
	if (restoredState !== undefined) {
		const consoleOutput = defined(console.value);
		consoleOutput.appendHtml(`<span class="error">${escapeHtml(restoredState.message)}</span>`);
		if (!restoredState.compile) {
			consoleOutput.appendHtml("<span class=\"warning\">Compiling this code crashed again, it will be compiled at the next edit.</span>");
		}
		isRestoring = true;
		try {
			defined(editor.value).setText(restoredState.code, restoredState.compile);
		} finally {
			isRestoring = false;
		}
		return;
	}
	const queryString = window.location.search;
	const urlParams = new URLSearchParams(queryString);
	const code = urlParams.get('code');
	if (code !== null) {
		defined(editor.value).setText(code);
	}
});
</script>

<template>
	<div class="toolbar">
		<div class="execution-controls">
			<SimpleButton
				:disabled="isRunDisabled"
				@click="runCode"
			>
				Run
			</SimpleButton>
			<DropdownSelect
				:items="executionModes.map(mode => mode.label)"
				:initial-index="executionModes.findIndex(mode => mode.value === executionMode)"
				placeholder="Execution"
				@selection-changed="updateExecutionMode"
			/>
		</div>
		<div class="revision" />
		<div class="demo-controls">
			<DropdownSelect
				:items="demoTitles"
				placeholder="Select a code sample"
				@selection-changed="updateEditor"
			/>
			<DropdownSelect
				:items="[...annotationModes]"
				:item-titles="annotationOptionTitles"
				:initial-index="annotationModes.indexOf(annotationMode)"
				placeholder="annotation"
				@selection-changed="updateAnnotationMode"
			/>
			<FlatLinkButton
				href="https://enlightware.github.io/ferlium/book/"
				title="Open documentation"
			>
				🕮
			</FlatLinkButton>
		</div>
	</div>
	<div
		ref="workbench"
		class="workbench"
		:class="{ 'with-ir': isIrVisible }"
	>
		<div
			class="source-pane"
			:style="sourcePaneStyle"
		>
			<CodeEditor
				ref="editor"
				:annotation-mode="annotationMode"
				:execution-mode="executionMode"
				@run-code="runCode()"
				@set-run-availability="setRunAvailability"
				@ir-changed="updateIr"
				@source-selection="updateSourceSelection"
			/>
		</div>
		<div
			v-if="isIrVisible"
			class="resize-handle"
			title="Drag to resize source and IR panes"
			@pointerdown="startResize"
		/>
		<IrViewer
			v-if="isIrVisible"
			:ir="ir"
			:title="irTitle"
			:language="executionMode === 'wasm' ? 'wasm' : 'mir'"
			:source-selection="sourceSelection"
			@source-selected="selectSource"
		/>
	</div>
	<ConsoleOutput
		ref="console"
	/>
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
.revision {
	color: gray;
}

.demo-controls {
	display: flex;
	align-items: center;
	gap: 8px;
}

.execution-controls {
	display: flex;
	align-items: center;
	gap: 8px;
}

.workbench {
	display: flex;
	min-height: 0;
	flex: 1;
}

.source-pane {
	display: flex;
	min-width: 0;
	min-height: 0;
	flex: 1;
}

.workbench.with-ir .source-pane {
	flex: 0 0 var(--source-pane-width);
}

.resize-handle {
	width: 6px;
	flex: 0 0 6px;
	cursor: col-resize;
	background-color: #e9ecef;
}

.resize-handle:hover {
	background-color: #b9d9ff;
}

@media (max-width: 800px) {
	.workbench.with-ir {
		flex-direction: column;
	}

	/* Splitting is vertical here and the handle is hidden, so the source keeps a fixed half of the
	   workbench; without the IR pane it keeps the full width of the base rule. */
	.workbench.with-ir .source-pane {
		flex: 0 0 50%;
	}

	.resize-handle {
		display: none;
	}
}
</style>
