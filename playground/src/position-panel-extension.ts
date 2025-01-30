import { EditorState } from "@codemirror/state";
import { EditorView, type Panel } from "@codemirror/view";
import { showPanel } from "@codemirror/view";
import { defined } from "./types";

function getCurrentPosition(state: EditorState): string {
	const ranges = state.selection.ranges;
	const cursors = ranges.filter(range => range.empty);
	if (cursors.length === 0) {
		if (ranges.length === 1) {
			return `${ranges.length} selection`;
		}
		return `${ranges.length} selections`;
	}
	if (cursors.length > 1) {
		return `${cursors.length} cursors`;
	}
	const line = state.doc.lineAt(state.selection.main.head);
	return `Ln ${line.number}, Col ${defined(cursors[0]).head - line.from}`;
}

function cursorPositionPanel(view: EditorView): Panel {
	const panel = document.createElement("div");
	panel.classList.add("cursor-panel");
	panel.textContent = getCurrentPosition(view.state);
	return {
		dom: panel,
		update(update) {
			if (update.selectionSet) {
				panel.textContent = getCurrentPosition(view.state);
			}
		}
	}
}

export function positionPanel() {
	return showPanel.of(cursorPositionPanel)
}