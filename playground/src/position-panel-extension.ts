// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
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
	return `Ln ${line.number}, Col ${defined(cursors[0]).head - line.from + 1}`;
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