import { EditorView, Decoration, type DecorationSet, ViewPlugin, ViewUpdate } from "@codemirror/view";
import { StateField, StateEffect } from "@codemirror/state";
import { ErrorData } from 'script-api';

const replaceErrorData = StateEffect.define<ErrorData[]>({
	map: (data, change) =>
		data.map(data => new ErrorData(change.mapPos(data.from), change.mapPos(data.to), data.text))
});

const errorUnderlineField = StateField.define<ErrorData[]>({
	create() {
		return [];
	},
	update(errorData, tr) {
		// errorData = errorData.map(tr.changes);
		for (const e of tr.effects) {
			if (e.is(replaceErrorData)) {
				errorData = e.value;
			}
		}
		return errorData;
	}
});

const errorUnderlineMark = Decoration.mark({ class: "cm-error-underline" });

function renderErrorData(data: ErrorData[]) {
	const decorations = data.map(data =>
		errorUnderlineMark.range(data.from, data.to)
	);
	return Decoration.set(decorations);
}

export const renderErrorDataPlugin = ViewPlugin.fromClass(
	class Plugin {
		decorations: DecorationSet;
		constructor() {
			this.decorations = Decoration.none;
		}
		update(update: ViewUpdate) {
			const erroData = update.state.field(errorUnderlineField, false);
			if (erroData !== undefined) {
				this.decorations = renderErrorData(erroData);
			}
		}
	},
	{
		decorations: (v) => v.decorations
	}
);


const errorUnderlineTheme = EditorView.baseTheme({
	".cm-error-underline": {
		textDecoration: "underline 3px red"
	}
});

export function setErrorUnderlines(view: EditorView, errorData: ErrorData[]) {
	const effects: StateEffect<unknown>[] = [];
	effects.push(replaceErrorData.of(errorData));
	if (!view.state.field(errorUnderlineField, false)) {
		effects.push(StateEffect.appendConfig.of([errorUnderlineField, errorUnderlineTheme]));
	}
	view.dispatch({ effects });
}