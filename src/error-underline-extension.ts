import { EditorView, Decoration, type DecorationSet } from "@codemirror/view";
import { StateField, StateEffect } from "@codemirror/state";

const clearErrorUnderlines = StateEffect.define({});
const addErrorUnderline = StateEffect.define<{ from: number, to: number }>({
	map: ({ from, to }, change) => ({ from: change.mapPos(from), to: change.mapPos(to) })
});

const errorUnderlineField = StateField.define<DecorationSet>({
	create() {
		return Decoration.none
	},
	update(underlines, tr) {
		underlines = underlines.map(tr.changes);
		for (const e of tr.effects) {
			if (e.is(clearErrorUnderlines)) {
				underlines = underlines.update({
					filter: () => false
				});
			}
			if (e.is(addErrorUnderline)) {
				underlines = underlines.update({
					add: [errorUnderlineMark.range(e.value.from, e.value.to)]
				});
			}
		}
		return underlines;
	},
	provide: f => EditorView.decorations.from(f)
});

const errorUnderlineMark = Decoration.mark({ class: "cm-error-underline" })

const errorUnderlineTheme = EditorView.baseTheme({
	".cm-error-underline": {
		textDecoration: "underline 3px red"
	}
});

export function setErrorUnderlines(view: EditorView, ranges: [number, number][]) {
	const effects: StateEffect<unknown>[] = [clearErrorUnderlines.of(null)];
	for (const [from, to] of ranges) {
		effects.push(addErrorUnderline.of({ from, to }));
	}
	if (!view.state.field(errorUnderlineField, false)) {
		effects.push(StateEffect.appendConfig.of([errorUnderlineField, errorUnderlineTheme]));
	}
	view.dispatch({ effects });
}