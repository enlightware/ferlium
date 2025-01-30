import { StateEffect, StateField } from "@codemirror/state";
import { Decoration, EditorView, ViewPlugin, ViewUpdate, WidgetType, type DecorationSet } from "@codemirror/view";
import { AnnotationData } from 'script-api';

const replaceAnnotations = StateEffect.define<AnnotationData[]>({
    map: (data, change) =>
        data.map(data => new AnnotationData(change.mapPos(data.pos), data.hint))
});

const AnnotationsField = StateField.define<AnnotationData[]>({
    create() {
        return [];
    },
    update(hints, tr) {
        //hints = hints.map(tr.changes);
        for (const e of tr.effects) {
            if (e.is(replaceAnnotations)) {
                hints = e.value;
            }
        }
        return hints;
    }
});

class AnnotationWidget extends WidgetType {
    constructor(readonly hint: string) { super() }

    eq(other: AnnotationWidget) { return other.hint === this.hint }

    toDOM() {
        const hint = document.createElement("span");
        hint.className = "cm-annotation";
        hint.innerText = this.hint;
        return hint;
    }
}

function renderAnnotations(data: AnnotationData[]) {
    const widgets = data.map(data => {
        const widget = Decoration.widget({
            widget: new AnnotationWidget(data.hint),
            side: 1
        });
        return widget.range(data.pos);
    });
    return Decoration.set(widgets);
}

export const renderAnnotationsPlugin = ViewPlugin.fromClass(
    class Plugin {
        decorations: DecorationSet;
        constructor() {
            this.decorations = Decoration.none;
        }
        update(update: ViewUpdate) {
            const typeHints = update.state.field(AnnotationsField, false);
            if (typeHints !== undefined) {
                this.decorations = renderAnnotations(typeHints);
            }
        }
    },
    {
        decorations: (v) => v.decorations
    }
);

const annotationsTheme = EditorView.baseTheme({
    ".cm-annotation": {
        opacity: 0.5
    }
});

export function setAnnotations(view: EditorView, data: AnnotationData[]) {
    const effects: StateEffect<unknown>[] = [];
    effects.push(replaceAnnotations.of(data));
    if (!view.state.field(AnnotationsField, false)) {
        effects.push(StateEffect.appendConfig.of([AnnotationsField, annotationsTheme]));
    }
    view.dispatch({ effects });
}