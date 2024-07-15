import { StateEffect, StateField } from "@codemirror/state";
import { Decoration, EditorView, ViewPlugin, ViewUpdate, WidgetType, type DecorationSet } from "@codemirror/view"

interface TypeHintData {
    pos: number;
    hint: string;
}

const replaceTypeHints = StateEffect.define<TypeHintData[]>({
    map: (data, change) =>
        data.map(({ pos, hint }) => ({ pos: change.mapPos(pos), hint }))
});

const TypeHintsField = StateField.define<TypeHintData[]>({
    create() {
        return [];
    },
    update(hints, tr) {
        //hints = hints.map(tr.changes);
        for (const e of tr.effects) {
            if (e.is(replaceTypeHints)) {
                hints = e.value;
            }
        }
        return hints;
    }
});

class TypeHintWidget extends WidgetType {
    constructor(readonly hint: string) { super() }

    eq(other: TypeHintWidget) { return other.hint == this.hint }

    toDOM() {
        const hint = document.createElement("span");
        hint.className = "cm-type-hint";
        hint.innerText = this.hint;
        return hint;
    }
}

function renderTypeHints(data: TypeHintData[]) {
    const widgets = data.map(data => {
        const widget = Decoration.widget({
            widget: new TypeHintWidget(data.hint),
            side: 1
        });
        return widget.range(data.pos);
    });
    return Decoration.set(widgets);
}

export const renderTypeHintPlugin = ViewPlugin.fromClass(
    class Plugin {
        decorations: DecorationSet;
        constructor() {
            this.decorations = Decoration.none;
        }
        update(update: ViewUpdate) {
            const typeHints = update.state.field(TypeHintsField, false);
            if (typeHints !== undefined) {
                this.decorations = renderTypeHints(typeHints);
            }
        }
    },
    {
        decorations: (v) => v.decorations
    }
);

const typeHintsTheme = EditorView.baseTheme({
    ".cm-type-hint": {
        opacity: 0.5
    }
});

export function setTypeHints(view: EditorView, data: TypeHintData[]) {
    const effects: StateEffect<unknown>[] = [];
    effects.push(replaceTypeHints.of(data));
    if (!view.state.field(TypeHintsField, false)) {
        effects.push(StateEffect.appendConfig.of([TypeHintsField, typeHintsTheme]));
    }
    view.dispatch({ effects });
}