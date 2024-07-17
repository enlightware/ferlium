import { parser } from "./language.grammar";
import { LRLanguage, LanguageSupport } from "@codemirror/language";
import { styleTags, tags as t } from "@lezer/highlight";

export function languageExtension() {
	return new LanguageSupport(LRLanguage.define({
		name: "Candli script",
		parser: parser.configure({
			props: [
				styleTags({
					Identifier: t.variableName,
					Integer: t.integer,
					BoolLiteral: t.bool,
					String: t.string,
					LineComment: t.comment,
					fn: t.definitionKeyword,
					let: t.definitionKeyword,
					var: t.definitionKeyword,
					return: t.keyword,
					if: t.controlKeyword,
					else: t.controlKeyword,
					"( )": t.paren
				}),
			]
		}),
		languageData: {
			commentTokens: { line: "//", block: { open: "/*", close: "*/" } },
		}
	}));
}
