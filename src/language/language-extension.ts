import { parser } from "./language.grammar";
import { LRLanguage, LanguageSupport, continuedIndent, flatIndent, indentNodeProp } from "@codemirror/language";
import { styleTags, tags as t } from "@lezer/highlight";

// list if tags: https://lezer.codemirror.net/docs/ref/#highlight.tags
const highlight = styleTags({
	"fn let var": t.definitionKeyword,
	"if else match return": t.controlKeyword,
	Identifier: t.variableName,
	Integer: t.integer,
	BoolLiteral: t.bool,
	String: t.string,
	LineComment: t.comment,
	ArithOp: t.arithmeticOperator,
	LogicOp: t.logicOperator,
	CompareOp: t.compareOperator,
	"( )": t.paren,
	"[ ]": t.squareBracket,
	"{ }": t.brace,
	", : ; ::": t.separator,
	"=": t.definitionOperator,
	"=>": t.punctuation,
})

export function languageExtension() {
	return new LanguageSupport(LRLanguage.define({
		name: "Candli script",
		parser: parser.configure({
			props: [
				highlight,
				indentNodeProp.add({
					Expr: flatIndent,
					"Function IfExpression": continuedIndent()
				}),
			]
		}),
		languageData: {
			commentTokens: { line: "//", block: { open: "/*", close: "*/" } },
		}
	}));
}
