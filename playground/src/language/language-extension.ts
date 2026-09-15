// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

import { parser } from "./language.grammar";
import { LRLanguage, LanguageSupport, continuedIndent, flatIndent, indentNodeProp } from "@codemirror/language";
import { styleTags, tags as t } from "@lezer/highlight";

// Note: test grammar here: https://lezer-playground.vercel.app/

// list if tags: https://lezer.codemirror.net/docs/ref/#highlight.tags
const highlight = styleTags({
	"pub fn let ref mut impl struct enum trait subscript const use": t.definitionKeyword,
	"TypeAliasDef/type": t.definitionKeyword,
	"if else match for return yield break continue loop": t.controlKeyword,
	"in as and or not": t.operatorKeyword,
	"Type/... TypeAllowRecordVariant/... TypeNoRecordVariant/...": t.typeName,
	"CastTargetType/...": t.typeName,
	MutTyOrInfer: t.typeName,
	"Attribute/...": t.annotation,
	"Attribute/Identifier": t.attributeName,
	Identifier: t.name,
	"TypeName/...": t.typeName,
	"TagName/...": t.tagName,
	"FieldName/...": t.propertyName,
	UInt: t.integer,
	Boolean: t.bool,
	String: t.string,
	LineComment: t.lineComment,
	BlockComment: t.blockComment,
	ArithOp: t.arithmeticOperator,
	LogicOp: t.logicOperator,
	CompareOp: t.compareOperator,
	AssignOp: t.definitionOperator,
	UpdateOp: t.updateOperator,
	".. =>": t.punctuation,
	"( )": t.paren,
	"[ ]": t.squareBracket,
	"{ }": t.brace,
	".": t.derefOperator,
	"|>": t.controlOperator,
	", : ; ::": t.separator,
})

export function languageExtension() {
	return new LanguageSupport(LRLanguage.define({
		name: "Ferlium",
		parser: parser.configure({
			props: [
				highlight,
				indentNodeProp.add({
					expr: flatIndent,
					Block: continuedIndent()
				}),
			]
		}),
		languageData: {
			commentTokens: { line: "//", block: { open: "/*", close: "*/" } },
		}
	}));
}
