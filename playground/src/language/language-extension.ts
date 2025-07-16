// Copyright 2025 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
import { parser } from "./language.grammar";
import { LRLanguage, LanguageSupport, continuedIndent, flatIndent, indentNodeProp } from "@codemirror/language";
import { styleTags, tags as t } from "@lezer/highlight";

// Note: test grammar here: https://lezer-playground.vercel.app/

// list if tags: https://lezer.codemirror.net/docs/ref/#highlight.tags
const highlight = styleTags({
	"fn let mut": t.definitionKeyword,
	"if else match for return": t.controlKeyword,
	"in": t.operatorKeyword,
	"Type/...": t.typeName,
	MutTyOrInfer: t.typeName,
	Identifier: t.variableName,
	Integer: t.integer,
	Boolean: t.bool,
	String: t.string,
	LineComment: t.lineComment,
	BlockComment: t.blockComment,
	ArithOp: t.arithmeticOperator,
	LogicOp: t.logicOperator,
	CompareOp: t.compareOperator,
	"=": t.definitionOperator,
	".. =>": t.punctuation,
	"( )": t.paren,
	"[ ]": t.squareBracket,
	"{ }": t.brace,
	".": t.derefOperator,
	", : ; ::": t.separator,
})

export function languageExtension() {
	return new LanguageSupport(LRLanguage.define({
		name: "Candli script",
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
