// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

/// <reference types="vite/client" />
declare const __GIT_REVISION__: string;

declare module "*.grammar" {
	import type { LRParser } from "@lezer/lr";

	export const parser: LRParser;
}
