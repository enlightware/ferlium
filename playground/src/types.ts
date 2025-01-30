// Copyright 2025 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
/**
 * Return [[value]], throw if null.
 * @param value - Value of type T | null
 * @param message - An optional user message to send with the exception
 * @return value of type T or throw if value is null
 */
export function nonnull<T>(value: T | null, message: string | null = null): T {
	const userMessage = message !== null ? message : 'value is null';
	if (value === null) {
		throw new TypeError(`nonnull: ${userMessage}`);
	}
	return value;
}

/**
 * Return [[value]], throw if undefined.
 * @param value - Value of type T | undefined
 * @param message - An optional user message to send with the exception
 * @return value of type T or throw if value is undefined
 */
export function defined<T>(value: T | undefined, message: string | null = null): T {
	const userMessage = message !== null ? message : 'value is undefined';
	if (value === undefined) {
		throw new TypeError(`defined: ${userMessage}`);
	}
	return value;
}