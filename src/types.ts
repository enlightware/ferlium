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