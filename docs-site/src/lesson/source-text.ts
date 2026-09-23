// UTF-8 byte ranges (the worker's SourceRange) <-> the UTF-16 indices of the
// editor text, and 1-based line/column positions for display.

/** UTF-16 index of a UTF-8 byte offset; offsets inside a code point round down, past the end clamp. */
export function byteToIndex(text: string, byteOffset: number): number {
  let bytes = 0
  let index = 0
  while (index < text.length) {
    const code = text.codePointAt(index)!
    const width = code < 0x80 ? 1 : code < 0x800 ? 2 : code < 0x10000 ? 3 : 4
    if (bytes + width > byteOffset) break
    bytes += width
    index += code >= 0x10000 ? 2 : 1
  }
  return index
}

/** 1-based line and column (in code points, as rustc counts) of a UTF-16 index. */
export function lineColumn(text: string, index: number): { line: number; column: number } {
  const before = text.slice(0, index)
  const lineStart = before.lastIndexOf('\n') + 1
  const line = before.split('\n').length
  return { line, column: [...text.slice(lineStart, index)].length + 1 }
}

export interface TextRange {
  start: number
  end: number
}

/** The editor range of an authored UTF-8 byte range. */
export function authoredRange(text: string, range: { start: number; end: number }): TextRange {
  return { start: byteToIndex(text, range.start), end: byteToIndex(text, range.end) }
}

export async function sha256Text(text: string): Promise<string> {
  const digest = await crypto.subtle.digest('SHA-256', new TextEncoder().encode(text))
  return [...new Uint8Array(digest)].map((byte) => byte.toString(16).padStart(2, '0')).join('')
}
