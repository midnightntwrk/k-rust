// Minimal reader for relocatable wasm objects (tool-conventions Linking.md):
// counts the entries of the WASM_INIT_FUNCS (6) subsection of the "linking"
// custom section. A missing subsection counts as 0; a non-wasm input as -1.

function leb(bytes: Uint8Array, at: { i: number }): number {
  let result = 0;
  let shift = 0;
  for (;;) {
    const byte = bytes[at.i++];
    if (byte === undefined) throw new Error("truncated LEB128");
    result += (byte & 0x7f) * 2 ** shift;
    if ((byte & 0x80) === 0) return result;
    shift += 7;
  }
}

export function initFuncCount(bytes: Uint8Array): number {
  if (bytes.length < 8 || bytes[0] !== 0 || bytes[1] !== 0x61 || bytes[2] !== 0x73 || bytes[3] !== 0x6d) return -1;
  const at = { i: 8 };
  while (at.i < bytes.length) {
    const id = bytes[at.i++]!;
    const size = leb(bytes, at);
    const end = at.i + size;
    if (id === 0) {
      const nameLength = leb(bytes, at);
      const name = new TextDecoder().decode(bytes.subarray(at.i, at.i + nameLength));
      at.i += nameLength;
      if (name === "linking") {
        leb(bytes, at); // version
        while (at.i < end) {
          const type = bytes[at.i++]!;
          const length = leb(bytes, at);
          const next = at.i + length;
          if (type === 6) return leb(bytes, at);
          at.i = next;
        }
        return 0;
      }
    }
    at.i = end;
  }
  return 0;
}
