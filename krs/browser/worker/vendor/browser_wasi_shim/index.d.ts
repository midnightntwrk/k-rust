// Declarations for the part of the vendored browser_wasi_shim that
// browser/worker uses. The implementation is index.js (minified upstream code).

export interface FdWriteResult {
  ret: number;
  nwritten: number;
}

export class Fd {
  fd_write(data: Uint8Array): FdWriteResult;
}

export class Inode {}

export class File extends Inode {
  constructor(data: ArrayBufferLike | ArrayLike<number>, options?: { readonly?: boolean });
  data: Uint8Array;
  readonly: boolean;
}

export class Directory extends Inode {
  constructor(contents: Array<[string, Inode]> | Map<string, Inode>);
  contents: Map<string, Inode>;
}

export class OpenFile extends Fd {
  constructor(file: File);
}

export class OpenDirectory extends Fd {
  constructor(dir: Directory);
  dir: Directory;
}

export class PreopenDirectory extends OpenDirectory {
  constructor(name: string, contents: Array<[string, Inode]> | Map<string, Inode>);
  prestat_name: string;
}

export class WASIProcExit extends Error {
  code: number;
}

export class WASI {
  constructor(args: string[], env: string[], fds: Fd[], options?: { debug?: boolean });
  wasiImport: Record<string, (...args: never[]) => unknown>;
  start(instance: { exports: { memory: WebAssembly.Memory; _start: () => unknown } }): number;
}
