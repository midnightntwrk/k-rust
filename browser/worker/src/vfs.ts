// VFS construction over the vendored browser_wasi_shim in-memory filesystem.
//
// Immutable layers (sysroot, pack, framework sources) are File objects created
// once per worker from verified bytes. Each build wraps them in fresh Directory
// objects, so no Directory (whose `parent` link the shim mutates) and no
// per-build file is shared between builds; File objects are read-only.

import { Directory, File, type Inode, PreopenDirectory } from "../vendor/browser_wasi_shim/index.js";
import { sha256Hex } from "./pack.ts";
import type { VfsEntry } from "./protocol.ts";

/** A directory description: name -> File (leaf) or nested Tree. */
export type Tree = Map<string, File | Tree>;

/** Parses the RIWB1 sysroot bundle: "RIWB1\n" + u32le index length + JSON index + data. */
export function parseSysrootBundle(bytes: Uint8Array): Map<string, Uint8Array> {
  const magic = new TextDecoder().decode(bytes.subarray(0, 6));
  if (magic !== "RIWB1\n") throw new Error("bad RIWB1 sysroot bundle magic");
  const indexLength = new DataView(bytes.buffer, bytes.byteOffset + 6, 4).getUint32(0, true);
  const index = JSON.parse(new TextDecoder().decode(bytes.subarray(10, 10 + indexLength))) as {
    files: Array<{ p: string; o: number; l: number }>;
  };
  const base = 10 + indexLength;
  const files = new Map<string, Uint8Array>();
  for (const file of index.files) {
    if (file.p === "manifest.json") continue;
    if (file.p.startsWith("/") || file.p.split("/").includes("..")) throw new Error(`unsafe bundle path ${file.p}`);
    files.set(file.p, bytes.subarray(base + file.o, base + file.o + file.l));
  }
  return files;
}

/** Inserts `file` at the relative `path` ("a/b/c") of `tree`. */
export function insert(tree: Tree, path: string, file: File): void {
  const parts = path.split("/").filter((part) => part !== "");
  const name = parts.pop();
  if (name === undefined) throw new Error(`empty VFS path ${path}`);
  let dir = tree;
  for (const part of parts) {
    let next = dir.get(part);
    if (next === undefined) {
      next = new Map();
      dir.set(part, next);
    }
    if (next instanceof File) throw new Error(`VFS path ${path} crosses a file`);
    dir = next;
  }
  if (dir.has(name)) throw new Error(`duplicate VFS path ${path}`);
  dir.set(name, file);
}

/** Builds a tree of read-only File objects from absolute or relative paths. */
export function readOnlyTree(entries: Iterable<[string, Uint8Array]>): Tree {
  const tree: Tree = new Map();
  for (const [path, bytes] of entries) insert(tree, path, new File(bytes, { readonly: true }));
  return tree;
}

/** Fresh Directory objects over the tree's (shared, read-only) File objects. */
function materialize(tree: Tree): Array<[string, Inode]> {
  return [...tree.entries()].map(([name, value]) => [name, value instanceof File ? value : new Directory(materialize(value))]);
}

export function preopen(name: string, tree: Tree): PreopenDirectory {
  return new PreopenDirectory(name, materialize(tree));
}

/** Merges trees; a path present in more than one is an error. */
export function merge(...trees: Tree[]): Tree {
  const out: Tree = new Map();
  const into = (target: Tree, source: Tree, prefix: string) => {
    for (const [name, value] of source) {
      const existing = target.get(name);
      if (value instanceof File) {
        if (existing !== undefined) throw new Error(`duplicate VFS path ${prefix}${name}`);
        target.set(name, value);
      } else {
        if (existing instanceof File) throw new Error(`VFS path ${prefix}${name} is a file and a directory`);
        const child: Tree = existing ?? new Map();
        target.set(name, child);
        into(child, value, `${prefix}${name}/`);
      }
    }
  };
  for (const tree of trees) into(out, tree, "/");
  return out;
}

/** Lists every file under a preopened directory, as absolute paths with hashes. */
export async function listDirectory(prefix: string, dir: Directory): Promise<VfsEntry[]> {
  const out: VfsEntry[] = [];
  const walk = async (path: string, node: Directory) => {
    for (const [name, child] of [...node.contents.entries()].sort(([a], [b]) => (a < b ? -1 : a > b ? 1 : 0))) {
      const full = path === "/" ? `/${name}` : `${path}/${name}`;
      if (child instanceof File) out.push({ path: full, bytes: child.data.byteLength, sha256: await sha256Hex(child.data) });
      else if (child instanceof Directory) await walk(full, child);
    }
  };
  await walk(prefix, dir);
  return out;
}

/** Reads a file out of a Directory by relative path, or null. */
export function readFile(dir: Directory, path: string): Uint8Array | null {
  let node: Inode | undefined = dir;
  for (const part of path.split("/").filter((p) => p !== "")) {
    if (!(node instanceof Directory)) return null;
    node = node.contents.get(part);
  }
  return node instanceof File ? node.data : null;
}
