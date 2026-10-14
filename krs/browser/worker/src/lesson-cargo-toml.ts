import { parse } from "smol-toml";

/** Reject Cargo workspace inheritance before mounting a lesson in the browser VFS. */
export function validateLessonCargoToml(text: string): void {
  let manifest: Record<string, unknown>;
  try {
    manifest = parse(text);
  } catch (error) {
    throw new Error(`cargo_toml is invalid TOML: ${String(error)}`);
  }
  const visit = (value: unknown, path: string): void => {
    if (Array.isArray(value)) {
      value.forEach((item, index) => visit(item, `${path}[${index}]`));
    } else if (value !== null && typeof value === "object") {
      for (const [key, item] of Object.entries(value)) {
        const child = path ? `${path}.${key}` : key;
        if (key === "workspace" && item === true) throw new Error(`cargo_toml contains unresolved ${child} = true`);
        visit(item, child);
      }
    }
  };
  visit(manifest, "");
}
