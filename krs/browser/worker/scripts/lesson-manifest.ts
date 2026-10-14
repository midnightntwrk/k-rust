import { parse, stringify, type TomlTable } from "smol-toml";
import { validateLessonCargoToml } from "../src/lesson-cargo-toml.ts";

type Table = Record<string, unknown>;
const table = (value: unknown, key: string): Table => {
  if (value === null || typeof value !== "object" || Array.isArray(value)) throw new Error(`${key} must be a table`);
  return value as Table;
};
const requiredString = (value: unknown, key: string): string => {
  if (typeof value !== "string") throw new Error(`${key} must be a string`);
  return value;
};
const dependencyTables = new Set(["dependencies", "dev-dependencies", "build-dependencies"]);

export interface BuiltLessonManifest {
  cargoToml: string;
  name: string;
  version: string;
  edition: string;
  libName: string;
  facadeAlias: string;
  lintFlags: string[];
  namespace?: string;
}

/** Resolve Cargo workspace inheritance once, before the manifest enters the lesson protocol. */
export function buildLessonManifest(packageText: string, workspaceText?: string): BuiltLessonManifest {
  const manifest = table(parse(packageText), "Cargo.toml");
  const workspace = manifest.workspace === undefined
    ? (workspaceText === undefined ? undefined : table(parse(workspaceText).workspace, "workspace"))
    : table(manifest.workspace, "workspace");
  const member = table(manifest.package, "package");
  let changed = false;
  for (const [key, value] of Object.entries(member)) {
    if (value !== null && typeof value === "object" && !Array.isArray(value) && table(value, `package.${key}`).workspace === true) {
      const inherited = workspace?.package === undefined ? undefined : table(workspace.package, "workspace.package")[key];
      if (inherited === undefined) throw new Error(`cannot resolve package.${key}.workspace`);
      member[key] = inherited;
      changed = true;
    }
  }

  const resolveDependencies = (parent: Table, prefix: string): void => {
    for (const [key, value] of Object.entries(parent)) {
      const path = prefix ? `${prefix}.${key}` : key;
      if (dependencyTables.has(key)) {
        const deps = table(value, path);
        for (const [alias, declaration] of Object.entries(deps)) {
          if (declaration === null || typeof declaration !== "object" || Array.isArray(declaration)) continue;
          const override = table(declaration, `${path}.${alias}`);
          if (override.workspace !== true) continue;
          const allowed = new Set(["workspace", "features", "optional", "default-features"]);
          const conflicting = Object.keys(override).filter((key) => !allowed.has(key));
          if (conflicting.length > 0) throw new Error(`cannot override workspace dependency with ${conflicting.map((key) => `${path}.${alias}.${key}`).join(", ")}`);
          const inherited = workspace?.dependencies === undefined ? undefined : table(workspace.dependencies, "workspace.dependencies")[alias];
          if (inherited === undefined) throw new Error(`cannot resolve ${path}.${alias}.workspace`);
          const base = typeof inherited === "string" ? { version: inherited } : table(inherited, `workspace.dependencies.${alias}`);
          if (override["default-features"] !== undefined) {
            if (typeof override["default-features"] !== "boolean") throw new Error(`${path}.${alias}.default-features must be a boolean`);
            if (override["default-features"] === false && base["default-features"] !== false) {
              throw new Error(`${path}.${alias}.default-features = false cannot override workspace.dependencies.${alias}.default-features`);
            }
          }
          if (override.optional !== undefined && typeof override.optional !== "boolean") throw new Error(`${path}.${alias}.optional must be a boolean`);
          const { workspace: _workspace, ...extra } = override;
          const merged = { ...base, ...extra };
          if (base.features !== undefined || extra.features !== undefined) {
            const baseFeatures = base.features ?? [];
            const extraFeatures = extra.features ?? [];
            if (!Array.isArray(baseFeatures) || !Array.isArray(extraFeatures)) throw new Error(`${path}.${alias}.features must be an array`);
            merged.features = [...new Set([...baseFeatures, ...extraFeatures])];
          }
          deps[alias] = merged;
          changed = true;
        }
      } else if (key === "target") {
        for (const [target, targetValue] of Object.entries(table(value, path))) resolveDependencies(table(targetValue, `${path}.${target}`), `${path}.${target}`);
      }
    }
  };
  resolveDependencies(manifest, "");

  if (manifest.lints !== undefined) {
    const lints = table(manifest.lints, "lints");
    if (lints.workspace === true) {
      const conflicting = Object.keys(lints).filter((key) => key !== "workspace");
      if (conflicting.length > 0) throw new Error(`lints.workspace cannot be combined with ${conflicting.map((key) => `lints.${key}`).join(", ")}`);
      if (workspace?.lints === undefined) throw new Error("cannot resolve lints.workspace");
      manifest.lints = table(workspace.lints, "workspace.lints");
      changed = true;
    }
  }
  const cargoToml = changed ? stringify(manifest as TomlTable) : packageText;
  validateLessonCargoToml(cargoToml);

  const name = requiredString(member.name, "package.name");
  const version = requiredString(member.version, "package.version");
  const edition = requiredString(member.edition, "package.edition");
  const libName = manifest.lib === undefined || table(manifest.lib, "lib").name === undefined
    ? name.replaceAll("-", "_")
    : requiredString(table(manifest.lib, "lib").name, "lib.name");
  const deps = manifest.dependencies === undefined ? {} : table(manifest.dependencies, "dependencies");
  const facadeAlias = Object.entries(deps).find(([alias, value]) => alias === "krs" || (value !== null && typeof value === "object" && !Array.isArray(value) && table(value, `dependencies.${alias}`).package === "krs"))?.[0];
  if (facadeAlias === undefined) throw new Error("dependencies.krs facade is missing");
  const rustLints = manifest.lints === undefined ? {} : (table(manifest.lints, "lints").rust === undefined ? {} : table(table(manifest.lints, "lints").rust, "lints.rust"));
  const levelFlag: Record<string, string> = { forbid: "-F", deny: "-D", warn: "-W", allow: "-A" };
  const lintFlags = Object.entries(rustLints)
    .map(([lint, value]) => {
      const entry = typeof value === "string" ? { level: value, priority: 0 } : table(value, `lints.rust.${lint}`);
      const level = requiredString(entry.level, `lints.rust.${lint}.level`);
      if (!levelFlag[level]) throw new Error(`lints.rust.${lint}.level is invalid`);
      return { lint, level, priority: Number(entry.priority ?? 0) };
    })
    .sort((a, b) => a.priority - b.priority || a.lint.localeCompare(b.lint))
    .flatMap(({ lint, level }) => [levelFlag[level]!, lint]);
  const metadata = member.metadata === undefined ? undefined : table(member.metadata, "package.metadata");
  const krs = metadata?.krs === undefined ? undefined : table(metadata.krs, "package.metadata.krs");
  const namespace = krs?.["k-namespace"];
  return { cargoToml, name, version, edition, libName, facadeAlias, lintFlags, ...(typeof namespace === "string" ? { namespace } : {}) };
}
