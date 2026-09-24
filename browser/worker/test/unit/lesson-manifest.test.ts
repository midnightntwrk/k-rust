import { describe, expect, test } from "bun:test";
import { parse } from "smol-toml";
import { buildLessonManifest } from "../../scripts/lesson-manifest.ts";

const workspace = `[workspace.package]
version = "1.2.3"
edition = "2024"

[workspace.dependencies]
k = { package = "krs", version = "1", features = ["base"], optional = true }

[workspace.lints.rust]
warnings = "deny"
`;
const member = `[package]
name = "example"
version.workspace = true
edition.workspace = true

[dependencies]
k = { workspace = true, features = ["extra"] }

[lints]
workspace = true
`;

describe("lesson manifest builder", () => {
  test("resolves package fields, dependency features and optional, and lints", () => {
    const built = buildLessonManifest(member, workspace);
    const cargo = parse(built.cargoToml) as { package: { version: string; edition: string }; dependencies: { k: { features: string[]; optional: boolean } }; lints: { rust: { warnings: string } } };
    expect(cargo.package.version).toBe("1.2.3");
    expect(cargo.package.edition).toBe("2024");
    expect(cargo.dependencies.k.features).toEqual(["base", "extra"]);
    expect(cargo.dependencies.k.optional).toBe(true);
    expect(cargo.lints.rust.warnings).toBe("deny");
    expect(built.lintFlags).toEqual(["-D", "warnings"]);
    expect(built.facadeAlias).toBe("k");
    expect(built.version).toBe("1.2.3");
  });

  test("names an unresolved key", () => {
    expect(() => buildLessonManifest(member, `[workspace.package]\nversion = "1.2.3"\nedition = "2024"\n`)).toThrow("dependencies.k.workspace");
    expect(() => buildLessonManifest(member.replace("version.workspace = true", "version.workspace = true\nreadme.workspace = true"), workspace)).toThrow("package.readme.workspace");
  });

  test("resolves build, dev, and target dependencies", () => {
    const extra = `[build-dependencies]\nk.workspace = true\n\n[dev-dependencies]\nk.workspace = true\n\n[target.'cfg(unix)'.dependencies]\nk.workspace = true\n`;
    const built = buildLessonManifest(member.replace("[lints]", `${extra}\n[lints]`), workspace);
    const cargo = parse(built.cargoToml) as { "build-dependencies": { k: { optional: boolean } }; "dev-dependencies": { k: { optional: boolean } }; target: { "cfg(unix)": { dependencies: { k: { optional: boolean } } } } };
    expect(cargo["build-dependencies"].k.optional).toBe(true);
    expect(cargo["dev-dependencies"].k.optional).toBe(true);
    expect(cargo.target["cfg(unix)"].dependencies.k.optional).toBe(true);
  });
});
