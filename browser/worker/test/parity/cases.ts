// IR-18 diagnostic parity cases: the BL-006 set (D001-D008; fixtures copied
// byte for byte from the BL-006 spike into test/fixtures/bl006, hashes
// checked against the BL-006 contract), D009, and
// two rustc cases that decide how respanned tokens map (X1, X2).
//
//   bun test/parity/cases.ts write-lessons ASSETS_DIR OUT_DIR   (lesson manifests for twin controls)

import { mkdirSync, readFileSync, writeFileSync } from "node:fs";
import { join } from "node:path";
import type { FaultInjection, LessonManifest } from "../../src/protocol.ts";

export const FIXTURES = join(import.meta.dir, "../fixtures");

export type Stage = "expander" | "policy" | "rustc" | "collector" | "lowering";

export interface DiagnosticCase {
  id: string;
  title: string;
  lesson: LessonName;
  /** Source file under test/fixtures. */
  fixture: string;
  /** BL-006 contract content_sha256 of the fixture, when it is a BL-006 fixture. */
  bl006Sha256?: string;
  faultInjection?: FaultInjection;
  /** Stage of the native producer (ticket table). */
  nativeStage: Stage;
  /** The browser bundle is lowered natively (IR-19 has no Wasm lowering yet). */
  nativeLoweringOfBrowserBundle?: boolean;
  /** Which native diagnostic(s) this case compares (index into the native list), when a compile emits several. */
  nativeSelect?: number[];
  /** A known blocker that makes the browser side fail before the target diagnostic. */
  blockedBy?: { ticket: string; reason: string };
  note: string;
}

export type LessonName = "tour-minimal" | "bl006-rust-expansion" | "bl006-wrong-result" | "bl006-overlap";

export const CASES: DiagnosticCase[] = [
  {
    id: "D001",
    title: "malformed KRS attribute",
    lesson: "bl006-rust-expansion",
    fixture: "bl006/malformed_macro.rs",
    bl006Sha256: "1042c8f578f4d523bcc973f2ca1faa78d6b875df8bebe1f2a43e666a5aee563e",
    nativeStage: "expander",
    note: "krs-macros compile_error! natively; the IR-11 expander diagnostic in the browser",
  },
  {
    id: "D002",
    title: "unresolved constructor sort in authored input",
    lesson: "bl006-rust-expansion",
    fixture: "bl006/unresolved_constructor.rs",
    bl006Sha256: "705c28f35e9f95938b7b95262ea6da8e9532fc1bf05eceb9b99a5aeceffebeaa",
    nativeStage: "rustc",
    nativeSelect: [0],
    blockedBy: { ticket: "IR-26", reason: "rustc.wasm (195111dff) traps with no diagnostic on E0433 for an unresolved module in a type path (IR-15 finding 1)" },
    note: "first E0433 (authored `missing`)",
  },
  {
    id: "D003",
    title: "wrong KRS rule result sort",
    lesson: "bl006-wrong-result",
    fixture: "bl006/wrong_result.rs",
    bl006Sha256: "d817ac0a9c9cbe5bf9fd634ea9e7b5d35b42c832dd85c840475038e56028d272",
    nativeStage: "lowering",
    nativeLoweringOfBrowserBundle: true,
    note: "unstructured InvalidTerm from lower_descriptor_bundle; must stay unmappable",
  },
  {
    id: "D004",
    title: "unresolved path in macro-generated reference check",
    lesson: "bl006-rust-expansion",
    fixture: "bl006/unresolved_constructor.rs",
    bl006Sha256: "705c28f35e9f95938b7b95262ea6da8e9532fc1bf05eceb9b99a5aeceffebeaa",
    nativeStage: "rustc",
    nativeSelect: [1],
    blockedBy: { ticket: "IR-26", reason: "same compile as D002" },
    note: "second E0433 (generated reference check, reported at the invocation)",
  },
  {
    id: "D005",
    title: "stale authored source at collection",
    lesson: "tour-minimal",
    fixture: "tour-minimal.rs",
    faultInjection: { kind: "collector-source", files: { "src/lib.rs": "@fixture:tour-minimal-e1.rs" } },
    nativeStage: "collector",
    note: "test-only fault: the collector reads the E1 source while the compiled descriptors come from the original",
  },
  {
    id: "D006",
    title: "missing authored source at collection",
    lesson: "tour-minimal",
    fixture: "tour-minimal.rs",
    faultInjection: { kind: "collector-source", files: { "src/lib.rs": null } },
    nativeStage: "collector",
    note: "test-only fault: src/lib.rs is absent from the collector's VFS",
  },
  {
    id: "D007",
    title: "unsupported external procedural macro",
    lesson: "bl006-rust-expansion",
    fixture: "bl006/external_proc_macro.rs",
    bl006Sha256: "0f488a13d0c0bcee66bff4d7472f29ae2e93d7b74136202e052ce61f9603b3c9",
    nativeStage: "policy",
    note: "native cargo check succeeds; the browser policy target is serde::Serialize 9..25 (BL-006 contract)",
  },
  {
    id: "D008",
    title: "overlapping readable rule heads",
    lesson: "bl006-overlap",
    fixture: "bl006/overlap.rs",
    bl006Sha256: "fc9f489244b8ad0423f0a3e40b29800359a83a59834a465201c2da74ca6a835c",
    nativeStage: "lowering",
    nativeLoweringOfBrowserBundle: true,
    note: "DiagnosticEnvelope overlapping-rule-heads (stage analysis) from krs-cli prepare()",
  },
  {
    id: "D009",
    title: "error wholly inside the generated registration table",
    lesson: "tour-minimal",
    fixture: "tour-minimal.rs",
    faultInjection: { kind: "registration-table-missing-factory" },
    nativeStage: "rustc",
    note: "test-only fault injection after the IR-11 expander (path C): no authored input reaches the table without an expander defect",
  },
  {
    id: "X1",
    title: "unresolved variant in k::k! (IR-15 two E0599)",
    lesson: "tour-minimal",
    fixture: "rustc-unresolved-variant.rs",
    nativeStage: "rustc",
    note: "the second E0599 is on the respanned __krs_variant_type_id_Missing (IR-10/IR-15 finding)",
  },
  {
    id: "X2",
    title: "rule head names a missing constructor",
    lesson: "tour-minimal",
    fixture: "rustc-rule-head-missing-constructor.rs",
    nativeStage: "rustc",
    note: "a rule-head anchor (IR-10: 4 respanned rule-head anchors) reaches rustc only as __krs_variant_type_id_Baz",
  },
];

export function fixtureText(name: string): string {
  return readFileSync(join(FIXTURES, name), "utf8");
}

/** Resolves "@fixture:<name>" values of a collector-source fault to fixture text. */
export function resolveFault(fault: FaultInjection | undefined): FaultInjection | undefined {
  if (!fault || fault.kind !== "collector-source") return fault;
  const files: Record<string, string | null> = {};
  for (const [path, value] of Object.entries(fault.files)) files[path] = value?.startsWith("@fixture:") ? fixtureText(value.slice(9)) : value;
  return { kind: "collector-source", files };
}

/**
 * Lesson manifests for the BL-006 packages, rendered as stage-assets.ts renders
 * tour-minimal's: the package Cargo.toml text verbatim (workspace-inherited
 * fields included), no [lints] (no lint flags), facade `k`.
 */
export function lessonManifest(name: LessonName, tourMinimal: LessonManifest): LessonManifest {
  if (name === "tour-minimal") return tourMinimal;
  const files: Record<Exclude<LessonName, "tour-minimal">, { toml: string; namespace: string }> = {
    // rust-expansion has no [package.metadata.krs]; its cases stop before collection.
    "bl006-rust-expansion": { toml: "bl006/rust-expansion.Cargo.toml", namespace: "BL006-RUST-EXPANSION" },
    "bl006-wrong-result": { toml: "bl006/wrong-result.Cargo.toml", namespace: "BL006-WRONG-RESULT" },
    "bl006-overlap": { toml: "bl006/overlap.Cargo.toml", namespace: "BL006-OVERLAP" },
  };
  const { toml, namespace } = files[name];
  const cargoToml = fixtureText(toml);
  const cargo = Bun.TOML.parse(cargoToml) as { package: { name: string; metadata?: { krs?: { "k-namespace"?: string } } } };
  const cargoName = cargo.package.name;
  if (cargo.package.metadata?.krs?.["k-namespace"] && cargo.package.metadata.krs["k-namespace"] !== namespace) throw new Error(`${name} namespace`);
  return {
    ...tourMinimal,
    lesson: name,
    package: {
      cargo_name: cargoName,
      // BL-006 workspace.package: version 0.0.0, edition 2024.
      cargo_version: "0.0.0",
      crate_name: cargoName.replaceAll("-", "_"),
      manifest_dir: `/workspace/${name}`,
      edition: "2024",
      k_namespace: namespace,
      cargo_source: "workspace",
      cargo_toml: cargoToml,
    },
    rustc_lint_flags: [],
  };
}

if (import.meta.main && Bun.argv[2] === "write-lessons") {
  const tour = JSON.parse(readFileSync(join(Bun.argv[3]!, "lessons/tour-minimal/lesson.json"), "utf8")) as LessonManifest;
  const out = Bun.argv[4]!;
  mkdirSync(out, { recursive: true });
  for (const name of ["tour-minimal", "bl006-rust-expansion", "bl006-wrong-result", "bl006-overlap"] as LessonName[]) {
    writeFileSync(join(out, `${name}.json`), `${JSON.stringify(lessonManifest(name, tour), null, 1)}\n`);
  }
}
