// Unit tests over recorded fixtures (bun test). Tests that need the staged
// Wasm modules read them from KRS_BROWSER_ASSETS (default krs-browser-assets
// under the scratch root) and skip when that directory holds no pack.json.

import { describe, expect, test } from "bun:test";
import { existsSync, readFileSync } from "node:fs";
import { join } from "node:path";
import { renderCollectorMain } from "../../src/collector-template.ts";
import { fromExpander, fromPolicy, fromRustc, lookupRanges } from "../../src/diagnostics.ts";
import type { ExpandResponse, LookupResponse, PolicyResponse } from "../../src/modules.ts";
import { runExpander, runLookup, runPolicy } from "../../src/modules.ts";
import { packFromManifest, type SourcePackManifest } from "../../src/pack-manifest.ts";
import { checkActivation, recomputePackId, sha256Hex } from "../../src/pack.ts";
import { createBuild, injectMissingFactory, runBuild, stageAssets, stageBundle, stagePolicy, StageFailure } from "../../src/pipeline.ts";
import type { CompileEvent, LessonManifest, PackManifest, VerifiedAssets } from "../../src/protocol.ts";
import { classifyRustc, collectorInvocation, lessonInvocation, parseStderr, reportable } from "../../src/rustc.ts";
import { parseSysrootBundle, readOnlyTree } from "../../src/vfs.ts";
import { scratchPath } from "../harness/environment.ts";

const FIXTURES = join(import.meta.dir, "../fixtures");
const fixture = (name: string) => readFileSync(join(FIXTURES, name), "utf8");
const ASSETS = process.env.KRS_BROWSER_ASSETS || scratchPath("krs-browser-assets");
const haveAssets = existsSync(join(ASSETS, "pack.json"));

const lesson: LessonManifest = {
  schema: 1,
  lesson: "tour-minimal",
  pack_id: "krs-pack-test",
  expansion: "krs-expander",
  package: {
    cargo_name: "krs-tour-minimal",
    cargo_version: "0.0.0",
    crate_name: "krs_tour_minimal",
    manifest_dir: "/workspace/tour-minimal",
    edition: "2024",
    k_namespace: "KRS-TOUR-MINIMAL",
    cargo_source: "workspace",
    cargo_toml: "[package]\nname = \"krs-tour-minimal\"\n",
  },
  facade: { alias: "k", path: "::k" },
  display_file: "src/lib.rs",
  policy: { editable_files: ["src/lib.rs"], facade_alias: "k" },
  rustc_lint_flags: ["-D", "warnings"],
};

const CRATES_TREE = "199c07cfc38861110966d0ce99805035602b0a91";
const manifestSource = () => Bun.TOML.parse(fixture("pack-manifest.toml")) as unknown as SourcePackManifest;
const moduleAsset = (path: string) => ({ path, sha256: "1".repeat(64), bytes: 1 });

async function adaptedPack(source = manifestSource(), cratesTree = CRATES_TREE): Promise<PackManifest> {
  return packFromManifest(source, {
    packDir: "pack",
    sourcePath: "pack-manifest.toml",
    sourceSha256: "0".repeat(64),
    policy: moduleAsset("modules/p.wasm"),
    expander: moduleAsset("modules/e.wasm"),
    modulesKrsRevision: "3501f86cf5c219c300107302ab76c1b2854464c4",
    modulesCratesTree: cratesTree,
    protocolVersion: 35,
  });
}

describe("collector template", () => {
  test("equals krs-cli render_production_main (explicit) for the lesson package", () => {
    expect(renderCollectorMain(lesson)).toBe(fixture("collector-main.expected.rs"));
  });
});

test("bundle stage hashes the compact collector payload and requires its newline", async () => {
  const pack = await adaptedPack();
  const ctx = { pack, modules: {} as VerifiedAssets["modules"], layers: { sysroot: new Map(), pack: new Map(), krs: new Map() }, activationProblems: [] };
  const build = createBuild(ctx, { generation: 1, lesson, files: {} }, { emit: () => {} });
  const bytes = new TextEncoder().encode(`{"protocol_version":${pack.protocol_version},"descriptors":[],"declarations":[]}\n`);
  build.stdout = bytes;
  expect(await stageBundle(build)).toEqual({ bundle: bytes, sha256: await sha256Hex(bytes) });
  build.stdout = bytes.slice(0, -1);
  await expect(stageBundle(build)).rejects.toMatchObject({ stage: "bundle", code: "collector-error" });
});

test("worker rejects an unresolved lesson dependency as a protocol error", async () => {
  const pack = await adaptedPack();
  const ctx = { pack, modules: {} as VerifiedAssets["modules"], layers: { sysroot: new Map(), pack: new Map(), krs: new Map() }, activationProblems: [] };
  const inherited = { ...lesson, package: { ...lesson.package, cargo_toml: '[package]\nname = "example"\n[dependencies]\nk.workspace = true\n' } };
  const build = createBuild(ctx, { generation: 1, lesson: inherited, files: {} }, { emit: () => {} });
  try {
    stageAssets(build);
    throw new Error("expected protocol failure");
  } catch (error) {
    expect(error).toBeInstanceOf(StageFailure);
    expect(error).toMatchObject({ code: "protocol-mismatch", stage: "assets" });
    expect(String(error)).toContain("dependencies.k.workspace");
  }
});

describe("pack adapter (pack manifest, schema_version 2)", () => {
  test("maps roles to mounts, externs, and [direct_rustc]", async () => {
    const pack = await adaptedPack();
    expect(pack.pack_id).toBe("sha256:6c4a48d666c88d7422979908a28f2633fdae7f486407c0f4e235c515f8004117");
    expect(pack.artifacts.length).toBe(28);
    expect(pack.externs.facade).toBe("/pack/deps/libkrs-add96ba03f57c1b6.rlib");
    expect(pack.externs.compiler_runtime).toBe("/pack/deps/libkrs_compiler-cb1260d0465cc762.rlib");
    expect(pack.artifacts.filter((a) => a.role === "proc-macro-metadata").map((a) => a.mount)).toEqual([
      "/pack/proc-macro-meta/libkrs_macros-e5fa7b53b7bfa6e3.rmeta",
      "/pack/proc-macro-meta/libserde_derive-34455017fa8b0d0c.rmeta",
    ]);
    expect(pack.framework_sources.map((s) => [s.path, s.mount])).toEqual([
      ["pack/krs/crates/krs/Cargo.toml", "/krs/crates/krs/Cargo.toml"],
      ["pack/krs/crates/krs/src/lib.rs", "/krs/crates/krs/src/lib.rs"],
    ]);
    expect(pack.compiler.rustc.path).toBe("pack/compiler/rustc.wasm");
    expect(pack.direct_rustc.common_flags).toEqual(["-C", "panic=abort", "-Zproc-macro-metadata-only"]);
    expect(pack.direct_rustc.library_dirs).toEqual(["/pack/deps", "/pack/proc-macro-meta"]);
    expect(pack.crates_tree).toBe(CRATES_TREE);
  });

  test("rejects a tampered artifact hash (pack_id no longer matches)", async () => {
    const source = manifestSource();
    source.artifact[3]!.sha256 = "f".repeat(64);
    await expect(adaptedPack(source)).rejects.toThrow(/pack_id/);
  });

  test("rejects modules built from another crates/ tree", async () => {
    await expect(adaptedPack(manifestSource(), "0".repeat(40))).rejects.toThrow(/crates\/ tree/);
  });

  test("activation fails for unverified assets", async () => {
    const pack = await adaptedPack();
    const problems = checkActivation(pack, {
      packId: pack.pack_id,
      modules: {} as VerifiedAssets["modules"],
      sysrootBundle: new Uint8Array(0),
      files: {},
      verified: {},
    });
    expect(problems.length).toBeGreaterThan(pack.artifacts.length);
  });

  test("the loader recomputes pack_id over the pack's own assets", async () => {
    const pack = await adaptedPack();
    expect(await recomputePackId(pack)).toBe(pack.pack_id);
    const tampered = { ...pack, artifacts: pack.artifacts.map((a, i) => (i === 0 ? { ...a, sha256: "e".repeat(64) } : a)) };
    expect(await recomputePackId(tampered)).not.toBe(pack.pack_id);
  });
});

describe("rustc invocations", () => {
  test("lesson and collector arguments follow the pack manifest's [consumer] contract", async () => {
    const pack = await adaptedPack();
    const l = lessonInvocation(pack, lesson);
    expect(l.args).toContain("-Zproc-macro-metadata-only");
    expect(l.args.slice(-6)).toEqual(["-A", "non_camel_case_types", "-A", "non_snake_case", "-o", "/work/out/libkrs_tour_minimal.rlib"]);
    expect(l.env).toContain("CARGO_MANIFEST_DIR=/workspace/tour-minimal");
    const c = collectorInvocation(pack, lesson);
    expect(c.args).toContain("krs_tour_minimal=/work/out/libkrs_tour_minimal.rlib");
    expect(c.args).toContain("opt-level=2");
    expect(c.env.some((e) => e.startsWith("CARGO_"))).toBe(false);
  });
});

describe("rustc output", () => {
  const parsed = parseStderr(fixture("rustc-e0599.stderr"));

  test("parses the recorded E0599 compile (diagnostics then trap)", () => {
    const shown = reportable(parsed.diagnostics);
    expect(shown.map((d) => [d.level, d.code?.code])).toEqual([
      ["error", "E0599"],
      ["error", "E0599"],
    ]);
    expect(parsed.residue).toEqual([]);
  });

  test("a trap after emitted errors is a compile error, not a crash", () => {
    const run = { exitCode: null, trap: "RuntimeError: unreachable", trapName: "RuntimeError" };
    expect(classifyRustc("rustc-lesson", run, parsed, false).code).toBe("compile-error");
    const silent = parseStderr("");
    expect(classifyRustc("rustc-lesson", run, silent, false).code).toBe("compiler-trap");
    expect(classifyRustc("rustc-lesson", { ...run, trapName: "RangeError", trap: "RangeError: Out of memory" }, silent, false).code).toBe(
      "out-of-memory",
    );
    expect(classifyRustc("rustc-lesson", { exitCode: 0, trap: null, trapName: null }, silent, true).ok).toBe(true);
  });

  test("reads the riwl timing line", () => {
    const riwl = parseStderr(fixture("rustc-collector-ok.stderr")).riwl;
    expect(riwl?.total_ms).toBeGreaterThan(0);
    expect(Object.keys(riwl ?? {})).toEqual(["total_ms", "load_ms", "resolve_ms", "layout_ms", "apply_ms", "emit_ms"]);
  });
});

describe("diagnostics", () => {
  test("policy diagnostic (D007) keeps the authored range 9..25", () => {
    const response = JSON.parse(fixture("policy-d007.response.json")) as PolicyResponse;
    expect(response.diagnostics.map(fromPolicy)).toEqual([
      {
        origin: "policy",
        code: "krs::policy::non-krs-proc-macro",
        severity: "error",
        message: response.diagnostics[0]!.message,
        class: "exact-authored",
        authored: { file: "src/lib.rs", start: 9, end: 25 },
        generated: null,
      },
    ]);
  });

  test("expander diagnostic (invalid sorts! probe) keeps 24..25 and code null", () => {
    const response = JSON.parse(fixture("expander-invalid.response.json")) as ExpandResponse;
    const [d] = response.diagnostics.map(fromExpander);
    expect(d).toMatchObject({ origin: "expander", code: null, class: "exact-authored", authored: { file: "src/lib.rs", start: 24, end: 25 } });
  });

  test("rustc diagnostics map through the recorded krs_expand_lookup responses; generated-only gets no authored range", () => {
    const generated = "/work/expanded/tour-minimal/src/lib.rs";
    const span = (start: number, end: number, file = generated) => ({
      file_name: file, byte_start: start, byte_end: end, line_start: 1, line_end: 1, column_start: 1, column_end: 1, is_primary: true, label: null,
    });
    const diag = (message: string, spans: ReturnType<typeof span>[]) => ({
      $message_type: "diagnostic" as const, message, code: { code: "E0000", explanation: null }, level: "error", spans, children: [], rendered: null,
    });
    const diagnostics = [
      diag("a", [span(554, 559)]),
      diag("elsewhere", [span(1, 2, "/krs/crates/krs/src/lib.rs")]),
      diag("b", [span(287, 290)]),
      diag("no span", []),
      diag("c", [span(55833, 56780)]),
    ];
    expect(lookupRanges(diagnostics, generated)).toEqual([[554, 559], null, [287, 290], null, [55833, 56780]]);
    const lookup = JSON.parse(fixture("lookup.response.json")) as LookupResponse;
    const mapped = fromRustc(diagnostics, generated, "src/lib.rs", lookup.mappings);
    expect(mapped.map((d) => [d.class, d.authored?.start ?? null, d.generated?.start ?? null])).toEqual([
      ["exact-authored", 303, 554],
      ["unmappable", null, 1],
      ["invocation-level", 287, 287],
      ["unmappable", null, null],
      ["generated-only", null, 55833],
    ]);
  });
});

describe("vfs", () => {
  test("parses an RIWB1 bundle and skips manifest.json", () => {
    const data = new TextEncoder().encode("abcdef");
    const index = new TextEncoder().encode(JSON.stringify({ files: [{ p: "manifest.json", o: 0, l: 2 }, { p: "lib/x.rlib", o: 2, l: 4 }], total: 6 }));
    const bytes = new Uint8Array(10 + index.byteLength + data.byteLength);
    bytes.set(new TextEncoder().encode("RIWB1\n"));
    new DataView(bytes.buffer).setUint32(6, index.byteLength, true);
    bytes.set(index, 10);
    bytes.set(data, 10 + index.byteLength);
    const files = parseSysrootBundle(bytes);
    expect([...files.keys()]).toEqual(["lib/x.rlib"]);
    expect(new TextDecoder().decode(files.get("lib/x.rlib"))).toBe("cdef");
  });

  test("consecutive builds share immutable files but no per-build directory object", async () => {
    const pack = await adaptedPack();
    const ctx = {
      pack,
      modules: {} as VerifiedAssets["modules"],
      layers: { sysroot: readOnlyTree([["lib/a", new Uint8Array(1)]]), pack: readOnlyTree([]), krs: readOnlyTree([]) },
      activationProblems: [],
    };
    const request = { generation: 1, lesson, files: { "src/lib.rs": "fn f() {}" } };
    const a = createBuild(ctx, request, { emit: () => {} });
    const b = createBuild(ctx, { ...request, generation: 2 }, { emit: () => {} });
    expect(a.work).not.toBe(b.work);
    expect(a.workspace).not.toBe(b.workspace);
    expect(a.work.contents.get("out")).not.toBe(b.work.contents.get("out"));
  });
});

describe.skipIf(!haveAssets)("modules (staged assets)", () => {
  const pack = haveAssets ? (JSON.parse(readFileSync(join(ASSETS, "pack.json"), "utf8")) as PackManifest) : null;
  const load = async (path: string) => WebAssembly.compile(readFileSync(join(ASSETS, path)));

  test("policy module rejects D007 at 9..25 and passes tour-minimal", async () => {
    const policy = await load(pack!.modules.policy.path);
    const request = (source: string) => ({ schema: 1 as const, policy: lesson.policy, files: { "src/lib.rs": source } });
    expect((await runPolicy(policy, request(fixture("tour-minimal.rs")))).ok).toBe(true);
    const rejected = await runPolicy(policy, request(fixture("policy-d007.rs")));
    expect(rejected.diagnostics.map((d) => d.authored)).toEqual([[9, 25]]);
  });

  test("the policy stage rejects a file outside editable_files before calling the module", async () => {
    const events: CompileEvent[] = [];
    const ctx = {
      pack: pack!,
      modules: { policy: await load(pack!.modules.policy.path) } as VerifiedAssets["modules"],
      layers: { sysroot: new Map(), pack: new Map(), krs: new Map() },
      activationProblems: [],
    };
    const build = createBuild(ctx, { generation: 7, lesson, files: { "src/lib.rs": "", "src/extra.rs": "" } }, { emit: (e) => events.push(e) });
    const failure = await stagePolicy(build).catch((error: unknown) => error);
    expect(failure).toBeInstanceOf(StageFailure);
    expect((failure as StageFailure).diagnostics[0]).toMatchObject({ code: "krs::policy::editable-file", class: "unmappable", authored: null });
    expect(events.map((e) => e.type)).toEqual(["diagnostics"]);
  });

  test("expander output for tour-minimal equals the recorded text and lookup answers", async () => {
    const expander = await load(pack!.modules.expander.path);
    const request = JSON.parse(fixture("expander-tour-minimal.request.json"));
    const response = await runExpander(expander, request);
    expect(await sha256Hex(new TextEncoder().encode(response.expanded!.text))).toBe(
      "4c445a68a10a09d6ca3551e14acd4a0b1818032240ca6573cf04ef44da21533d",
    );
    const segments = (response.source_map as { segments: Array<{ class: string; generated: [number, number] }> }).segments;
    const generated = segments.find((segment) => segment.class === "generated-only")!;
    const lookup = await runLookup(expander, {
      schema: 1,
      authored_source: request.file.source,
      text: response.expanded!.text,
      source_map: response.source_map,
      ranges: [generated.generated],
    });
    expect(lookup.mappings[0]!.class).toBe("generated-only");
  });

  test("a lesson for another pack fails in the assets stage", async () => {
    const ctx = { pack: pack!, modules: {} as VerifiedAssets["modules"], layers: { sysroot: new Map(), pack: new Map(), krs: new Map() }, activationProblems: [] };
    const events: CompileEvent[] = [];
    await runBuild(ctx, { generation: 1, lesson: { ...lesson, pack_id: "other" }, files: {} }, { emit: (e) => events.push(e) });
    expect(events.at(-1)).toMatchObject({ type: "failure", stage: "assets", code: "pack-integrity" });
  });
});

describe("test-only fault injection", () => {
  const table = [
    "fn a() {}\n",
    "fn __krs_register_descriptors(r: &mut R) {\n    r.factory(crate::__krs_sort_descriptor_14a572b2d7631807);\n}\n",
  ];
  const text = table.join("");
  const response = {
    source_map: { segments: [{ generated: [0, table[0]!.length], class: "exact-authored" }, { generated: [table[0]!.length, text.length], class: "generated-only" }] },
    registrations: [{ factory: "__krs_sort_descriptor_14a572b2d7631807" }],
  } as unknown as ExpandResponse;

  test("registration-table-missing-factory renames one table reference and keeps every offset", () => {
    const { text: faulted, detail } = injectMissingFactory(text, response);
    expect(faulted.length).toBe(text.length);
    expect(faulted).toContain("crate::__krs_sort_descriptor_14a572b2d763180X)");
    expect(faulted.slice(0, table[0]!.length)).toBe(table[0]!);
    expect(detail).toContain("-> __krs_sort_descriptor_14a572b2d763180X");
  });

  test("registration-table-missing-factory refuses text without the table reference", () => {
    expect(() => injectMissingFactory("fn a() {}\n", response)).toThrow(StageFailure);
  });
});
