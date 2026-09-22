// Scenarios shared by the Node/Bun runner and the browser page.
// Sources are fixture file names under test/fixtures/ (served next to the page).

import type { FailureCode, Stage } from "../src/protocol.ts";

export const ORACLE_SHA256 = "8460248238982e624d9d75e541e036d88f2508e4aa27ed5498f19ea0112eca47";
export const ORACLE_BYTES = 183292;

export interface Expectation {
  outcome: "success" | "failure";
  bundleSha256?: string;
  stage?: Stage;
  code?: FailureCode;
  /** Expected diagnostics (subset match on the listed fields). */
  diagnostics?: Array<{ origin: string; code: string | null; class: string; authored: [number, number] | null }>;
  /** Exact number of diagnostics on the terminal event, when set. */
  diagnosticCount?: number;
}

export interface Scenario {
  name: string;
  fixture: string;
  expect: Expectation;
  /** Expectations that differ by the pack's fork_revision (compiler behaviour changes). */
  expectByFork?: Record<string, Expectation>;
}

/** Fork 195111dff (IR-04): rustc.wasm traps after errors and loses the stashed type-path E0433. */
export const FORK_IR04 = "195111dff60e2ce0c6d71f7302401cc4c07b0365";
/** Fork 0ce51e933 (IR-26): errors finish as natively (summary lines, exit 1, no trap). */
export const FORK_IR26 = "0ce51e9339ee538c16580fea01ca98dd89f6d7a0";

/** The expectation for a scenario under the pack's fork revision. */
export function expectationFor(scenario: Scenario, forkRevision: string): Expectation {
  return scenario.expectByFork?.[forkRevision] ?? scenario.expect;
}

export const SCENARIOS: Scenario[] = [
  {
    name: "tour-minimal",
    fixture: "tour-minimal.rs",
    expect: { outcome: "success", bundleSha256: ORACLE_SHA256 },
  },
  {
    name: "policy-d007",
    fixture: "policy-d007.rs",
    expect: {
      outcome: "failure",
      stage: "policy",
      code: "policy",
      diagnostics: [{ origin: "policy", code: "krs::policy::non-krs-proc-macro", class: "exact-authored", authored: [9, 25] }],
    },
  },
  {
    name: "expander-invalid-sorts",
    fixture: "expander-invalid-sorts.rs",
    expect: {
      outcome: "failure",
      stage: "expand",
      code: "expansion",
      diagnostics: [{ origin: "expander", code: null, class: "exact-authored", authored: [19, 20] }],
    },
  },
  {
    // tour-minimal with `k::k![Object::Missing()]`: E0599 on the authored
    // `Missing` (copied verbatim by k!), plus E0599 on the generated
    // `__krs_variant_type_id_Missing` check. That identifier is respanned at the
    // authored `Missing`; native rustc reports both there, and so does lookup
    // since IR-18 (IR-15 expected the #[k::init] call site 593..603).
    name: "rustc-unresolved-variant",
    fixture: "rustc-unresolved-variant.rs",
    expect: {
      outcome: "failure",
      stage: "rustc-lesson",
      code: "compile-error",
      diagnostics: [
        { origin: "rustc", code: "E0599", class: "exact-authored", authored: [676, 683] },
      ],
      diagnosticCount: 2,
    },
  },
  {
    // BL-006 D002 shape (`sort = missing::M2Obj`). rustc.wasm at 195111dff traps
    // with no output on E0433 in a type path (the twin reports E0433): compiler-trap.
    // The IR-26 fork (0ce51e933) reports the E0433 and exits 1, as the twin does.
    name: "rustc-e0433-type-path-trap",
    fixture: "rustc-e0433-type-path.rs",
    expect: { outcome: "failure", stage: "rustc-lesson", code: "compiler-trap" },
    expectByFork: {
      [FORK_IR26]: {
        outcome: "failure",
        stage: "rustc-lesson",
        code: "compile-error",
        diagnostics: [{ origin: "rustc", code: "E0433", class: "exact-authored", authored: [347, 354] }],
        diagnosticCount: 1,
      },
    },
  },
  {
    name: "tour-minimal-again",
    fixture: "tour-minimal.rs",
    expect: { outcome: "success", bundleSha256: ORACLE_SHA256 },
  },
];

export interface Check {
  ok: boolean;
  problems: string[];
}

interface TerminalEvent {
  type: string;
  stage?: string;
  code?: string;
  bundleSha256?: string;
  diagnostics?: Array<{ origin: string; code: string | null; class: string; authored: { start: number; end: number } | null }>;
}

/** Checks the terminal event and the progress ordering of one scenario's events. */
export function check(expect: Expectation, events: Array<{ type: string; stage?: string; state?: string }>): Check {
  const problems: string[] = [];
  const terminal = events.filter((e) => e.type === "success" || e.type === "failure" || e.type === "cancelled");
  if (terminal.length !== 1) problems.push(`expected one terminal event, got ${terminal.length}`);
  const last = terminal[0] as TerminalEvent | undefined;
  if (last && last !== events[events.length - 1]) problems.push("events after the terminal event");
  if (last?.type !== expect.outcome) problems.push(`outcome ${last?.type}, expected ${expect.outcome}`);
  if (expect.bundleSha256 && last?.bundleSha256 !== expect.bundleSha256) problems.push(`bundle ${last?.bundleSha256}`);
  if (expect.stage && last?.stage !== expect.stage) problems.push(`stage ${last?.stage}, expected ${expect.stage}`);
  if (expect.code && last?.code !== expect.code) problems.push(`code ${last?.code}, expected ${expect.code}`);
  if (expect.diagnosticCount !== undefined && (last?.diagnostics ?? []).length !== expect.diagnosticCount) {
    problems.push(`${(last?.diagnostics ?? []).length} diagnostics, expected ${expect.diagnosticCount}`);
  }
  for (const want of expect.diagnostics ?? []) {
    const found = (last?.diagnostics ?? []).some((d) =>
      d.origin === want.origin && d.code === want.code && d.class === want.class &&
      (want.authored === null ? d.authored === null : d.authored?.start === want.authored[0] && d.authored?.end === want.authored[1]));
    if (!found) problems.push(`missing diagnostic ${JSON.stringify(want)}`);
  }
  // Progress: start/end pairs in stage order, each end directly after its start.
  const progress = events.filter((e) => e.type === "progress");
  const order = ["assets", "policy", "expand", "rustc-lesson", "rustc-collector", "collect", "bundle"];
  let expected = 0;
  let open: string | null = null;
  for (const event of progress) {
    if (event.state === "start") {
      if (open !== null) problems.push(`stage ${event.stage} started while ${open} open`);
      if (event.stage !== order[expected]) problems.push(`stage ${event.stage} out of order`);
      open = event.stage ?? null;
    } else {
      if (event.stage !== open) problems.push(`stage ${event.stage} ended while ${open} open`);
      open = null;
      expected += 1;
    }
  }
  if (expect.outcome === "success" && expected !== order.length) problems.push(`only ${expected} stages completed`);
  return { ok: problems.length === 0, problems };
}
