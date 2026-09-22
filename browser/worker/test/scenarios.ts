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
}

export interface Scenario {
  name: string;
  fixture: string;
  expect: Expectation;
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
    // `__krs_variant_type_id_Missing` check, which maps to the #[k::init] call site.
    name: "rustc-unresolved-variant",
    fixture: "rustc-unresolved-variant.rs",
    expect: {
      outcome: "failure",
      stage: "rustc-lesson",
      code: "compile-error",
      diagnostics: [
        { origin: "rustc", code: "E0599", class: "exact-authored", authored: [676, 683] },
        { origin: "rustc", code: "E0599", class: "invocation-level", authored: [593, 603] },
      ],
    },
  },
  {
    // BL-006 D002 shape (`sort = missing::M2Obj`). rustc.wasm at 195111dff traps
    // with no output on E0433 in a type path (the twin reports E0433), so the
    // worker must classify it as compiler-trap. Pinned until the fork is fixed.
    name: "rustc-e0433-type-path-trap",
    fixture: "rustc-e0433-type-path.rs",
    expect: { outcome: "failure", stage: "rustc-lesson", code: "compiler-trap" },
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
