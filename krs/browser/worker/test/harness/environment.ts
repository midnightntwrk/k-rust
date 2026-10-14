// Host environment shared by every browser test runner: the scratch root that
// all default output locations derive from, the checkout root, the Firefox
// binary, and the load-average wait that precedes each heavy step. Runs under
// Bun and Node (test/run-pipeline.ts and the backend suite's Node host).

import { createHash } from "node:crypto";
import { mkdirSync, readFileSync, realpathSync } from "node:fs";
import { basename, join } from "node:path";

/** The disk-backed scratch root: `KRS_GATE_SCRATCH`, as for the other gates, else /var/tmp. */
export function scratchRoot(): string {
  return process.env.KRS_GATE_SCRATCH || "/var/tmp";
}

/** A default output location: `name` under the scratch root. */
export function scratchPath(name: string): string {
  return join(scratchRoot(), name);
}

/** The KRS checkout that contains this module. */
export const REPO = join(import.meta.dirname, "../../../..");

/** The persistent scratch directory keyed by this resolved KRS checkout. */
export function checkoutScratch(): string {
  const key = createHash("sha256").update(realpathSync(REPO, { encoding: "buffer" })).digest("hex").slice(0, 12);
  const directory = join(scratchRoot(), `krs-${basename(REPO)}-${key}`);
  mkdirSync(directory, { recursive: true });
  return directory;
}

/** The Firefox binary the drivers start: `KRS_FIREFOX`, else the system Firefox. */
export function firefoxBinary(): string {
  return process.env.KRS_FIREFOX || "/usr/lib/firefox/firefox";
}

/** Waits while the 1-minute load average exceeds `maximum`; returns the load it started at. */
export async function waitForLoad(maximum: number, intervalMs = 60_000): Promise<number> {
  for (;;) {
    const load = Number(readFileSync("/proc/loadavg", "utf8").split(" ")[0]);
    if (load <= maximum) return load;
    process.stderr.write(`load ${load} > ${maximum}, waiting ${intervalMs / 1000} s\n`);
    await new Promise((resolve) => setTimeout(resolve, intervalMs));
  }
}
