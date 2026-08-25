import { readFile, stat } from "node:fs/promises";
import { dirname, resolve } from "node:path";
import { readJson, requireObject } from "./io.js";
import type { BundleComparison, CapturedArtifact, ComparedArtifact, OracleBundle } from "./types.js";

async function bundleFile(path: string): Promise<string> {
  const absolute = resolve(path);
  return (await stat(absolute)).isDirectory() ? `${absolute}/bundle.json` : absolute;
}

async function loadBundle(path: string): Promise<{ readonly path: string; readonly root: string; readonly bundle: OracleBundle }> {
  const resolved = await bundleFile(path);
  const value = await readJson(resolved);
  const object = requireObject(value, resolved);
  if (object["schemaVersion"] !== 1 || !Array.isArray(object["runs"])) throw new Error(`${resolved} is not an oracle bundle`);
  return { path: resolved, root: dirname(resolved), bundle: value as OracleBundle };
}

function artifacts(bundle: OracleBundle): Map<string, CapturedArtifact> {
  const result = new Map<string, CapturedArtifact>();
  for (const run of bundle.runs) {
    for (const artifact of run.artifacts) {
      const boundary = `${run.id}:${artifact.id}`;
      if (result.has(boundary)) throw new Error(`Duplicate artifact boundary in bundle: ${boundary}`);
      result.set(boundary, artifact);
    }
  }
  return result;
}

function excerpt(value: string, offset: number): string {
  const start = Math.max(0, offset - 40);
  const end = Math.min(value.length, offset + 80);
  return value.slice(start, end).replaceAll("\n", "\\n");
}

function firstDifference(left: string, right: string): NonNullable<ComparedArtifact["firstDifference"]> {
  const limit = Math.min(left.length, right.length);
  let offset = 0;
  while (offset < limit && left.charCodeAt(offset) === right.charCodeAt(offset)) offset++;
  const prefix = left.slice(0, offset);
  const lines = prefix.split("\n");
  return {
    offset,
    line: lines.length,
    column: (lines.at(-1)?.length ?? 0) + 1,
    leftExcerpt: excerpt(left, offset),
    rightExcerpt: excerpt(right, offset),
  };
}

export async function compareBundles(
  leftPath: string,
  rightPath: string,
  selectedBoundaries?: ReadonlySet<string>,
): Promise<BundleComparison> {
  const [left, right] = await Promise.all([loadBundle(leftPath), loadBundle(rightPath)]);
  const leftArtifacts = artifacts(left.bundle);
  const rightArtifacts = artifacts(right.bundle);
  const boundaries = [...new Set([...leftArtifacts.keys(), ...rightArtifacts.keys()])]
    .filter((boundary) => selectedBoundaries === undefined || selectedBoundaries.has(boundary))
    .sort();
  if (selectedBoundaries !== undefined) {
    for (const expected of selectedBoundaries) {
      if (!boundaries.includes(expected)) throw new Error(`Selected boundary does not exist in either bundle: ${expected}`);
    }
  }

  const compared: ComparedArtifact[] = [];
  for (const boundary of boundaries) {
    const leftArtifact = leftArtifacts.get(boundary);
    const rightArtifact = rightArtifacts.get(boundary);
    if (leftArtifact === undefined) {
      compared.push({
        boundary,
        status: "missing-left",
        ...(rightArtifact === undefined ? {} : { rightSha256: rightArtifact.normalizedSha256 }),
      });
      continue;
    }
    if (rightArtifact === undefined) {
      compared.push({ boundary, status: "missing-right", leftSha256: leftArtifact.normalizedSha256 });
      continue;
    }
    if (leftArtifact.normalizedSha256 === rightArtifact.normalizedSha256) {
      compared.push({
        boundary,
        status: "equal",
        leftSha256: leftArtifact.normalizedSha256,
        rightSha256: rightArtifact.normalizedSha256,
      });
      continue;
    }
    const [leftText, rightText] = await Promise.all([
      readFile(resolve(left.root, leftArtifact.normalizedPath), "utf8"),
      readFile(resolve(right.root, rightArtifact.normalizedPath), "utf8"),
    ]);
    compared.push({
      boundary,
      status: "different",
      leftSha256: leftArtifact.normalizedSha256,
      rightSha256: rightArtifact.normalizedSha256,
      firstDifference: firstDifference(leftText, rightText),
    });
  }
  return {
    leftBundle: left.path,
    rightBundle: right.path,
    equal: compared.every((item) => item.status === "equal"),
    artifacts: compared,
  };
}

export function assertComparisonExpectations(
  comparison: BundleComparison,
  expectedDifferent: readonly string[],
  expectedEqual: readonly string[],
): void {
  const expectations = new Map<string, "different" | "equal">([
    ...expectedDifferent.map((boundary) => [boundary, "different"] as const),
    ...expectedEqual.map((boundary) => [boundary, "equal"] as const),
  ]);
  const actual = new Map(comparison.artifacts.map((item) => [item.boundary, item.status]));
  for (const boundary of actual.keys()) {
    if (!expectations.has(boundary)) throw new Error(`No smoke expectation declared for boundary ${boundary}`);
  }
  for (const [boundary, expected] of expectations) {
    const status = actual.get(boundary);
    if (status === undefined) throw new Error(`Expected smoke boundary was not captured: ${boundary}`);
    if (status !== expected) throw new Error(`Boundary ${boundary}: expected ${expected}, got ${status}`);
  }
}
