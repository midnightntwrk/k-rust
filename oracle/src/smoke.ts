import { mkdir } from "node:fs/promises";
import { resolve } from "node:path";
import { captureManifest } from "./capture.js";
import { assertComparisonExpectations, compareBundles } from "./compare.js";
import { pathExists, writeJson } from "./io.js";
import { loadSmokeSuite } from "./manifest.js";

export async function runSmokeSuite(suiteFile: string, outputDirectory: string): Promise<string> {
  const loaded = await loadSmokeSuite(suiteFile);
  const output = resolve(outputDirectory);
  if (await pathExists(output)) throw new Error(`Refusing to overwrite existing smoke directory: ${output}`);
  await mkdir(output, { recursive: true });

  const baselineA = await captureManifest(loaded.baselineManifest, `${output}/baseline-a`);
  const baselineB = await captureManifest(loaded.baselineManifest, `${output}/baseline-b`);
  const mutation = await captureManifest(loaded.mutationManifest, `${output}/mutation`);

  const repeatComparison = await compareBundles(baselineA, baselineB);
  if (!repeatComparison.equal) {
    throw new Error(`Repeated baseline capture was not deterministic; see ${output}/smoke-report.json`);
  }
  const mutationComparison = await compareBundles(baselineA, mutation);
  assertComparisonExpectations(mutationComparison, loaded.suite.expectedDifferent, loaded.suite.expectedEqual);

  const reportPath = `${output}/smoke-report.json`;
  await writeJson(reportPath, {
    schemaVersion: 1,
    suiteId: loaded.suite.id,
    suitePath: loaded.suitePath,
    captures: { baselineA, baselineB, mutation },
    repeatComparison,
    mutationComparison,
    verdict: "pass",
  });
  return reportPath;
}
