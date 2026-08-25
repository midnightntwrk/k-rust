import { mkdir, readFile, writeFile } from "node:fs/promises";
import { resolve } from "node:path";
import {
  decodeP3Result,
  normalizeProjection,
  projectCompiled,
  projectExecution,
  renderKast,
  selectedKoreAxioms,
} from "./projection.js";

const root = resolve(import.meta.dir, "../..");
const build = resolve(root, "p3/build");
const fixture = resolve(root, "p3/fixtures/coupled.k");
const officialDefinition = resolve(build, "coupled-kompiled");
const modelDefinition = resolve(build, "p3-kompiled");

interface CommandEvidence {
  readonly argv: readonly string[];
  readonly exitCode: number;
  readonly durationMs: number;
  readonly stderr: string;
}

async function run(
  argv: readonly string[], expectedExitCodes: readonly number[] = [0], expectedStderr?: string,
): Promise<{ readonly stdout: string; readonly evidence: CommandEvidence }> {
  const started = performance.now();
  const child = Bun.spawn([...argv], { cwd: root, stdout: "pipe", stderr: "pipe" });
  const [stdout, stderr, exitCode] = await Promise.all([
    new Response(child.stdout).text(), new Response(child.stderr).text(), child.exited,
  ]);
  const evidence = { argv, exitCode, durationMs: Math.round(performance.now() - started), stderr: stderr.trim() };
  if (!expectedExitCodes.includes(exitCode) || (expectedStderr !== undefined && !stderr.includes(expectedStderr))) {
    throw new Error(`${argv.join(" ")} failed its exit contract (${exitCode})\n${stderr}`);
  }
  return { stdout, evidence };
}

async function main(): Promise<void> {
  await mkdir(build, { recursive: true });
  const commands: CommandEvidence[] = [];
  commands.push((await run([
    "kompile", fixture, "--backend", "haskell", "--emit-json",
    "--main-module", "P3-COUPLED", "--syntax-module", "P3-COUPLED-SYNTAX",
    "--output-definition", officialDefinition,
  ])).evidence);
  const contextSteps = [
    "resolveComm", "resolveIO", "resolveFun", "resolveFunctionWithConfig", "resolveStrict", "resolveAnonVars", "resolveContexts",
  ];
  const cellSteps = [
    ...contextSteps, "numberSentences1", "resolveHeatCoolAttribute", "resolveSemanticCasts", "subsortKItem1",
    "constantFolding", "propagateMacroToRules", "guardOrs", "resolveFreshConfigConstants", "generateSortPredicateSyntax1",
    "generateSortProjections1", "expandMacros", "addImplicitComputationCell", "resolveFreshConstants",
    "generateSortPredicateSyntax2", "generateSortProjections2", "checkSimplificationRules", "subsortKItem2", "concretizeCells",
  ];
  commands.push((await run([
    "kompile", fixture, "--backend", "haskell", "--emit-json",
    "--main-module", "P3-COUPLED", "--syntax-module", "P3-COUPLED-SYNTAX",
    "--output-definition", resolve(build, "contexts-prefix"), "--kore-backend-steps", contextSteps.join(","),
  ], [1], "GeneratedTopCell")).evidence);
  commands.push((await run([
    "kompile", fixture, "--backend", "haskell", "--emit-json",
    "--main-module", "P3-COUPLED", "--syntax-module", "P3-COUPLED-SYNTAX",
    "--output-definition", resolve(build, "cells-prefix"), "--kore-backend-steps", cellSteps.join(","),
  ], [1], "None.get")).evidence);
  commands.push((await run([
    "kompile", resolve(root, "p3/src/p3.k"), "--backend", "haskell", "--emit-json",
    "--main-module", "P3-PROBE", "--syntax-module", "P3-PROBE-SYNTAX",
    "--output-definition", modelDefinition,
  ])).evidence);

  const modelRun = await run([
    "krun", resolve(root, "p3/fixtures/coupled.p3"), "--definition", modelDefinition, "--output", "json",
  ]);
  commands.push(modelRun.evidence);
  const modelDocument = JSON.parse(modelRun.stdout);
  const model = decodeP3Result(modelDocument);
  await writeFile(resolve(build, "p3-output.json"), modelRun.stdout);

  const contextsProjection = projectCompiled(
    JSON.parse(await readFile(resolve(build, "contexts-prefix/compiled.json"), "utf8")), fixture,
  );
  const cellsProjection = projectCompiled(
    JSON.parse(await readFile(resolve(build, "cells-prefix/compiled.json"), "utf8")), fixture,
  );
  const official = projectCompiled(
    JSON.parse(await readFile(resolve(officialDefinition, "compiled.json"), "utf8")), fixture,
  );
  const cellsProjectionEqual = JSON.stringify(model.projection) === JSON.stringify(cellsProjection);
  const fullProjectionEqual = JSON.stringify(model.projection) === JSON.stringify(official);
  const contextsGenerated = contextsProjection.facts.filter((fact) => fact.kind === "context").length === 6;
  const contextBump = contextsProjection.facts.find((fact) => fact.kind === "rule" && fact.label === "bump-state");
  const contextsPreconcretized = contextBump?.kind === "rule"
    && JSON.stringify(contextBump.cells) === JSON.stringify(["k", "state"]);

  const fixedInput = resolve(build, "fixed-point.p3");
  await writeFile(fixedInput, `${renderKast(model.term)}\n`);
  const fixedRun = await run(["krun", fixedInput, "--definition", modelDefinition, "--output", "json"]);
  commands.push(fixedRun.evidence);
  const fixed = decodeP3Result(JSON.parse(fixedRun.stdout));
  const fixedPointEqual = JSON.stringify(model.projection) === JSON.stringify(fixed.projection);

  const executionRun = await run([
    "krun", resolve(root, "p3/fixtures/program.exp"), "--definition", officialDefinition, "--output", "json",
  ]);
  commands.push(executionRun.evidence);
  const execution = projectExecution(JSON.parse(executionRun.stdout));
  const executionEqual = execution.k === "1" && execution.state === "2";

  const koreAxioms = selectedKoreAxioms(await readFile(resolve(officialDefinition, "definition.kore"), "utf8"));
  const expectedLabels = new Set(official.facts
    .filter((fact) => fact.kind !== "function-injection")
    .map((fact) => fact.label));
  const koreLabels = new Set(koreAxioms.map((axiom) => axiom.label));
  const finalKoreCoverage = expectedLabels.size === koreLabels.size && [...expectedLabels].every((label) => koreLabels.has(label));

  const result = {
    probe: "P3 configuration, contexts, and concretization",
    checks: {
      contextsPrefixGeneratedSixRules: contextsGenerated,
      contextsPrefixRemainsPreconcretized: contextsPreconcretized,
      cellsPrefixProjectionEqual: cellsProjectionEqual,
      fullCompiledProjectionEqual: fullProjectionEqual,
      fixedPointEqual,
      finalKoreContainsEverySelectedRule: finalKoreCoverage,
      representativeExecutionEqual: executionEqual,
    },
    coverage: [
      "nested non-preconcretized configuration", "seqstrict heating/cooling", "explicit context heating/cooling",
      "function context and configuration argument injection", "cell completion", "requires/ensures", "final Kore emission", "execution",
    ],
    counts: {
      cellEdges: model.projection.edges.length,
      generatedContextRules: model.projection.facts.filter((fact) => fact.kind === "context").length,
      concretizedSourceRules: model.projection.facts.filter((fact) => fact.kind === "rule").length,
      functionInjections: model.projection.facts.filter((fact) => fact.kind === "function-injection").length,
      selectedFinalKoreAxioms: koreAxioms.length,
    },
    execution,
    finalKoreAxioms: koreAxioms,
    projections: { model: normalizeProjection(model.projection), contextsPrefix: contextsProjection, cellsPrefix: cellsProjection, full: official },
    commands,
  };
  await writeFile(resolve(build, "probe-result.json"), `${JSON.stringify(result, null, 2)}\n`);
  process.stdout.write(`${JSON.stringify(result, null, 2)}\n`);
  if (!Object.values(result.checks).every(Boolean)) process.exitCode = 1;
}

await main();
