import { mkdir, readFile, writeFile } from "node:fs/promises";
import { resolve } from "node:path";
import { adaptParsedDefinition, renderPDefinition } from "./adapter.js";
import { decodeKrunResult, renderKast } from "./decode.js";
import { projectOfficialKore } from "./official.js";
import { keyOf, normalizeProjection, type CanonicalProjection } from "./types.js";

const root = resolve(import.meta.dir, "../..");
const build = resolve(root, "p1/build");
const fixture = resolve(root, "p1/fixtures/peano.k");
const officialDefinition = resolve(build, "peano-kompiled");
const p1Definition = resolve(build, "p1-kompiled");

interface CommandResult {
  readonly command: readonly string[];
  readonly exitCode: number;
  readonly durationMs: number;
  readonly stdout: string;
  readonly stderr: string;
}

async function run(command: readonly string[], cwd = root): Promise<CommandResult> {
  const started = performance.now();
  const process = Bun.spawn([...command], { cwd, stdout: "pipe", stderr: "pipe" });
  const [stdout, stderr, exitCode] = await Promise.all([
    new Response(process.stdout).text(),
    new Response(process.stderr).text(),
    process.exited,
  ]);
  const result = { command, exitCode, durationMs: Math.round(performance.now() - started), stdout, stderr };
  if (exitCode !== 0) {
    throw new Error(`${command.join(" ")} failed (${exitCode})\n${stderr}`);
  }
  return result;
}

const withoutRewrites = (projection: CanonicalProjection): CanonicalProjection => normalizeProjection({
  ...projection,
  axioms: projection.axioms.filter((axiom) => axiom.kind !== "rewrite"),
});

async function main(): Promise<void> {
  await mkdir(build, { recursive: true });
  const commands: CommandResult[] = [];
  commands.push(await run([
    "kompile", fixture,
    "--backend", "haskell", "--emit-json",
    "--main-module", "P1-PEANO", "--syntax-module", "P1-PEANO-SYNTAX",
    "--output-definition", officialDefinition,
  ]));
  commands.push(await run([
    "kompile", resolve(root, "p1/src/p1.k"),
    "--backend", "haskell", "--emit-json",
    "--main-module", "P1", "--syntax-module", "P1-SYNTAX",
    "--output-definition", p1Definition,
  ]));

  const parsedPath = resolve(officialDefinition, "parsed.json");
  const definition = await adaptParsedDefinition(parsedPath, fixture, "P1-PEANO");
  const p1Input = resolve(build, "peano-generated.p1");
  await writeFile(p1Input, renderPDefinition(definition));
  const p1Run = await run(["krun", p1Input, "--definition", p1Definition, "--output", "json"]);
  commands.push(p1Run);
  const p1Output = resolve(build, "peano-p1-output.json");
  await writeFile(p1Output, p1Run.stdout);

  const decoded = await decodeKrunResult(p1Output);
  const official = await projectOfficialKore(resolve(officialDefinition, "definition.kore"), fixture, definition);
  const structuralP1 = withoutRewrites(decoded.projection);
  const structuralEqual = keyOf(structuralP1) === keyOf(official);

  const parsedRewrites = definition.rules.filter((rule) => rule.kind === "rewrite");
  const p1Rewrites = decoded.projection.axioms.filter((axiom) => axiom.kind === "rewrite");
  const parsedRewriteEqual = keyOf(parsedRewrites) === keyOf(p1Rewrites.map(({ kind: _, ...rule }) => ({ kind: "rewrite", ...rule })));

  const fixedInput = resolve(build, "peano-fixed-point.p1");
  await writeFile(fixedInput, `${renderKast(decoded.term)}\n`);
  const fixedRun = await run(["krun", fixedInput, "--definition", p1Definition, "--output", "json"]);
  commands.push(fixedRun);
  const fixedOutput = resolve(build, "peano-fixed-point-output.json");
  await writeFile(fixedOutput, fixedRun.stdout);
  const fixed = await decodeKrunResult(fixedOutput);
  const fixedPointEqual = keyOf(decoded.projection) === keyOf(fixed.projection);

  const execution = await run([
    "krun", resolve(root, "p1/fixtures/program.peano"),
    "--definition", officialDefinition, "--output", "pretty",
  ]);
  commands.push(execution);

  const foobarFixture = resolve(root, "p1/fixtures/foobar.k");
  const foobarOfficialDefinition = resolve(build, "foobar-kompiled");
  commands.push(await run([
    "kompile", foobarFixture,
    "--backend", "haskell", "--emit-json",
    "--main-module", "P1-FOOBAR", "--syntax-module", "P1-FOOBAR-SYNTAX",
    "--output-definition", foobarOfficialDefinition,
  ]));
  const foobarDefinition = await adaptParsedDefinition(
    resolve(foobarOfficialDefinition, "parsed.json"), foobarFixture, "P1-FOOBAR",
  );
  const foobarInput = resolve(build, "foobar-generated.p1");
  await writeFile(foobarInput, renderPDefinition(foobarDefinition));
  const foobarRun = await run(["krun", foobarInput, "--definition", p1Definition, "--output", "json"]);
  commands.push(foobarRun);
  const foobarOutput = resolve(build, "foobar-p1-output.json");
  await writeFile(foobarOutput, foobarRun.stdout);
  const foobarP1 = (await decodeKrunResult(foobarOutput)).projection;
  const foobarOfficial = await projectOfficialKore(
    resolve(foobarOfficialDefinition, "definition.kore"), foobarFixture, foobarDefinition,
  );
  const foobarStructuralEqual = keyOf(withoutRewrites(foobarP1)) === keyOf(foobarOfficial);
  const foobarExecution = await run([
    "krun", resolve(root, "p1/fixtures/program.foobar"),
    "--definition", foobarOfficialDefinition, "--output", "pretty",
  ]);
  commands.push(foobarExecution);
  const foobarExecutes = foobarExecution.stdout.includes("bar");

  const result = {
    probe: "P1 minimal lowering",
    fixture: "p1/fixtures/peano.k",
    boundary: {
      officialKore: ["sorts", "symbols", "constructor functional axioms", "constructor no-confusion axioms", "sort no-junk axioms", "function equations"],
      parsedKast: ["ordinary semantic rewrites"],
      excluded: ["configuration concretization of semantic rewrites", "full textual Kore serialization"],
    },
    checks: {
      structuralKoreProjectionEqual: structuralEqual,
      parsedRewriteProjectionEqual: parsedRewriteEqual,
      fixedPointEqual,
      officialKoreExecutes: execution.exitCode === 0,
      foobarStructuralKoreProjectionEqual: foobarStructuralEqual,
      foobarOfficialKoreExecutes: foobarExecutes,
    },
    counts: {
      sorts: decoded.projection.sorts.length,
      symbols: decoded.projection.symbols.length,
      structuralAxioms: structuralP1.axioms.length,
      functionEquations: decoded.projection.axioms.filter((axiom) => axiom.kind === "equation").length,
      semanticRewrites: p1Rewrites.length,
    },
    executionOutput: execution.stdout.trim(),
    commands: commands.map(({ command, exitCode, durationMs, stderr }) => ({ command, exitCode, durationMs, stderr: stderr.trim() })),
    projections: { peano: { p1: decoded.projection, official }, foobar: { p1: foobarP1, official: foobarOfficial } },
  };
  await writeFile(resolve(build, "probe-result.json"), `${JSON.stringify(result, null, 2)}\n`);
  process.stdout.write(`${JSON.stringify(result, null, 2)}\n`);
  if (!structuralEqual || !parsedRewriteEqual || !fixedPointEqual || execution.exitCode !== 0
    || !foobarStructuralEqual || !foobarExecutes) process.exitCode = 1;
}

await main();
