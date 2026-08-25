import { mkdir, readFile, writeFile } from "node:fs/promises";
import { resolve } from "node:path";
import { app, canonicalTerm, extractLabelledRule, token, type CanonicalTerm } from "./canonical.js";

const root = resolve(import.meta.dir, "../..");
const fixtureDir = resolve(root, "p2/fixtures");
const buildDir = resolve(root, "p2/build");

interface CommandEvidence {
  readonly argv: readonly string[];
  readonly exitCode: number;
  readonly durationMs: number;
  readonly stderr: string;
}

async function run(argv: readonly string[]): Promise<{ readonly evidence: CommandEvidence; readonly stdout: string }> {
  const start = performance.now();
  const child = Bun.spawn([...argv], { cwd: root, stdout: "pipe", stderr: "pipe" });
  const [stdout, stderr, exitCode] = await Promise.all([
    new Response(child.stdout).text(), new Response(child.stderr).text(), child.exited,
  ]);
  const evidence = { argv, exitCode, durationMs: Math.round(performance.now() - start), stderr: stderr.trim() };
  if (exitCode !== 0) throw new Error(`${argv.join(" ")} failed (${exitCode})\n${stderr}`);
  return { evidence, stdout };
}

const n = app("n");
const block = app("block");
const dangling = app("ifThen", app("true"), app("ifThenElse", app("false"), block, block));

const programs: readonly {
  readonly id: string;
  readonly definition: string;
  readonly file: string;
  readonly sort: string;
  readonly expected: CanonicalTerm;
}[] = [
  { id: "priority", definition: "expressions", file: "priority.exp", sort: "Exp", expected: app("plus", n, app("times", n, n)) },
  { id: "associativity", definition: "expressions", file: "associativity.exp", sort: "Exp", expected: app("plus", app("plus", n, n), n) },
  { id: "avoid", definition: "avoid", file: "avoid.stmt", sort: "Stmt", expected: dangling },
  { id: "prefer", definition: "prefer", file: "prefer.stmt", sort: "Stmt", expected: dangling },
  {
    id: "user-list", definition: "list", file: "list.pgm", sort: "Pgm",
    expected: app("bracket", app("atoms", n, app("atoms", n, app("atoms", n, app(".atoms"))))),
  },
  {
    id: "overload", definition: "overload", file: "overload.exp", sort: "Exp",
    expected: app("lvalDot", app("lval"), token("Id", "field")),
  },
];

const definitions = [
  { id: "expressions", module: "P2-EXPRESSIONS" },
  { id: "avoid", module: "P2-AVOID" },
  { id: "prefer", module: "P2-PREFER" },
  { id: "list", module: "P2-LIST" },
  { id: "overload", module: "P2-OVERLOAD", checkedInference: true },
] as const;

async function main(): Promise<void> {
  await mkdir(buildDir, { recursive: true });
  const commands: CommandEvidence[] = [];
  for (const definition of definitions) {
    const argv = [
      "kompile", resolve(fixtureDir, `${definition.id}.k`),
      "--backend", "haskell", "--emit-json",
      "--main-module", definition.module, "--syntax-module", definition.module,
      "--output-definition", resolve(buildDir, `${definition.id}-kompiled`),
    ];
    if ("checkedInference" in definition) argv.push("--type-inference-mode", "checked");
    commands.push((await run(argv)).evidence);
  }

  const cases = [];
  for (const program of programs) {
    const result = await run([
      "kast", resolve(fixtureDir, program.file),
      "--definition", resolve(buildDir, `${program.definition}-kompiled`),
      "--sort", program.sort, "--output", "json",
    ]);
    commands.push(result.evidence);
    const actual = canonicalTerm(JSON.parse(result.stdout).term);
    const equal = JSON.stringify(actual) === JSON.stringify(program.expected);
    cases.push({ id: program.id, equal, expected: program.expected, actual });
  }

  const parsed = JSON.parse(await readFile(resolve(buildDir, "overload-kompiled/parsed.json"), "utf8"));
  const inferenceActual = extractLabelledRule(parsed, "infer-lval");
  const inferenceExpected = {
    node: "app", label: "#KRewrite", args: [
      { node: "variable", name: "_", sort: "LVal" },
      { node: "app", label: "done", args: [] },
    ],
  } satisfies CanonicalTerm;
  // KRewrite is represented as its own node in parsed JSON; canonicalize it explicitly.
  const inferenceEqual = inferenceActual.node === "app"
    && inferenceActual.label === "#KRewrite"
    && JSON.stringify(inferenceActual.args) === JSON.stringify(inferenceExpected.args);
  cases.push({ id: "sort-inference-checked", equal: inferenceEqual, expected: inferenceExpected, actual: inferenceActual });

  const result = {
    probe: "P2 inner parsing and disambiguation",
    architecture: "replaceable official-K parsed-KAST adapter",
    decision: "Use the adapter for the first lowering delivery; keep a specified parser as a separate critical-path project.",
    checks: {
      allCasesPass: cases.every((item) => item.equal),
      checkedInferenceMode: true,
      independentRawForestOracleAvailable: false,
    },
    coverage: ["priority", "left associativity", "avoid", "prefer", "overload", "user-list completion", "SimpleSub/Z3 checked sort inference"],
    upstreamCensus: { innerParserJavaFiles: 31, innerParserJavaLines: 7429, orderedFilterStages: 12 },
    cases,
    commands,
  };
  await writeFile(resolve(buildDir, "probe-result.json"), `${JSON.stringify(result, null, 2)}\n`);
  process.stdout.write(`${JSON.stringify(result, null, 2)}\n`);
  if (!result.checks.allCasesPass) process.exitCode = 1;
}

await main();
