import { dirname, isAbsolute, resolve } from "node:path";
import {
  pathExists,
  readJson,
  requireBoolean,
  requireNumberArray,
  requireObject,
  requireString,
  requireStringArray,
} from "./io.js";
import type { ArtifactSpec, LoadedManifest, OracleManifest, RunSpec, SmokeSuite } from "./types.js";

function optionalStringArray(value: unknown, where: string): readonly string[] | undefined {
  return value === undefined ? undefined : requireStringArray(value, where);
}

function requireId(value: unknown, where: string): string {
  const id = requireString(value, where);
  if (!/^[a-z0-9][a-z0-9-]*$/.test(id)) throw new Error(`${where} must use lowercase letters, digits, and hyphens`);
  return id;
}

function requireArtifactPath(value: unknown, where: string): string {
  const path = requireString(value, where);
  if (isAbsolute(path) || path.split(/[\\/]/u).includes("..")) {
    throw new Error(`${where} must be a safe relative path within the definition output`);
  }
  return path;
}

function parseArtifact(value: unknown, where: string): ArtifactSpec {
  const object = requireObject(value, where);
  return {
    id: requireId(object["id"], `${where}.id`),
    path: requireArtifactPath(object["path"], `${where}.path`),
    profile: requireId(object["profile"], `${where}.profile`),
  };
}

function parseRun(value: unknown, where: string): RunSpec {
  const object = requireObject(value, where);
  if (!Array.isArray(object["artifacts"]) || object["artifacts"].length === 0) {
    throw new Error(`${where}.artifacts must be a non-empty array`);
  }
  const steps = optionalStringArray(object["steps"], `${where}.steps`);
  if (steps?.some((step) => !/^[A-Za-z0-9]+$/.test(step)) === true) {
    throw new Error(`${where}.steps contains an invalid stage name`);
  }
  const stderr = optionalStringArray(object["expectedStderrSubstrings"], `${where}.expectedStderrSubstrings`);
  return {
    id: requireId(object["id"], `${where}.id`),
    ...(steps === undefined ? {} : { steps }),
    expectedExitCodes: requireNumberArray(object["expectedExitCodes"], `${where}.expectedExitCodes`),
    ...(stderr === undefined ? {} : { expectedStderrSubstrings: stderr }),
    artifacts: object["artifacts"].map((item, index) => parseArtifact(item, `${where}.artifacts[${index}]`)),
  };
}

function unique(values: readonly string[], where: string): void {
  const duplicates = values.filter((value, index) => values.indexOf(value) !== index);
  if (duplicates.length > 0) throw new Error(`${where} contains duplicate IDs: ${[...new Set(duplicates)].join(", ")}`);
}

export async function loadManifest(path: string): Promise<LoadedManifest> {
  const manifestPath = resolve(path);
  const object = requireObject(await readJson(manifestPath), manifestPath);
  if (object["schemaVersion"] !== 1) throw new Error(`${manifestPath}.schemaVersion must be 1`);
  const expected = requireObject(object["expectedK"], `${manifestPath}.expectedK`);
  if (!Array.isArray(object["runs"]) || object["runs"].length === 0) {
    throw new Error(`${manifestPath}.runs must be a non-empty array`);
  }
  const backend = requireString(object["backend"], `${manifestPath}.backend`);
  if (backend !== "haskell" && backend !== "kore") throw new Error(`${manifestPath}.backend must be haskell or kore`);
  const includes = optionalStringArray(object["includeDirectories"], `${manifestPath}.includeDirectories`);
  const extra = optionalStringArray(object["extraArguments"], `${manifestPath}.extraArguments`);
  const controlledArguments = new Set([
    "--backend",
    "--emit-json",
    "--main-module",
    "--syntax-module",
    "--output-definition",
    "-o",
    "--kore-backend-steps",
  ]);
  const forbiddenExtra = extra?.find((argument) => controlledArguments.has(argument));
  if (forbiddenExtra !== undefined) {
    throw new Error(`${manifestPath}.extraArguments cannot override harness-controlled option ${forbiddenExtra}`);
  }
  const manifest: OracleManifest = {
    schemaVersion: 1,
    id: requireId(object["id"], `${manifestPath}.id`),
    definition: requireString(object["definition"], `${manifestPath}.definition`),
    workingDirectory: requireString(object["workingDirectory"], `${manifestPath}.workingDirectory`),
    kompile: requireString(object["kompile"], `${manifestPath}.kompile`),
    expectedK: {
      release: requireString(expected["release"], `${manifestPath}.expectedK.release`),
      commit: requireString(expected["commit"], `${manifestPath}.expectedK.commit`),
      requireCommitInExecutablePath: requireBoolean(
        expected["requireCommitInExecutablePath"],
        `${manifestPath}.expectedK.requireCommitInExecutablePath`,
      ),
    },
    backend,
    mainModule: requireString(object["mainModule"], `${manifestPath}.mainModule`),
    syntaxModule: requireString(object["syntaxModule"], `${manifestPath}.syntaxModule`),
    normalization: requireString(object["normalization"], `${manifestPath}.normalization`),
    ...(includes === undefined ? {} : { includeDirectories: includes }),
    ...(extra === undefined ? {} : { extraArguments: extra }),
    runs: object["runs"].map((item, index) => parseRun(item, `${manifestPath}.runs[${index}]`)),
  };
  unique(manifest.runs.map((run) => run.id), `${manifestPath}.runs`);
  for (const run of manifest.runs) unique(run.artifacts.map((artifact) => artifact.id), `${manifestPath}.${run.id}.artifacts`);

  const base = dirname(manifestPath);
  const loaded: LoadedManifest = {
    manifest,
    manifestPath,
    definitionPath: resolve(base, manifest.definition),
    workingDirectory: resolve(base, manifest.workingDirectory),
    normalizationPath: resolve(base, manifest.normalization),
    includeDirectories: (manifest.includeDirectories ?? []).map((item) => resolve(base, item)),
  };
  for (const [label, candidate] of [
    ["definition", loaded.definitionPath],
    ["working directory", loaded.workingDirectory],
    ["normalization config", loaded.normalizationPath],
    ...loaded.includeDirectories.map((item) => ["include directory", item] as const),
  ] as const) {
    if (!(await pathExists(candidate))) throw new Error(`Manifest ${label} does not exist: ${candidate}`);
  }
  return loaded;
}

export async function loadSmokeSuite(path: string): Promise<{
  readonly suite: SmokeSuite;
  readonly suitePath: string;
  readonly baselineManifest: string;
  readonly mutationManifest: string;
}> {
  const suitePath = resolve(path);
  const object = requireObject(await readJson(suitePath), suitePath);
  if (object["schemaVersion"] !== 1) throw new Error(`${suitePath}.schemaVersion must be 1`);
  const suite: SmokeSuite = {
    schemaVersion: 1,
    id: requireId(object["id"], `${suitePath}.id`),
    baselineManifest: requireString(object["baselineManifest"], `${suitePath}.baselineManifest`),
    mutationManifest: requireString(object["mutationManifest"], `${suitePath}.mutationManifest`),
    expectedDifferent: requireStringArray(object["expectedDifferent"], `${suitePath}.expectedDifferent`),
    expectedEqual: requireStringArray(object["expectedEqual"], `${suitePath}.expectedEqual`),
  };
  unique([...suite.expectedDifferent, ...suite.expectedEqual], `${suitePath} expectations`);
  return {
    suite,
    suitePath,
    baselineManifest: resolve(dirname(suitePath), suite.baselineManifest),
    mutationManifest: resolve(dirname(suitePath), suite.mutationManifest),
  };
}
