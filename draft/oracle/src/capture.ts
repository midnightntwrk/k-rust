import { copyFile, mkdir, stat, writeFile } from "node:fs/promises";
import { dirname, relative, sep } from "node:path";
import { loadManifest } from "./manifest.js";
import { pathExists, resolveExecutable, sha256File, writeJson } from "./io.js";
import { loadNormalizationConfig, normalizeArtifact } from "./normalize.js";
import type { CapturedArtifact, CapturedRun, OracleBundle } from "./types.js";

function portableRelative(from: string, to: string): string {
  return relative(from, to).split(sep).join("/");
}

async function runProcess(argv: readonly string[], cwd: string, environment: Record<string, string>): Promise<{
  readonly exitCode: number;
  readonly stdout: string;
  readonly stderr: string;
  readonly durationMs: number;
}> {
  const start = performance.now();
  const process = Bun.spawn([...argv], {
    cwd,
    env: environment,
    stdout: "pipe",
    stderr: "pipe",
  });
  const [exitCode, stdout, stderr] = await Promise.all([
    process.exited,
    new Response(process.stdout).text(),
    new Response(process.stderr).text(),
  ]);
  return { exitCode, stdout, stderr, durationMs: Math.round(performance.now() - start) };
}

function controlledEnvironment(): Record<string, string> {
  const environment: Record<string, string> = { LC_ALL: "C", LANG: "C", TZ: "UTC" };
  for (const name of ["PATH", "HOME", "USER", "TMPDIR"] as const) {
    const value = process.env[name];
    if (value !== undefined) environment[name] = value;
  }
  return environment;
}

function releaseFromVersion(output: string): string {
  const match = /^K version:\s*(\S+)/m.exec(output);
  if (match?.[1] === undefined) throw new Error(`Could not parse K release from kompile --version output:\n${output}`);
  return match[1];
}

export async function captureManifest(manifestFile: string, outputDirectory: string): Promise<string> {
  const loaded = await loadManifest(manifestFile);
  if (await pathExists(outputDirectory)) throw new Error(`Refusing to overwrite existing capture directory: ${outputDirectory}`);
  await mkdir(outputDirectory, { recursive: true });

  const executable = await resolveExecutable(loaded.manifest.kompile);
  const environment = controlledEnvironment();
  const version = await runProcess([executable.invoked, "--version"], loaded.workingDirectory, environment);
  if (version.exitCode !== 0) throw new Error(`kompile --version exited ${version.exitCode}: ${version.stderr}`);
  const release = releaseFromVersion(version.stdout);
  if (release !== loaded.manifest.expectedK.release) {
    throw new Error(`K release mismatch: expected ${loaded.manifest.expectedK.release}, got ${release}`);
  }
  if (
    loaded.manifest.expectedK.requireCommitInExecutablePath &&
    !executable.resolved.toLowerCase().includes(loaded.manifest.expectedK.commit.toLowerCase())
  ) {
    throw new Error(
      `Could not verify K commit ${loaded.manifest.expectedK.commit} from executable path ${executable.resolved}`,
    );
  }
  const kInstallRoot = dirname(dirname(executable.resolved));
  const normalization = await loadNormalizationConfig(loaded.normalizationPath);

  const inputsDirectory = `${outputDirectory}/inputs`;
  await mkdir(inputsDirectory, { recursive: true });
  await copyFile(loaded.manifestPath, `${inputsDirectory}/manifest.json`);
  await copyFile(loaded.definitionPath, `${inputsDirectory}/definition.k`);
  await copyFile(loaded.normalizationPath, `${inputsDirectory}/normalization.json`);

  const capturedRuns: CapturedRun[] = [];
  for (const run of loaded.manifest.runs) {
    const runRoot = `${outputDirectory}/raw/${run.id}`;
    const definitionOutput = `${runRoot}/definition`;
    await mkdir(runRoot, { recursive: true });
    const argv = [
      executable.invoked,
      loaded.definitionPath,
      "--backend",
      loaded.manifest.backend,
      "--emit-json",
      "--main-module",
      loaded.manifest.mainModule,
      "--syntax-module",
      loaded.manifest.syntaxModule,
      "--output-definition",
      definitionOutput,
    ];
    for (const include of loaded.includeDirectories) argv.push("-I", include);
    if (run.steps !== undefined) argv.push("--kore-backend-steps", run.steps.join(","));
    argv.push(...(loaded.manifest.extraArguments ?? []));
    await writeJson(`${runRoot}/invocation.json`, { cwd: loaded.workingDirectory, argv, environment });

    const result = await runProcess(argv, loaded.workingDirectory, environment);
    await writeFile(`${runRoot}/stdout.txt`, result.stdout, "utf8");
    await writeFile(`${runRoot}/stderr.txt`, result.stderr, "utf8");
    if (!run.expectedExitCodes.includes(result.exitCode)) {
      throw new Error(
        `Run ${run.id} exited ${result.exitCode}; expected ${run.expectedExitCodes.join(", ")}. See ${runRoot}/stderr.txt`,
      );
    }
    for (const expected of run.expectedStderrSubstrings ?? []) {
      if (!result.stderr.includes(expected)) {
        throw new Error(`Run ${run.id} stderr did not contain ${JSON.stringify(expected)}. See ${runRoot}/stderr.txt`);
      }
    }

    const capturedArtifacts: CapturedArtifact[] = [];
    for (const artifact of run.artifacts) {
      const rawPath = `${definitionOutput}/${artifact.path}`;
      if (!(await pathExists(rawPath))) throw new Error(`Run ${run.id} did not produce required artifact ${rawPath}`);
      const normalizedPath = `${outputDirectory}/normalized/${run.id}/${artifact.id}`;
      await normalizeArtifact(rawPath, normalizedPath, artifact.profile, normalization, {
        definitionPath: loaded.definitionPath,
        kInstallRoot,
      });
      const [rawStats, normalizedStats] = await Promise.all([stat(rawPath), stat(normalizedPath)]);
      capturedArtifacts.push({
        id: artifact.id,
        profile: artifact.profile,
        rawPath: portableRelative(outputDirectory, rawPath),
        normalizedPath: portableRelative(outputDirectory, normalizedPath),
        rawSha256: await sha256File(rawPath),
        normalizedSha256: await sha256File(normalizedPath),
        rawBytes: rawStats.size,
        normalizedBytes: normalizedStats.size,
      });
    }
    capturedRuns.push({
      id: run.id,
      steps: run.steps ?? null,
      argv,
      exitCode: result.exitCode,
      acceptedNonzeroExit: result.exitCode !== 0,
      durationMs: result.durationMs,
      stdoutPath: portableRelative(outputDirectory, `${runRoot}/stdout.txt`),
      stderrPath: portableRelative(outputDirectory, `${runRoot}/stderr.txt`),
      artifacts: capturedArtifacts,
    });
  }

  const bundle: OracleBundle = {
    schemaVersion: 1,
    manifestId: loaded.manifest.id,
    manifestPath: loaded.manifestPath,
    manifestSha256: await sha256File(loaded.manifestPath),
    definition: { path: loaded.definitionPath, sha256: await sha256File(loaded.definitionPath) },
    normalization: { path: loaded.normalizationPath, sha256: await sha256File(loaded.normalizationPath) },
    inputs: {
      manifestSnapshot: "inputs/manifest.json",
      definitionSnapshot: "inputs/definition.k",
      normalizationSnapshot: "inputs/normalization.json",
    },
    toolchain: {
      executable: executable.invoked,
      resolvedExecutable: executable.resolved,
      kInstallRoot,
      versionOutput: version.stdout,
      release,
      expectedCommit: loaded.manifest.expectedK.commit,
      commitEvidence: "executable-path",
    },
    environment,
    runs: capturedRuns,
  };
  const bundlePath = `${outputDirectory}/bundle.json`;
  await writeJson(bundlePath, bundle);
  return bundlePath;
}
