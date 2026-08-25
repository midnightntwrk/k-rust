export type JsonValue = null | boolean | number | string | JsonValue[] | { [key: string]: JsonValue };

export interface ArtifactSpec {
  readonly id: string;
  readonly path: string;
  readonly profile: string;
}

export interface RunSpec {
  readonly id: string;
  readonly steps?: readonly string[];
  readonly expectedExitCodes: readonly number[];
  readonly expectedStderrSubstrings?: readonly string[];
  readonly artifacts: readonly ArtifactSpec[];
}

export interface OracleManifest {
  readonly schemaVersion: 1;
  readonly id: string;
  readonly definition: string;
  readonly workingDirectory: string;
  readonly kompile: string;
  readonly expectedK: {
    readonly release: string;
    readonly commit: string;
    readonly requireCommitInExecutablePath: boolean;
  };
  readonly backend: "haskell" | "kore";
  readonly mainModule: string;
  readonly syntaxModule: string;
  readonly normalization: string;
  readonly includeDirectories?: readonly string[];
  readonly extraArguments?: readonly string[];
  readonly runs: readonly RunSpec[];
}

export interface LoadedManifest {
  readonly manifest: OracleManifest;
  readonly manifestPath: string;
  readonly definitionPath: string;
  readonly workingDirectory: string;
  readonly normalizationPath: string;
  readonly includeDirectories: readonly string[];
}

export type NormalizationOperation =
  | "canonical-json-object-keys"
  | "canonical-newlines"
  | "replace-definition-path"
  | "replace-k-install-root";

export interface NormalizationRule {
  readonly id: string;
  readonly operation: NormalizationOperation;
  readonly reason: string;
  readonly evidence: string;
}

export interface NormalizationProfile {
  readonly kind: "json" | "text";
  readonly rules: readonly NormalizationRule[];
}

export interface NormalizationConfig {
  readonly schemaVersion: 1;
  readonly profiles: Readonly<Record<string, NormalizationProfile>>;
}

export interface NormalizationContext {
  readonly definitionPath: string;
  readonly kInstallRoot: string;
}

export interface CapturedArtifact {
  readonly id: string;
  readonly profile: string;
  readonly rawPath: string;
  readonly normalizedPath: string;
  readonly rawSha256: string;
  readonly normalizedSha256: string;
  readonly rawBytes: number;
  readonly normalizedBytes: number;
}

export interface CapturedRun {
  readonly id: string;
  readonly steps: readonly string[] | null;
  readonly argv: readonly string[];
  readonly exitCode: number;
  readonly acceptedNonzeroExit: boolean;
  readonly durationMs: number;
  readonly stdoutPath: string;
  readonly stderrPath: string;
  readonly artifacts: readonly CapturedArtifact[];
}

export interface OracleBundle {
  readonly schemaVersion: 1;
  readonly manifestId: string;
  readonly manifestPath: string;
  readonly manifestSha256: string;
  readonly definition: {
    readonly path: string;
    readonly sha256: string;
  };
  readonly normalization: {
    readonly path: string;
    readonly sha256: string;
  };
  readonly inputs: {
    readonly manifestSnapshot: string;
    readonly definitionSnapshot: string;
    readonly normalizationSnapshot: string;
  };
  readonly toolchain: {
    readonly executable: string;
    readonly resolvedExecutable: string;
    readonly kInstallRoot: string;
    readonly versionOutput: string;
    readonly release: string;
    readonly expectedCommit: string;
    readonly commitEvidence: "executable-path";
  };
  readonly environment: Readonly<Record<string, string>>;
  readonly runs: readonly CapturedRun[];
}

export interface ComparedArtifact {
  readonly boundary: string;
  readonly status: "equal" | "different" | "missing-left" | "missing-right";
  readonly leftSha256?: string;
  readonly rightSha256?: string;
  readonly firstDifference?: {
    readonly offset: number;
    readonly line: number;
    readonly column: number;
    readonly leftExcerpt: string;
    readonly rightExcerpt: string;
  };
}

export interface BundleComparison {
  readonly leftBundle: string;
  readonly rightBundle: string;
  readonly equal: boolean;
  readonly artifacts: readonly ComparedArtifact[];
}

export interface SmokeSuite {
  readonly schemaVersion: 1;
  readonly id: string;
  readonly baselineManifest: string;
  readonly mutationManifest: string;
  readonly expectedDifferent: readonly string[];
  readonly expectedEqual: readonly string[];
}
