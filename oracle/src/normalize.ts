import { readFile, writeFile } from "node:fs/promises";
import { dirname } from "node:path";
import { mkdir } from "node:fs/promises";
import { readJson, requireObject, requireString } from "./io.js";
import type {
  JsonValue,
  NormalizationConfig,
  NormalizationContext,
  NormalizationOperation,
  NormalizationProfile,
  NormalizationRule,
} from "./types.js";

const OPERATIONS: readonly NormalizationOperation[] = [
  "canonical-json-object-keys",
  "canonical-newlines",
  "replace-definition-path",
  "replace-k-install-root",
];

function parseRule(value: unknown, where: string): NormalizationRule {
  const object = requireObject(value, where);
  const operation = requireString(object["operation"], `${where}.operation`);
  if (!OPERATIONS.includes(operation as NormalizationOperation)) {
    throw new Error(`${where}.operation is unsupported: ${operation}`);
  }
  return {
    id: requireString(object["id"], `${where}.id`),
    operation: operation as NormalizationOperation,
    reason: requireString(object["reason"], `${where}.reason`),
    evidence: requireString(object["evidence"], `${where}.evidence`),
  };
}

export async function loadNormalizationConfig(path: string): Promise<NormalizationConfig> {
  const object = requireObject(await readJson(path), path);
  if (object["schemaVersion"] !== 1) throw new Error(`${path}.schemaVersion must be 1`);
  const rawProfiles = requireObject(object["profiles"], `${path}.profiles`);
  const profiles: Record<string, NormalizationProfile> = {};
  for (const [name, raw] of Object.entries(rawProfiles)) {
    const profile = requireObject(raw, `${path}.profiles.${name}`);
    const kind = requireString(profile["kind"], `${path}.profiles.${name}.kind`);
    if (kind !== "json" && kind !== "text") throw new Error(`${path}.profiles.${name}.kind must be json or text`);
    if (!Array.isArray(profile["rules"]) || profile["rules"].length === 0) {
      throw new Error(`${path}.profiles.${name}.rules must be a non-empty array`);
    }
    const rules = profile["rules"].map((item, index) => parseRule(item, `${path}.profiles.${name}.rules[${index}]`));
    const duplicates = rules.filter((rule, index) => rules.findIndex((other) => other.id === rule.id) !== index);
    if (duplicates.length > 0) throw new Error(`${path}.profiles.${name} has duplicate rule IDs`);
    if (kind === "json" && !rules.some((rule) => rule.operation === "canonical-json-object-keys")) {
      throw new Error(`${path}.profiles.${name} must explicitly canonicalize JSON object keys`);
    }
    profiles[name] = { kind, rules };
  }
  return { schemaVersion: 1, profiles };
}

function replaceAllExact(value: string, from: string, to: string): string {
  return from.length === 0 ? value : value.split(from).join(to);
}

function replacementFor(operation: NormalizationOperation, context: NormalizationContext): readonly [string, string] | null {
  switch (operation) {
    case "replace-definition-path":
      return [context.definitionPath, "<DEFINITION>"];
    case "replace-k-install-root":
      return [context.kInstallRoot, "<K_INSTALL>"];
    default:
      return null;
  }
}

function transformJson(value: JsonValue, rules: readonly NormalizationRule[], context: NormalizationContext): JsonValue {
  if (typeof value === "string") {
    let transformed = value;
    for (const rule of rules) {
      const replacement = replacementFor(rule.operation, context);
      if (replacement !== null) transformed = replaceAllExact(transformed, replacement[0], replacement[1]);
    }
    return transformed;
  }
  if (Array.isArray(value)) return value.map((item) => transformJson(item, rules, context));
  if (value !== null && typeof value === "object") {
    const result: Record<string, JsonValue> = {};
    for (const key of Object.keys(value).sort()) result[key] = transformJson(value[key] as JsonValue, rules, context);
    return result;
  }
  return value;
}

export function normalizeJsonText(text: string, profile: NormalizationProfile, context: NormalizationContext): string {
  let parsed: JsonValue;
  try {
    parsed = JSON.parse(text) as JsonValue;
  } catch (error) {
    throw new Error(`Could not parse JSON artifact: ${error instanceof Error ? error.message : String(error)}`);
  }
  return `${JSON.stringify(transformJson(parsed, profile.rules, context), null, 2)}\n`;
}

export function normalizePlainText(text: string, profile: NormalizationProfile, context: NormalizationContext): string {
  let result = text;
  for (const rule of profile.rules) {
    switch (rule.operation) {
      case "canonical-newlines":
        result = result.replaceAll("\r\n", "\n").replaceAll("\r", "\n");
        break;
      case "replace-definition-path":
      case "replace-k-install-root": {
        const replacement = replacementFor(rule.operation, context);
        if (replacement !== null) result = replaceAllExact(result, replacement[0], replacement[1]);
        break;
      }
      case "canonical-json-object-keys":
        throw new Error(`JSON canonicalization rule ${rule.id} cannot be used by a text profile`);
    }
  }
  return result;
}

export async function normalizeArtifact(
  inputPath: string,
  outputPath: string,
  profileName: string,
  config: NormalizationConfig,
  context: NormalizationContext,
): Promise<void> {
  const profile = config.profiles[profileName];
  if (profile === undefined) throw new Error(`Unknown normalization profile: ${profileName}`);
  const input = await readFile(inputPath, "utf8");
  const output = profile.kind === "json" ? normalizeJsonText(input, profile, context) : normalizePlainText(input, profile, context);
  await mkdir(dirname(outputPath), { recursive: true });
  await writeFile(outputPath, output, "utf8");
}
