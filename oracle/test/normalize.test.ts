import { describe, expect, test } from "bun:test";
import { resolve } from "node:path";
import { loadNormalizationConfig, normalizeJsonText, normalizePlainText } from "../src/normalize.js";
import type { NormalizationContext, NormalizationProfile } from "../src/types.js";

const context: NormalizationContext = {
  definitionPath: "/checkout/definition.k",
  kInstallRoot: "/nix/store/pinned-k",
};

describe("normalization allowlist", () => {
  test("checked policy parses and exposes only named profiles", async () => {
    const config = await loadNormalizationConfig(resolve(import.meta.dir, "../normalization.json"));
    expect(Object.keys(config.profiles).sort()).toEqual(["k-json-v1", "kore-text-v1", "plain-text-v1"]);
  });

  test("JSON sorts object keys, preserves array order, and replaces exact roots", () => {
    const profile: NormalizationProfile = {
      kind: "json",
      rules: [
        { id: "definition", operation: "replace-definition-path", reason: "test", evidence: "test" },
        { id: "install", operation: "replace-k-install-root", reason: "test", evidence: "test" },
        { id: "keys", operation: "canonical-json-object-keys", reason: "test", evidence: "test" },
      ],
    };
    const input = JSON.stringify({ z: [2, 1], a: "Source(/checkout/definition.k)", k: "/nix/store/pinned-k/include" });
    expect(normalizeJsonText(input, profile, context)).toBe(
      '{\n  "a": "Source(<DEFINITION>)",\n  "k": "<K_INSTALL>/include",\n  "z": [\n    2,\n    1\n  ]\n}\n',
    );
  });

  test("text normalization does not reorder or otherwise rewrite content", () => {
    const profile: NormalizationProfile = {
      kind: "text",
      rules: [
        { id: "lines", operation: "canonical-newlines", reason: "test", evidence: "test" },
        { id: "definition", operation: "replace-definition-path", reason: "test", evidence: "test" },
      ],
    };
    expect(normalizePlainText("b\r\na /checkout/definition.k\r", profile, context)).toBe("b\na <DEFINITION>\n");
  });
});
