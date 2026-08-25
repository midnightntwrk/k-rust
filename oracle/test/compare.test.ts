import { afterEach, describe, expect, test } from "bun:test";
import { mkdtemp, mkdir, rm, writeFile } from "node:fs/promises";
import { tmpdir } from "node:os";
import { resolve } from "node:path";
import { compareBundles } from "../src/compare.js";
import { sha256, writeJson } from "../src/io.js";

const roots: string[] = [];

afterEach(async () => {
  await Promise.all(roots.splice(0).map((root) => rm(root, { recursive: true, force: true })));
});

async function fakeBundle(content: string): Promise<string> {
  const root = await mkdtemp(resolve(tmpdir(), "kink-oracle-test-"));
  roots.push(root);
  await mkdir(`${root}/normalized/full`, { recursive: true });
  await writeFile(`${root}/normalized/full/compiled-json`, content, "utf8");
  const digest = sha256(content);
  await writeJson(`${root}/bundle.json`, {
    schemaVersion: 1,
    runs: [
      {
        id: "full",
        artifacts: [
          {
            id: "compiled-json",
            normalizedPath: "normalized/full/compiled-json",
            normalizedSha256: digest,
          },
        ],
      },
    ],
  });
  return root;
}

describe("bundle comparison", () => {
  test("equal normalized boundaries compare equal", async () => {
    const left = await fakeBundle('{"value":1}\n');
    const right = await fakeBundle('{"value":1}\n');
    const comparison = await compareBundles(left, right);
    expect(comparison.equal).toBe(true);
    expect(comparison.artifacts).toEqual([
      expect.objectContaining({ boundary: "full:compiled-json", status: "equal" }),
    ]);
  });

  test("a one-token mutation is detected and localized", async () => {
    const left = await fakeBundle('{"value":1}\n');
    const right = await fakeBundle('{"value":2}\n');
    const comparison = await compareBundles(left, right);
    expect(comparison.equal).toBe(false);
    expect(comparison.artifacts[0]).toEqual(
      expect.objectContaining({
        boundary: "full:compiled-json",
        status: "different",
        firstDifference: expect.objectContaining({ line: 1, column: 10 }),
      }),
    );
  });
});
