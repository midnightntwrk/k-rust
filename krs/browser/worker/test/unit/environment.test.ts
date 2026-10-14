import { expect, test } from "bun:test";
import { existsSync } from "node:fs";
import { checkoutScratch, REPO } from "../harness/environment.ts";

test("checkout scratch matches the Python gate helper", () => {
  const result = Bun.spawnSync(
    [
      "python3", "-c",
      "import sys; sys.path.insert(0, 'tests'); from support.tools import checkout_scratch; print(checkout_scratch())",
    ],
    { cwd: REPO, env: { ...process.env, PYTHONDONTWRITEBYTECODE: "1" } },
  );
  expect(result.exitCode).toBe(0);
  const pythonPath = new TextDecoder().decode(result.stdout).trim();
  expect(checkoutScratch()).toBe(pythonPath);
  expect(existsSync(pythonPath)).toBe(true);
});
