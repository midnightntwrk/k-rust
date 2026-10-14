import { expect, test } from "bun:test";
import { check, SCENARIOS } from "../scenarios.ts";

const tour = SCENARIOS.find((scenario) => scenario.name === "tour-minimal")!.expect!;

function successfulEvents(bundleSha256: string) {
  return [
    ...["assets", "policy", "expand", "rustc-lesson", "rustc-collector", "collect", "bundle"].flatMap((stage) => [
      { type: "progress", stage, state: "start" },
      { type: "progress", stage, state: "end" },
    ]),
    { type: "success", bundleSha256 },
  ];
}

test("tour success compares with the runner's native oracle digest", () => {
  for (const digest of ["a".repeat(64), "b".repeat(64)]) {
    expect(check(tour, successfulEvents(digest), digest)).toEqual({ ok: true, problems: [] });
  }
  const verdict = check(tour, successfulEvents("a".repeat(64)), "b".repeat(64));
  expect(verdict.ok).toBe(false);
  expect(verdict.problems).toEqual([`bundle ${"a".repeat(64)}, expected native oracle ${"b".repeat(64)}`]);
});

test("scenario checks require a native oracle digest", () => {
  expect(() => check(tour, successfulEvents("a".repeat(64)), "")).toThrow("native oracle bundle SHA-256");
});
