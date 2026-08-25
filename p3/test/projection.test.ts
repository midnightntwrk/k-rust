import { describe, expect, test } from "bun:test";
import { normalizeProjection } from "../src/projection.js";

describe("P3 projection normalization", () => {
  test("normalizes fact order and completed cell sets", () => {
    const projection = normalizeProjection({
      edges: [{ child: "state", parent: "T" }, { child: "k", parent: "T" }],
      facts: [
        { kind: "rule", label: "z", mode: "rewrite", cells: ["T", "k", "T"], requires: false, ensures: false },
        { kind: "context", label: "a", phase: "heat", cells: ["k", "generatedTop", "T"] },
      ],
    });
    expect(projection.edges[0]).toEqual({ child: "k", parent: "T" });
    expect(projection.facts[0]).toEqual({
      kind: "context", label: "a", phase: "heat", cells: ["T", "generatedTop", "k"],
    });
    expect(projection.facts[1]).toEqual({
      kind: "rule", label: "z", mode: "rewrite", cells: ["T", "k"], requires: false, ensures: false,
    });
  });
});
