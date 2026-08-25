import { describe, expect, test } from "bun:test";
import { renderPDefinition, renderPTerm } from "../src/adapter.js";
import { normalizeProjection } from "../src/types.js";

describe("P1 probe utilities", () => {
  test("renders explicit recursive P1 syntax", () => {
    expect(renderPTerm({ kind: "app", label: "zero", args: [] })).toBe('pApp("zero", pTermNil)');
    expect(renderPDefinition({ module: "M", sorts: [], productions: [], rules: [] }))
      .toBe('pDefinition("M", pSortNil, pProductionNil, pRuleNil)\n');
  });

  test("normalizes declaration and axiom order", () => {
    const normalized = normalizeProjection({
      module: "M",
      sorts: ["Z", "A"],
      symbols: [],
      axioms: [
        { kind: "functional", label: "z" },
        { kind: "functional", label: "a" },
      ],
    });
    expect(normalized.sorts).toEqual(["A", "Z"]);
    expect(normalized.axioms.map((axiom) => "label" in axiom ? axiom.label : "")).toEqual(["a", "z"]);
  });
});
