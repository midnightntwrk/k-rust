import { describe, expect, test } from "bun:test";
import { app, canonicalTerm, token } from "../src/canonical.js";

describe("P2 canonical parsed-KAST projection", () => {
  test("preserves application grouping and tokens", () => {
    expect(canonicalTerm({
      node: "KApply", label: { name: "f" }, args: [
        { node: "KToken", sort: { name: "Id" }, token: "x" },
      ],
    })).toEqual(app("f", token("Id", "x")));
  });

  test("turns semantic casts into inferred variable sorts", () => {
    expect(canonicalTerm({
      node: "KApply", label: { name: "#SemanticCastToExp" }, args: [
        { node: "KVariable", name: "X" },
      ],
    })).toEqual({ node: "variable", name: "X", sort: "Exp" });
  });
});
