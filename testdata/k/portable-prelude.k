// Stand-ins for the three domains.md modules that kast.md imports.
// k-rust built without z3-inference cannot load the embedded prelude.md
// (Z3InferenceRequired; k-rust tests/inner_rules.rs
// portable_build_rejects_the_standard_prelude), so the shared test
// definitions load kast.md plus this file instead.
// KRS-owned request z3-free-structured-compile (k-rust KR-09, KR-20, KR-21,
// KR-22): delete this file once KR-22 lands and load prelude.md.
module SORT-BOOL
  syntax Bool [hook(BOOL.Bool)]
  syntax Bool ::= "true" [token] | "false" [token]
endmodule

module INT-SYNTAX
  syntax Int [hook(INT.Int)]
  syntax Int ::= r"[\\+\\-]?[0-9]+" [prefer, token, prec(2)]
endmodule

module STRING-SYNTAX
  syntax String [hook(STRING.String)]
  syntax String ::= r"[\\\"](([^\\\"\\n\\r\\\\])|([\\\\][nrtf\\\"\\\\])|([\\\\][x][0-9a-fA-F]{2})|([\\\\][u][0-9a-fA-F]{4})|([\\\\][U][0-9a-fA-F]{8}))*[\\\"]" [token]
endmodule
