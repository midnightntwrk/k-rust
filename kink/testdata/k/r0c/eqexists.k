// Re-pin R0-tail (R0c-fix-4 review minor 1, the reviewer's eqx.k and eqy.k): `{ A #Equals B }` in
// the ensures of a rewrite rule whose right-hand side has an existential variable. kompile emits
// `\rewrites(.., \exists ?Y. \and(rhs, ensures))`, so the ensures is under the binder. In `gy` the
// ensures is a conjunction of two equalities. Each is read as an equals-condition, which excludes
// the definition; `plain` has none.
module EQEXISTS-SYNTAX
  imports INT-SYNTAX
  imports ML-SYNTAX
  syntax Exp ::= Int
               | go(Int) [symbol(go)]
               | gy(Int) [symbol(gy)]
               | val(Int) [symbol(val)]
endmodule

module EQEXISTS
  imports EQEXISTS-SYNTAX
  imports INT
  imports BOOL
  configuration <k> $PGM:Exp </k>

  syntax KResult ::= Int
  rule [go]: go(I) => val(?Y) ensures { ?Y #Equals 10 /Int I }
  rule [gy]: gy(I) => val(?Y) ensures { ?Y #Equals I } #And { 10 /Int I #Equals 20 /Int I }
  rule [plain]: val(I) => I +Int 1
endmodule
