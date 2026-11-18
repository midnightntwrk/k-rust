// Each hooked function of UNIFICATION (unification.k) that is not sort-parametric, read as a
// parameter symbol of the definition's own (a builtin file's sentence about names no library text
// declares, Parse.isOwnBuiltin; no registry hook), applied once in a rule's right side to
// variables; fixture.toml params records `kcore sem-fields`'s parameter lines.
requires "unification.k"
module E6-PARAM-UNIFICATION
  imports UNIFICATION
  imports INT
  imports BOOL
  imports SET
  syntax KItem ::= go(Int, K, K) [symbol(go)]
  rule <k> go(1, X1:K, _) => #metaKVariables(X1) ... </k>
  rule <k> go(2, X1:K, _) => #renameVariables(X1) ... </k>
  rule <k> go(3, X1:K, X2:K) => #unifiable(X1, X2) ... </k>
  rule <k> go(4, X1:K, _) => #variables(X1) ... </k>
  rule <k> go(5, X1:K, _) => #variablesMap(X1) ... </k>
endmodule
