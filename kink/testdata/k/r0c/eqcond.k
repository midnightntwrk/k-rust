// Re-pin R0c-fix-3 (R0c-fix-2 review minor 3): a rule condition `{ A #Equals B }` over two
// possibly undefined terms. k-rust 501f18b9 keeps it as written and its SMT translation has no
// model where both sides are undefined (docs/compatibility.md, "Two gaps remain"), so answers
// over the definition may be wrong; kink excludes such a definition (equals-condition).
module EQCOND-SYNTAX
  imports INT-SYNTAX
  imports ML-SYNTAX
  syntax Prog ::= go(Int) [symbol(go)] | yes() [symbol(yes)]
endmodule
module EQCOND
  imports EQCOND-SYNTAX
  imports INT
  imports BOOL
  configuration <k> $PGM:Prog </k>
  rule [go]: <k> go(I) => yes() </k> requires { 10 /Int I #Equals 10 /Int I }
endmodule
