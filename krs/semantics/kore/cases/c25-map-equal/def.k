// Map concatenation is commutative: A B and B A are one map, so the variable M seen twice in
// p(M, M) matches them.
module CASE-SYNTAX
  imports INT-SYNTAX
  imports MAP
  syntax S ::= go(Map, Map) | p(Map, Map) | same(Map)
endmodule
module CASE
  imports CASE-SYNTAX
  imports INT
  imports MAP
  configuration <k> $PGM:S </k>
  rule <k> go(A, B) => p(A B, B A) </k>
  rule <k> p(M, M) => same(M) </k>
endmodule
