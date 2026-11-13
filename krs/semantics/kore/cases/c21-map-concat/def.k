// Map concatenation is defined on maps with disjoint keys: M (1 |-> 3) where M has the key 1 is
// undefined, so that rule has no successor; M (2 |-> 3) is the union; M .Map is M.
module CASE-SYNTAX
  imports INT-SYNTAX
  imports MAP
  syntax S ::= go(Map) | r(Int, Map)
endmodule
module CASE
  imports CASE-SYNTAX
  imports INT
  imports MAP
  configuration <k> $PGM:S </k>
  rule <k> go(M) => r(1, M (1 |-> 3)) </k>
  rule <k> go(M) => r(2, M (2 |-> 3)) </k>
  rule <k> go(M) => r(3, M .Map) </k>
endmodule
