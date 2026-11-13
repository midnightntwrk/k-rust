// A map is strict in its entries: an entry whose value is undefined (1 /Int 0) makes the map,
// and so the rule's result, undefined; the rule of the same priority with a defined entry
// gives the one final configuration.
module CASE-SYNTAX
  imports INT-SYNTAX
  imports MAP
  syntax S ::= go(Map, Int) | r(Int, Map)
endmodule
module CASE
  imports CASE-SYNTAX
  imports INT
  imports MAP
  configuration <k> $PGM:S </k>
  rule <k> go(M, Z) => r(1, M (5 |-> 1 /Int Z)) </k>
  rule <k> go(M, Z) => r(2, M (5 |-> 1 /Int (Z +Int 1))) </k>
endmodule
