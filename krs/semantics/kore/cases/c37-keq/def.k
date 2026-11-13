// ==K and =/=K: a value reached through a subsort against the same value written at its own sort,
// values of one sort and of two sorts, maps built in two orders, and maps that differ in one
// value.
module CASE-SYNTAX
  imports INT-SYNTAX
  imports BOOL-SYNTAX
  imports MAP
  syntax Val ::= Int | a(Int) | b(Int)
  syntax S ::= go(Val, Map, Map) | r(Bool, Bool, Bool, Bool, Bool, Bool, Bool)
endmodule
module CASE
  imports CASE-SYNTAX
  imports INT
  imports BOOL
  imports MAP
  imports K-EQUAL
  configuration <k> $PGM:S </k>
  rule <k> go(V, M, N) => r(V ==K 1, V =/=K 1, a(1) ==K b(1), V ==K a(1), M ==K N, M =/=K N, M ==K N[1 <- 5]) </k>
endmodule
