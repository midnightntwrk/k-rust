// As-patterns written with #as: an alias of a Map pattern with a frame, bound to the whole map
// for each entry the pattern takes; an alias in a function's argument whose variable occurs
// earlier in the same left side, so that it matches only a value equal to that occurrence.
module CASE-SYNTAX
  imports INT-SYNTAX
  imports MAP
  syntax Pair ::= pair(Int, Int)
  syntax Int ::= same(Pair) [function]
  syntax S ::= go(Map, Pair, Pair) | r(Int, Int) | got(KItem, Map)
endmodule
module CASE
  imports CASE-SYNTAX
  imports INT
  imports MAP
  configuration <k> $PGM:S </k>
  rule same(pair(Y, X #as Y)) => X
  rule same(_) => 0 [owise]
  rule <k> go((K |-> _ _:Map) #as M, _, _) => got(K, M) </k>
  rule <k> go(_, P, Q) => r(same(P), same(Q)) </k>
endmodule
