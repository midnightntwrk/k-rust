// A function declared total used in a requires: its equation gives its value, and the rule applies
// where that value is true; the [owise] rule applies where it is false.
module CASE-SYNTAX
  imports INT-SYNTAX
  imports BOOL-SYNTAX
  syntax Bool ::= small(Int) [function, total]
  syntax S ::= two(Int, Int) | go(Int) | yes(Int) | no(Int)
endmodule
module CASE
  imports CASE-SYNTAX
  imports INT
  imports BOOL
  configuration <k> $PGM:S </k>
  rule small(I) => I <Int 10
  rule <k> two(A, _) => go(A) </k>
  rule <k> two(_, B) => go(B) </k>
  rule <k> go(I) => yes(I) </k> requires small(I)
  rule <k> go(I) => no(I) </k> [owise]
endmodule
