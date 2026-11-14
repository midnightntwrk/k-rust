// An equation of priority 60 whose requires is undefined: where the equation of priority 40 applies it gives the value; elsewhere the undefined requires does not hold and the [owise] equation applies.
module CASE-SYNTAX
  imports INT-SYNTAX
  syntax S ::= a(Int, Int) | b(Int, Int)
  syntax Int ::= g(Int) [function]
endmodule
module CASE
  imports CASE-SYNTAX
  imports INT
  configuration <k> $PGM:S </k>
  rule g(X) => 1 requires X >Int 0 [priority(40)]
  rule g(X) => 2 requires X /Int 0 ==Int 0 [priority(60)]
  rule g(_) => 3 [owise]
  rule <k> a(X, Y) => b(g(X), g(Y)) </k>
endmodule
