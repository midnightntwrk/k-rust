// A variable seen twice in a left side: the equation and the rule apply only to equal values.
module CASE-SYNTAX
  imports INT-SYNTAX
  syntax S ::= two(Int, Int) | "same"
  syntax Int ::= eq(Int, Int) [function]
endmodule
module CASE
  imports CASE-SYNTAX
  imports INT
  configuration <k> $PGM:S </k>
  rule eq(X, X) => 1
  rule eq(_, _) => 0 [owise]
  rule <k> two(X, X) => same </k>
  rule <k> two(X, Y) => two(X, Y +Int 1 +Int eq(Y, 1) +Int eq(Y, 2)) </k> [priority(60)]
endmodule
