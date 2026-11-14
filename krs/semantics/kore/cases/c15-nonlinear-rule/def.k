// A variable seen twice in a rule's left side: the rule does not apply to distinct values.
module CASE-SYNTAX
  imports INT-SYNTAX
  syntax S ::= two(Int, Int) | "same" | "diff"
endmodule
module CASE
  imports CASE-SYNTAX
  imports INT
  configuration <k> $PGM:S </k>
  rule <k> two(X, X) => same </k>
  rule <k> two(_, _) => diff </k> [priority(60)]
endmodule
