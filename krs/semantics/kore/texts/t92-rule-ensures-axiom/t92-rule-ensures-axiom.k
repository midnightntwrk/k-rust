// A rewrite rule with a requires and an ensures clause: where the two conditions stand in the
// axiom of the rule.
module T92-RULE-ENSURES-AXIOM
  imports INT
  syntax Exp ::= a(Int) | b(Int)
  rule <k> a(X) => b(X -Int 1) ... </k> requires X >=Int 0 ensures X >Int 0
endmodule
