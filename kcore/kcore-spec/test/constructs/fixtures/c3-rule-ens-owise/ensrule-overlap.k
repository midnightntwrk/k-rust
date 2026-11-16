// A rewrite rule with an `ensures` beside an `[owise]` rule that matches what it matches. At
// `assume(false)` the text's rule applies (its left side and `requires` hold) and gives no
// successor, so it blocks the `[owise]` rule; read with B among its `requires` it would not apply
// there, and the `[owise]` rule would step to `stuck()`. The reader reads B as `Rule.ens`.
module ENSRULE-OVERLAP-SYNTAX
  imports INT-SYNTAX
  imports BOOL-SYNTAX
  syntax Cmd ::= assume(Bool) [symbol(assume)] | ok() [symbol(ok)] | stuck() [symbol(stuck)]
endmodule

module ENSRULE-OVERLAP
  imports ENSRULE-OVERLAP-SYNTAX
  imports INT
  imports BOOL
  configuration <k> $PGM:Cmd </k>
  rule [assume]: <k> assume(B) => ok() </k> ensures B
  rule [other]: <k> _:Cmd => stuck() </k> [owise]
endmodule
