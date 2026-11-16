// f2-examples/ensrule-overlap.k without the `[owise]` of its second rule: a rewrite rule with an
// `ensures` beside a plain rule that matches what it matches.
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
  rule [other]: <k> _:Cmd => stuck() </k>
endmodule
