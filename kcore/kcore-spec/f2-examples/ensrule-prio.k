// A rewrite rule with a `requires` and an `ensures`, `assume(B, C) => ok() requires C ensures B`, of
// priority 50, beside a rule of priority 60 on every `assume(_, _)`. Its axiom's left side is
// `lhs ∧ (C = true)` and its right side `ok() ∧ (B = true)`: where C holds the rule applies, so the
// rule of priority 60 does not, and where B is not true it has no successor. Where C does not hold
// it does not apply, and the rule of priority 60 steps to `stuck()`.
module ENSRULE-PRIO-SYNTAX
  imports INT-SYNTAX
  imports BOOL-SYNTAX
  syntax Cmd ::= assume(Bool, Bool) [symbol(assume)] | ok() [symbol(ok)] | stuck() [symbol(stuck)]
endmodule

module ENSRULE-PRIO
  imports ENSRULE-PRIO-SYNTAX
  imports INT
  imports BOOL
  configuration <k> $PGM:Cmd </k>
  rule [assume]: <k> assume(B, C) => ok() </k> requires C ensures B [priority(50)]
  rule [fallback]: <k> assume(_, _) => stuck() </k> [priority(60)]
endmodule
