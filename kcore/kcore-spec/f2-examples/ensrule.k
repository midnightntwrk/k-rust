// A rewrite rule with an `ensures`: `assume(B) => ok() ensures B`. Its axiom's right side is
// `ok() ∧ (B = true)`: the rule gives a successor only where B is true. Its left side and
// `requires` are what applies (and so what blocks the rules of a larger priority); the one rule of
// a larger priority, the `[owise]` rule on `other(N)`, matches no configuration it matches. The
// reader reads B as the rule's `ensures` (`Rule.ens`).
module ENSRULE-SYNTAX
  imports INT-SYNTAX
  imports BOOL-SYNTAX
  syntax Cmd ::= assume(Bool) [symbol(assume)] | ok() [symbol(ok)] | other(Int) [symbol(other)]
               | stuck() [symbol(stuck)]
endmodule

module ENSRULE
  imports ENSRULE-SYNTAX
  imports INT
  imports BOOL
  configuration <k> $PGM:Cmd </k>
  rule [assume]: <k> assume(B) => ok() </k> ensures B
  rule [other]: <k> other(_) => stuck() </k> [owise]
endmodule
