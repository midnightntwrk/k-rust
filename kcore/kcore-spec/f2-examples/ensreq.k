// A function equation's `ensures` that fails, reached through a rule's `requires`:
// `f(X) => 1 ensures X >Int 0`, and `<k> a => b </k> requires f(0) ==Int 7`. The text's equation is
// `f(X) = 1 ∧ (X >Int 0 = true)`: at 0 the equation applies and its right side is empty, so f(0)
// has no value, `f(0) ==Int 7` has none, and the rule's axiom states nothing for `a`.
module ENSREQ-SYNTAX
  imports INT-SYNTAX
  syntax Int ::= f(Int) [function, symbol(f)]
  syntax Cmd ::= "a" [symbol(a)] | "b" [symbol(b)]
endmodule

module ENSREQ
  imports ENSREQ-SYNTAX
  imports INT
  imports BOOL
  configuration <k> $PGM:Cmd </k>
  rule f(X) => 1 ensures X >Int 0
  rule [go]: <k> a => b </k> requires f(0) ==Int 7
endmodule
