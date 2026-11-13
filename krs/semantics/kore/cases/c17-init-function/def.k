// The initial term applies a function: it is evaluated before the first step.
module CASE-SYNTAX
  imports INT-SYNTAX
  syntax S ::= a(Int) | "yes" | "no"
  syntax Int ::= inc(Int) [function]
endmodule
module CASE
  imports CASE-SYNTAX
  imports INT
  configuration <k> $PGM:S </k>
  rule inc(X) => X +Int 1
  rule <k> a(2) => yes </k>
  rule <k> a(_) => no </k> [owise]
endmodule
