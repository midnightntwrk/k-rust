// A function declared total that no equation applies to, used in a requires: the definition
// states that even(3) has a value but not which; kore.k keeps the application, which is not
// true, so the rule does not apply and the [owise] rule does.
module CASE-SYNTAX
  imports INT-SYNTAX
  imports BOOL-SYNTAX
  syntax Bool ::= even(Int) [function, total]
  syntax S ::= go(Int) | yes(Int) | no(Int)
endmodule
module CASE
  imports CASE-SYNTAX
  imports INT
  imports BOOL
  configuration <k> $PGM:S </k>
  rule even(I) => true requires I %Int 2 ==Int 0
  rule <k> go(I) => yes(I) </k> requires even(I)
  rule <k> go(I) => no(I) </k> [owise]
endmodule
