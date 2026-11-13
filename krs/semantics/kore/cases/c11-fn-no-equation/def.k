// A function application that no equation applies to stays in the configuration.
module CASE-SYNTAX
  imports INT-SYNTAX
  syntax S ::= a(Int) | b(Int)
  syntax Int ::= half(Int) [function]
endmodule
module CASE
  imports CASE-SYNTAX
  imports INT
  configuration <k> $PGM:S </k>
  rule half(X) => X /Int 2 requires X %Int 2 ==Int 0
  rule <k> a(X) => b(half(X)) </k>
endmodule
