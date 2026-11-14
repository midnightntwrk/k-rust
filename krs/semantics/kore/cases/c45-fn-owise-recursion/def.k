// A recursive function with an [owise] equation: the [owise] right side is evaluated only where no equation of smaller priority applies, so f(2) reaches f(0) and stops.
module CASE-SYNTAX
  imports INT-SYNTAX
  syntax S ::= a(Int) | b(Int)
  syntax Int ::= f(Int) [function]
endmodule
module CASE
  imports CASE-SYNTAX
  imports INT
  configuration <k> $PGM:S </k>
  rule f(0) => 0
  rule f(N) => f(N -Int 1) [owise]
  rule <k> a(X) => b(f(X)) </k>
endmodule
