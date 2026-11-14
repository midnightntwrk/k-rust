// Two rules of one priority apply, one with an undefined right side: the other's successor is kept.
module CASE-SYNTAX
  imports INT-SYNTAX
  syntax S ::= a(Int) | b(Int) | c(Int)
endmodule
module CASE
  imports CASE-SYNTAX
  imports INT
  configuration <k> $PGM:S </k>
  rule <k> a(X) => b(X /Int 0) </k>
  rule <k> a(X) => c(X) </k>
endmodule
