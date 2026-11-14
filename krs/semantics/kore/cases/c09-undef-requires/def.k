// A requires that is undefined (a division by zero) is not true: the rule does not apply and
// does not block the rule of larger priority.
module CASE-SYNTAX
  imports INT-SYNTAX
  syntax S ::= a(Int) | b(Int) | c(Int)
endmodule
module CASE
  imports CASE-SYNTAX
  imports INT
  configuration <k> $PGM:S </k>
  rule <k> a(X) => b(X) </k> requires 10 /Int X >Int 0 [priority(40)]
  rule <k> a(X) => c(X) </k>
endmodule
