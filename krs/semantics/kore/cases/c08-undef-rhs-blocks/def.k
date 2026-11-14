// A rule that applies with an undefined right side (a division by zero) has no successor, and
// it blocks the rule of larger priority: the configuration has no successor and is not final.
module CASE-SYNTAX
  imports INT-SYNTAX
  syntax S ::= a(Int) | b(Int) | c(Int)
endmodule
module CASE
  imports CASE-SYNTAX
  imports INT
  configuration <k> $PGM:S </k>
  rule <k> a(X) => b(10 /Int X) </k> [priority(40)]
  rule <k> a(X) => c(X) </k>
endmodule
