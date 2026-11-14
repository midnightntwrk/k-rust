// A rule of priority 50 applies; the rule of priority 60 beside it, whose requires has no value (its evaluation does not terminate), is not tried.
module CASE-SYNTAX
  imports INT-SYNTAX
  imports BOOL-SYNTAX
  syntax S ::= a(Int) | b(Int) | c(Int)
  syntax Bool ::= loop(Int) [function]
endmodule
module CASE
  imports CASE-SYNTAX
  imports INT
  imports BOOL
  configuration <k> $PGM:S </k>
  rule loop(X) => loop(X +Int 1)
  rule <k> a(X) => b(X) </k> [priority(50)]
  rule <k> a(X) => c(X) </k> requires loop(X) [priority(60)]
endmodule
