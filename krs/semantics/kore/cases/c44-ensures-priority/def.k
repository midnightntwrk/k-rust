// A rule whose ensures is false and an overlapping rule of larger priority number: the first rule
// has applied with an empty result, so the second does not apply and a(0) has no successor; where
// the ensures holds the first rule gives b(1).
module CASE-SYNTAX
  imports INT-SYNTAX
  imports BOOL-SYNTAX
  syntax S ::= "go" | a(Int) | b(Int) | c(Int)
endmodule
module CASE
  imports CASE-SYNTAX
  imports INT
  imports BOOL
  configuration <k> $PGM:S </k>
  rule <k> go => a(1) </k>
  rule <k> go => a(0) </k>
  rule <k> a(I) => b(I) </k> ensures I >Int 0
  rule <k> a(I) => c(I) </k> [priority(60)]
endmodule
