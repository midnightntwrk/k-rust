// A rule whose ensures is not true: where the ensures holds the rule gives its right side; where it
// is false the rule has applied with an empty result, so that configuration has no successor and
// is not final.
module CASE-SYNTAX
  imports INT-SYNTAX
  imports BOOL-SYNTAX
  syntax S ::= "go" | a(Int) | b(Int)
endmodule
module CASE
  imports CASE-SYNTAX
  imports INT
  imports BOOL
  configuration <k> $PGM:S </k>
  rule <k> go => a(1) </k>
  rule <k> go => a(0) </k>
  rule <k> a(I) => b(I) </k> ensures I >Int 0
endmodule
