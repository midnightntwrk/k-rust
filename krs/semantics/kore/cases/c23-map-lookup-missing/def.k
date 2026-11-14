// A lookup of a missing key is undefined: the rule that builds a(M[5]) has no successor, and
// the rule of the same priority that looks up a present key gives the one final configuration.
module CASE-SYNTAX
  imports INT-SYNTAX
  imports MAP
  syntax S ::= go(Map) | a(KItem) | b(KItem)
endmodule
module CASE
  imports CASE-SYNTAX
  imports INT
  imports MAP
  configuration <k> $PGM:S </k>
  rule <k> go(M) => a(M[5]) </k>
  rule <k> go(M) => b(M[1]) </k>
endmodule
