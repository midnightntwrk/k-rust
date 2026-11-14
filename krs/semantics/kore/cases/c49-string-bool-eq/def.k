// ==String, <String and ==Bool on String domain values, and a String literal in a left side.
module CASE-SYNTAX
  imports BOOL-SYNTAX
  imports STRING-SYNTAX
  syntax S ::= a(String, String) | b(Bool, Bool, Bool, Bool, Bool, Bool) | c(String)
endmodule
module CASE
  imports CASE-SYNTAX
  imports BOOL
  imports STRING
  configuration <k> $PGM:S </k>
  rule <k> a(X, Y) => b(X ==String Y, X <String Y, Y <String X, (X ==String Y) ==Bool (Y <String X), (X <String Y) ==Bool (Y <String X), X ==String X) </k>
  rule <k> a("ab", Y) => c(Y) </k>
endmodule
