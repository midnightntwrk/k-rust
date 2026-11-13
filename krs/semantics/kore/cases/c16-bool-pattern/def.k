// A Bool domain value in a left side matches only itself.
module CASE-SYNTAX
  imports BOOL-SYNTAX
  syntax S ::= b(Bool) | "yes"
endmodule
module CASE
  imports CASE-SYNTAX
  imports BOOL
  configuration <k> $PGM:S </k>
  rule <k> b(true) => yes </k>
endmodule
