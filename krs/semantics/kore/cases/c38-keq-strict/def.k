// ==K with an undefined operand: _==K_ is a function of its two arguments, so the application is
// undefined and the rule that builds it has no successor; the rule of the same priority gives
// the final configuration.
module CASE-SYNTAX
  imports INT-SYNTAX
  imports BOOL-SYNTAX
  syntax S ::= go(Int) | r(Bool) | ok(Int)
endmodule
module CASE
  imports CASE-SYNTAX
  imports INT
  imports BOOL
  imports K-EQUAL
  configuration <k> $PGM:S </k>
  rule <k> go(I) => r(10 /Int I ==K 1) </k>
  rule <k> go(I) => ok(I) </k>
endmodule
