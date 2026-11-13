// An equation whose requires is undefined (a division by zero) does not apply: the [owise]
// equation gives the value.
module CASE-SYNTAX
  imports INT-SYNTAX
  syntax S ::= go(Int) | res(Int)
  syntax Int ::= f(Int) [function]
endmodule
module CASE
  imports CASE-SYNTAX
  imports INT
  configuration <k> $PGM:S </k>
  rule f(X) => 1 requires 10 /Int X >Int 0
  rule f(_) => 2 [owise]
  rule <k> go(X) => res(f(X)) </k>
endmodule
