// Function equations of three priorities, an [owise] equation, and requires that fail.
module CASE-SYNTAX
  imports INT-SYNTAX
  syntax S ::= go(Int) | out(Int, Int, Int)
  syntax Int ::= f(Int) [function]
endmodule
module CASE
  imports CASE-SYNTAX
  imports INT
  configuration <k> $PGM:S </k>
  rule f(X) => 1 requires X >Int 10 [priority(60)]
  rule f(X) => 2 requires X >Int 5
  rule f(X) => 3 requires X >Int 0 [priority(40)]
  rule f(_) => 4 [owise]
  rule <k> go(X) => out(f(X), f(X -Int 3), f(0 -Int X)) </k>
endmodule
