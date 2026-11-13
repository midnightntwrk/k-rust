// A function's argument is evaluated before its equations are matched: f(g(1)) matches f(kk()).
module CASE-SYNTAX
  imports INT-SYNTAX
  syntax K2 ::= kk() | mm()
  syntax K2 ::= g(Int) [function]
  syntax Int ::= f(K2) [function]
  syntax S ::= go(Int) | res(Int)
endmodule
module CASE
  imports CASE-SYNTAX
  imports INT
  configuration <k> $PGM:S </k>
  rule g(1) => kk()
  rule g(_) => mm() [owise]
  rule f(kk()) => 10
  rule f(mm()) => 20
  rule <k> go(X) => res(f(g(X)) +Int f(g(X +Int 1))) </k>
endmodule
