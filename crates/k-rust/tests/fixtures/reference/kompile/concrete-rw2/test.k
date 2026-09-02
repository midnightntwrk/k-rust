module CONCRETE-RW2
  imports INT
  syntax KItem ::= foo(Int) [symbol(foo)] | bar(Int) [symbol(bar)]
  rule <k> foo(X) => bar(X) ... </k> [concrete(X)]
  rule <k> bar(X) => foo(X) ... </k> [symbolic(X)]
  syntax Int ::= f(Int) [function, symbol(f)]
  rule f(X) => X +Int 1 [simplification, concrete(X)]
  configuration <k> $PGM:KItem </k>
endmodule
