module T10-FN-INNERMOST
  imports INT
  syntax Int ::= dbl(Int) [function, symbol(dbl)]
               | pred(Int) [function, symbol(pred)]
  syntax Exp ::= p(Int) [symbol(p)]
  rule dbl(X) => X +Int X
  rule pred(X) => X -Int 1 requires X >Int 0
  rule pred(X) => #Bottom requires X <=Int 0
endmodule
