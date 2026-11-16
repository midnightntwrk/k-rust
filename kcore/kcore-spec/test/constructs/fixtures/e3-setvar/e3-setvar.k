module E3-SETVAR
  imports INT
  syntax Int ::= f(Int) [function, symbol(f)]
  rule f(X) => X
  rule f(@S) => @S [simplification]
endmodule
