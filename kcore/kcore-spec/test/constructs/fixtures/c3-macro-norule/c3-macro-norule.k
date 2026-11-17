module C3-MACRO-NORULE
  syntax Exp ::= "x" [symbol(x)] | g(Exp) [symbol(g)] | m(Exp) [macro, symbol(m)]
  syntax Exp ::= f(Exp) [function, symbol(f)]
  rule f(X) => m(X)
endmodule
