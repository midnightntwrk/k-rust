module C3-MACRO-RULE-NOMACRO
  syntax Exp ::= "x" [symbol(x)] | g(Exp) [symbol(g)] | m(Exp) [symbol(m)]
  syntax Exp ::= f(Exp) [function, symbol(f)]
  rule m(X) => g(X)
  rule f(X) => m(X)
endmodule
