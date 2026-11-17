module C3-MACRO-RULE-EXPANDED
  syntax Exp ::= "x" [symbol(x)] | g(Exp) [symbol(g)] | m(Exp) [macro, symbol(m)]
  syntax Exp ::= f(Exp) [function, symbol(f)]
  rule m(X) => g(X)
  rule f(X) => g(X)
endmodule
