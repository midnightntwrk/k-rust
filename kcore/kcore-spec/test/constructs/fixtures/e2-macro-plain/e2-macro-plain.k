module E2-MACRO-PLAIN
  syntax Exp ::= "x" [symbol(x)] | g(Exp) [symbol(g)]
               | m1(Exp) [macro, symbol(m1)]
               | m2(Exp) [macro-rec, symbol(m2)]
               | a1(Exp) [alias, symbol(a1)]
               | a2(Exp) [alias-rec, symbol(a2)]
  syntax Exp ::= f(Exp) [function, symbol(f)]
  rule m1(X) => g(X)
  rule m2(X) => g(X)
  rule a1(X) => g(X)
  rule a2(X) => g(X)
  rule f(X) => m1(m2(a1(a2(X))))
endmodule
