module E3-ML-RULE-LHS-EXISTS
  syntax Exp ::= a() [symbol(a)] | b() [symbol(b)] | c(Exp) [symbol(c)] | d(Exp, Exp) [symbol(d)]
  rule <k> c(#Exists Y:Exp. d(Y, b())) => a() ... </k>
endmodule
