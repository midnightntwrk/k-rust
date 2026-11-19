module E3-ML-RULE-LHS-IMPLIES
  syntax Exp ::= a() [symbol(a)] | b() [symbol(b)] | c(Exp) [symbol(c)] | d(Exp, Exp) [symbol(d)]
  rule <k> c(a() #Implies b()) => b() ... </k>
endmodule
