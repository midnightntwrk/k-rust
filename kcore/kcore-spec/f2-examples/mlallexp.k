module E3-ML-RULE-LHS-FORALL-EXP
  syntax Exp ::= a() [symbol(a)] | b() [symbol(b)] | c(Exp) [symbol(c)]
  rule <k> c(#Forall Y:Exp. Y) => a() ... </k>
endmodule
