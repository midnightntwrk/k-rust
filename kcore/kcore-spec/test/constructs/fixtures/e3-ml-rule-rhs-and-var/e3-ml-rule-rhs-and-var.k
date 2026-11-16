module E3-ML-RULE-RHS-AND-VAR
  syntax Exp ::= a() [symbol(a)] | b() [symbol(b)] | c(Exp) [symbol(c)]
  rule <k> c(X) => a() #And X ... </k>
endmodule
