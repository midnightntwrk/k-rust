module E3-ML-RULE-RHS-OR
  syntax Exp ::= a() [symbol(a)] | b() [symbol(b)] | c(Exp) [symbol(c)] | d(Exp, Exp) [symbol(d)]
  syntax Exp ::= "go" [symbol(go)]
  rule <k> go => a() #Or b() ... </k>
endmodule
