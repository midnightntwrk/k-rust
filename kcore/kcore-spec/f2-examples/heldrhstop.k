module E3-ML-RULE-RHS-TOP
  syntax Exp ::= a() [symbol(a)] | b() [symbol(b)] | c(Exp) [symbol(c)] | d(Exp, Exp) [symbol(d)]
  syntax Exp ::= "go" [symbol(go)]
  rule <k> go => #Top ... </k>
endmodule
