module E3-ML-RULE-LHS-BOTTOM
  syntax Exp ::= a() [symbol(a)] | b() [symbol(b)] | c(Exp) [symbol(c)] | d(Exp, Exp) [symbol(d)]
  rule <k> c(#Bottom) => a() ... </k>
endmodule
