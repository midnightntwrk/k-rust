module T124-RULE-LHS-TOP
  syntax Exp ::= a() [symbol(a)] | b() [symbol(b)] | c(Exp) [symbol(c)] | d(Exp, Exp) [symbol(d)]
  rule <k> c(#Top) => a() ... </k>
endmodule
