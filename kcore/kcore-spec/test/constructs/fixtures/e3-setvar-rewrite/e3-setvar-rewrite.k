module E3-SETVAR-REWRITE
  syntax Exp ::= a() [symbol(a)] | b() [symbol(b)] | c(Exp, Exp) [symbol(c)] | d(Exp) [symbol(d)]
  rule <k> c(@S, @S) => d(@S) ... </k>
endmodule
