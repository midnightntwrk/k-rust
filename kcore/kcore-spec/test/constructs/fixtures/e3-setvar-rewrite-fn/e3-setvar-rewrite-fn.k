module E3-SETVAR-REWRITE-FN
  syntax Exp ::= a() [symbol(a)] | b() [symbol(b)] | c(Exp, Exp) [symbol(c)] | d(Exp) [symbol(d)]
  syntax Exp ::= g(Exp) [function, symbol(g)]
  rule g(_) => a()
  rule <k> c(@S, @S) => d(g(@S)) ... </k>
endmodule
