module E3-SETVAR-READ
  syntax Exp ::= a() [symbol(a)] | b() [symbol(b)] | c(Exp) [symbol(c)] | d(Exp, Exp) [symbol(d)]
  syntax Exp ::= w(Exp) [function, symbol(w)]
  rule w(@S:Exp) => @S
endmodule
