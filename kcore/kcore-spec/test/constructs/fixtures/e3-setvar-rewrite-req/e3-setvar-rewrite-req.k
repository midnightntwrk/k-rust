module E3-SETVAR-REWRITE-REQ
  imports BOOL
  syntax Exp ::= a() [symbol(a)] | b() [symbol(b)] | c(Exp) [symbol(c)] | d() [symbol(d)]
  syntax Bool ::= p(Exp) [function, symbol(p)]
  rule p(b()) => true
  rule <k> c(@S) => d() ... </k> requires p(@S)
endmodule
