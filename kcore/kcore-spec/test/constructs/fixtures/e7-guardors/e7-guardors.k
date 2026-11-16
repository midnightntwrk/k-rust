module E7-GUARDORS
  syntax Exp ::= a() [symbol(a)] | b() [symbol(b)] | c(Exp) [symbol(c)]
  rule <k> c(a() #Or b()) => a() ... </k>
endmodule
