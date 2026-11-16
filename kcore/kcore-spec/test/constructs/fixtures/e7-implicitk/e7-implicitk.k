module E7-IMPLICITK
  syntax Exp ::= a() [symbol(a)] | b() [symbol(b)]
  rule a() => b()
endmodule
