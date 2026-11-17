module T18-AS-PATTERN
  imports INT
  syntax Exp ::= a(Int) [symbol(a)] | b(Exp) [symbol(b)]
  syntax Exp ::= f(Exp) [function, symbol(f)]
  rule f(a(_) #as E) => b(E)
  rule f(_) => a(0) [owise]
endmodule
