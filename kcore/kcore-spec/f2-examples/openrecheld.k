module E2-OPEN-REC-HELD
  syntax B ::= "e" [symbol(e)] | B "&" B [comm, symbol(and)]
  syntax KItem ::= c(B, B, B) [symbol(c)] | d(B) [symbol(d)]
  rule <k> c(X & Y, X, Y) => d(X) </k>
endmodule
