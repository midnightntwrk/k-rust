module E2-OPEN-REC
  syntax B ::= "e" [symbol(e)] | B "&" B [comm, symbol(and)]
  syntax KItem ::= c(B) [symbol(c)] | d(B) [symbol(d)]
  rule <k> c(X & Y) => d(X) </k>
endmodule
