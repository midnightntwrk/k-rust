module E2-OPEN-MIXED
  syntax A ::= "x" [symbol(x)] | "y" [symbol(y)]
  syntax B ::= A "&" A [comm, symbol(and)]
  syntax KItem ::= c(B) [symbol(c)] | d(A) [symbol(d)]
  rule <k> c(X & Y) => d(X) </k>
endmodule
