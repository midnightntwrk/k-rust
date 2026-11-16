module E2-OPEN-MIXED-CLAUSE
  syntax A ::= "x" [symbol(x)] | "y" [symbol(y)]
  syntax B ::= A "&" A [comm, symbol(and)]
  syntax A ::= first(B) [function, symbol(first)]
  rule first(X & _) => X
endmodule
