module TEST
  imports INT
  imports BOOL
  syntax Exp ::= Int
  syntax A ::= Exp
  syntax B ::= Exp
  syntax {S} S ::= wrap(S) [function]
  syntax Top ::= f(A) | f(B)
  syntax Top ::= g(Int) [function]
  rule g(I) => f(wrap(I))
endmodule
