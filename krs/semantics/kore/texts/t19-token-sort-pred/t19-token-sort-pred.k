module T19-TOKEN-SORT-PRED
  imports BOOL
  syntax Id ::= r"[a-z]+" [token]
  syntax Exp ::= Id | n(Exp) [symbol(n)]
endmodule
