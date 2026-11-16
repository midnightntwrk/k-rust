module E3-ML-REQ-AND-OWISE
  imports INT
  imports BOOL
  syntax Int ::= f(Int) [function, symbol(f)]
  syntax Bool ::= g(Int) [function, symbol(g)] | hh(Int) [function, symbol(hh)]
  rule f(X) => 1 requires g(X) #And hh(X)
  rule f(X) => 2 [owise]
  rule g(X) => g(X) requires X >Int 0
  rule hh(X) => true
endmodule
