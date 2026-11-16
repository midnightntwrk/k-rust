module E3-ML-ENS-AND-EQ
  imports INT
  imports BOOL
  syntax Int ::= f(Int) [function, symbol(f)]
  syntax Bool ::= g(Int) [function, symbol(g)] | hh(Int) [function, symbol(hh)]
  rule f(X) => 1 ensures g(X) #And hh(X)
  rule g(X) => g(X) requires X >Int 0
  rule hh(X) => true
endmodule
