module E3-EQ-EXISTS-ARGNAME-ML
  imports BOOL
  syntax Bool ::= p(Bool) [function, symbol(p)]
  rule p(X) => #Exists X:Bool. X
endmodule
