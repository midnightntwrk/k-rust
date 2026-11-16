module E3-EQ-EXISTS-NOENS-ML
  imports BOOL
  syntax Bool ::= f(Bool) [function, symbol(f)]
  rule f(_) => #Exists B:Bool. B
endmodule
