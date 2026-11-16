module E3-EQ-EXISTS-ML-AND-TERMS
  imports INT
  imports BOOL
  syntax Bool ::= f(Bool) [function, symbol(f)]
  rule f(X) => #Exists B:Bool. (B #And (notBool X))
  syntax Int ::= k(Int) [function, symbol(k)]
  rule k(X) => #Exists Z:Int. (Z #And (X +Int 1))
endmodule
