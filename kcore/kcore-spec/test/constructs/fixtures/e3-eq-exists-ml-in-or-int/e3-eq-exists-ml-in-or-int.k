module E3-EQ-EXISTS-ML-IN-OR-INT
  imports INT
  syntax Int ::= f(Int) [function, symbol(f)]
  rule f(X) => X #Or (#Exists B:Int. (B #And {B #Equals X +Int 1}))
endmodule
