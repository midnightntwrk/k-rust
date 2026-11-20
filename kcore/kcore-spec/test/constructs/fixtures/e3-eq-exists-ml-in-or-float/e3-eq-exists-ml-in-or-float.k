module E3-EQ-EXISTS-ML-IN-OR-FLOAT
  imports FLOAT
  syntax Float ::= f(Float) [function, symbol(f)]
  rule f(X) => X #Or (#Exists B:Float. (B #And {B #Equals X +Float 1.0}))
endmodule
