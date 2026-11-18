module E3-ML-EQ-RHS-OR-NEST
  imports INT
  imports BOOL
  syntax Int ::= f(Int) [function, total, symbol(f)] | g(Int) [function, total, symbol(g)] | k(Int) [function, total, symbol(k)] | h(Int) [function, total, symbol(h)]
  rule f(X) => X
  rule g(X) => X +Int 0
  rule k(X) => X +Int 1
  rule h(X) => (k(f(X) #Or g(X)) #Or #Bottom) #And {X *Int X >=Int 0 #Equals true}
endmodule
