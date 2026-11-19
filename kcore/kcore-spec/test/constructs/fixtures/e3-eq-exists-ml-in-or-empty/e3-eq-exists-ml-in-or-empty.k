// A binder in an alternative of an \or, of a sort S whose one constructor s takes an S (no value):
// fl() => true #Or (#Exists B:S. (k(B) #And {B #Equals lp()})), k and lp functions with no equation.
module E3-EQ-EXISTS-ML-IN-OR-EMPTY
  imports BOOL
  syntax S ::= s(S) [symbol(s)]
             | lp() [function, symbol(lp)]
  syntax Bool ::= k(S) [function, symbol(k)]
                | fl() [function, symbol(fl)]
  rule fl() => true #Or (#Exists B:S. (k(B) #And {B #Equals lp()}))
endmodule
