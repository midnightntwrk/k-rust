module E3-EQ-EXISTS-ML-SUPERSORT
  imports INT
  imports BOOL
  syntax KItem ::= f(Int) [function, symbol(f)]
  rule f(X) => #Exists B:Bool. (B #And {B #Equals (X >Int 0)})
  syntax Int ::= h(KItem) [function, symbol(h)]
  rule h(K) => #Exists Z:Int. (Z #And {Z #Equals K})
endmodule
