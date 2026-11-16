module E3-EQ-EXISTS-INT-ML
  imports INT
  imports BOOL
  syntax Int ::= h(Int) [function, symbol(h)]
  rule h(X) => #Exists Z:Int. (Z #And {(Z *Int 2 ==Int X) #Equals true})
endmodule
