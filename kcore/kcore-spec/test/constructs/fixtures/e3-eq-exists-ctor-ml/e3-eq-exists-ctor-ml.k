module E3-EQ-EXISTS-CTOR-ML
  imports K-EQUAL
  imports BOOL
  syntax Col ::= "r" [symbol(r)] | "g" [symbol(g)]
  syntax Col ::= pick(Col) [function, symbol(pick)]
  rule pick(X) => #Exists C:Col. (C #And {(C =/=K X) #Equals true})
endmodule
