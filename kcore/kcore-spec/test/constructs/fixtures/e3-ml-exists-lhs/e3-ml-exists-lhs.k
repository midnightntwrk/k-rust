module E3-ML-EXISTS-LHS
  imports INT
  syntax Int ::= f(Int) [function, symbol(f)]
  rule f(X) => X
  rule #Exists Y. {f(X) #Equals Y} => #Top [simplification]
endmodule
