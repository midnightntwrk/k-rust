module E3-ML
  imports INT
  syntax Int ::= f(Int) [function, symbol(f)] | g(Int) [function, symbol(g)] | h(Int) [function, symbol(h)]
  rule f(X) => X
  rule g(X) => X
  rule #Ceil(f(X)) => #Top [simplification]
  rule #Ceil(g(X)) => #Not(#Bottom) [simplification]
  rule {f(X) #Equals g(X)} => #Top [simplification]
  rule h(X) => f(X) #And g(X) [simplification]
  rule h(X) => f(X) #Or g(X) [simplification(60)]
  rule #Ceil(g(X)) => #Ceil(f(X)) #Implies #Top [simplification(70)]
  rule #Ceil(h(X)) => #Exists Y. {f(X) #Equals Y} [simplification]
  rule #Ceil(h(X)) => #Floor(#Forall Y. {f(Y) #Equals g(Y)}) [simplification(60)]
endmodule
