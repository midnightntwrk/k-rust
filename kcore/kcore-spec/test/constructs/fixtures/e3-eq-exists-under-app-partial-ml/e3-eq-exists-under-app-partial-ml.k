// A binder under an application on an equation's right side, of a function that is not total:
// f(X) => g(#Exists B:Bool. (B #And {B #Equals X})), g total, g(B) => notBool B (the text of
// e3-eq-exists-ml-under-app with f not total).
module E3-EQ-EXISTS-UNDER-APP-PARTIAL-ML
  imports BOOL
  syntax Bool ::= f(Bool) [function, symbol(f)] | g(Bool) [function, total, symbol(g)]
  rule f(X) => g(#Exists B:Bool. (B #And {B #Equals X}))
  rule g(B) => notBool B
endmodule
