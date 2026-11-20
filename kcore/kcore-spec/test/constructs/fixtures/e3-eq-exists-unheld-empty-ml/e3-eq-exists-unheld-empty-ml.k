// A binder whose variable the body does not hold, of a sort S whose one constructor s takes an S
// (no value), no argument being of the sort S: p(X:Bool) => #Exists Z:S. X.
module E3-EQ-EXISTS-UNHELD-EMPTY-ML
  imports BOOL
  syntax S ::= s(S) [symbol(s)]
  syntax Bool ::= p(Bool) [function, symbol(p)]
  rule p(X) => #Exists Z:S. X
endmodule
