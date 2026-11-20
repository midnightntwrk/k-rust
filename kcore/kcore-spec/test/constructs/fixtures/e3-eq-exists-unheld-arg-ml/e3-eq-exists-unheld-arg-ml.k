// A binder whose variable the body does not hold, the argument being of the binder's sort:
// q(X:Int) => #Exists Z:Int. X (e3-eq-exists-unheld-ml's q, at the unconfined sort Int and alone
// in its text).
module E3-EQ-EXISTS-UNHELD-ARG-ML
  imports INT
  syntax Int ::= q(Int) [function, symbol(q)]
  rule q(X) => #Exists Z:Int. X
endmodule
