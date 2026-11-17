module E3-EQ-EXISTS-UNHELD-ML
  imports INT
  imports BOOL
  syntax Bool ::= p(Bool) [function, symbol(p)] | q(Bool) [function, symbol(q)]
  rule p(X) => #Exists Z:Int. X
  rule q(X) => #Exists Z:Bool. X
endmodule
