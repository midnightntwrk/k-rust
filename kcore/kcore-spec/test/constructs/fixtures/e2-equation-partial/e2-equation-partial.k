module E2-EQUATION-PARTIAL
  imports INT
  syntax Int ::= p(Int, Int) [function, symbol(p)]
  rule p(X, Y) => X +Int Y [concrete(X), symbolic(Y)]
endmodule
