module E2-COMM-EQ
  imports INT
  syntax Int ::= g(Int, Int) [function, comm, symbol(g)]
  rule g(X, Y) => X +Int Y [comm]
endmodule
