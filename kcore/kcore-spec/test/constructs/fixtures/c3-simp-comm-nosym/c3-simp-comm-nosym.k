module C3-SIMP-COMM-NOSYM
  imports INT
  syntax Int ::= g(Int, Int) [function, total, symbol(g)]
  rule g(X, Y) => X +Int Y
  rule g(X, 0) => X [simplification, comm]
endmodule
