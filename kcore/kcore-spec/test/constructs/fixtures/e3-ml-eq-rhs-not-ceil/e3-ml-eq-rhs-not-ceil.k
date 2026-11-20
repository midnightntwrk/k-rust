module E3-ML-EQ-RHS-NOT-CEIL
  imports INT
  syntax Int ::= f(Int) [function, symbol(f)] | h(Int) [function, symbol(h)]
  rule f(X) => X requires X >Int 0
  rule h(X) => X #And #Not(#Ceil(f(X)))
endmodule
