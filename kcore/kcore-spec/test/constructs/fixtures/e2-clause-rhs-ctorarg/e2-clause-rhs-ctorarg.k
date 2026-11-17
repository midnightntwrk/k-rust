module E2-CLAUSE-RHS-CTORARG
  imports INT
  syntax W ::= w(Int) [symbol(w)]
  syntax T ::= h(W) [symbol(h)]
  syntax T ::= f() [function, symbol(f)]
  rule f() => h(Y:W) [unboundVariables(Y)]
endmodule
