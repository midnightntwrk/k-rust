module E2-CLAUSE-RHS-EMPTY
  imports INT
  syntax Empty
  syntax T ::= g(Empty) [symbol(g)]
  syntax T ::= f() [function, symbol(f)]
  rule f() => g(Y:Empty) [unboundVariables(Y)]
endmodule
