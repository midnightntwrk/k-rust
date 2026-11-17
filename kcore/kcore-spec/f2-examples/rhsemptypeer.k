module E2-CLAUSE-RHS-EMPTY-PEER
  imports INT
  syntax Empty
  syntax T ::= "a" [symbol(a)]
  syntax T ::= g(Empty) [symbol(g)]
  syntax T ::= f() [function, symbol(f)]
  rule f() => g(Y:Empty) [unboundVariables(Y)]
  rule f() => a
endmodule
