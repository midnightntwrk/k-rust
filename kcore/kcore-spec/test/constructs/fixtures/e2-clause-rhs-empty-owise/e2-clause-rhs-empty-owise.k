module E2-CLAUSE-RHS-EMPTY-OWISE
  imports INT
  syntax Empty
  syntax T ::= "a" [symbol(a)]
  syntax T ::= g(Empty) [symbol(g)]
  syntax T ::= f(Int) [function, symbol(f)]
  rule f(0) => g(Y:Empty) [unboundVariables(Y)]
  rule f(_) => a [owise]
endmodule
