module E2-CLAUSE-RHS-INT
  imports INT
  syntax T ::= c(Int) [symbol(c)]
  syntax T ::= f() [function, symbol(f)]
  rule f() => c(Y:Int) [unboundVariables(Y)]
endmodule
