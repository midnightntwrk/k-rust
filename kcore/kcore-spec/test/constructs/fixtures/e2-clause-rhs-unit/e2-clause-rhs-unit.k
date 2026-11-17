module E2-CLAUSE-RHS-UNIT
  imports INT
  syntax U ::= "u" [symbol(u)]
  syntax T ::= h(U) [symbol(h)]
  syntax T ::= f() [function, symbol(f)]
  rule f() => h(Y:U) [unboundVariables(Y)]
endmodule
