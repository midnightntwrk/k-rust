module E2-CLAUSE-RHS-KITEM
  imports INT
  syntax T ::= h(KItem) [symbol(h)]
  syntax T ::= f() [function, symbol(f)]
  rule f() => h(Y:KItem) [unboundVariables(Y)]
endmodule
