module E2-CLAUSE-RHS-STRING
  imports INT
  imports STRING
  syntax T ::= h(String) [symbol(h)]
  syntax T ::= f() [function, symbol(f)]
  rule f() => h(Y:String) [unboundVariables(Y)]
endmodule
