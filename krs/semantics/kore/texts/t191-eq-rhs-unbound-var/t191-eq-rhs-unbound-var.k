// A function equation whose right side holds a variable no argument binds, allowed by
// unboundVariables, under a constructor.
module T191-EQ-RHS-UNBOUND-VAR
  imports INT
  syntax T ::= c(Int) [symbol(c)]
  syntax T ::= f() [function, symbol(f)]
  rule f() => c(Y:Int) [unboundVariables(Y)]
endmodule
