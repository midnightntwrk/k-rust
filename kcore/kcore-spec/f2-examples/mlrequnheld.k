module E3-ML-REQ-OR-UNHELD
  imports INT
  syntax Exp ::= go(Int) [symbol(go)] | "done" [symbol(done)]
  rule <k> go(X) => done ... </k> requires X >Int 0 #Or Y:Int >Int 2 [unboundVariables(Y)]
endmodule
