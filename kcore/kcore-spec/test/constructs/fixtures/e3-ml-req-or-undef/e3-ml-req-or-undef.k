module E3-ML-REQ-OR-UNDEF
  imports INT
  syntax Exp ::= go(Int) [symbol(go)] | "done" [symbol(done)]
  rule <k> go(X) => done ... </k> requires X >=Int 0 #Or 10 /Int X >Int 0
endmodule
