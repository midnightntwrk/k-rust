module E3-ML-REQ-AND-VAR
  imports BOOL
  syntax Exp ::= go(Bool) [symbol(go)] | "done" [symbol(done)]
  rule <k> go(B) => done ... </k> requires true #And B
endmodule
