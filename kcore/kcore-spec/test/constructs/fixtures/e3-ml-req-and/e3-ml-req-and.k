module E3-ML-REQ-AND
  imports INT
  syntax Exp ::= go(Int) [symbol(go)] | "done" [symbol(done)] | "other" [symbol(other)]
  rule <k> go(X) => done ... </k> requires X >Int 0 #And X <Int 5
endmodule
