module E3-ML-REQ-NOT-PRED
  imports INT
  syntax Exp ::= go(Int) [symbol(go)] | "done" [symbol(done)] | "other" [symbol(other)]
  rule <k> go(X) => done ... </k> requires #Not({X #Equals 0})
  rule <k> go(_) => other ... </k> [priority(60)]
endmodule
