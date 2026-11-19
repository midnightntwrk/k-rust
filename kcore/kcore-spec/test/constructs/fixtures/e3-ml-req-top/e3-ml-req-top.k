module E3-ML-REQ-TOP
  imports INT
  syntax Exp ::= go(Int) [symbol(go)] | "done" [symbol(done)] | "other" [symbol(other)]
  rule <k> go(_) => done ... </k> requires #Top
  rule <k> go(_) => other ... </k> [priority(60)]
endmodule
