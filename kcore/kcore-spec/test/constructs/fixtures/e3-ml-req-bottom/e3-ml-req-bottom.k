module E3-ML-REQ-BOTTOM
  imports INT
  syntax Exp ::= go(Int) [symbol(go)] | "done" [symbol(done)] | "other" [symbol(other)]
  rule <k> go(_) => done ... </k> requires #Bottom
  rule <k> go(_) => other ... </k> [priority(60)]
endmodule
