module E3-ML-REQ-FLOOR
  imports INT
  syntax Exp ::= go(Int) [symbol(go)] | "done" [symbol(done)] | "other" [symbol(other)]
  rule <k> go(X) => done ... </k> requires #Floor(#Ceil(1 /Int X):Bool)
  rule <k> go(_) => other ... </k> [priority(60)]
endmodule
