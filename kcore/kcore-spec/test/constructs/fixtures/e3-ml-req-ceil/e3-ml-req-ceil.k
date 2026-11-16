module E3-ML-REQ-CEIL
  imports INT
  syntax Exp ::= go(Int) [symbol(go)] | "done" [symbol(done)] | "other" [symbol(other)]
  rule <k> go(X) => done ... </k> requires #Ceil(1 /Int X)
  rule <k> go(_) => other ... </k> [priority(60)]
endmodule
