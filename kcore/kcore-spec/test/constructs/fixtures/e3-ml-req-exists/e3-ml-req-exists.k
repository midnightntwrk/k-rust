module E3-ML-REQ-EXISTS
  imports INT
  syntax Exp ::= go(Int) [symbol(go)] | "done" [symbol(done)] | "other" [symbol(other)]
  rule <k> go(X) => done ... </k> requires #Exists Y:Int. {X #Equals Y +Int 1}
  rule <k> go(_) => other ... </k> [priority(60)]
endmodule
