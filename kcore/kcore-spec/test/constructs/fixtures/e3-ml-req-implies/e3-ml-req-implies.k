module E3-ML-REQ-IMPLIES
  imports INT
  syntax Exp ::= go(Int) [symbol(go)] | "done" [symbol(done)] | "other" [symbol(other)]
  rule <k> go(X) => done ... </k> requires {X #Equals 1} #Implies #Ceil(1 /Int X)
  rule <k> go(_) => other ... </k> [priority(60)]
endmodule
