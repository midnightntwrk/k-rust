module E3-ML-REQ-AND-UNDER
  imports BOOL
  syntax Exp ::= go(Bool) [symbol(go)] | "done" [symbol(done)]
  syntax Bool ::= f(Bool) [function, symbol(f)]
  rule f(B) => B
  rule <k> go(B) => done ... </k> requires f(true #And B)
endmodule
