module E3-ML-EQ-REQ-NOT
  imports INT
  syntax Exp ::= go(Int) [symbol(go)] | "done" [symbol(done)]
  syntax Int ::= f(Int) [function, total, symbol(f)]
  rule f(X) => 1 requires #Not(X >Int 0)
  rule f(_) => 0 [owise]
  rule <k> go(X) => done ... </k> requires f(X) ==Int 1
endmodule
