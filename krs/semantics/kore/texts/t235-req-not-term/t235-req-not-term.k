module T235-REQ-NOT-TERM
  imports INT
  syntax Exp ::= go(Int) [symbol(go)] | "done" [symbol(done)] | "other" [symbol(other)]
  rule <k> go(X) => done ... </k> requires #Not(X >Int 0)
endmodule
