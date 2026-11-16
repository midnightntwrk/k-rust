module E3-ML-RULE-RHS-BOTTOM
  imports INT
  syntax Exp ::= go(Int) [symbol(go)] | "done" [symbol(done)] | "other" [symbol(other)]
  rule <k> go(_) => #Bottom ... </k>
  rule <k> go(_) => done ... </k> [priority(60)]
endmodule
