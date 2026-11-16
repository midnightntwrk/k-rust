module E3-ML-RULE-RHS-FORALL
  imports INT
  syntax Exp ::= go(Int) [symbol(go)] | "done" [symbol(done)] | "other" [symbol(other)]
  rule <k> go(_) => go(#Forall Y:Int. Y) ... </k>
endmodule
