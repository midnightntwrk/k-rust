module E3-ML-RULE-LHS-FORALL
  imports INT
  syntax Exp ::= go(Int) [symbol(go)] | "done" [symbol(done)] | "other" [symbol(other)]
  rule <k> go(#Forall Y:Int. Y) => done ... </k>
endmodule
