module E3-ML-RULE-RHS-AND-PRED
  imports INT
  imports BOOL
  syntax Exp ::= go(Int) [symbol(go)] | "done" [symbol(done)] | "other" [symbol(other)]
  rule <k> go(X) => done #And {(X >Int 0) #Equals true} ... </k>
endmodule
