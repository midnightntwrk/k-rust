module E3-ML-RULE-LHS-CEIL-CTOR
  imports INT
  syntax Exp ::= go(Int) [symbol(go)] | "done" [symbol(done)] | "other" [symbol(other)]
  rule <k> go(X) #And #Ceil(go(X)) => done ... </k>
endmodule
