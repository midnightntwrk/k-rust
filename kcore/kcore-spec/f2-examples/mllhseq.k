module E3-ML-RULE-LHS-EQUALS
  imports INT
  syntax Exp ::= go(Int) [symbol(go)] | "done" [symbol(done)] | "other" [symbol(other)]
  rule <k> go(X) #And {X #Equals 1} => done ... </k>
endmodule
