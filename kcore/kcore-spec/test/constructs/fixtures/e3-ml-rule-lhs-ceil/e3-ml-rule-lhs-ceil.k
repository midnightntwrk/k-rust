module E3-ML-RULE-LHS-CEIL
  imports INT
  syntax Exp ::= go(Int) [symbol(go)] | "done" [symbol(done)] | "other" [symbol(other)]
  rule <k> go(X) #And #Ceil(1 /Int X) => done ... </k>
endmodule
