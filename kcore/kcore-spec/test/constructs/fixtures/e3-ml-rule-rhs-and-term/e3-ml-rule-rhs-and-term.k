module E3-ML-RULE-RHS-AND-TERM
  imports INT
  syntax Exp ::= go(Int) [symbol(go)] | "done" [symbol(done)] | "other" [symbol(other)]
  syntax Int ::= f(Int) [function, symbol(f)] | g(Int) [function, symbol(g)] | h(Int) [function, symbol(h)]
  rule f(X) => X
  rule g(X) => 0 -Int X
  rule <k> go(X) => f(X) #And g(X) ... </k>
endmodule
