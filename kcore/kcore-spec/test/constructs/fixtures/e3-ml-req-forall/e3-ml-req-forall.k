module E3-ML-REQ-FORALL
  imports INT
  syntax Exp ::= go(Int) [symbol(go)] | "done" [symbol(done)] | "other" [symbol(other)]
  syntax Int ::= f(Int) [function, symbol(f)] | g(Int) [function, symbol(g)] | h(Int) [function, symbol(h)]
  rule f(X) => X
  rule <k> go(_) => done ... </k> requires #Forall Y:Int. {f(Y) #Equals Y}
endmodule
