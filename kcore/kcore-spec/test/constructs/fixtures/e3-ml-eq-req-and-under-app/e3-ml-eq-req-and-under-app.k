module E3-ML-EQ-REQ-AND-UNDER-APP
  imports INT
  syntax Exp ::= go(Int, Int) [symbol(go)] | "done" [symbol(done)]
  syntax Int ::= f(Int) [function, total, symbol(f)]
               | g(Int, Int) [function, total, symbol(g)]
  rule f(X) => X -Int 1
  rule g(X, Y) => 1 requires f(X #And Y) ==Int 0
  rule g(_, _) => 0 [owise]
  rule <k> go(X, Y) => done ... </k> requires g(X, Y) ==Int 1
endmodule
