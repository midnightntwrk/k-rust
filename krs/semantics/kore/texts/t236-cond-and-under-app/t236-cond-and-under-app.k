// #And of two Int terms under a function application in a requires.
module T236-COND-AND-UNDER-APP
  imports INT
  syntax Exp ::= go(Int, Int) [symbol(go)] | "done" [symbol(done)]
  syntax Int ::= f(Int) [function, total, symbol(f)]
  rule f(X) => X -Int 1
  rule <k> go(X, Y) => done ... </k> requires f(X #And Y) ==Int 0
endmodule
