module E5-FN-NOEQ
  imports INT
  syntax Exp ::= go(Int) [symbol(go)] | done(Int) [symbol(done)]
  syntax Int ::= f(Int) [function, symbol(f)]
  rule <k> go(X) => done(f(X)) ... </k>
endmodule
