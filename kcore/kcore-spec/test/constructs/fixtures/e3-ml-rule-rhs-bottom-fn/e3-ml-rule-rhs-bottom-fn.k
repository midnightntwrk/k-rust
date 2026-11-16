module E3-ML-RULE-RHS-BOTTOM-FN
  imports INT
  syntax Exp ::= go(Int) [symbol(go)] | pair(Int, Int) [symbol(pair)]
  syntax Int ::= f(Int) [function, symbol(f)]
  rule f(0) => 1
  rule <k> go(X) => pair(f(X), #Bottom) ... </k>
endmodule
