module E3-RULE-LHS-FUN
  imports INT
  syntax Exp ::= c(Int) [symbol(c)] | d(Int) [symbol(d)]
  syntax Int ::= f(Int) [function, total, symbol(f)]
  rule f(1) => 7
  rule f(2) => 7
  rule f(_) => 0 [owise]
  rule <k> c(f(X:Int)) => d(X) ... </k>
endmodule
