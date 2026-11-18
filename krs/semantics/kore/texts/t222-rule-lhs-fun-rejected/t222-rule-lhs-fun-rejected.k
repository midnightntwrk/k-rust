// A function application under a constructor in a rewrite rule's left side.
module T222-RULE-LHS-FUN-REJECTED
  imports INT
  syntax Exp ::= c(Int) [symbol(c)] | d(Int) [symbol(d)]
  syntax Int ::= f(Int) [function, total, symbol(f)]
  rule f(1) => 7
  rule f(2) => 7
  rule f(_) => 0 [owise]
  rule <k> c(f(X:Int)) => d(X) ... </k>
endmodule
