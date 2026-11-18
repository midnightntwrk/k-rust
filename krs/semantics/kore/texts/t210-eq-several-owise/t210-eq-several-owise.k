// Several [owise] equations of one function, two of which apply at some arguments and agree there.
module T210-EQ-SEVERAL-OWISE
  imports INT
  imports BOOL
  syntax Int ::= f(Int) [function, symbol(f)]
  rule f(0) => 0
  rule f(X) => 1 requires X >Int 0 [owise]
  rule f(X) => 1 requires X >Int 10 [owise]
  rule f(X) => 2 requires X <Int 0 [owise]
endmodule
