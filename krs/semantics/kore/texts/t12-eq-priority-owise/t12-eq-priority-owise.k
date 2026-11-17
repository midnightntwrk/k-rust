module T12-EQ-PRIORITY-OWISE
  imports INT
  syntax Int ::= f(Int) [function, symbol(f)]
  rule f(X) => 1 requires X >Int 0 [priority(40)]
  rule f(X) => 2 requires X >Int 10
  rule f(_) => 3 [owise]
endmodule
