module C3-EQ-HEAT-REQ
  imports INT
  imports BOOL
  syntax KResult ::= Int
  syntax Int ::= f(Int) [function, symbol(f)]
  rule f(X) => X requires X >Int 0 [heat]
endmodule
