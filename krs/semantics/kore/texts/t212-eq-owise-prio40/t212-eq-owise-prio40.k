// An equation with both owise and priority(40), beside an equation of the default priority.
module T212-EQ-OWISE-PRIO40
  imports INT
  imports BOOL
  syntax Int ::= f(Int) [function, symbol(f)]
  rule f(X) => X requires X >Int 0
  rule f(_) => 0 [owise, priority(40)]
endmodule
