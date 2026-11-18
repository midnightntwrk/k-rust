// A total function whose one equation has an ensures that is false at some arguments.
module T190-EQ-ENS-TOTAL
  imports INT
  imports BOOL
  syntax Int ::= f(Int) [function, total, symbol(f)]
  rule f(X) => X ensures X >=Int 0
endmodule
