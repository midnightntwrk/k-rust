module C3-HOOK-EQ-REQ
  imports INT
  imports BOOL
  syntax Int ::= plus(Int, Int) [function, total, hook(INT.add), symbol(plus)]
  rule plus(X, Y) => X requires Y ==Int 0
endmodule
