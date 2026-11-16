module C3-HOOK-EQ
  imports INT
  imports BOOL
  syntax Int ::= plus(Int, Int) [function, total, hook(INT.add), symbol(plus)]
  rule plus(X, 0) => X
endmodule
