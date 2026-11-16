module C3-HOOK-EQ-OWISE
  imports INT
  imports BOOL
  syntax Int ::= plus(Int, Int) [function, total, hook(INT.add), symbol(plus)]
  rule plus(X, 0) => X
  rule plus(X, Y) => X +Int Y [owise]
endmodule
