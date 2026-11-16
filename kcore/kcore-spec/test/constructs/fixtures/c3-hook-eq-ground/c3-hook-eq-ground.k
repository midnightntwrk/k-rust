module C3-HOOK-EQ-GROUND
  imports INT
  imports BOOL
  syntax Int ::= plus(Int, Int) [function, total, hook(INT.add), symbol(plus)]
  rule plus(1, 2) => 3
endmodule
