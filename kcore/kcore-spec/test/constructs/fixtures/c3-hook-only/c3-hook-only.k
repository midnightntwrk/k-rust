module C3-HOOK-ONLY
  imports INT
  imports BOOL
  syntax Int ::= plus(Int, Int) [function, total, hook(INT.add), symbol(plus)]
endmodule
