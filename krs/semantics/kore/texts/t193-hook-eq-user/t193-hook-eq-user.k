// A symbol of the text's own hooked to INT.add, with an equation of the text's own.
module T193-HOOK-EQ-USER
  imports INT
  imports BOOL
  syntax Int ::= plus(Int, Int) [function, total, hook(INT.add), symbol(plus)]
  rule plus(X, 0) => X
endmodule
