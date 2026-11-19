module C3-HOOK-ONLY-PARAM-TOTAL
  imports INT
  imports BOOL
  syntax Int ::= lg(Int) [function, total, hook(INT.rand), symbol(lg)]
endmodule
