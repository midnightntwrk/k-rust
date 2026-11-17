module C3-HOOK-ONLY-PARAM
  imports INT
  imports BOOL
  syntax Int ::= lg(Int) [function, hook(INT.rand), symbol(lg)]
endmodule
