module C3-HOOK-ONLY-PARAM
  imports INT
  imports BOOL
  syntax Int ::= lg(Int) [function, hook(INT.log2), symbol(lg)]
endmodule
