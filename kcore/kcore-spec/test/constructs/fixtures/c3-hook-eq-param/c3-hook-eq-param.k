module C3-HOOK-EQ-PARAM
  imports INT
  imports BOOL
  syntax Int ::= lg(Int) [function, hook(INT.rand), symbol(lg)]
  rule lg(1) => 0
endmodule
