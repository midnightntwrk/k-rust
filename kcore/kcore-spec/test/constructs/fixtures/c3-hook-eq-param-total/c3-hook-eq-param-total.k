module C3-HOOK-EQ-PARAM-TOTAL
  imports INT
  imports BOOL
  syntax Int ::= lg(Int) [function, total, hook(INT.rand), symbol(lg)]
  rule lg(1) => 0
endmodule
