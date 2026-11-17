module C3-HOOK-EQ-PARAM-OWISE
  imports INT
  imports BOOL
  syntax Int ::= lg(Int) [function, hook(INT.rand), symbol(lg)]
  rule lg(1) => 0
  rule lg(_) => -1 [owise]
endmodule
