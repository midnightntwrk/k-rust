module C3-HOOK-EQ-PARAM-SIMP
  imports INT
  imports BOOL
  syntax Int ::= lg(Int) [function, hook(INT.log2), symbol(lg)]
  rule lg(1) => 0 [simplification]
endmodule
