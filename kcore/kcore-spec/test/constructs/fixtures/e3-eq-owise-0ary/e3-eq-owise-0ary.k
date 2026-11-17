module E3-EQ-OWISE-0ARY
  imports INT
  imports BOOL
  syntax Bool ::= g() [function, symbol(g)]
  syntax Int ::= f() [function, symbol(f)]
  rule g() => true
  rule f() => 1 requires g()
  rule f() => 0 [owise]
endmodule
