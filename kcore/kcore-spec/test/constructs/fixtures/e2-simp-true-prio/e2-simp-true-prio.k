module E2-SIMP-TRUE-PRIO
  imports INT
  syntax Int ::= f0(Int) [function, symbol(f0)]
               | f1(Int) [function, symbol(f1)]
               | f2(Int) [function, symbol(f2)]
               | f3(Int) [function, symbol(f3)]
               | f4(Int) [function, symbol(f4)]
  rule f0(X) => X
  rule f1(X) => X
  rule f2(X) => X
  rule f3(X) => X
  rule f4(X) => X
  rule f0(f0(X)) => f0(X) [simplification]
  rule f1(f1(X)) => f1(X) [simplification(10)]
  rule f2(f2(X)) => f2(X) [simplification(50)]
  rule f3(f3(X)) => f3(X) [simplification(200)]
  rule f4(f4(X)) => f4(X) [simplification(300)]
endmodule
