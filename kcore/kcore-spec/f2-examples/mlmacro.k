module E2-MACRO
  imports INT
  syntax Int ::= m1(Int)                             [macro, symbol(m1)]
               | m2(Int)                             [macro-rec, symbol(m2)]
               | a1(Int)                             [alias, symbol(a1)]
               | a2(Int)                             [alias-rec, symbol(a2)]
               | f(Int)                              [function, symbol(f)]
  rule m1(X) => X +Int 1
  rule m2(X) => X +Int 2
  rule a1(X) => X +Int 3
  rule a2(X) => X +Int 4
  rule f(X) => m1(X) +Int m2(X) +Int a1(X) +Int a2(X)
endmodule
