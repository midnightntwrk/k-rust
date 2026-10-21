// Float-free hook computations, restricted to exact test values.
module T12HOOK-SYNTAX
  imports INT-SYNTAX
  imports FLOAT-SYNTAX
  syntax Prog ::= square(Int) [symbol(square)] | widen(Int) [symbol(widen)]
                | nan(Int) [symbol(nan)] | negzero(Int) [symbol(negzero)] | done(Int) [symbol(done)]
endmodule
module T12HOOK
  imports T12HOOK-SYNTAX
  imports BASIC-K
  imports INT
  imports BOOL
  imports FLOAT
  imports K-EQUAL
  configuration <k> .K </k>
  // VI-T13 D6: natural signature, falsely declared total for division by zero.
  syntax Int ::= totalQuotient(Int, Int) [function, total, symbol(totalQuotient), hook(INT.tdiv)]
  syntax Int ::= alike(Float, Float) [function, total, symbol(alike)]
  rule [alike]: alike(A, B) => 7 requires A ==K B
  rule [alikeow]: alike(_, _) => 0 [owise]
  rule [square]: square(I) => done(alike(Int2Float(I *Int I, 53, 11), Int2Float(I, 53, 11) *Float Int2Float(I, 53, 11))) requires I ==Int 1
  rule [widen]: widen(I) => done(alike(Int2Float(I, 53, 11), roundFloat(Int2Float(I, 24, 8), 53, 11))) requires I ==Int 1
  rule [nan]: nan(I) => done(alike(Int2Float(I, 53, 11) /Float Int2Float(I, 53, 11), (Int2Float(I +Int 1, 53, 11) /Float Int2Float(I, 53, 11)) -Float (Int2Float(I +Int 1, 53, 11) /Float Int2Float(I, 53, 11)))) requires I ==Int 0
  rule [negzero]: negzero(I) => done(alike(--Float Int2Float(I, 53, 11), Int2Float(I, 53, 11) *Float Int2Float(I -Int 1, 53, 11))) requires I ==Int 0
endmodule
