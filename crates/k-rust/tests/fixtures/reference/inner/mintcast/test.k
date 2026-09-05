// Derived from k/k-distribution/tests/regression-new/mint-llvm/test.k (line 33, with and without
// its `::MInt{8}` cast) plus the `:MInt{8}` and `:>MInt{8}` cast terminals over the declared
// instance; every rule needs the `KItem ::= MInt{8}` subsort or an `MInt{8}` cast production.
module TEST
  imports INT
  imports MINT

  syntax MInt{8}
  syntax KItem ::= foo(MInt{8})

  rule I:Int => Int2MInt(I)
  rule I:Int => foo(Int2MInt(I))
  rule I:Int => Int2MInt(I)::MInt{8}
  rule I:Int => {Int2MInt(I)}:>MInt{8}
  rule foo(X:MInt{8}) => X
endmodule
