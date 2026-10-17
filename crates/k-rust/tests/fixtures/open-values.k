requires "substitution.md"

// Rules whose results read values the definition leaves open (Base2String's letter case,
// minFloat of the two zeros, substOne's names under a binder) beside rules that read k-rust's
// specified readings (String2Bytes byte per code point, Float2Int ties to even, the ECDSA
// failure value). `kprove_proves_no_claim_that_depends_on_an_open_value` in cli.rs.
module OPEN
  imports DOMAINS
  imports BYTES
  imports FLOAT
  imports SUBSTITUTION
  syntax Exp ::= KVar | lam(KVar, Exp) [binder] | app(Exp, Exp)
  syntax Bytes ::= EcdsaRecover(Bytes, Int, Bytes, Bytes) [function, hook(KRYPTO.ecdsaRecover)]
  syntax Pgm ::= b2s(Int, Int) | s2b(String) | sub(Exp, Exp, KVar) | r(KItem) | ccase(Int)
               | mn(Float, Float) | rt(Int, Int) | f2i(Float) | rec(Bytes, Int, Bytes, Bytes)
               | mx(Float, Float) | g(Int) | eqk(Int)
  configuration <k> $PGM:Pgm </k>
  rule b2s(I, B) => r(Base2String(I, B))
  rule s2b(S) => r(String2Bytes(S))
  rule sub(T, V, X) => r(T[V / X])
  rule ccase(I) => r(Base2String(I, 16) ==String "ff")
  rule mn(X:Float, Y:Float) => r(minFloat(X, Y))
  rule rt(I, B) => r(String2Base(Base2String(I, B), B))
  rule f2i(F) => r(Float2Int(F))
  rule rec(H, V, R, S) => r(EcdsaRecover(H, V, R, S))
  rule mx(X:Float, Y:Float) => r(maxFloat(X, Y))
  // Decided through a rule condition, and through apartness of `==K` against the other case.
  rule g(I) => r(1) requires Base2String(I, 16) ==String "ff"
  rule g(I) => r(2) requires Base2String(I, 16) =/=String "ff"
  rule eqk(I) => r(Base2String(I, 16) ==K "FF")
endmodule
