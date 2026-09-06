// Derived from k/k-distribution/tests/regression-new/mint-llvm-4/test.k (lines 21-22, 66-68): a
// parametric-result production (`Bytes "[" MInt{Width} "]"`, `Int2MInt(Int)`) in the argument
// slot of `==MInt`, whose rule-grammar instantiation reads `MInt{K}`, with and without a cast.
module TEST
  imports INT
  imports MINT
  imports BYTES
  imports BOOL

  syntax MInt{64}
  syntax MInt{256}

  syntax Bytes ::= "bytesString2" [macro]
  rule bytesString2 =>
      b"a\x00\x1b`\x00\x81`\x0b\x829\xf3`\x01`\x01Us\x8a\n\x19X\x951iBP\xd5p\x04"

  syntax Bool ::= "testBytesGet" [function]
                | "testBytesGetBare" [function]

  rule testBytesGet =>
      {bytesString2[2p64]}:>MInt{64} ==MInt Int2MInt(bytesString2[2]) andBool
      {bytesString2[2p256]}:>MInt{256} ==MInt Int2MInt(bytesString2[2])

  rule testBytesGetBare => bytesString2[2p64] ==MInt 0p64
endmodule
