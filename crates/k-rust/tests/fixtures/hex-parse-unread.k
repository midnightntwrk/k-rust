// KEVM's hex parsing (serialization.md, `#parseByteStack` and what it calls) with the INT
// lemmas it meets, over a digest whose argument no evaluation reads, a symbolic `B`, and over the
// digest of the spelling of `String2Bytes("execute()")`, the shape `#abiCallData` reaches,
// which the amendments AM-1 and AM-2 determine.
module HEXS
  imports STRING
  imports BYTES
  imports INT
  imports INT-SYMBOLIC
  imports BOOL
  syntax String ::= Keccak256(Bytes) [function, hook(KRYPTO.keccak256)]

  syntax String ::= #alignHexString ( String ) [symbol(#alignHexString), function, total]
  rule #alignHexString(S) => S             requires         lengthString(S) modInt 2 ==Int 0
  rule #alignHexString(S) => "0" +String S requires notBool lengthString(S) modInt 2 ==Int 0

  syntax Bytes ::= #parseHexBytes     ( String ) [symbol(parseHexBytes), function]
                 | #parseHexBytesAux  ( String ) [symbol(parseHexBytesAux), function]
                 | #parseByteStack    ( String ) [symbol(parseByteStack), function]
  rule #parseByteStack(S) => #parseHexBytes(replaceAll(S, "0x", ""))
  rule #parseHexBytes(S)  => #parseHexBytesAux(#alignHexString(S))
  rule #parseHexBytesAux("") => .Bytes
  rule #parseHexBytesAux(S)  => Int2Bytes(lengthString(S) /Int 2, String2Base(S, 16), BE) requires lengthString(S) >=Int 2

  rule A  >Int B  => B  <Int A [simplification]
  rule A >=Int B  => B <=Int A [simplification]
endmodule
