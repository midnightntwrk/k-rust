// The seven sort-parametric hooked functions of BYTES over MInt{Width} (domains.md), each applied
// once, in a rule of its own labelled with the hook's name, at the instance MInt{64}.
module E6-REFUSED-BYTES-MINT
  imports BYTES
  imports MINT
  imports INT
  syntax MInt{64}
  syntax KItem ::= go(Int) [symbol(go)]
  rule [bytes-updateMInt]:   <k> go(1) ~> B:Bytes ~> I:MInt{64} ~> V:MInt{64} => B [ I <- V ] ... </k>
  rule [bytes-getMInt]:      <k> go(2) ~> B:Bytes ~> I:MInt{64} => B [ I ] ... </k>
  rule [bytes-substrMInt]:   <k> go(3) ~> B:Bytes ~> I:MInt{64} ~> J:MInt{64} => substrBytes(B, I, J) ... </k>
  rule [bytes-replaceAtMInt]: <k> go(4) ~> B:Bytes ~> I:MInt{64} ~> C:Bytes => replaceAtBytes(B, I, C) ... </k>
  rule [bytes-padRightMInt]: <k> go(5) ~> B:Bytes ~> I:MInt{64} ~> V:MInt{64} => padRightBytes(B, I, V) ... </k>
  rule [bytes-padLeftMInt]:  <k> go(6) ~> B:Bytes ~> I:MInt{64} ~> V:MInt{64} => padLeftBytes(B, I, V) ... </k>
  rule [bytes-lengthMInt]:   <k> go(7) ~> B:Bytes => lengthBytes(B):MInt{64} ... </k>
endmodule
