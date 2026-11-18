// Each hooked function of BYTES-HOOKED and BYTES-STRING-ENCODE that the library reads as a parameter symbol (no registry
// hook), applied once in a rule's right side to variables (literal arguments would be folded
// by kompile); fixture.toml params records `kcore sem-fields`'s parameter lines.
module E6-PARAM-BYTES
  imports BYTES
  imports INT
  imports STRING
  syntax KItem ::= go(Int, K, K) [symbol(go)]
  rule <k> go(1, X1:Bytes, _) => Bytes2Hex(X1) ... </k>
  rule <k> go(2, X1:Bytes, _) => Bytes2String(X1) ... </k>
  rule <k> go(3, X1:String, _) => String2Bytes(X1) ... </k>
  rule <k> go(4, X1:String, X2:Bytes) => decodeBytes(X1, X2) ... </k>
  rule <k> go(5, X1:String, X2:String) => encodeBytes(X1, X2) ... </k>
endmodule
