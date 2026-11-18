// Each hooked function of FFI (ffi.md), read as a parameter symbol of the definition's own (a
// builtin file's sentence about names no library text declares, Parse.isOwnBuiltin; no registry
// hook), applied once in a rule's right side to variables (literal arguments would be folded by
// kompile); fixture.toml params records `kcore sem-fields`'s parameter lines.
requires "ffi.md"
module E6-PARAM-FFI
  imports FFI
  imports INT
  imports BYTES
  imports LIST
  imports STRING
  syntax KItem ::= go(Int, K, K, K, K, K) [symbol(go)]
  rule <k> go(1, X1:Bytes, _, _, _, _) => #address(X1) ... </k>
  rule <k> go(2, X1:KItem, X2:Int, X3:Int, _, _) => #alloc(X1, X2, X3) ... </k>
  rule <k> go(3, X1:Int, X2:List, X3:List, X4:FFIType, _) => #ffiCall(X1, X2, X3, X4) ... </k>
  rule <k> go(4, X1:Int, X2:List, X3:List, X4:List, X5:FFIType) => #ffiCall(X1, X2, X3, X4, X5) ... </k>
  rule <k> go(5, X1:KItem, _, _, _, _) => #free(X1) ... </k>
  rule <k> go(6, X1:String, _, _, _, _) => #functionAddress(X1) ... </k>
  rule <k> go(7, X1:Int, X2:Bytes, _, _, _) => #nativeRead(X1, X2) ... </k>
  rule <k> go(8, X1:Int, X2:Bytes, _, _, _) => #nativeWrite(X1, X2) ... </k>
endmodule
