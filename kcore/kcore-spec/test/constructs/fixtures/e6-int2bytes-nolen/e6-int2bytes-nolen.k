// BYTES-HOOKED's `Int2Bytes` without a length (symbol Int2BytesNoLen) and INT-COMMON's `~Int`, each
// applied in a rule's right side to variables, so the reading holds both as parameter symbols (a
// bare import gives Γ neither: the library's equations of Int2BytesNoLen apply them).
module E6-INT2BYTES-NOLEN
  imports BYTES
  imports INT
  syntax KItem ::= go(Int, Endianness, Signedness) [symbol(go)]
                 | neg(Int) [symbol(neg)]
  rule <k> go(I:Int, E:Endianness, S:Signedness) => Int2Bytes(I, E, S) ... </k>
  rule <k> neg(I:Int) => ~Int I ... </k>
endmodule
