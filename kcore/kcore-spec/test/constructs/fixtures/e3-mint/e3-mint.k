module E3-MINT
  imports MINT
  imports INT
  syntax MInt{8}
  syntax Exp ::= a(MInt{8}) [symbol(a)] | b(Int) [symbol(b)]
  rule <k> a(X) => b(MInt2Unsigned(X +MInt X)) ... </k>
endmodule
