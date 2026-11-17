module C3-UNBOUND-RHS-NOKEY
  imports INT
  syntax Exp ::= a() [symbol(a)] | b(Int) [symbol(b)]
  rule <k> a() => b(X) ... </k>
endmodule
