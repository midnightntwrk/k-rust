module E3-FRESH
  imports INT
  syntax Exp ::= a() [symbol(a)] | b(Int) [symbol(b)]
  rule <k> a() => b(!X:Int) ... </k>
endmodule
