module REWRITE
  syntax State ::= "a" [symbol(a)]
  syntax State ::= "b" [symbol(b)]

  configuration <k> $PGM:State </k>

  rule <k> a => b </k>
endmodule
