module DUP
  imports INT
  imports BASIC-K
  syntax Prog ::= "a" [symbol(a)] | "b" [symbol(b)] | "c" [symbol(c)]
  configuration <k> $PGM:Prog </k>
  rule <k> a => b </k>
  rule <k> a => c </k>
endmodule
module DUP-SPEC
  imports DUP
  claim [one]: <k> a => b </k> [one-path]
  claim [all]: <k> a => b </k>
endmodule
