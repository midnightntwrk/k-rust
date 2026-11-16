requires "domains.md"
module RMP
  imports DOMAINS
  imports FLOAT
  imports RANGEMAP
  syntax Foo ::= foo(Int) [symbol(foo)]
  configuration <k> $PGM:Foo </k>
  rule <k> foo(I) => foo(I +Int 1) </k>
endmodule
