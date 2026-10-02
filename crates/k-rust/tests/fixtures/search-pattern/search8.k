// The sort checks reject numeral terms and operand positions before search-pattern parsing.
module SEARCH8-SYNTAX
  imports BOOL-SYNTAX
  syntax 8 ::= "eight"
  syntax Foo ::= foo(8) | "done"
endmodule

module SEARCH8
  imports SEARCH8-SYNTAX
  imports BOOL
  configuration <k> $PGM:Foo </k>
  rule foo(eight) => done
endmodule
