module TEST
  syntax Small ::= small() [symbol(small)]
  syntax Big ::= Small | big() [symbol(big)]
  syntax Foo ::= foo(Small) [symbol(foo)]
  syntax Bar ::= bar(Big) [symbol(bar)]
  rule bar(X:Big) => foo(X)
endmodule
