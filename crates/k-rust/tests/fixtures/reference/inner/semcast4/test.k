module TEST
  syntax Small ::= small() [symbol(small)]
  syntax Big ::= Small | big() [symbol(big)]
  syntax Foo ::= foo(Small) [symbol(foo)]
  syntax Bar ::= bar(Big) [symbol(bar)]
  syntax A ::= "a" "(" Small ")" [symbol(aS)]
  syntax B ::= "a" "(" Foo ")" [symbol(aF)]
  rule bar(X:Big) ~> foo(X) => a(X)
endmodule
