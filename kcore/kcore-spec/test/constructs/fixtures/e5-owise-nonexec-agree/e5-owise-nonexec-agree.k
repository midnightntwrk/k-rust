module E5-OWISE-NONEXEC-AGREE
  syntax Foo ::= "a" [symbol(a)] | "b" [symbol(b)]
  syntax Foo ::= choose(Foo, Foo) [function, symbol(choose)]
  rule choose(a, Y) => Y
  rule choose(b, Y) => b [non-executable]
  rule choose(X, _) => X [owise]
endmodule
