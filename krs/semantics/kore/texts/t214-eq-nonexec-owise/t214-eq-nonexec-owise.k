// A non-executable equation beside an executable one and an [owise] one, disagreeing with the
// [owise] equation where both apply.
module T214-EQ-NONEXEC-OWISE
  syntax Foo ::= "a" [symbol(a)] | "b" [symbol(b)]
  syntax Foo ::= choose(Foo, Foo) [function, symbol(choose)]
  rule choose(a, Y) => Y
  rule choose(b, Y) => Y [non-executable]
  rule choose(X, _) => X [owise]
endmodule
