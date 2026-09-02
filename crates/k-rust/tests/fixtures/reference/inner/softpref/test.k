module TEST
  imports INT
  syntax Foo ::= "foo"
  syntax A ::= "a" "(" K "," Int ")" [symbol(aK)]
  syntax B ::= "a" "(" Int "," Foo ")" [symbol(aF)]
  rule a(X, Y) => X ~> Y
endmodule
