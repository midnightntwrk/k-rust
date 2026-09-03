module TEST
  syntax A ::= "a" [symbol(a)]
  syntax B ::= "b" [symbol(b)]
  syntax Base ::= A | B
  syntax Foo ::= foo(Base) [symbol(foo)]
  rule foo(a => b) [anywhere]
endmodule
