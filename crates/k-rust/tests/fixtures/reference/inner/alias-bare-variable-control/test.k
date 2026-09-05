module TEST
  imports INT
  syntax Foo ::= foo(Int)
  context alias [foo]: foo(HERE)
    requires isFoo(HOLE)
endmodule
