module TEST
  imports INT
  syntax Foo ::= "foo" | "bar" | "baz"
  rule foo #Or bar #Or baz => 0
endmodule
