module BASE
  syntax Foo ::= "foo"
endmodule

module MID
  imports private BASE
endmodule

module PRIVATE-IMPORT-EXPLICIT
  imports MID
  rule foo => .K
endmodule
