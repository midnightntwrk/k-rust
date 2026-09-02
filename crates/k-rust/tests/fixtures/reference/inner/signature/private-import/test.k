module BASE
  syntax Foo ::= "foo"
endmodule

module MID [private]
  imports BASE
endmodule

module PRIVATE-IMPORT
  imports MID
  rule foo => .K
endmodule
