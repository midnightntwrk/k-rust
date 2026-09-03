module A
  syntax E ::= "e"
  syntax Es ::= List{E, ","}
endmodule

module B
  syntax E ::= "f"
  syntax Es ::= List{E, ";"}
endmodule

module DUPLICATE-USER-LIST
  imports A
  imports B
endmodule
