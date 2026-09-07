module MAIN
  syntax Small ::= "small" [symbol(small)]
  syntax Large ::= Small | "large" [symbol(large)]
  syntax Box ::= box(Large) [symbol(box)]
endmodule
