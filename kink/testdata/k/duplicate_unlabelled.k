module DUPLICATE_UNLABELLED-SYNTAX
  syntax S ::= "x" [symbol(x)]
             | "y" [symbol(y)]
endmodule

module DUPLICATE_UNLABELLED
  imports DUPLICATE_UNLABELLED-SYNTAX
  imports BASIC-K
  imports INT-SYNTAX
  configuration <k> .K </k>

  rule x => y
  rule x => y
endmodule
