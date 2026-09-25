module UNLABELLED-SYNTAX
  syntax S ::= "a" [symbol(a)]
             | "b" [symbol(b)]
             | "c" [symbol(c)]
             | "x" [symbol(x)]
             | "y" [symbol(y)]
endmodule

module UNLABELLED
  imports UNLABELLED-SYNTAX
  imports BASIC-K
  imports INT-SYNTAX
  configuration <k> .K </k>

  rule a => b
  rule b => c
  rule x => y
endmodule
