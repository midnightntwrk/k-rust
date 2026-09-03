module TEST
  imports INT
  syntax A ::= "a" "(" Int ")" [symbol(aA)]
  syntax B ::= "a" "(" Int ")" [symbol(aB)]
  syntax A ::= mkA() [symbol(mkA)]
  rule a(1) => mkA()
endmodule
