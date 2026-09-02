module TEST
  imports INT
  syntax A ::= "a" "(" K ")" [symbol(aK)]
  syntax B ::= "a" "(" Int ")" [symbol(aI)]
  rule a(X) => X
endmodule
