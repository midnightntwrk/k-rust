module E3-EQ-EXISTS-CTOR
  imports K-EQUAL
  syntax Col ::= "r" [symbol(r)] | "g" [symbol(g)]
  syntax Col ::= pick(Col) [function, symbol(pick)]
  rule pick(X) => ?C ensures ?C =/=K X
endmodule
