module E3-EQ-EXISTS-INT
  imports INT
  syntax Int ::= h(Int) [function, symbol(h)]
  rule h(X) => ?Z ensures ?Z *Int 2 ==Int X
endmodule
