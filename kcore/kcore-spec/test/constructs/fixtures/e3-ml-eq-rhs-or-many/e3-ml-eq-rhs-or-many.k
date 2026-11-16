module E3-ML-EQ-RHS-OR-MANY
  imports INT
  syntax Int ::= k(Int) [function, total, symbol(k)]
  rule k(_) => 1 #Or 2 #Or 3 #Or 4 #Or 5 #Or 6 #Or 7 #Or 8 #Or 9
endmodule
