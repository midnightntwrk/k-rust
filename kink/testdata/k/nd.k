module ND-SYNTAX
  syntax S ::= "start" [symbol(start)]
             | "mid1" [symbol(mid1)]
             | "mid2" [symbol(mid2)]
             | "done" [symbol(done)]
             | "spin" [symbol(spin)]
endmodule

module ND
  imports ND-SYNTAX
  imports BASIC-K
  imports INT-SYNTAX
  configuration <k> .K </k>

  rule [left]: start => mid1
  rule [right]: start => mid2
  rule [l2]: mid1 => done
  rule [r2]: mid2 => done
  rule [spin]: spin => spin
endmodule
