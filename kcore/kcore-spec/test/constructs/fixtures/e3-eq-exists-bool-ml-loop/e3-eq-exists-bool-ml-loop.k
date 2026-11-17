module E3-EQ-EXISTS-BOOL-ML-LOOP
  imports INT
  imports BOOL
  syntax Int ::= lp() [function, symbol(lp)]
               | pick(Bool) [function, symbol(pick)]
               | f() [function, total, symbol(f)]
  rule lp() => lp()
  rule pick(true) => 1
  rule pick(false) => lp()
  rule f() => #Exists B:Bool. pick(B)
endmodule
