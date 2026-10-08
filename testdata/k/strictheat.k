// Coverage fixture (corpus-scale CS-03): `add` is a user `strict` production, so kompile
// generates its heating and cooling rules from the production; no written rule states them.
// `add(inc(1), 2)` heats `inc(1)` out of the first argument, rewrites it to `add(1, 1)`, adds,
// cools `2` back and adds again: `<k> 4 </k>`.
module STRICTHEAT-SYNTAX
  imports INT-SYNTAX
  syntax Exp ::= Int
               | add(Exp, Exp) [strict, symbol(add)]
               | inc(Exp) [symbol(inc)]
endmodule

module STRICTHEAT
  imports STRICTHEAT-SYNTAX
  imports BASIC-K
  imports INT
  configuration <k> .K </k>

  syntax KResult ::= Int
  rule [add]: add(I1:Int, I2:Int) => I1 +Int I2
  rule [inc]: inc(E) => add(E, 1)
endmodule
