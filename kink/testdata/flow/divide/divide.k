// Flow fixture (F-13): a guarded division. Without the guard, `1 / 0` takes a step whose
// result is undefined (`1 /Int 0`) where the baseline is stuck. An undefined step is no end
// (kink27 R1-UNDEF), so the mutant has no end: the exit stop and the whole final configuration
// both distinguish (a removed end).
module DIVIDE-SYNTAX
  imports INT-SYNTAX
  syntax Exp ::= Int
               | Exp "/" Exp [strict, symbol(div)]
endmodule

module DIVIDE
  imports DIVIDE-SYNTAX
  imports INT
  configuration <k> $PGM:Exp </k>

  syntax KResult ::= Int
  rule [div]: I1:Int / I2:Int => I1 /Int I2 requires I2 =/=Int 0
endmodule
