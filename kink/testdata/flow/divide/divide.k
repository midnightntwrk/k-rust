// Flow fixture (F-13): a guarded division. Without the guard, `1 / 0` takes a step whose
// result is undefined (`1 /Int 0`) where the baseline is stuck: the exit stop distinguishes
// (stuck against undefined-step) while the whole final configuration agrees (an undefined
// step's terminal is its pre-step configuration).
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
