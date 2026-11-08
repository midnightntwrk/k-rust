// Flow fixture (KINK-guard-mcdc): a conjunction, a disjunction and a conjunction one of whose
// operands is implied by the other, each with an `owise` alternative, so that every step of a
// program enters one guard and the program goes on. A program is a sequence of steps; each step
// adds to `<out>` what the rule it took adds, so that every guard decision shows in the result.
module MCDC-SYNTAX
  imports INT-SYNTAX
  imports BOOL-SYNTAX
  syntax Step ::= both(Bool, Bool)   [symbol(both)]
                | either(Bool, Bool) [symbol(either)]
                | big(Int)           [symbol(big)]
  syntax Steps ::= List{Step, ";"}   [symbol(steps)]
endmodule

module MCDC
  imports MCDC-SYNTAX
  imports INT
  imports BOOL
  configuration <k> $PGM:Steps </k> <out> 0 </out>

  rule [next]: <k> S:Step ; Ss:Steps => S ~> Ss ... </k>
  rule [done]: <k> .Steps => .K ... </k>

  rule [both]:        <k> both(A, B) => .K ... </k> <out> N => N +Int 1 </out> requires A andThenBool B
  rule [both-not]:    <k> both(_, _) => .K ... </k> <out> N => N +Int 10 </out> [owise]
  rule [either]:      <k> either(A, B) => .K ... </k> <out> N => N +Int 100 </out> requires A orElseBool B
  rule [either-not]:  <k> either(_, _) => .K ... </k> <out> N => N +Int 1000 </out> [owise]
  rule [big]:         <k> big(X) => .K ... </k> <out> N => N +Int 10000 </out> requires X >Int 0 andThenBool X >Int 10
  rule [big-not]:     <k> big(_) => .K ... </k> <out> N => N +Int 100000 </out> [owise]
endmodule
