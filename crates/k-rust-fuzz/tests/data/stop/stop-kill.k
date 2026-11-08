// Mutant of stop.k whose `tick` sets <n> to N + 1: neither side halts, and under the stop
// `before = [tick, late]` with count 3 the run of `tick(0)` ends at `<k> tick(2) </k>` with
// `<n> 1 </n>` on the baseline and `<n> 2 </n>` here, an end the baseline does not reach.

module STOP-SYNTAX
  imports INT-SYNTAX

  syntax Pgm ::= tick(Int)  [symbol(tick)]
               | fork(Int)  [symbol(fork)]
endmodule

module STOP
  imports STOP-SYNTAX
  imports INT
  imports BOOL

  configuration <k> $PGM:Pgm </k>
                <n> 0 </n>

  rule [tick]:  <k> tick(N) => tick(N +Int 1) ... </k> <n> _ => N +Int 1 </n> requires N <Int 5
  rule [late]:  <k> tick(N) => tick(N +Int 1) ... </k> <n> _ => N </n> requires N >=Int 5
  rule [left]:  <k> fork(N) => tick(N) ... </k>
  rule [right]: <k> fork(N) => tick(N +Int 10) ... </k>
endmodule
