// A machine that never halts, for the campaign's stop (`CaseOptions::stop`). `tick(N)` steps
// forever: rule `tick` while N < 5 and rule `late` from 5 on, each step setting <n> to N and
// each the state's one successor. So the stop `before = [tick, late]` with count C ends the
// run of `tick(N)` at its Cth step, as a `cut-point` leaf `<k> tick(N + C - 1) </k>
// <n> N + C - 2 </n>` (`<n> 0 </n>` when C = 1), and `late` fires on that path exactly when
// N + C - 2 >= 5. `fork(N)` steps by `left` to `tick(N)` or by `right` to `tick(N +Int 10)`:
// two successors of one state, so a stop on `left` is passed there.

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

  rule [tick]:  <k> tick(N) => tick(N +Int 1) ... </k> <n> _ => N </n> requires N <Int 5
  rule [late]:  <k> tick(N) => tick(N +Int 1) ... </k> <n> _ => N </n> requires N >=Int 5
  rule [left]:  <k> fork(N) => tick(N) ... </k>
  rule [right]: <k> fork(N) => tick(N +Int 10) ... </k>
endmodule
