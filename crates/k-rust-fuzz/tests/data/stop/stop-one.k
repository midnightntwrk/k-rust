// Mutant of stop.k without `right`: `fork(N)` has the one successor `tick(N)` by `left`, so a
// stop on `left` is an event here where stop.k passes it.

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
endmodule
