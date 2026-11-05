// A free-running clock, for kink-flow's `[stop]`. `tick` advances the count and the phase; every
// fourth step is `frame`, which advances the count and resets the phase, so no run of
// `clock(0, 0)` ends on its own and its end is where the stop puts it. `halt` (preempting every
// other rule) is guarded so that no run of `clock(0, 0)` takes it. `later` is a function: its
// label names an equation and no rewrite rule.
module CLOCK-SYNTAX
  imports INT-SYNTAX
  syntax Clock ::= clock(Int, Int) [symbol(clock)]
                 | halted(Int) [symbol(halted)]
endmodule
module CLOCK
  imports CLOCK-SYNTAX
  imports INT
  imports BOOL
  configuration <k> $PGM:Clock </k>
  syntax Int ::= later(Int) [function]
  rule [later]: later(N) => N +Int 1
  rule [tick]: <k> clock(N, P) => clock(N +Int 1, P +Int 1) </k> requires P <Int 3
  rule [frame]: <k> clock(N, 3) => clock(N +Int 1, 0) </k>
  rule [halt]: <k> clock(N, _) => halted(N) </k> requires N >Int 1000000 [priority(10)]
endmodule
