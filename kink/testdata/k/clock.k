// A free-running clock, for the counted stop (kink-campaign `Stop`). `tick` advances the count
// and the phase; every fourth step is `frame`, which advances the count and resets the phase, so
// no run of `clock(0, 0)` ends on its own and its end is where a stop puts it. `halt` (preempting
// every other rule) and `warp` are guarded so that no run of `clock(0, 0)` takes them. Nor does
// it take `split` or `skip`, which only a negative count reaches: there `split` branches off the
// first tick of every frame to phase 5, where `skip` advances the count and resets the phase, so
// that the state before `frame` and the state before `skip` are two states with the same next
// one. `later` is a function: its label names an equation and no rewrite rule. The mutations
// kink-campaign's tests/stop.rs makes: tick's count step 1 becomes 2; frame's count step 1
// becomes 5; frame loses its label; tick's guard 3 becomes 4 (frame's step gets a sibling);
// halt's bound becomes 2 (the run ends on its own before its first frame); warp's -1 becomes 0
// (the first step branches into a short and a long way to the next frame).
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
  rule [warp]: <k> clock(N, _) => clock(N +Int 100, 3) </k> requires N ==Int -1
  rule [split]: <k> clock(N, 1) => clock(N +Int 2, 5) </k> requires N <Int 0
  rule [skip]: <k> clock(N, P) => clock(N +Int 1, 0) </k> requires P >Int 4
endmodule
