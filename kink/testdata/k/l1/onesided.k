// Re-pin L1-2 (decision 6, finding A-15): the one-sided early kill. start(N) has two successors:
// early: done(N +Int 7), stuck at once; late: loop(N *Int 2), which counts down 2N steps to
// done(5). k-rust explores depth first and takes the early branch first, so a run whose work
// budget is smaller than its work has finished the early branch when the budget cuts the loop.
// The mutations the kink-campaign tests make: early's 7 becomes 8 (the early final configuration
// is one the baseline lacks), stop's 5 becomes 6 (only the late final configuration changes), and
// late's 2 becomes 3 (a longer loop to the same final configurations).
module ONESIDED-SYNTAX
  imports INT-SYNTAX
  syntax Prog ::= start(Int) [symbol(start)]
                | loop(Int) [symbol(loop)]
                | done(Int) [symbol(done)]
endmodule
module ONESIDED
  imports ONESIDED-SYNTAX
  imports INT
  imports BOOL
  configuration <k> $PGM:Prog </k>
  rule [early]: <k> start(N) => done(N +Int 7) </k>
  rule [late]: <k> start(N) => loop(N *Int 2) </k>
  rule [step]: <k> loop(N) => loop(N -Int 1) </k> requires N >Int 0
  rule [stop]: <k> loop(0) => done(5) </k>
endmodule
