// The one-sided early kill over a cell projection. onesided.k with an unobservable cell
// <scratch>, which the early branch also writes: start(N) has two successors, early:
// done(N +Int 7) with <scratch> N +Int 1, stuck at once; late: loop(N *Int 2), which counts down
// 2N steps to done(5) and leaves <scratch> 0. k-rust explores depth first and takes the early
// branch first, so a run whose work budget is smaller than its work has finished the early branch
// when the budget cuts the loop.
// The mutations the kink-campaign tests make: early's 7 becomes 8 (the early final configuration
// differs in <k>, which every slot compares), and early's 1 becomes 2 (it differs only in
// <scratch>, which a slot leaving out the unobservable cells does not compare).
module ONESIDEDCELL-SYNTAX
  imports INT-SYNTAX
  syntax Prog ::= start(Int) [symbol(start)]
                | loop(Int) [symbol(loop)]
                | done(Int) [symbol(done)]
endmodule
module ONESIDEDCELL
  imports ONESIDEDCELL-SYNTAX
  imports INT
  imports BOOL
  configuration <k> $PGM:Prog </k> <scratch unobservable=""> 0 </scratch>
  rule [early]: <k> start(N) => done(N +Int 7) </k> <scratch> _ => N +Int 1 </scratch>
  rule [late]: <k> start(N) => loop(N *Int 2) </k>
  rule [step]: <k> loop(N) => loop(N -Int 1) </k> requires N >Int 0
  rule [stop]: <k> loop(0) => done(5) </k>
endmodule
