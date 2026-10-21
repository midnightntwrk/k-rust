// Re-pin L1-2 review probe l12ct (pinned in L1-2-fix-1): a false `total` claim reached only on a
// path other than the one-sided killing leaf's. f is claimed total, but its equation divides by
// its argument, so f(0) is undefined. start(N) goes to go(N, 7), which has two successors:
// early: done(N +Int K), stuck at once; late: loop(N, K), which counts N down to loop(0, K) and
// ends in done(f(K -Int 6)). The baseline's finals from start(10) are {done(17), done(100)}. The
// mutant (init's 7 becomes 6) ends in done(16) early and reaches f(0) late, where k-rust names
// the contradicted claim (an undefined step, `contradictedTotal`). The early branch is explored
// first, so a work budget below the mutant's work cuts the late branch after done(16) finished.
module L12CT-SYNTAX
  imports INT-SYNTAX
  syntax Prog ::= start(Int) [symbol(start)]
                | go(Int, Int) [symbol(go)]
                | loop(Int, Int) [symbol(loop)]
                | done(Int) [symbol(done)]
endmodule
module L12CT
  imports L12CT-SYNTAX
  imports INT
  imports BOOL
  syntax Int ::= f(Int) [function, total, symbol(f)]
  rule f(N) => 100 /Int N
  configuration <k> $PGM:Prog </k>
  rule [init]: <k> start(N) => go(N, 7) </k>
  rule [early]: <k> go(N, K) => done(N +Int K) </k>
  rule [late]: <k> go(N, K) => loop(N, K) </k>
  rule [step]: <k> loop(N, K) => loop(N -Int 1, K) </k> requires N >Int 0
  rule [stop]: <k> loop(0, K) => done(f(K -Int 6)) </k>
endmodule
