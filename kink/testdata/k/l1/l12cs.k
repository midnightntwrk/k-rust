// Re-pin L1-2 review probe l12cs (pinned in L1-2-fix-1): a false `total` claim that k-rust does
// not flag, reached only on a path other than the one-sided killing leaf's. f is claimed total,
// but its only equation requires a natural argument, so f(-1) stays unevaluated. start(N) goes to
// go(N, 7), which has two successors: early: done(N +Int K), stuck at once; late: loop(N, K),
// which counts N down to loop(0, K) and ends in done(f(K -Int 7)). The baseline's finals from
// start(10) are {done(17), done(0)}. The mutant (init's 7 becomes 6) ends in done(16) early and
// in done(f(-1)) late, a stuck configuration that is not a value. The early branch is explored
// first, so a work budget below the mutant's work cuts the late branch after done(16) finished.
module L12CS-SYNTAX
  imports INT-SYNTAX
  syntax Prog ::= start(Int) [symbol(start)]
                | go(Int, Int) [symbol(go)]
                | loop(Int, Int) [symbol(loop)]
                | done(Int) [symbol(done)]
endmodule
module L12CS
  imports L12CS-SYNTAX
  imports INT
  imports BOOL
  syntax Int ::= f(Int) [function, total, symbol(f)]
  rule f(N) => N requires N >=Int 0
  configuration <k> $PGM:Prog </k>
  rule [init]: <k> start(N) => go(N, 7) </k>
  rule [early]: <k> go(N, K) => done(N +Int K) </k>
  rule [late]: <k> go(N, K) => loop(N, K) </k>
  rule [step]: <k> loop(N, K) => loop(N -Int 1, K) </k> requires N >Int 0
  rule [stop]: <k> loop(0, K) => done(f(K -Int 7)) </k>
endmodule
