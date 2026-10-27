// fz26 KINK-PATHSET-FALLBACK: the one-sided early kill (kink-campaign tests/one_sided.rs) on a
// state set that holds an undefined step. start(N) has five successors, explored depth first in
// rule order: early: done(N +Int 7), stuck at once; za and zb, which converge on zm(N), whose step
// is undefined (one Trivial leaf in a state set); zc, which ends in done(N +Int 100) and, through
// zx, in done(td(N)); late: loop(N *Int 4), which counts down to done(5). A work budget smaller
// than the run's work cuts the loop after every other branch has finished.
// The mutations the test makes: early's 7 becomes 8 (a clean leaf the baseline lacks, one-sided
// kill), and zc's 0 becomes 1 (a clean leaf done(111) the baseline lacks, beside zx's td(11),
// whose undefined step contradicts td's `total` claim on another explored path: the run is
// excluded, so the fact voids the kill).
module ONESIDEDZ-SYNTAX
  imports INT-SYNTAX
  syntax Prog ::= start(Int) [symbol(start)]
                | za(Int) [symbol(za)]
                | zb(Int) [symbol(zb)]
                | zm(Int) [symbol(zm)]
                | zc(Int) [symbol(zc)]
                | zx(Int) [symbol(zx)]
                | loop(Int) [symbol(loop)]
                | done(Int) [symbol(done)]
  syntax Int ::= td(Int) [function, total, symbol(td)]
endmodule
module ONESIDEDZ
  imports ONESIDEDZ-SYNTAX
  imports INT
  imports BOOL
  configuration <k> $PGM:Prog </k>
  rule [tdeq]: td(I) => 10 /Int (I -Int 11)
  rule [early]: <k> start(N) => done(N +Int 7) </k>
  rule [za]: <k> start(N) => za(N) </k>
  rule [zb]: <k> start(N) => zb(N) </k>
  rule [zc]: <k> start(N) => zc(N +Int 0) </k>
  rule [late]: <k> start(N) => loop(N *Int 4) </k>
  rule [zam]: <k> za(N) => zm(N) </k>
  rule [zbm]: <k> zb(N) => zm(N) </k>
  rule [zmv]: <k> zm(N) => done(N /Int 0) </k>
  rule [zcd]: <k> zc(N) => done(N +Int 100) </k>
  rule [zcx]: <k> zc(N) => zx(N) </k>
  rule [zxv]: <k> zx(N) => done(td(N)) </k>
  rule [step]: <k> loop(N) => loop(N -Int 1) </k> requires N >Int 0
  rule [stop]: <k> loop(0) => done(5) </k>
endmodule
