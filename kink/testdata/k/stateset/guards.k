// fz26 KINK-PATHSET-FALLBACK: the soundness guards, one per leaf kind kink reads, each reached by
// two converging paths, so a state set has one leaf where a path set has one per path.
// - two(X): two paths to join(X), whose rule `join` carries `preserves-definedness` and divides by
//   zero: one Trivial leaf naming `join` (never a producing rule), with the record.
// - tc(X): two paths to tm(X), whose step `val(td(X))` contradicts td's `total` at X = 0: one
//   Trivial leaf with `contradictedTotal`.
// - ab(X): two paths to am(X); on the second, `acm`'s condition `td(X) >Int 0` is refuted at 0
//   through td's contradicted `total`, and `aco` takes it to am(X): the state set merges that
//   arrival into the clean first one, so its record is on the run's list and on no leaf.
// - cr(X): a crash beside an undefined step, on two branches: two terminals.
module GUARDS-SYNTAX
  imports INT-SYNTAX
  syntax Prog ::= two(Int) [symbol(two)]
                | ja(Int) [symbol(ja)]
                | jb(Int) [symbol(jb)]
                | join(Int) [symbol(join)]
                | tc(Int) [symbol(tc)]
                | ta(Int) [symbol(ta)]
                | tb(Int) [symbol(tb)]
                | tm(Int) [symbol(tm)]
                | ab(Int) [symbol(ab)]
                | aa(Int) [symbol(aa)]
                | ac(Int) [symbol(ac)]
                | am(Int) [symbol(am)]
                | cr(Int) [symbol(cr)]
                | k1(Int) [symbol(k1)]
                | crash(Int) [symbol(crash)]
                | val(Int) [symbol(val)]
                | "done" [symbol(done)]
  syntax Int ::= td(Int) [function, total, symbol(td)]
endmodule

module GUARDS
  imports GUARDS-SYNTAX
  imports INT
  configuration <k> $PGM:Prog </k>
  rule [tdeq]: td(I) => 10 /Int I

  rule [ja]: <k> two(X) => ja(X) </k>
  rule [jb]: <k> two(X) => jb(X) </k>
  rule [jaj]: <k> ja(X) => join(X) </k>
  rule [jbj]: <k> jb(X) => join(X) </k>
  rule [join]: <k> join(X) => val(X /Int 0) </k> [preserves-definedness]

  rule [ta]: <k> tc(X) => ta(X) </k>
  rule [tb]: <k> tc(X) => tb(X) </k>
  rule [tam]: <k> ta(X) => tm(X) </k>
  rule [tbm]: <k> tb(X) => tm(X) </k>
  rule [tmv]: <k> tm(X) => val(td(X)) </k>

  rule [aa]: <k> ab(X) => aa(X) </k>
  rule [ac]: <k> ab(X) => ac(X) </k>
  rule [aam]: <k> aa(X) => am(X) </k>
  rule [acm]: <k> ac(X) => am(X) </k> requires td(X) >Int 0
  rule [aco]: <k> ac(X) => am(X) </k> [owise]
  rule [amd]: <k> am(_) => done </k>

  rule [crk]: <k> cr(X) => k1(X) </k>
  rule [crc]: <k> cr(X) => crash(X) </k>
  rule [k1v]: <k> k1(X) => val(X /Int 0) </k>
endmodule
