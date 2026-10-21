// Re-pin adoption A-1b (review A-1-review-1 finding 6): a state set replaced by its path set
// under a work budget keeps a fact only the state set reached. `s(I)` branches to `x(I)`, explored
// first, and `y(I)`. Under `x` the diamond `x -> a -> c`, `x -> b -> c` meets `c` twice: a state
// set merges the second arrival, a path set explores the chain `c -> c1 -> c2 -> c3 -> c4` again.
// The chain ends in `val(10 /Int I)`, an undefined step at 0 (a `Trivial` leaf), so the state set
// is replaced by the path set of the same request. Under `y`, as `sib` in a1claims.k, `ytd`'s
// result `val(td(I))` is undefined at 0 beside the defined `yok`: only the run's list holds `ytd`'s
// record. With a work budget between the two runs' counts, the state set reaches `y` and lists the
// record; the path set spends the budget on the second chain and does not.
module REPLACE-SYNTAX
  imports INT-SYNTAX
  syntax Prog ::= s(Int) [symbol(s)]
                | x(Int) [symbol(x)]
                | y(Int) [symbol(y)]
                | a(Int) [symbol(a)]
                | b(Int) [symbol(b)]
                | c(Int) [symbol(c)]
                | c1(Int) [symbol(c1)]
                | c2(Int) [symbol(c2)]
                | c3(Int) [symbol(c3)]
                | c4(Int) [symbol(c4)]
                | val(Int) [symbol(val)]
                | "done" [symbol(done)]
  syntax Int ::= td(Int) [function, total, symbol(td)]
endmodule
module REPLACE
  imports REPLACE-SYNTAX
  imports INT
  configuration <k> $PGM:Prog </k>
  rule [tdeq]: td(I) => 10 /Int I
  rule [sx]: <k> s(I) => x(I) </k>
  rule [sy]: <k> s(I) => y(I) </k>
  rule [xa]: <k> x(I) => a(I) </k>
  rule [xb]: <k> x(I) => b(I) </k>
  rule [ac]: <k> a(I) => c(I) </k>
  rule [bc]: <k> b(I) => c(I) </k>
  rule [cc1]: <k> c(I) => c1(I) </k>
  rule [c1c2]: <k> c1(I) => c2(I) </k>
  rule [c2c3]: <k> c2(I) => c3(I) </k>
  rule [c3c4]: <k> c3(I) => c4(I) </k>
  rule [c4val]: <k> c4(I) => val(10 /Int I) </k>
  rule [ytd]: <k> y(I) => val(td(I)) </k>
  rule [yok]: <k> y(_) => done </k>
endmodule
