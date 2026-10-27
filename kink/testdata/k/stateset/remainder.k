// KINK-PATHSET-FALLBACK (D39): a remainder below a merged state that its own normalization
// refutes. `p(X)` is produced by `g1` on one path and by `g2` on the other. `pr` leaves the
// remainder `X ==Int 0`, which the solver finds satisfiable beside the initial condition
// `h(X) =/=Int 3` (it does not know `h`); its normalization evaluates `h(0)`, which divides by
// zero, so the remainder is a `Trivial` leaf. A remainder takes no step of its own, so the leaf
// names the rule that produced its parent: under a state set the witness path's `g1` only, under
// a path set `g1` and `g2`. `g2` carries `preserves-definedness`, but its result `p(X)` is
// defined: nothing contradicts the claim.
//
// With `g`, a total function that is 3 at 0, in the initial condition instead of `h`, the
// remainder's normalization refutes `g(0) =/=Int 3`, so it is a `Vacuous` leaf, which names the
// producing rule the same way.
//
// REMAINDER-RECORD adds a step after `q` whose candidate `qz` contradicts `tz`'s `total` claim and
// is covered by its defined sibling `qr`: a record on the run's list that no leaf carries.
module REMAINDER-SYNTAX
  imports INT-SYNTAX
  syntax Prog ::= x(Int) [symbol(x)]
                | a(Int) [symbol(a)]
                | b(Int) [symbol(b)]
                | p(Int) [symbol(p)]
                | q(Int) [symbol(q)]
                | r(Int) [symbol(r)]
  syntax Int ::= h(Int) [function, symbol(h)]
               | g(Int) [function, total, symbol(g)]
               | tz(Int) [function, total, symbol(tz)]
endmodule

module REMAINDER
  imports REMAINDER-SYNTAX
  imports INT
  configuration <k> $PGM:Prog </k>
  rule [h0]: h(0) => 1 /Int 0
  rule [g0]: g(0) => 3
  rule [xa]: <k> x(X) => a(X) </k>
  rule [xb]: <k> x(X) => b(X) </k>
  rule [g1]: <k> a(X) => p(X) </k>
  rule [g2]: <k> b(X) => p(X) </k> [preserves-definedness]
  rule [pr]: <k> p(X) => q(X) </k> requires X =/=Int 0
endmodule

module REMAINDER-RECORD
  imports REMAINDER
  rule [tzeq]: tz(I) => I /Int 0
  rule [qz]: <k> q(_) => r(tz(1)) </k>
  rule [qr]: <k> q(_) => r(0) </k>
endmodule
