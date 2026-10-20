// Re-pin adoption A-1 (draft/tasks/repin-58720d2e/ADOPTION.md section 2.2): contradicted claims
// that show on k-rust's run-level `contradictedClaims` list. `td` is declared total but divides by
// its argument, so the claim is false at 0 (k-rust docs/compatibility.md, "A contradicted `total`
// attribute is named, not repaired", the `sib`, `r` and `tdiv` examples).
// - sib(0): `sibtd`'s result `val(td(0))` is undefined and `sibok` covers every instance, so the
//   one leaf `done` rests on no contradiction and only the list holds `sibtd`'s record.
// - sob(X): as sib with `td(X +Int 1)`, so sob(0) is clean; its mutant `X +Int 0` is sib.
// - r(0): the condition `td(0) >Int 0` is undefined, read as false: the stuck leaf carries the
//   record. rr(X): steps to rq(X +Int 1), whose rule has r's condition, so rr(0) is clean; its
//   mutant `X +Int 0` reaches rq(0), stuck with the record.
// - m(0): two paths reach `fin` at depth 2, through `p` and through `n`; the second only by
//   `nfin`, the `owise` rule an undefined condition leaves applicable, so its arrival rests on the
//   record, and a state set absorbs it into the first path's state during exploration: the `fin`
//   leaf carries no record and only the list holds it.
// - tv(0): the step's result is undefined: a `Trivial` leaf naming the contradicted `total`, so
//   the state set is replaced by its path set.
module A1CLAIMS-SYNTAX
  imports INT-SYNTAX
  syntax Prog ::= sib(Int) [symbol(sib)]
                | sob(Int) [symbol(sob)]
                | r(Int) [symbol(r)]
                | rr(Int) [symbol(rr)]
                | rq(Int) [symbol(rq)]
                | m(Int) [symbol(m)]
                | n(Int) [symbol(n)]
                | p(Int) [symbol(p)]
                | tv(Int) [symbol(tv)]
                | val(Int) [symbol(val)]
                | "done" [symbol(done)]
                | "other" [symbol(other)]
                | "fin" [symbol(fin)]
  syntax Int ::= td(Int) [function, total, symbol(td)]
endmodule
module A1CLAIMS
  imports A1CLAIMS-SYNTAX
  imports INT
  configuration <k> $PGM:Prog </k>
  rule [tdeq]: td(I) => 10 /Int I
  rule [sibtd]: <k> sib(X) => val(td(X)) </k>
  rule [sibok]: <k> sib(_) => done </k>
  rule [sobtd]: <k> sob(X) => val(td(X +Int 1)) </k>
  rule [sobok]: <k> sob(_) => done </k>
  rule [r]: <k> r(I) => done </k> requires td(I) >Int 0
  rule [rr]: <k> rr(I) => rq(I +Int 1) </k>
  rule [rq]: <k> rq(I) => done </k> requires td(I) >Int 0
  rule [mp]: <k> m(I) => p(I) </k>
  rule [mn]: <k> m(I) => n(I) </k>
  rule [pfin]: <k> p(_) => fin </k>
  rule [nother]: <k> n(I) => other </k> requires td(I) >Int 0
  rule [nfin]: <k> n(_) => fin </k> [owise]
  rule [tv]: <k> tv(I) => val(td(I)) </k>
endmodule
