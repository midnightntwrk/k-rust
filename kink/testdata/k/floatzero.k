// R3-ADMIT-FLOAT: Float literals are compared by value. `start(I)` reaches `chk` with the
// binary64 value of I; `point` matches the binary64 zero. A respelling of `0.0` that names the
// same element (`0.00e5`, `0e+00p53x11`) is the baseline's rule. `0.0f` names the binary32 zero,
// another element by K's text (the suffix fixes the format, and `precisionFloat` is a function).
// `-0.0` names the other signed zero only by k-rust's reading that a zero literal keeps the sign
// written (kink README, premise P-F2): K's text reads `-0.0` as the rational 0, which both zeros
// are equally near.
//
// R3-ADMIT-FLOAT fix round 1 (TB-03 without the census): the rows below reach NaN, Infinity,
// `==K`, a function equation and the route V5b through exact `Int2Float` conversions and (since
// kink27 GK-0) one-format `/Float` and `-Float`, whose values their `smt-hook`s fix (domains.md
// 1568, 1572), so no rule applies a hook the census reads and no run takes a value k-rust marks.
// kompile folds `fold`'s `0.1 +Float 0.2` into a literal, so no `FLOAT.add` application is left;
// FLOATMIXED's sum of a binary32 and a binary64 literal is not folded, and its run is marked.
module FLOATZERO-SYNTAX
  imports INT-SYNTAX
  imports FLOAT-SYNTAX
  syntax Prog ::= start(Int) [symbol(start)] | chk(Float) [symbol(chk)] | done(Int) [symbol(done)]
  syntax Prog ::= nans(Int) [symbol(nans)] | nanc(Float) [symbol(nanc)]
  syntax Prog ::= infs(Int) [symbol(infs)] | infc(Float) [symbol(infc)]
  syntax Prog ::= eqs(Int) [symbol(eqs)] | eqc(Float) [symbol(eqc)]
  syntax Prog ::= eqns(Int) [symbol(eqns)] | eqnc(Float) [symbol(eqnc)]
  syntax Prog ::= lstart(Int) [symbol(lstart)]
  syntax Prog ::= fold(Int) [symbol(fold)] | mixed(Int) [symbol(mixed)] | fchk(Float) [symbol(fchk)]
  syntax Float ::= one() [function, total, symbol(one)]
  syntax Int ::= eqk(Float, Float) [function, total, symbol(eqk)]
endmodule
module FLOATMIXED
  imports FLOATZERO-SYNTAX
  imports BASIC-K
  imports INT
  imports BOOL
  imports FLOAT
  configuration <k> .K </k>
  rule [mixed]: mixed(_) => fchk(0.1f +Float 0.2)
  rule [mpoint]: fchk(0.30000000000000004) => done(7)
  rule [mpointow]: fchk(_) => done(0) [owise]
endmodule
module FLOATZERO
  imports FLOATZERO-SYNTAX
  imports BASIC-K
  imports INT
  imports BOOL
  imports FLOAT
  imports K-EQUAL
  configuration <k> .K </k>
  rule [start]: start(I) => chk(Int2Float(I, 53, 11))
  rule [point]: chk(0.0) => done(7)
  rule [pointow]: chk(_) => done(0) [owise]
  // F8: the binary64 NaN, the quotient of two zeros (`fp.div`, domains.md 1568).
  rule [nans]: nans(I) => nanc(Int2Float(I, 53, 11) /Float Int2Float(I, 53, 11))
  rule [nanp]: nanc(NaN) => done(7)
  rule [nanow]: nanc(_) => done(0) [owise]
  // F9: the binary64 infinity, 1.0 over `1.0 -Float 1.0`, which is +0.0 (`fp.div`, `fp.sub`).
  rule [infs]: infs(I) => infc(Int2Float(I, 53, 11) /Float (Int2Float(I, 53, 11) -Float Int2Float(I, 53, 11)))
  rule [infp]: infc(Infinity) => done(7)
  rule [infow]: infc(_) => done(0) [owise]
  // F11: `==Float` against a literal (the mutant writes `==K`).
  rule [eqs]: eqs(I) => eqc(Int2Float(I, 53, 11))
  rule [eqp]: eqc(F) => done(7) requires F ==Float 1.0
  rule [eqow]: eqc(_) => done(0) [owise]
  // F12: a literal in a function equation's right-hand side, compared with `==K`.
  rule [onee]: one() => 1.0
  rule [eqns]: eqns(I) => eqnc(Int2Float(I, 53, 11))
  rule [eqnp]: eqnc(F) => done(7) requires F ==K one()
  rule [eqnow]: eqnc(_) => done(0) [owise]
  // V5b: two literals of one value compared with `==K` inside a function.
  rule [eqkyes]: eqk(A, B) => 7 requires A ==K B
  rule [eqkno]: eqk(_, _) => 0 [owise]
  rule [lstart]: lstart(_) => done(eqk(1.0, 1.00))
  // Fold: kompile writes the binary64 sum of two literals as a literal.
  rule [fold]: fold(_) => fchk(0.1 +Float 0.2)
  rule [fpoint]: fchk(0.30000000000000004) => done(7)
  rule [fpointow]: fchk(_) => done(0) [owise]
endmodule
