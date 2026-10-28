// Alias patterns (`P #as X`, KORE `\and(P, X)`) in function equations and their owise competitors,
// one function per shape (k2lean/docs/design.md, section 3, "Alias patterns").
module ALIAS-SYNTAX
  imports INT-SYNTAX
  imports LIST
  imports MAP
  syntax Pr ::= c(Int) [symbol(c)] | d(Int) [symbol(d)] | wrap(Pr, Pr) [symbol(wrap)] | "nil" [symbol(nil)]
  syntax Pgm ::= run(Pr, List, Map, KItem) [symbol(run)]
endmodule

module ALIAS
  imports ALIAS-SYNTAX
  imports INT
  imports BOOL
  imports LIST
  imports MAP
  configuration <k> $PGM:Pgm </k>

  // S1 a left-hand subterm repeated on the right-hand side (no #as in the source)
  syntax List ::= sh(List) [function, total, symbol(sh)]
  rule sh(.List) => .List
  rule sh(ListItem(X:Int) L) => ListItem(X +Int 1) sh(L)
  rule sh(L) => L [owise]

  // S2 an owise equation whose competitor has an alias nested under a constructor
  syntax Pr ::= nw(Pr) [function, total, symbol(nw)]
  rule nw(wrap(P, nil)) => wrap(nil, P)
  rule nw(c(N)) => d(N)
  rule nw(_) => nil [owise]
  syntax Int ::= pv(Pr) [function, total, symbol(pv)]
  rule pv(c(N)) => N
  rule pv(d(N)) => 0 -Int N
  rule pv(_) => 0 [owise]
  syntax Int ::= one(KItem) [function, total, symbol(one)]
  rule one(_) => 1

  // S3 a user alias whose variable also occurs in another argument (non-linear)
  syntax Int ::= tw(Pr, Pr) [function, total, symbol(tw)]
  rule tw(c(N) #as X, X) => N
  rule tw(_, _) => 0 [owise]
  syntax Int ::= tw2(Pr, Pr) [function, total, symbol(tw2)]
  rule tw2(X, c(N) #as X) => N
  rule tw2(_, _) => 0 [owise]

  // S4 an alias of an alias
  syntax Int ::= aa(Pr) [function, total, symbol(aa)]
  rule aa((c(N) #as X) #as Y) => N +Int pv(X) +Int pv(Y)
  rule aa(_) => 0 [owise]

  // S5 an alias around a list pattern
  syntax Int ::= la(List) [function, total, symbol(la)]
  rule la((ListItem(A:Int) _) #as L) => A +Int size(L)
  rule la(_) => 0 [owise]

  // S6 an alias around a map pattern
  syntax Int ::= ma(Map) [function, total, symbol(ma)]
  rule ma(((K:Int |-> _) _) #as M) => K +Int size(M)
  rule ma(_) => 0 [owise]

  // S7 an alias of an injection (a sort cast at a supersort position)
  syntax Int ::= ik(KItem) [function, total, symbol(ik)]
  rule ik((I:Int) #as X) => I +Int one(X)
  rule ik(_) => 0 [owise]

  // S8 an alias whose variable occurs in the requires
  syntax Int ::= rq(Pr) [function, total, symbol(rq)]
  rule rq(c(N) #as X) => N requires pv(X) >Int 0
  rule rq(_) => 0 [owise]

  // S9 an alias of a variable (two variables)
  syntax Int ::= vv(Pr) [function, total, symbol(vv)]
  rule vv(X #as Y) => pv(X) +Int pv(Y)

  // S10 a literal, and an injected literal, repeated on the right-hand side (KMIR #popcount, consP)
  syntax Int ::= lt(Int) [function, total, symbol(lt)]
  rule lt(0) => 0
  rule lt(_) => 1 [owise]
  syntax Mi ::= Int | mb(Bool) [symbol(mb)]
  syntax Mi ::= mi(Mi) [function, total, symbol(mi)]
  rule mi(0) => 0
  rule mi(_) => 1 [owise]

  rule <k> run(P, L, M, I) => sh(L) ~> nw(P) ~> tw(P, P) ~> tw2(P, P) ~> aa(P) ~> la(L) ~> ma(M) ~> ik(I) ~> rq(P) ~> vv(P) ~> lt(0) ~> mi(0) </k>
endmodule
