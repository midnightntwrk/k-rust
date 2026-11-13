// kore.k: an interpreter, written in K, of a fragment of KORE as kompile writes it.
//
// A program is pgm(D, T): D an encoded object definition (its subsorts, its functions with their
// equations, its rewrite rules) and T an encoded initial term of its single configuration cell.
// The result is done(Fs): every configuration reachable from T that has no successor, sorted by
// `cmp` and without repetition, which is what a search for all final configurations returns.
// Symbols and sorts are numbers given by the encoder (tools/korek.py); hooked symbols of INT,
// BOOL and KEQUAL are operation codes (`hookOp`).
//
// Reading of KORE implemented here:
//   - a function application is evaluated innermost: arguments first; an undefined argument
//     (\bottom) makes the application undefined; a constructor application is a value;
//   - an equation applies when its argument patterns match and its requires evaluates to true;
//     among the applicable equations one of the least priority gives the result (an [owise]
//     equation has priority 200, an equation without priority 50); an application no equation
//     applies to stays as it is;
//   - a rewrite rule applies when its left side matches and its requires evaluates to true; the
//     successors are the defined results of the applicable rules of the least priority; a rule
//     whose result is undefined still blocks the rules of larger priority;
//   - a configuration is final when no rule applies to it; one to which rules apply but all
//     with undefined results has no successor and is not final (the path is undefined);
//   - matching is syntactic up to injections: inj{A,B}(P) matches inj{C,B}(V) where C = A, with P
//     against V, or C < A in the reflexive-transitive closure of the stated subsorts, with P
//     against inj{C,A}(V); a variable seen twice must be bound to equal values; an as-pattern
//     \and(P, V) matches what P matches and binds V to it;
//   - inj{A,B}(inj{C,A}(V)) is inj{C,B}(V);
//   - hooks are strict: an undefined operand makes the operation undefined; /Int and %Int are
//     undefined on a zero divisor.

module KORE-SYNTAX
  imports INT-SYNTAX
  imports BOOL-SYNTAX

  syntax Term ::= ap(Int, Ts)          // a symbol applied to arguments
                | iv(Int)              // \dv{SortInt{}}
                | bv(Bool)             // \dv{SortBool{}}
                | ij(Int, Int, Term)   // inj{From, To}(T)
                | vr(Int)              // a variable of an axiom
                | as(Term, Int)        // \and(P, V) in a left side: P, its value also bound to V
                | hk(Int, Ts)          // a hooked symbol, by operation code
                | "bot"                // \bottom{S}()
  syntax Ts ::= ".Ts" | Term ";" Ts

  syntax Subs ::= ".Subs" | sub(Int, Int, Subs)                       // subsort{A, B}: A < B
  syntax Clauses ::= ".Cls" | cl(Int, Bool, Ts, Term, Term, Clauses)  // priority, owise, arguments, requires, right side
  syntax Fns ::= ".Fns" | fn(Int, Clauses, Fns)                        // a function symbol and its equations
  syntax Rules ::= ".Rules" | rl(Int, Bool, Term, Term, Term, Rules)   // priority, owise, left side, requires, right side
  syntax Def ::= def(Subs, Fns, Rules)
  syntax Pgm ::= pgm(Def, Term)
endmodule

module KORE
  imports KORE-SYNTAX
  imports INT
  imports BOOL
  imports K-EQUAL

  configuration <k> $PGM:Pgm </k>

  // ---------------------------------------------------------------- search
  syntax State ::= start(Def, Term)
                 | run(Def, Ts, Ts, Ts)              // frontier, seen, finals
                 | visit(Def, Term, Step, Ts, Ts, Ts)  // configuration, its step, frontier, seen, finals
                 | push(Def, Ts, Ts, Ts, Ts)         // successors to push, frontier, seen, finals
                 | done(Ts)

  rule [init]: pgm(D, T) => start(D, eval(D, T))
  rule [init-bot]: start(_, bot) => done(.Ts)
  rule [init-ok]: start(D, T) => run(D, T ; .Ts, T ; .Ts, .Ts) requires T =/=K bot
  rule [run-done]: run(_, .Ts, _, F) => done(F)
  rule [run-next]: run(D, T ; Fr, Seen, F) => visit(D, T, succs(D, T), Fr, Seen, F)
  rule [visit-final]: visit(D, T, stuck, Fr, Seen, F) => run(D, Fr, Seen, insert(T, F))
  rule [visit-step]: visit(D, _, next(Ss), Fr, Seen, F) => push(D, Ss, Fr, Seen, F)
  rule [push-done]: push(D, .Ts, Fr, Seen, F) => run(D, Fr, Seen, F)
  rule [push-new]: push(D, S ; Ss, Fr, Seen, F) => push(D, Ss, S ; Fr, insert(S, Seen), F)
    requires notBool member(S, Seen)
  rule [push-seen]: push(D, S ; Ss, Fr, Seen, F) => push(D, Ss, Fr, Seen, F)
    requires member(S, Seen)

  // ---------------------------------------------------------------- rewrite rules
  syntax Res ::= "none" | some(Term)
  syntax Cands ::= ".Cands" | cand(Int, Term, Cands)   // an applicable rule's priority and result

  syntax Step ::= "stuck" | next(Ts)   // no rule applies; the successors
  syntax Step ::= succs(Def, Term) [function]
  rule [succs]: succs(def(S, Fs, Rs), T) => pick(cands(def(S, Fs, Rs), Rs, T))

  syntax Cands ::= cands(Def, Rules, Term) [function]
  rule [cands-nil]: cands(_, .Rules, _) => .Cands
  rule [cands-cons]: cands(D, rl(P, O, L, R, Rhs, Rs), T) => addCand(prio(P, O), fire(D, L, R, Rhs, T), cands(D, Rs, T))

  syntax Int ::= prio(Int, Bool) [function]
  rule [prio-owise]: prio(_, true) => 200
  rule [prio-given]: prio(P, false) => P

  syntax Res ::= fire(Def, Term, Term, Term, Term) [function]
  rule [fire]: fire(D, L, R, Rhs, T) => fireM(D, R, Rhs, match(L, T, .Bind, subsOf(D)))
  syntax Res ::= fireM(Def, Term, Term, MRes) [function]
  rule [fire-nomatch]: fireM(_, _, _, fail) => none
  rule [fire-holds]: fireM(D, R, Rhs, ok(B)) => some(eval(D, inst(Rhs, B)))
    requires eval(D, inst(R, B)) ==K bv(true)
  rule [fire-refuted]: fireM(D, R, _, ok(B)) => none
    requires eval(D, inst(R, B)) =/=K bv(true)

  syntax Cands ::= addCand(Int, Res, Cands) [function]
  rule [add-none]: addCand(_, none, Cs) => Cs
  rule [add-some]: addCand(P, some(T), Cs) => cand(P, T, Cs)

  syntax Step ::= pick(Cands) [function]
  rule [pick-none]: pick(.Cands) => stuck
  rule [pick]: pick(cand(P, T, Cs)) => next(keep(minPrio(cand(P, T, Cs)), cand(P, T, Cs)))

  syntax Int ::= minPrio(Cands) [function]
  rule [min-nil]: minPrio(.Cands) => 1000000
  rule [min-cons]: minPrio(cand(P, _, Cs)) => lesser(P, minPrio(Cs))
  syntax Int ::= lesser(Int, Int) [function]
  rule [lesser-left]: lesser(P, Q) => P requires P <=Int Q
  rule [lesser-right]: lesser(P, Q) => Q requires P >Int Q

  syntax Ts ::= keep(Int, Cands) [function]
  rule [keep-nil]: keep(_, .Cands) => .Ts
  rule [keep-take]: keep(P, cand(Q, T, Cs)) => T ; keep(P, Cs)
    requires Q ==Int P andBool T =/=K bot
  rule [keep-skip]: keep(P, cand(Q, T, Cs)) => keep(P, Cs)
    requires Q =/=Int P orBool T ==K bot

  // ---------------------------------------------------------------- evaluation
  syntax Term ::= eval(Def, Term) [function]
  rule [ev-int]: eval(_, iv(I)) => iv(I)
  rule [ev-bool]: eval(_, bv(B)) => bv(B)
  rule [ev-inj]: eval(D, ij(A, B, T)) => mkInj(A, B, eval(D, T))
  rule [ev-app]: eval(D, ap(F, As)) => apply(D, F, evalTs(D, As))
  rule [ev-hook]: eval(D, hk(O, As)) => strictHook(O, evalTs(D, As))

  syntax Ts ::= evalTs(Def, Ts) [function]
  rule [evs-nil]: evalTs(_, .Ts) => .Ts
  rule [evs-cons]: evalTs(D, T ; Ts) => eval(D, T) ; evalTs(D, Ts)

  syntax Bool ::= hasBot(Ts) [function]
  rule [hasbot-nil]: hasBot(.Ts) => false
  rule [hasbot-cons]: hasBot(T ; Ts) => T ==K bot orBool hasBot(Ts)

  syntax Term ::= mkInj(Int, Int, Term) [function]
  rule [inj-bot]: mkInj(_, _, bot) => bot
  rule [inj-compose]: mkInj(_, B, ij(C, _, T)) => ij(C, B, T)
  rule [inj-new]: mkInj(A, B, T) => ij(A, B, T) [owise]

  syntax Look ::= "nofn" | fnd(Clauses)
  syntax Look ::= lookup(Int, Fns) [function]
  rule [lookup-nil]: lookup(_, .Fns) => nofn
  rule [lookup-hit]: lookup(F, fn(G, Cs, _)) => fnd(Cs) requires F ==Int G
  rule [lookup-miss]: lookup(F, fn(G, _, Fs)) => lookup(F, Fs) requires F =/=Int G

  syntax Term ::= apply(Def, Int, Ts) [function]
  rule [apply-bot]: apply(_, _, As) => bot requires hasBot(As)
  rule [apply-look]: apply(def(S, Fs, Rs), F, As) => applyL(def(S, Fs, Rs), F, As, lookup(F, Fs))
    requires notBool hasBot(As)
  syntax Term ::= applyL(Def, Int, Ts, Look) [function]
  rule [apply-ctor]: applyL(_, F, As, nofn) => ap(F, As)
  rule [apply-fn]: applyL(D, F, As, fnd(Cs)) => result(F, As, bestCl(D, As, Cs, 1000000, none))

  syntax Term ::= result(Int, Ts, Res) [function]
  rule [result-some]: result(_, _, some(T)) => T
  rule [result-none]: result(F, As, none) => ap(F, As)

  // the applicable equation of least priority (the first one of that priority)
  syntax Res ::= bestCl(Def, Ts, Clauses, Int, Res) [function]
  rule [best-nil]: bestCl(_, _, .Cls, _, R) => R
  rule [best-cons]: bestCl(D, As, cl(P, O, Ps, Req, Rhs, Cs), Best, R)
    => bestCl2(D, As, Cs, Best, R, prio(P, O), tryCl(D, Ps, Req, Rhs, As))
  syntax Res ::= bestCl2(Def, Ts, Clauses, Int, Res, Int, Res) [function]
  rule [best-better]: bestCl2(D, As, Cs, Best, _, P, some(T)) => bestCl(D, As, Cs, P, some(T))
    requires P <Int Best
  rule [best-worse]: bestCl2(D, As, Cs, Best, R, P, some(_)) => bestCl(D, As, Cs, Best, R)
    requires P >=Int Best
  rule [best-none]: bestCl2(D, As, Cs, Best, R, _, none) => bestCl(D, As, Cs, Best, R)

  syntax Res ::= tryCl(Def, Ts, Term, Term, Ts) [function]
  rule [try]: tryCl(D, Ps, Req, Rhs, As) => tryM(D, Req, Rhs, matchTs(Ps, As, .Bind, subsOf(D)))
  syntax Res ::= tryM(Def, Term, Term, MRes) [function]
  rule [try-nomatch]: tryM(_, _, _, fail) => none
  rule [try-holds]: tryM(D, Req, Rhs, ok(B)) => some(eval(D, inst(Rhs, B)))
    requires eval(D, inst(Req, B)) ==K bv(true)
  rule [try-refuted]: tryM(D, Req, _, ok(B)) => none
    requires eval(D, inst(Req, B)) =/=K bv(true)

  syntax Subs ::= subsOf(Def) [function]
  rule [subs-of]: subsOf(def(S, _, _)) => S

  // ---------------------------------------------------------------- matching
  syntax Bind ::= ".Bind" | bind(Int, Term, Bind)
  syntax MRes ::= "fail" | ok(Bind)

  syntax MRes ::= match(Term, Term, Bind, Subs) [function]
  rule [m-var]: match(vr(X), T, B, _) => bindVar(X, T, B, look(X, B))
  rule [m-int]: match(iv(I), iv(J), B, _) => ok(B) requires I ==Int J
  rule [m-bool]: match(bv(X), bv(Y), B, _) => ok(B) requires X ==Bool Y
  rule [m-app]: match(ap(F, Ps), ap(G, Ts), B, S) => matchTs(Ps, Ts, B, S) requires F ==Int G
  rule [m-inj-same]: match(ij(A, _, P), ij(C, _, T), B, S) => match(P, T, B, S) requires A ==Int C
  rule [m-inj-sub]: match(ij(A, _, P), ij(C, _, T), B, S) => match(P, ij(C, A, T), B, S)
    requires A =/=Int C andBool leq(C, A, S)
  rule [m-as]: match(as(P, X), T, B, S) => bindAfter(X, T, match(P, T, B, S))
  rule [m-fail]: match(_, _, _, _) => fail [owise]
  syntax MRes ::= bindAfter(Int, Term, MRes) [function]
  rule [as-fail]: bindAfter(_, _, fail) => fail
  rule [as-bind]: bindAfter(X, T, ok(B)) => bindVar(X, T, B, look(X, B))

  syntax MRes ::= matchTs(Ts, Ts, Bind, Subs) [function]
  rule [ms-nil]: matchTs(.Ts, .Ts, B, _) => ok(B)
  rule [ms-cons]: matchTs(P ; Ps, T ; Ts, B, S) => matchK(match(P, T, B, S), Ps, Ts, S)
  syntax MRes ::= matchK(MRes, Ts, Ts, Subs) [function]
  rule [mk-fail]: matchK(fail, _, _, _) => fail
  rule [mk-ok]: matchK(ok(B), Ps, Ts, S) => matchTs(Ps, Ts, B, S)

  syntax Res ::= look(Int, Bind) [function]
  rule [look-nil]: look(_, .Bind) => none
  rule [look-hit]: look(X, bind(Y, T, _)) => some(T) requires X ==Int Y
  rule [look-miss]: look(X, bind(Y, _, B)) => look(X, B) requires X =/=Int Y

  syntax MRes ::= bindVar(Int, Term, Bind, Res) [function]
  rule [bind-new]: bindVar(X, T, B, none) => ok(bind(X, T, B))
  rule [bind-same]: bindVar(_, T, B, some(U)) => ok(B) requires T ==K U
  rule [bind-clash]: bindVar(_, T, _, some(U)) => fail requires T =/=K U

  // A < B in the reflexive-transitive closure of the stated subsorts
  syntax Bool ::= leq(Int, Int, Subs) [function]
  rule [leq-refl]: leq(A, B, _) => true requires A ==Int B
  rule [leq-up]: leq(A, B, S) => above(A, B, S, S) requires A =/=Int B
  syntax Bool ::= above(Int, Int, Subs, Subs) [function]
  rule [above-nil]: above(_, _, .Subs, _) => false
  rule [above-hit]: above(A, B, sub(X, Y, Rest), All) => leq(Y, B, All) orBool above(A, B, Rest, All)
    requires X ==Int A
  rule [above-miss]: above(A, B, sub(X, _, Rest), All) => above(A, B, Rest, All)
    requires X =/=Int A

  syntax Term ::= inst(Term, Bind) [function]
  rule [inst-var]: inst(vr(X), B) => valOf(look(X, B))
  rule [inst-app]: inst(ap(F, Ts), B) => ap(F, instTs(Ts, B))
  rule [inst-hook]: inst(hk(O, Ts), B) => hk(O, instTs(Ts, B))
  rule [inst-inj]: inst(ij(A, C, T), B) => ij(A, C, inst(T, B))
  rule [inst-int]: inst(iv(I), _) => iv(I)
  rule [inst-bool]: inst(bv(X), _) => bv(X)
  syntax Ts ::= instTs(Ts, Bind) [function]
  rule [insts-nil]: instTs(.Ts, _) => .Ts
  rule [insts-cons]: instTs(T ; Ts, B) => inst(T, B) ; instTs(Ts, B)
  syntax Term ::= valOf(Res) [function]
  rule [val-of]: valOf(some(T)) => T

  // ---------------------------------------------------------------- hooks
  // 1 +Int, 2 -Int, 3 *Int, 4 /Int, 5 %Int, 10 <Int, 11 <=Int, 12 >Int, 13 >=Int, 14 ==Int,
  // 15 =/=Int, 20 andBool, 21 orBool, 22 notBool, 30 #if_#then_#else_#fi
  syntax Term ::= strictHook(Int, Ts) [function]
  rule [hook-bot]: strictHook(_, As) => bot requires hasBot(As)
  rule [hook-def]: strictHook(O, As) => hookOp(O, As) requires notBool hasBot(As)

  syntax Term ::= hookOp(Int, Ts) [function]
  rule [op-add]: hookOp(1, iv(X) ; iv(Y) ; .Ts) => iv(X +Int Y)
  rule [op-sub]: hookOp(2, iv(X) ; iv(Y) ; .Ts) => iv(X -Int Y)
  rule [op-mul]: hookOp(3, iv(X) ; iv(Y) ; .Ts) => iv(X *Int Y)
  rule [op-div]: hookOp(4, iv(X) ; iv(Y) ; .Ts) => iv(X /Int Y) requires Y =/=Int 0
  rule [op-mod]: hookOp(5, iv(X) ; iv(Y) ; .Ts) => iv(X %Int Y) requires Y =/=Int 0
  rule [op-lt]: hookOp(10, iv(X) ; iv(Y) ; .Ts) => bv(X <Int Y)
  rule [op-le]: hookOp(11, iv(X) ; iv(Y) ; .Ts) => bv(X <=Int Y)
  rule [op-gt]: hookOp(12, iv(X) ; iv(Y) ; .Ts) => bv(X >Int Y)
  rule [op-ge]: hookOp(13, iv(X) ; iv(Y) ; .Ts) => bv(X >=Int Y)
  rule [op-eq]: hookOp(14, iv(X) ; iv(Y) ; .Ts) => bv(X ==Int Y)
  rule [op-ne]: hookOp(15, iv(X) ; iv(Y) ; .Ts) => bv(X =/=Int Y)
  rule [op-and]: hookOp(20, bv(X) ; bv(Y) ; .Ts) => bv(X andBool Y)
  rule [op-or]: hookOp(21, bv(X) ; bv(Y) ; .Ts) => bv(X orBool Y)
  rule [op-not]: hookOp(22, bv(X) ; .Ts) => bv(notBool X)
  rule [op-ite-then]: hookOp(30, bv(C) ; T ; _ ; .Ts) => T requires C
  rule [op-ite-else]: hookOp(30, bv(C) ; _ ; E ; .Ts) => E requires notBool C
  rule [op-undef]: hookOp(_, _) => bot [owise]

  // ---------------------------------------------------------------- a total order on values
  syntax Int ::= cmp(Term, Term) [function]
  rule [cmp-int]: cmp(iv(X), iv(Y)) => cmpI(X, Y)
  rule [cmp-bool]: cmp(bv(X), bv(Y)) => cmpI(b2i(X), b2i(Y))
  rule [cmp-app]: cmp(ap(F, As), ap(G, Bs)) => lex(cmpI(F, G), cmpTs(As, Bs))
  rule [cmp-inj]: cmp(ij(A, B, T), ij(C, E, U)) => lex(cmpI(A, C), lex(cmpI(B, E), cmp(T, U)))
  rule [cmp-tag]: cmp(T, U) => cmpI(tag(T), tag(U)) [owise]
  syntax Int ::= cmpTs(Ts, Ts) [function]
  rule [cmps-nil]: cmpTs(.Ts, .Ts) => 0
  rule [cmps-short]: cmpTs(.Ts, _ ; _) => -1
  rule [cmps-long]: cmpTs(_ ; _, .Ts) => 1
  rule [cmps-cons]: cmpTs(T ; Ts, U ; Us) => lex(cmp(T, U), cmpTs(Ts, Us))
  syntax Int ::= cmpI(Int, Int) [function]
  rule [cmpi-lt]: cmpI(X, Y) => -1 requires X <Int Y
  rule [cmpi-eq]: cmpI(X, Y) => 0 requires X ==Int Y
  rule [cmpi-gt]: cmpI(X, Y) => 1 requires X >Int Y
  syntax Int ::= lex(Int, Int) [function]
  rule [lex-tie]: lex(X, Y) => Y requires X ==Int 0
  rule [lex-first]: lex(X, _) => X requires X =/=Int 0
  syntax Int ::= b2i(Bool) [function]
  rule [b2i-true]: b2i(true) => 1
  rule [b2i-false]: b2i(false) => 0
  syntax Int ::= tag(Term) [function]
  rule [tag-int]: tag(iv(_)) => 0
  rule [tag-bool]: tag(bv(_)) => 1
  rule [tag-app]: tag(ap(_, _)) => 2
  rule [tag-inj]: tag(ij(_, _, _)) => 3
  rule [tag-other]: tag(_) => 4 [owise]

  syntax Ts ::= insert(Term, Ts) [function]
  rule [ins-nil]: insert(T, .Ts) => T ; .Ts
  rule [ins-before]: insert(T, U ; Us) => T ; U ; Us requires cmp(T, U) <Int 0
  rule [ins-dup]: insert(T, U ; Us) => U ; Us requires cmp(T, U) ==Int 0
  rule [ins-after]: insert(T, U ; Us) => U ; insert(T, Us) requires cmp(T, U) >Int 0

  syntax Bool ::= member(Term, Ts) [function]
  rule [mem-nil]: member(_, .Ts) => false
  rule [mem-cons]: member(T, U ; Us) => cmp(T, U) ==Int 0 orBool member(T, Us)
endmodule
