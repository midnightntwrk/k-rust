// kk.k: the text of krs/semantics/kore/kore.k as it stands at k-rust commit de05a5c619dddfb60c510e85109d16e1a62e585b, with this line added
// kore.k: an interpreter, written in K, of a fragment of KORE as kompile writes it.
//
// A program is pgm(D, T): D an encoded object definition (its subsorts, its functions with their
// equations, its rewrite rules) and T an encoded initial term of its single configuration cell.
// The result is done(Fs): every configuration reachable from T that has no successor, sorted by
// `cmp` and without repetition, which is what a search for all final configurations returns.
// Symbols and sorts are numbers given by the encoder (tools/korek.py); hooked symbols of INT,
// BOOL, KEQUAL and the collections are operation codes (`hookOp`). A configuration of several
// cells is the application of its top cell's constructor, a cell collection a Map.
//
// Reading of KORE implemented here:
//   - a function application is evaluated innermost: arguments first; an undefined argument
//     (\bottom) makes the application undefined; a constructor application is a value;
//   - an equation applies when its argument patterns match and its requires evaluates to true;
//     among the applicable equations one of the least priority gives the result (an [owise]
//     equation has priority 200, an equation without priority 50); an application no equation
//     applies to is given no value here (bot): the equations leave it open, and this interpreter
//     is the member of KCore's family whose interpretation gives nothing (HookParams.none), not
//     the text's meaning for every interpretation; a function declared total is read the same,
//     so at such a point the result is outside what the text admits;
//   - a rewrite rule applies when its left side matches and its requires evaluates to true; the
//     successors are the defined results of the applicable rules of the least priority; a rule
//     whose result is undefined still blocks the rules of larger priority;
//   - equations and rules are tried by ascending priority, the first equation of a priority in
//     the order of the text: one of a larger priority applies only where none of a smaller one
//     does, so its requires and right side are evaluated only there (a requires or right side
//     without a value at a larger priority does not affect a result decided at a smaller one);
//   - a configuration is final when no rule applies to it; one to which rules apply but all
//     with undefined results has no successor and is not final (the path is undefined);
//   - a rule's ensures is part of its result: r ensures E is r where E evaluates to true and
//     undefined (an empty result) otherwise, so a rule whose ensures is false has applied and
//     blocks the rules of larger priority as one with an undefined right side does;
//   - an equation's ensures is part of its right side in the same way (kompile writes
//     f(P) = \and(r, E = true)): where the equation applies and E is not true the application
//     has no value; the ensures does not decide whether the equation applies, so an equation of
//     larger priority or an [owise] one does not apply there;
//   - matching is syntactic up to injections: inj{A,B}(P) matches inj{C,B}(V) where C = A, with P
//     against V, or C < A in the reflexive-transitive closure of the stated subsorts, with P
//     against inj{C,A}(V); a variable seen twice must be bound to equal values; an as-pattern
//     \and(P, V) matches what P matches and binds V to it;
//   - inj{A,B}(inj{C,A}(V)) is inj{C,B}(V);
//   - hooks are strict: an undefined operand makes the operation undefined; /Int and %Int are
//     undefined on a zero divisor;
//   - ==K and =/=K compare two values: equal values are equal terms, since a value's injections
//     are composed and its collections canonical; a domain value of a token sort is a value of
//     that sort, so tokens of two sorts with one text differ;
//   - a domain value of String is a value of that sort, its text; ==String is the equality of
//     texts and <String their lexicographic order, ==Bool the equality of Bool values;
//   - a Map is a finite map, a Set a finite set, a List a finite sequence; a value of each is
//     canonical (a map's entries ordered by key and a set's elements by value, without
//     repetition), so that equal collections are equal terms. Map and Set concatenation are
//     partial: defined on disjoint keys (elements), undefined where they overlap; List
//     concatenation is total, associative and not commutative. A missing key makes a lookup
//     undefined;
//   - a collection pattern of elements and at most one frame variable matches every split of
//     its subject: each element pattern any element (for a List: the element at its position),
//     the frame the rest. Matching therefore gives a set of substitutions; a rewrite rule gives
//     one result per substitution whose requires holds, and an equation the result of one such
//     substitution (on a consistent definition they agree).

module KORE-SYNTAX
  imports INT-SYNTAX
  imports BOOL-SYNTAX
  imports STRING-SYNTAX

  syntax Term ::= ap(Int, Ts)          // a symbol applied to arguments
                | iv(Int)              // \dv{SortInt{}}
                | bv(Bool)             // \dv{SortBool{}}
                | tk(Int, String)      // \dv{S}(Text) of a token sort S
                | ij(Int, Int, Term)   // inj{From, To}(T)
                | vr(Int)              // a variable of an axiom
                | as(Term, Int)        // \and(P, V) in a left side: P, its value also bound to V
                | hk(Int, Ts)          // a hooked symbol, by operation code
                | "bot"                // \bottom{S}()
                | cb(Kind, Int, Ts)    // a collection of sort Int built by its concatenation, unit
                                       // and element symbols from parts: elements, and terms of
                                       // the collection's sort
                | co(Kind, Int, Ts)    // a collection value: its elements, canonical (below)
                | en(Term, Term)       // a rule's or an equation's right side and its ensures
                | kv(Term, Term)       // the element K |-> V of a map
                | el(Term)             // the element of a set or a list
  syntax Kind ::= "map" | "set" | "list"
  syntax Ts ::= ".Ts" | Term ";" Ts

  syntax Subs ::= ".Subs" | sub(Int, Int, Subs)                       // subsort{A, B}: A < B
  syntax Clauses ::= ".Cls" | cl(Int, Bool, Ts, Term, Term, Clauses)  // priority, owise, arguments, requires, right side (en(R, E) with an ensures)
  syntax Fns ::= ".Fns" | fn(Int, Clauses, Fns)                        // a function symbol and its equations
  syntax Rules ::= ".Rules" | rl(Int, Bool, Term, Term, Term, Rules)   // priority, owise, left side, requires, right side
  syntax Def ::= def(Subs, Fns, Rules)
  syntax Pgm ::= pgm(Def, Term)
endmodule

module KORE
  imports KORE-SYNTAX
  imports INT
  imports BOOL
  imports STRING
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
  // Priorities are walked in ascending order. A rule applies only where no rule of a smaller
  // priority does, so the rules of a priority are tried only where none of a smaller priority
  // applies; where one does, no requires or right side of a larger priority is evaluated, and a
  // larger priority could only have removed results.
  syntax Res ::= "none" | some(Term)
  syntax Prio ::= "noP" | at(Int)   // no priority; a priority

  syntax Step ::= "stuck" | next(Ts)   // no rule applies; the successors
  syntax Step ::= succs(Def, Term) [function]
  rule [succs]: succs(def(S, Fs, Rs), T) => stepAt(def(S, Fs, Rs), Rs, T, nextRl(Rs, noP))

  // at priority P: the results of the rules of P, else the next priority, else no rule applies
  syntax Step ::= stepAt(Def, Rules, Term, Prio) [function]
  rule [step-none]: stepAt(_, _, _, noP) => stuck
  rule [step-at]: stepAt(D, Rs, T, at(P)) => stepIf(D, Rs, T, P, fireAt(D, Rs, T, P))
  syntax Step ::= stepIf(Def, Rules, Term, Int, Ts) [function]
  rule [step-next]: stepIf(D, Rs, T, P, .Ts) => stepAt(D, Rs, T, nextRl(Rs, at(P)))
  // rules of P apply: their defined results are the successors; an undefined result is no
  // successor and still blocks the larger priorities
  rule [step-some]: stepIf(_, _, _, _, R ; Rs) => next(drop(bot, R ; Rs))

  // the results of the rules of priority P, in the order of the text
  syntax Ts ::= fireAt(Def, Rules, Term, Int) [function]
  rule [fa-nil]: fireAt(_, .Rules, _, _) => .Ts
  rule [fa-take]: fireAt(D, rl(Q, O, L, R, Rhs, Rs), T, P) => app(fire(D, L, R, Rhs, T), fireAt(D, Rs, T, P))
    requires rprio(Q, O) ==Int P
  rule [fa-skip]: fireAt(D, rl(Q, O, _, _, _, Rs), T, P) => fireAt(D, Rs, T, P)
    requires rprio(Q, O) =/=Int P

  // the least priority of the rules (equations) above the bound, noP when there is none
  syntax Prio ::= nextRl(Rules, Prio) [function]
  rule [nrl-nil]: nextRl(.Rules, _) => noP
  rule [nrl-cons]: nextRl(rl(Q, O, _, _, _, Rs), B) => least(over(rprio(Q, O), B), nextRl(Rs, B))
  syntax Prio ::= nextCl(Clauses, Prio) [function]
  rule [ncl-nil]: nextCl(.Cls, _) => noP
  rule [ncl-cons]: nextCl(cl(Q, O, _, _, _, Cs), B) => least(over(cprio(Q, O), B), nextCl(Cs, B))
  syntax Prio ::= over(Int, Prio) [function]   // the priority if it is above the bound
  rule [over-free]: over(P, noP) => at(P)
  rule [over-above]: over(P, at(B)) => at(P) requires P >Int B
  rule [over-below]: over(P, at(B)) => noP requires P <=Int B
  syntax Prio ::= least(Prio, Prio) [function]
  rule [least-none]: least(noP, Q) => Q
  rule [least-only]: least(at(P), noP) => at(P)
  rule [least-left]: least(at(P), at(Q)) => at(P) requires P <=Int Q
  rule [least-right]: least(at(P), at(Q)) => at(Q) requires P >Int Q

  syntax Int ::= prio(Int, Bool) [function]
  rule [prio-owise]: prio(_, true) => 200
  rule [prio-given]: prio(P, false) => P
  syntax Int ::= rprio(Int, Bool) [function]   // a rule's priority
  rule [rprio]: rprio(P, O) => prio(P, O)
  syntax Int ::= cprio(Int, Bool) [function]   // an equation's priority
  rule [cprio]: cprio(P, O) => prio(P, O)

  // the results of a rule: one for each substitution of its left side whose requires holds
  syntax Ts ::= fire(Def, Term, Term, Term, Term) [function]
  rule [fire]: fire(D, L, R, Rhs, T) => fireM(D, R, Rhs, match(L, T, .Bind, subsOf(D)))
  syntax Ts ::= fireM(Def, Term, Term, Ms) [function]
  rule [fire-nomatch]: fireM(_, _, _, .Ms) => .Ts
  rule [fire-holds]: fireM(D, R, Rhs, m(B, Ms)) => eval(D, inst(Rhs, B)) ; fireM(D, R, Rhs, Ms)
    requires eval(D, inst(R, B)) ==K bv(true)
  rule [fire-refuted]: fireM(D, R, Rhs, m(B, Ms)) => fireM(D, R, Rhs, Ms)
    requires eval(D, inst(R, B)) =/=K bv(true)

  // the list without the elements equal to the term
  syntax Ts ::= drop(Term, Ts) [function]
  rule [drop-nil]: drop(_, .Ts) => .Ts
  rule [drop-keep]: drop(X, T ; Ts) => T ; drop(X, Ts) requires T =/=K X
  rule [drop-hit]: drop(X, T ; Ts) => drop(X, Ts) requires T ==K X

  // ---------------------------------------------------------------- evaluation
  syntax Term ::= eval(Def, Term) [function]
  rule [ev-int]: eval(_, iv(I)) => iv(I)
  rule [ev-bool]: eval(_, bv(B)) => bv(B)
  rule [ev-tok]: eval(_, tk(S, X)) => tk(S, X)
  rule [ev-inj]: eval(D, ij(A, B, T)) => mkInj(A, B, eval(D, T))
  rule [ev-app]: eval(D, ap(F, As)) => apply(D, F, evalTs(D, As))
  rule [ev-hook]: eval(D, hk(O, As)) => strictHook(O, evalTs(D, As))
  rule [ev-col]: eval(D, cb(K, C, Ps)) => colOf(K, C, evalTs(D, Ps))
  rule [ev-kv]: eval(D, kv(A, V)) => mkKv(eval(D, A), eval(D, V))
  rule [ev-el]: eval(D, el(X)) => mkEl(eval(D, X))
  rule [ev-val]: eval(_, co(K, C, Es)) => co(K, C, Es)
  rule [ev-en]: eval(D, en(T, E)) => ensure(eval(D, E), eval(D, T))

  syntax Term ::= ensure(Term, Term) [function]
  rule [ensure-holds]: ensure(bv(true), T) => T
  rule [ensure-fails]: ensure(_, _) => bot [owise]

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
  rule [apply-fn]: applyL(D, F, As, fnd(Cs)) => result(F, As, evalAt(D, As, Cs, nextCl(Cs, noP)))

  syntax Term ::= result(Int, Ts, Res) [function]
  rule [result-some]: result(_, _, some(T)) => T
  rule [result-none]: result(_, _, none) => bot

  // Equations by ascending priority, as rules are: at priority P the first equation of P that
  // applies gives the result, else the next priority. An equation applies only where none of a
  // smaller priority does, so one of a larger priority is not evaluated where one of P applies.
  syntax Res ::= evalAt(Def, Ts, Clauses, Prio) [function]
  rule [ea-none]: evalAt(_, _, _, noP) => none
  rule [ea-at]: evalAt(D, As, Cs, at(P)) => evalIf(D, As, Cs, P, tryAt(D, As, Cs, P))
  syntax Res ::= evalIf(Def, Ts, Clauses, Int, Res) [function]
  rule [ei-some]: evalIf(_, _, _, _, some(T)) => some(T)
  rule [ei-next]: evalIf(D, As, Cs, P, none) => evalAt(D, As, Cs, nextCl(Cs, at(P)))

  // the result of the first equation of priority P that applies, in the order of the text
  syntax Res ::= tryAt(Def, Ts, Clauses, Int) [function]
  rule [ta-nil]: tryAt(_, _, .Cls, _) => none
  rule [ta-take]: tryAt(D, As, cl(Q, O, Ps, Req, Rhs, Cs), P) => orElse(tryCl(D, Ps, Req, Rhs, As), D, As, Cs, P)
    requires cprio(Q, O) ==Int P
  rule [ta-skip]: tryAt(D, As, cl(Q, O, _, _, _, Cs), P) => tryAt(D, As, Cs, P)
    requires cprio(Q, O) =/=Int P
  syntax Res ::= orElse(Res, Def, Ts, Clauses, Int) [function]
  rule [else-some]: orElse(some(T), _, _, _, _) => some(T)
  rule [else-none]: orElse(none, D, As, Cs, P) => tryAt(D, As, Cs, P)

  syntax Res ::= tryCl(Def, Ts, Term, Term, Ts) [function]
  rule [try]: tryCl(D, Ps, Req, Rhs, As) => tryM(D, Req, Rhs, matchTs(Ps, As, .Bind, subsOf(D)))
  // the first substitution whose requires holds gives the equation's result
  syntax Res ::= tryM(Def, Term, Term, Ms) [function]
  rule [try-nomatch]: tryM(_, _, _, .Ms) => none
  rule [try-holds]: tryM(D, Req, Rhs, m(B, _)) => some(eval(D, inst(Rhs, B)))
    requires eval(D, inst(Req, B)) ==K bv(true)
  rule [try-refuted]: tryM(D, Req, Rhs, m(B, Ms)) => tryM(D, Req, Rhs, Ms)
    requires eval(D, inst(Req, B)) =/=K bv(true)

  syntax Subs ::= subsOf(Def) [function]
  rule [subs-of]: subsOf(def(S, _, _)) => S

  // ---------------------------------------------------------------- matching
  // matching gives every substitution, in order; none when the pattern does not match
  syntax Bind ::= ".Bind" | bind(Int, Term, Bind)
  syntax Ms ::= ".Ms" | m(Bind, Ms)

  syntax Ms ::= match(Term, Term, Bind, Subs) [function]
  rule [m-var]: match(vr(X), T, B, _) => bindVar(X, T, B, look(X, B))
  rule [m-int]: match(iv(I), iv(J), B, _) => m(B, .Ms) requires I ==Int J
  rule [m-bool]: match(bv(X), bv(Y), B, _) => m(B, .Ms) requires X ==Bool Y
  rule [m-tok]: match(tk(S, X), tk(T, Y), B, _) => m(B, .Ms) requires S ==Int T andBool X ==String Y
  rule [m-app]: match(ap(F, Ps), ap(G, Ts), B, S) => matchTs(Ps, Ts, B, S) requires F ==Int G
  rule [m-inj-same]: match(ij(A, _, P), ij(C, _, T), B, S) => match(P, T, B, S) requires A ==Int C
  rule [m-inj-sub]: match(ij(A, _, P), ij(C, _, T), B, S) => match(P, ij(C, A, T), B, S)
    requires A =/=Int C andBool leq(C, A, S)
  rule [m-as]: match(as(P, X), T, B, S) => bindAfter(X, T, match(P, T, B, S))
  rule [m-col]: match(cb(K, C, Ps), co(_, _, Es), B, S) => matchCol(K, C, Ps, Es, B, S)
  rule [m-kv]: match(kv(P, Q), kv(A, V), B, S) => matchTs(P ; Q ; .Ts, A ; V ; .Ts, B, S)
  rule [m-el]: match(el(P), el(X), B, S) => match(P, X, B, S)
  rule [m-fail]: match(_, _, _, _) => .Ms [owise]
  syntax Ms ::= bindAfter(Int, Term, Ms) [function]
  rule [as-fail]: bindAfter(_, _, .Ms) => .Ms
  rule [as-bind]: bindAfter(X, T, m(B, Ms)) => cat(bindVar(X, T, B, look(X, B)), bindAfter(X, T, Ms))

  syntax Ms ::= matchTs(Ts, Ts, Bind, Subs) [function]
  rule [ms-nil]: matchTs(.Ts, .Ts, B, _) => m(B, .Ms)
  rule [ms-cons]: matchTs(P ; Ps, T ; Ts, B, S) => matchK(match(P, T, B, S), Ps, Ts, S)
  syntax Ms ::= matchK(Ms, Ts, Ts, Subs) [function]
  rule [mk-fail]: matchK(.Ms, _, _, _) => .Ms
  rule [mk-ok]: matchK(m(B, Ms), Ps, Ts, S) => cat(matchTs(Ps, Ts, B, S), matchK(Ms, Ps, Ts, S))

  syntax Ms ::= cat(Ms, Ms) [function]
  rule [cat-nil]: cat(.Ms, Ns) => Ns
  rule [cat-cons]: cat(m(B, Ms), Ns) => m(B, cat(Ms, Ns))

  // A collection pattern's parts against a value's elements. The encoder puts a Map or Set
  // pattern's element patterns before its one frame. An element pattern of a Map or Set takes
  // each element in turn (every split); a List's takes the element at its position, and a
  // List's frame followed by more parts takes each prefix in turn. A last frame takes the rest.
  syntax Ms ::= matchCol(Kind, Int, Ts, Ts, Bind, Subs) [function]
  rule [mc-done]: matchCol(_, _, .Ts, .Ts, B, _) => m(B, .Ms)
  rule [mc-choose]: matchCol(K, C, P ; Ps, Es, B, S) => choose(K, C, P, Ps, .Ts, Es, B, S)
    requires isElem(P) andBool K =/=K list
  rule [mc-head]: matchCol(list, C, P ; Ps, E ; Es, B, S) => rest(list, C, Ps, Es, match(P, E, B, S), S)
    requires isElem(P)
  rule [mc-frame]: matchCol(K, C, F ; .Ts, Es, B, S) => match(F, co(K, C, Es), B, S)
    requires notBool isElem(F)
  rule [mc-split]: matchCol(list, C, F ; P ; Ps, Es, B, S) => split(C, F, P ; Ps, .Ts, Es, B, S)
    requires notBool isElem(F)
  rule [mc-fail]: matchCol(_, _, _, _, _, _) => .Ms [owise]

  syntax Ms ::= choose(Kind, Int, Term, Ts, Ts, Ts, Bind, Subs) [function]
  rule [ch-nil]: choose(_, _, _, _, _, .Ts, _, _) => .Ms
  rule [ch-cons]: choose(K, C, P, Ps, Pre, E ; Post, B, S)
    => cat(rest(K, C, Ps, app(Pre, Post), match(P, E, B, S), S), choose(K, C, P, Ps, app(Pre, E ; .Ts), Post, B, S))

  syntax Ms ::= split(Int, Term, Ts, Ts, Ts, Bind, Subs) [function]
  rule [sp-here]: split(C, F, Ps, Pre, Post, B, S)
    => cat(rest(list, C, Ps, Post, match(F, co(list, C, Pre), B, S), S), splitOn(C, F, Ps, Pre, Post, B, S))
  syntax Ms ::= splitOn(Int, Term, Ts, Ts, Ts, Bind, Subs) [function]
  rule [sp-end]: splitOn(_, _, _, _, .Ts, _, _) => .Ms
  rule [sp-next]: splitOn(C, F, Ps, Pre, E ; Post, B, S) => split(C, F, Ps, app(Pre, E ; .Ts), Post, B, S)

  // the remaining parts against the remaining elements, under each substitution so far
  syntax Ms ::= rest(Kind, Int, Ts, Ts, Ms, Subs) [function]
  rule [rest-nil]: rest(_, _, _, _, .Ms, _) => .Ms
  rule [rest-cons]: rest(K, C, Ps, Es, m(B, Ms), S) => cat(matchCol(K, C, Ps, Es, B, S), rest(K, C, Ps, Es, Ms, S))

  syntax Bool ::= isElem(Term) [function]
  rule [elem-kv]: isElem(kv(_, _)) => true
  rule [elem-el]: isElem(el(_)) => true
  rule [elem-not]: isElem(_) => false [owise]

  syntax Res ::= look(Int, Bind) [function]
  rule [look-nil]: look(_, .Bind) => none
  rule [look-hit]: look(X, bind(Y, T, _)) => some(T) requires X ==Int Y
  rule [look-miss]: look(X, bind(Y, _, B)) => look(X, B) requires X =/=Int Y

  syntax Ms ::= bindVar(Int, Term, Bind, Res) [function]
  rule [bind-new]: bindVar(X, T, B, none) => m(bind(X, T, B), .Ms)
  rule [bind-same]: bindVar(_, T, B, some(U)) => m(B, .Ms) requires T ==K U
  rule [bind-clash]: bindVar(_, T, _, some(U)) => .Ms requires T =/=K U

  // A < B in the reflexive-transitive closure of the stated subsorts
  syntax Bool ::= leq(Int, Int, Subs) [function]
  rule [leq-refl]: leq(A, B, _) => true requires A ==Int B
  rule [leq-up]: leq(A, B, S) => above(A, B, S, S, S) requires A =/=Int B
  // above(A, B, T, All, F): an entry of T starts at A and reaches B by at most as many entries as F has
  syntax Bool ::= above(Int, Int, Subs, Subs, Subs) [function]
  rule [above-nil]: above(_, _, .Subs, _, _) => false
  rule [above-dry]: above(_, _, sub(_, _, _), _, .Subs) => false
  rule [above-hit]: above(A, B, sub(X, Y, Rest), All, sub(P, Q, F))
    => (Y ==Int B orBool above(Y, B, All, All, F)) orBool above(A, B, Rest, All, sub(P, Q, F))
    requires X ==Int A
  rule [above-miss]: above(A, B, sub(X, _, Rest), All, sub(P, Q, F)) => above(A, B, Rest, All, sub(P, Q, F))
    requires X =/=Int A

  syntax Term ::= inst(Term, Bind) [function]
  rule [inst-var]: inst(vr(X), B) => valOf(look(X, B))
  rule [inst-app]: inst(ap(F, Ts), B) => ap(F, instTs(Ts, B))
  rule [inst-hook]: inst(hk(O, Ts), B) => hk(O, instTs(Ts, B))
  rule [inst-inj]: inst(ij(A, C, T), B) => ij(A, C, inst(T, B))
  rule [inst-int]: inst(iv(I), _) => iv(I)
  rule [inst-bool]: inst(bv(X), _) => bv(X)
  rule [inst-tok]: inst(tk(S, X), _) => tk(S, X)
  rule [inst-col]: inst(cb(K, C, Ts), B) => cb(K, C, instTs(Ts, B))
  rule [inst-kv]: inst(kv(T, U), B) => kv(inst(T, B), inst(U, B))
  rule [inst-el]: inst(el(T), B) => el(inst(T, B))
  rule [inst-en]: inst(en(T, E), B) => en(inst(T, B), inst(E, B))
  syntax Ts ::= instTs(Ts, Bind) [function]
  rule [insts-nil]: instTs(.Ts, _) => .Ts
  rule [insts-cons]: instTs(T ; Ts, B) => inst(T, B) ; instTs(Ts, B)
  syntax Term ::= valOf(Res) [function]
  rule [val-of]: valOf(some(T)) => T

  // ---------------------------------------------------------------- collections
  // A value co(K, C, Es) is canonical: a map's entries kv(A, V) ordered by key and a set's
  // elements el(X) ordered by value, by `cmp`, without two of one key (value); a list's elements
  // el(X) in order. A construction cb(K, C, Ps) adds its parts' elements to the empty value one
  // by one: for a Map or a Set an element whose key (value) is already there makes the whole
  // undefined, since concatenation is defined only on disjoint collections.
  syntax Term ::= mkKv(Term, Term) [function]
  rule [kv-bot]: mkKv(A, V) => bot requires hasBot(A ; V ; .Ts)
  rule [kv-def]: mkKv(A, V) => kv(A, V) requires notBool hasBot(A ; V ; .Ts)
  syntax Term ::= mkEl(Term) [function]
  rule [el-bot]: mkEl(bot) => bot
  rule [el-def]: mkEl(X) => el(X) [owise]

  syntax Term ::= colOf(Kind, Int, Ts) [function]
  rule [col-bot]: colOf(_, _, Ps) => bot requires hasBot(Ps)
  rule [col-def]: colOf(K, C, Ps) => join(co(K, C, .Ts), Ps) requires notBool hasBot(Ps)

  // a part is an element or a value of the collection's sort, whose elements it contributes
  syntax Term ::= join(Term, Ts) [function]
  rule [join-nil]: join(V, .Ts) => V
  rule [join-bot]: join(bot, _ ; _) => bot
  rule [join-col]: join(co(K, C, Es), co(_, _, Fs) ; Ps) => join(co(K, C, Es), app(Fs, Ps))
  rule [join-list]: join(co(list, C, Es), E ; Ps) => join(co(list, C, app(Es, E ; .Ts)), Ps)
    requires isElem(E)
  rule [join-elem]: join(co(K, C, Es), E ; Ps) => join(mkCol(K, C, insE(K, E, Es)), Ps)
    requires isElem(E) andBool K =/=K list

  syntax Term ::= mkCol(Kind, Int, Ts) [function]
  rule [mkcol-bot]: mkCol(_, _, Es) => bot requires hasBot(Es)
  rule [mkcol-def]: mkCol(K, C, Es) => co(K, C, Es) requires notBool hasBot(Es)

  // insert an element by its key; bot marks an element whose key is already there
  syntax Ts ::= insE(Kind, Term, Ts) [function]
  rule [inse-nil]: insE(_, E, .Ts) => E ; .Ts
  rule [inse-before]: insE(_, E, F ; Fs) => E ; F ; Fs requires ckey(E, F) <Int 0
  rule [inse-overlap]: insE(_, E, F ; Fs) => bot ; F ; Fs requires ckey(E, F) ==Int 0
  rule [inse-after]: insE(K, E, F ; Fs) => F ; insE(K, E, Fs) requires ckey(E, F) >Int 0

  // insert or replace an element by its key (Map update, Set union)
  syntax Ts ::= putE(Term, Ts) [function]
  rule [pute-nil]: putE(E, .Ts) => E ; .Ts
  rule [pute-before]: putE(E, F ; Fs) => E ; F ; Fs requires ckey(E, F) <Int 0
  rule [pute-replace]: putE(E, F ; Fs) => E ; Fs requires ckey(E, F) ==Int 0
  rule [pute-after]: putE(E, F ; Fs) => F ; putE(E, Fs) requires ckey(E, F) >Int 0

  // remove the element of a key, if there is one
  syntax Ts ::= delE(Term, Ts) [function]
  rule [dele-nil]: delE(_, .Ts) => .Ts
  rule [dele-hit]: delE(E, F ; Fs) => Fs requires ckey(E, F) ==Int 0
  rule [dele-miss]: delE(E, F ; Fs) => F ; delE(E, Fs) requires ckey(E, F) =/=Int 0

  // the value of a key, or the given default when the key is missing
  syntax Term ::= valueOr(Term, Term, Ts) [function]
  rule [at-missing]: valueOr(_, V, .Ts) => V
  rule [at-hit]: valueOr(A, _, kv(A2, V) ; _) => V requires cmp(A, A2) ==Int 0
  rule [at-miss]: valueOr(A, V, kv(A2, _) ; Es) => valueOr(A, V, Es) requires cmp(A, A2) =/=Int 0

  syntax Bool ::= hasKey(Term, Ts) [function]
  rule [haskey-nil]: hasKey(_, .Ts) => false
  rule [haskey-cons]: hasKey(E, F ; Fs) => ckey(E, F) ==Int 0 orBool hasKey(E, Fs)

  syntax Int ::= len(Ts) [function]
  rule [len-nil]: len(.Ts) => 0
  rule [len-cons]: len(_ ; Ts) => 1 +Int len(Ts)

  syntax Ts ::= app(Ts, Ts) [function]
  rule [app-nil]: app(.Ts, Us) => Us
  rule [app-cons]: app(T ; Ts, Us) => T ; app(Ts, Us)

  // ---------------------------------------------------------------- hooks
  // 1 +Int, 2 -Int, 3 *Int, 4 /Int, 5 %Int, 10 <Int, 11 <=Int, 12 >Int, 13 >=Int, 14 ==Int,
  // 15 =/=Int, 20 andBool, 21 orBool, 22 notBool, 23 ==Bool, 30 #if_#then_#else_#fi,
  // 40 Map:lookup, 41 Map:lookupOrDefault, 42 Map:update, 43 _[_<-undef], 44 _in_keys(_),
  // 45 sizeMap, 50 Set:in, 51 size(Set), 52 |Set, 60 sizeList, 70 ==K, 71 =/=K, 80 ==String,
  // 81 <String (a String value is tk(S, Text) with S the sort String)
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
  rule [op-bool-eq]: hookOp(23, bv(X) ; bv(Y) ; .Ts) => bv(X ==Bool Y)
  rule [op-ite-then]: hookOp(30, bv(C) ; T ; _ ; .Ts) => T requires C
  rule [op-ite-else]: hookOp(30, bv(C) ; _ ; E ; .Ts) => E requires notBool C
  rule [op-lookup]: hookOp(40, co(map, _, Es) ; A ; .Ts) => valueOr(A, bot, Es)
  rule [op-lookup-or]: hookOp(41, co(map, _, Es) ; A ; V ; .Ts) => valueOr(A, V, Es)
  rule [op-update]: hookOp(42, co(map, C, Es) ; A ; V ; .Ts) => co(map, C, putE(kv(A, V), Es))
  rule [op-remove]: hookOp(43, co(map, C, Es) ; A ; .Ts) => co(map, C, delE(kv(A, A), Es))
  rule [op-in-keys]: hookOp(44, A ; co(map, _, Es) ; .Ts) => bv(hasKey(kv(A, A), Es))
  rule [op-size-map]: hookOp(45, co(map, _, Es) ; .Ts) => iv(len(Es))
  rule [op-set-in]: hookOp(50, X ; co(set, _, Es) ; .Ts) => bv(hasKey(el(X), Es))
  rule [op-size-set]: hookOp(51, co(set, _, Es) ; .Ts) => iv(len(Es))
  rule [op-union]: hookOp(52, co(set, C, Es) ; co(set, _, Fs) ; .Ts) => co(set, C, union(Es, Fs))
  rule [op-size-list]: hookOp(60, co(list, _, Es) ; .Ts) => iv(len(Es))
  rule [op-keq]: hookOp(70, A ; B ; .Ts) => bv(cmp(A, B) ==Int 0)
  rule [op-kne]: hookOp(71, A ; B ; .Ts) => bv(cmp(A, B) =/=Int 0)
  rule [op-str-eq]: hookOp(80, tk(_, X) ; tk(_, Y) ; .Ts) => bv(X ==String Y)
  rule [op-str-lt]: hookOp(81, tk(_, X) ; tk(_, Y) ; .Ts) => bv(X <String Y)
  // No other case gives a value. Where the hook's text states none (/Int and %Int by zero, a
  // missing key), bot is the text's \bottom; at a point the text leaves open, bot is the value
  // of HookParams.none, the member of KCore's family this interpreter is, not the text's \bottom.
  rule [op-undef]: hookOp(_, _) => bot [owise]

  syntax Ts ::= union(Ts, Ts) [function]
  rule [union-nil]: union(Es, .Ts) => Es
  rule [union-cons]: union(Es, F ; Fs) => union(putE(F, Es), Fs)

  // ---------------------------------------------------------------- a total order on values
  syntax Int ::= cmp(Term, Term) [function]
  rule [cmp-int]: cmp(iv(X), iv(Y)) => cmpI(X, Y)
  rule [cmp-bool]: cmp(bv(X), bv(Y)) => cmpI(b2i(X), b2i(Y))
  rule [cmp-tok]: cmp(tk(S, X), tk(T, Y)) => lex(cmpI(S, T), cmpI(b2i(Y <String X), b2i(X <String Y)))
  rule [cmp-app]: cmp(ap(F, As), ap(G, Bs)) => lex(cmpI(F, G), cmpTs(As, Bs))
  rule [cmp-inj]: cmp(ij(A, B, T), ij(C, E, U)) => lex(cmpI(A, C), lex(cmpI(B, E), cmp(T, U)))
  rule [cmp-col]: cmp(co(_, C, Es), co(_, D, Fs)) => lex(cmpI(C, D), cmpTs(Es, Fs))
  rule [cmp-kv]: cmp(kv(A, V), kv(B, W)) => lex(cmp(A, B), cmp(V, W))
  rule [cmp-el]: cmp(el(X), el(Y)) => cmp(X, Y)
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
  rule [tag-col]: tag(co(_, _, _)) => 4
  rule [tag-tok]: tag(tk(_, _)) => 5
  rule [tag-other]: tag(_) => 6 [owise]

  // the order of a collection's elements: a map entry by its key, a set element by its value
  syntax Int ::= ckey(Term, Term) [function]
  rule [ckey-kv]: ckey(kv(A, _), kv(B, _)) => cmp(A, B)
  rule [ckey-el]: ckey(el(X), el(Y)) => cmp(X, Y)

  syntax Ts ::= insert(Term, Ts) [function]
  rule [ins-nil]: insert(T, .Ts) => T ; .Ts
  rule [ins-before]: insert(T, U ; Us) => T ; U ; Us requires cmp(T, U) <Int 0
  rule [ins-dup]: insert(T, U ; Us) => U ; Us requires cmp(T, U) ==Int 0
  rule [ins-after]: insert(T, U ; Us) => U ; insert(T, Us) requires cmp(T, U) >Int 0

  syntax Bool ::= member(Term, Ts) [function]
  rule [mem-nil]: member(_, .Ts) => false
  rule [mem-cons]: member(T, U ; Us) => cmp(T, U) ==Int 0 orBool member(T, Us)
endmodule
