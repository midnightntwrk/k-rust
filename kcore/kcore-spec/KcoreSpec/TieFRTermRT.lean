/-
  `altsTrOK` from the reader: the alternatives `Parse.frRead` gives `Parse.frClauses` translate,
  through `Term.kore`, as the alternatives it keeps of the text's right side, and their conditions
  as the text's.

  `frRead N eq = .ok (some z)` reads (`frRead_inv`): the head of the equation (`eqnHead`), with its
  `ensures`; the conditions lifted at the top of the normalised right side (`sideConds` of
  `frConds`); and each kept alternative (`altsOf`): its side by `Parse.term`, its own lifted
  conditions by `sideConds`. Its clauses are `frClauses` of the alternatives so read, each with the
  `ensures`, the top's conditions and its own, in that order (`frRead_alts`), over the sorts of the
  variables `z.2` (`varSorts`).

  Each such reading is a `Parse.term` of a pattern of the text where the condition is one Bool
  term (`condRT`: not a predicate, not a conjunction of several), so the round trip of
  KcoreSpec/TermRoundTrip.lean (`term_rt`) gives its translation: `altsTrOK_of_frRead`, for a text
  that is `frRT` (its `ensures`, lifted conditions and kept alternatives are `condRT` and `rtPat`),
  with the names of `N` those of `c` and the tables aligned on `z.2` (`alignOK`).

  `frClauses_inj`: the clauses `frClauses` writes of alternatives `frAltsOf xs` give `xs` back, so
  the alternatives of a function whose clauses are literally `frClauses … (frAltsOf xs)` are the
  ones read.
-/
import KcoreSpec.TieFRRead
import KcoreSpec.TermRoundTrip

set_option autoImplicit false

namespace KCore

namespace TieFRRT

open ML Faithful KoreAML
open KCore.TieFRRead KCore.TermRT

/-! ## Conditions -/

/-- A condition `Parse.condTerm` reads as the term of its pattern: no predicate, one conjunct, and
`rtPat`. -/
def condRT (N : Parse.Names) (b : Kore.Pattern) : Bool :=
  !Parse.isPred b && (Parse.boolConj b).length == 1 && rtPat N b

/-- A lifted condition that a Bool term be `true`, the term `condRT`. -/
def scRT (N : Parse.Names) : Parse.SideCond → Bool
  | .isTrue b => condRT N b
  | .same .. => false

/-- `Parse.condTerm` extends the list of variables at its end. -/
theorem condTerm_prefix {N : Parse.Names} {vs vs' : List Var} {b : Kore.Pattern} {t : Term}
    (h : Parse.condTerm N vs b = .ok (t, vs')) : vs <+: vs' := by
  unfold Parse.condTerm at h
  split at h
  · cases h; exact List.prefix_refl _
  · split at h
    · cases h
    · split at h
      · exact term_prefix h
      · obtain ⟨⟨ts, vs1⟩, h1, h⟩ := TermRT.bind_ok h
        dsimp only at h
        split at h
        · obtain ⟨_, -, h⟩ := TermRT.bind_ok h
          cases h
          exact terms_prefix h1
        · cases h
          exact terms_prefix h1

section
variable {N : Parse.Names} {c : Semantics} (hsy : N.syms = c.symNames) (hso : N.sorts = c.sortNames)
  {tbl tblT : VarTable} {vars : List Srt} {vsF : List Var}
  (hA : alignOK c tbl tblT vars vsF = true)
include hsy hso hA

/-- **The term `Parse.condTerm` reads of a `condRT` condition translates as the condition.** -/
theorem condTerm_rt {vs vs' : List Var} {b : Kore.Pattern} {t : Term} (h : Parse.condTerm N vs b = .ok (t, vs'))
    (hrt : condRT N b = true) (hp : vs' <+: vsF) :
    tr ⟨tblT, []⟩ b = tr ⟨tbl, []⟩ (Term.kore c (Faithful.canonVars c vars) t) := by
  unfold condRT at hrt
  simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at hrt
  obtain ⟨⟨hpred, hlen⟩, hpat⟩ := hrt
  obtain ⟨x, hx⟩ := List.length_eq_one_iff.mp hlen
  unfold Parse.condTerm at h
  rw [hpred, hx] at h
  simp only [Bool.false_eq_true, ↓reduceIte] at h
  split at h
  · cases h
  · exact term_rt hsy hso hA h hpat hp

/-- **The terms `Parse.sideConds` reads of conditions that Bool terms be `true`** translate as the
Bool terms, where each is `scRT`. -/
theorem sideConds_rt : ∀ {cs : List Parse.SideCond} {vs : List Var} {ts : List Term} {vs' : List Var},
    Parse.sideConds N vs cs = .ok (ts, vs') → AllTrue cs →
    vs <+: vs' ∧ (cs.all (scRT N) = true → vs' <+: vsF →
      ts.map (fun b => tr ⟨tbl, []⟩ (Term.kore c (Faithful.canonVars c vars) b)) =
        (cs.filterMap scTrue).map (tr ⟨tblT, []⟩))
  | [], vs, ts, vs', h, _ => by
    rw [Parse.sideConds] at h
    cases h
    exact ⟨List.prefix_refl _, fun _ _ => rfl⟩
  | .isTrue b :: cs, vs, ts, vs', h, hall => by
    rw [Parse.sideConds] at h
    obtain ⟨⟨t, vs1⟩, h1, h⟩ := TermRT.bind_ok h
    obtain ⟨⟨ts1, vs2⟩, h2, h⟩ := TermRT.bind_ok h
    cases h
    obtain ⟨p2, r2⟩ := sideConds_rt h2 (fun x hx => hall x (List.mem_cons_of_mem _ hx))
    have p1 := condTerm_prefix h1
    refine ⟨p1.trans p2, fun hrt hp => ?_⟩
    rw [List.all_cons, Bool.and_eq_true] at hrt
    simp only [List.map_cons, List.filterMap_cons, scTrue]
    rw [← condTerm_rt hsy hso hA h1 hrt.1 (p2.trans hp), r2 hrt.2 hp]
  | .same s t u :: cs, vs, ts, vs', _, hall => by
    have := hall (.same s t u) (List.mem_cons_self ..)
    simp [scTrue] at this

end

/-! ## The alternatives -/

/-- The alternatives kept of a list (`keptAlts` of `orAlts r`). -/
def keptOf (as : List Kore.Pattern) : List (Kore.Pattern × List Parse.SideCond) :=
  as.filterMap fun a => if (Parse.hoist a).2.2 then none else some ((Parse.hoist a).1, (Parse.hoist a).2.1)

theorem keptAlts_eq (r : Kore.Pattern) : keptAlts r = keptOf (Parse.orAlts r) := rfl

/-- **What `altOf` reads of an alternative**: nothing where it is empty; else its side as a term
and its lifted conditions as Bool terms. -/
theorem altOf_inv {N : Parse.Names} {vs vs' : List Var} {a : Kore.Pattern} {o : Option (Term × List Cond)}
    (h : Parse.altOf N vs a = .ok (o, vs')) :
    ((Parse.hoist a).2.2 = true ∧ o = none ∧ vs' = vs) ∨
    ((Parse.hoist a).2.2 = false ∧ ∃ t ts vs1, o = some (t, ts.map Parse.isTrueC) ∧
      Parse.term N vs (Parse.hoist a).1 = .ok (t, vs1) ∧ Parse.sideConds N vs1 (Parse.hoist a).2.1 = .ok (ts, vs')) := by
  unfold Parse.altOf at h
  rcases hx : Parse.hoist a with ⟨r, conds, emp⟩
  rw [hx] at h
  simp only at h ⊢
  cases emp with
  | true =>
    simp only [↓reduceIte] at h
    cases h
    exact .inl ⟨rfl, rfl, rfl⟩
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h
    split at h
    · cases h
    · split at h
      · obtain ⟨⟨t, vs1⟩, h1, h⟩ := TermRT.bind_ok h
        obtain ⟨⟨ts, vs2⟩, h2, h⟩ := TermRT.bind_ok h
        cases h
        exact .inr ⟨rfl, t, ts, vs1, rfl, h1, h2⟩
      · first | cases h | (obtain ⟨_, h', -⟩ := TermRT.bind_ok h; cases h')

/-- A kept alternative `k` and the alternative `y` read of it translate as one: the sides, and
the conditions of `y` as the Bool terms of `k`'s lifted conditions. -/
def PairRT (c : Semantics) (tbl tblT : VarTable) (vars : List Srt)
    (k : Kore.Pattern × List Parse.SideCond) (y : Term × List Term) : Prop :=
  tr ⟨tblT, []⟩ k.1 = tr ⟨tbl, []⟩ (Term.kore c (Faithful.canonVars c vars) y.1) ∧
    y.2.map (fun b => tr ⟨tbl, []⟩ (Term.kore c (Faithful.canonVars c vars) b)) =
      (k.2.filterMap scTrue).map (tr ⟨tblT, []⟩)

/-- Every kept alternative has an `rtPat` side and `scRT` conditions. -/
def keptRT (N : Parse.Names) (ks : List (Kore.Pattern × List Parse.SideCond)) : Bool :=
  ks.all fun k => rtPat N k.1 && k.2.all (scRT N)

section
variable {N : Parse.Names} {c : Semantics} (hsy : N.syms = c.symNames) (hso : N.sorts = c.sortNames)
  {tbl tblT : VarTable} {vars : List Srt} {vsF : List Var}
  (hA : alignOK c tbl tblT vars vsF = true)
include hsy hso hA

/-- **What `altsOf` reads**: the kept alternatives (`keptOf`), in order, each as a term with Bool
terms as its conditions, translating as the kept alternative (`PairRT`) where the kept
alternatives are `keptRT`. -/
theorem altsOf_inv : ∀ {as : List Kore.Pattern} {vs : List Var} {alts : List (Term × List Cond)} {vs' : List Var},
    Parse.altsOf N vs as = .ok (alts, vs') →
    vs <+: vs' ∧ ∃ ys : List (Term × List Term), alts = ys.map (fun y => (y.1, y.2.map Parse.isTrueC)) ∧
      (keptRT N (keptOf as) = true → vs' <+: vsF → All2 (PairRT c tbl tblT vars) (keptOf as) ys)
  | [], vs, alts, vs', h => by
    rw [Parse.altsOf] at h
    cases h
    exact ⟨List.prefix_refl _, [], rfl, fun _ _ => .nil⟩
  | a :: as, vs, alts, vs', h => by
    rw [Parse.altsOf] at h
    obtain ⟨⟨x, vs1⟩, h1, h⟩ := TermRT.bind_ok h
    obtain ⟨⟨xs, vs2⟩, h2, h⟩ := TermRT.bind_ok h
    cases h
    obtain ⟨p2, ys, rfl, r2⟩ := altsOf_inv h2
    rcases altOf_inv h1 with ⟨he, rfl, rfl⟩ | ⟨he, t, ts, vsm, rfl, ht, hs⟩
    · refine ⟨p2, ys, rfl, fun hrt hp => ?_⟩
      have hk : keptOf (a :: as) = keptOf as := by simp [keptOf, he]
      rw [hk] at hrt ⊢
      exact r2 hrt hp
    · have hall := altOf_allTrue h1 he
      obtain ⟨ps, rs⟩ := sideConds_rt hsy hso hA hs hall
      have pt := term_prefix ht
      refine ⟨(pt.trans ps).trans p2, (t, ts) :: ys, rfl, fun hrt hp => ?_⟩
      have hk : keptOf (a :: as) = ((Parse.hoist a).1, (Parse.hoist a).2.1) :: keptOf as := by simp [keptOf, he]
      rw [hk] at hrt ⊢
      rw [keptRT, List.all_cons, Bool.and_eq_true, Bool.and_eq_true] at hrt
      exact .cons ⟨term_rt hsy hso hA ht hrt.1.1 ((ps.trans p2).trans hp), rs hrt.1.2 (p2.trans hp)⟩ (r2 hrt.2 hp)

omit hsy hso hA in
/-- **`altsTrOK` of paired alternatives**: each alternative with the conditions `pre` before its
own, `pre` translating as the `ensures` part's Bool terms and the top's lifted conditions. -/
theorem altsTrOK_of_all2 {cs : List Parse.SideCond} {bs : List Kore.Pattern} {pre : List Term}
    (hpre : pre.map (fun b => tr ⟨tbl, []⟩ (Term.kore c (Faithful.canonVars c vars) b)) =
      (bs ++ cs.filterMap scTrue).map (tr ⟨tblT, []⟩)) :
    ∀ {ks : List (Kore.Pattern × List Parse.SideCond)} {ys : List (Term × List Term)},
    All2 (PairRT c tbl tblT vars) ks ys →
    altsTrOK c tbl (Faithful.canonVars c vars) tblT cs bs ks (ys.map fun y => (y.1, pre ++ y.2)) = true
  | _, _, .nil => rfl
  | _, _, .cons h hs => by
    rw [List.map_cons, altsTrOK, Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_iff, decide_eq_true_iff]
    refine ⟨⟨h.1, ?_⟩, altsTrOK_of_all2 hpre hs⟩
    simp only [List.map_append, List.filterMap_append] at hpre ⊢
    rw [hpre, h.2, List.append_assoc]

end

/-! ## What `frRead` reads -/

/-- The term `eqnCondTerm` reads is `condTerm`'s. -/
theorem eqnCondTerm_ok {N : Parse.Names} {vs vs' : List Var} {b : Kore.Pattern} {t : Term}
    (h : Parse.eqnCondTerm N vs b = .ok (t, vs')) : Parse.condTerm N vs b = .ok (t, vs') := by
  unfold Parse.eqnCondTerm at h
  obtain ⟨r, hr, h⟩ := TermRT.bind_ok h
  split at h
  · cases h
    exact hr
  · obtain ⟨_, h', -⟩ := TermRT.bind_ok h; cases h'

/-- **The `ensures` of the head `eqnHead` reads**: none where the equation has none, else the term
`condTerm` reads of it, the variables then being the head's. -/
theorem eqnHead_ens {N : Parse.Names} {e : Parse.RawEqn} {pats : List Term} {req ens : Option Term}
    {vs0 : List Var} {np : Nat} (h : Parse.eqnHead N e = .ok (pats, req, ens, vs0, np)) :
    (e.ens = none ∧ ens = none) ∨
      ∃ b t vsA, e.ens = some b ∧ ens = some t ∧ Parse.condTerm N vsA b = .ok (t, vs0) := by
  unfold Parse.eqnHead at h
  obtain ⟨⟨pats', vs⟩, -, h⟩ := TermRT.bind_ok h
  dsimp only at h
  split at h
  · obtain ⟨_, hp, h⟩ := TermRT.bind_ok h
    cases hp
    dsimp only at h
    split at h
    · rename_i he
      obtain ⟨_, hp, h⟩ := TermRT.bind_ok h
      cases hp
      cases h
      exact .inl ⟨he, rfl⟩
    · rename_i b he
      obtain ⟨⟨t, vs3⟩, hc, h⟩ := TermRT.bind_ok h
      dsimp only at h
      obtain ⟨_, hp, h⟩ := TermRT.bind_ok h
      cases hp
      cases h
      exact .inr ⟨b, t, _, he, rfl, eqnCondTerm_ok hc⟩
  · obtain ⟨⟨t0, vsr⟩, -, h⟩ := TermRT.bind_ok h
    dsimp only at h
    obtain ⟨_, hp, h⟩ := TermRT.bind_ok h
    cases hp
    dsimp only at h
    split at h
    · rename_i he
      obtain ⟨_, hp, h⟩ := TermRT.bind_ok h
      cases hp
      cases h
      exact .inl ⟨he, rfl⟩
    · rename_i b he
      obtain ⟨⟨t, vs3⟩, hc, h⟩ := TermRT.bind_ok h
      dsimp only at h
      obtain ⟨_, hp, h⟩ := TermRT.bind_ok h
      cases hp
      cases h
      exact .inr ⟨b, t, _, he, rfl, eqnCondTerm_ok hc⟩

/-- **What `frRead` reads as clauses** (`frRead N eq = .ok (some z)`): the head, the conditions
lifted at the top of the normalised right side, the alternatives of its side, the sorts of the
variables `z.2`, and the clauses `frClauses` of the alternatives, each with the `ensures` and the
top's conditions before its own. -/
theorem frRead_inv {N : Parse.Names} {eq : Parse.RawEqn} {z : List Clause × List Var}
    (h : Parse.frRead N eq = .ok (some z)) :
    ∃ pats req ens vs0 np ts vs1 alts s vars,
      Parse.eqnHead N eq = .ok (pats, req, ens, vs0, np) ∧
      Parse.sideConds N vs0 (frConds eq.rhs) = .ok (ts, vs1) ∧
      Parse.altsOf N vs1 (Parse.orAlts (frSide eq.rhs)) = .ok (alts, z.2) ∧
      Parse.varSorts N z.2 = .ok vars ∧
      z.1 = Parse.frClauses s vars pats req (Parse.eqnPrio eq).2 (Parse.nonExec eq)
        (alts.map fun a => (a.1, (ens.toList ++ ts).map Parse.isTrueC ++ a.2)) := by
  unfold Parse.frRead at h
  obtain ⟨_, -, h⟩ := bind_ok_FR h
  unfold frSide frConds
  rcases hx : Parse.hoist (Parse.dropEmptyAlts eq.rhs) with ⟨r, conds, emp⟩
  rw [hx] at h
  dsimp only at h ⊢
  split at h
  · cases h
  split at h
  · cases h
  obtain ⟨⟨pats, req, ens, vs, np⟩, hhead, h⟩ := bind_ok_FR h
  dsimp only at h
  split at h
  · split at h
    · obtain ⟨_, h', -⟩ := bind_ok_FR h; cases h'
    · split at h
      · obtain ⟨⟨cs, vs1⟩, hsc, h⟩ := bind_ok_FR h
        dsimp only at h
        obtain ⟨⟨alts, vs2⟩, hal, h⟩ := bind_ok_FR h
        dsimp only at h
        split at h
        · cases h
        · obtain ⟨_, -, h⟩ := bind_ok_FR h
          obtain ⟨s, -, h⟩ := bind_ok_FR h
          obtain ⟨vars, hvars, h⟩ := bind_ok_FR h
          cases h
          exact ⟨pats, req, ens, vs, np, cs, vs1, alts, s, vars, hhead, hsc, hal, hvars, rfl⟩
      · first | cases h | (obtain ⟨_, h', -⟩ := bind_ok_FR h; cases h')
  · first | cases h | (obtain ⟨_, h', -⟩ := bind_ok_FR h; cases h')

/-- The equation's `ensures`, the conditions lifted at the top of its normalised right side and
its kept alternatives are read as the terms of their patterns (`condRT`, `scRT`, `keptRT`). -/
def frRT (N : Parse.Names) (eq : Parse.RawEqn) : Bool :=
  eq.ens.all (condRT N) && (frConds eq.rhs).all (scRT N) && keptRT N (keptAlts (frSide eq.rhs))

section
variable {N : Parse.Names} {c : Semantics} (hsy : N.syms = c.symNames) (hso : N.sorts = c.sortNames)
  {tbl tblT : VarTable} {vars : List Srt}
include hsy hso

/-- **The alternatives `frRead` gives `frClauses` translate as the kept ones** (`altsTrOK`). Where
`frRead` reads the equation as clauses with the variables `z.2`, of the sorts `vars`: the clauses
are `frClauses` of alternatives `frAltsOf xs` over `vars`, and, the names of `N` being those of
`c`, the tables aligned on `z.2` and the text `frRT`, `xs` translate over `canonVars c vars` as the
kept alternatives of the right side, their conditions as the `ensures`, the top's lifted
conditions and their own. -/
theorem altsTrOK_of_frRead {eq : Parse.RawEqn} {z : List Clause × List Var}
    (hrd : Parse.frRead N eq = .ok (some z)) (hvars : Parse.varSorts N z.2 = .ok vars)
    (hA : alignOK c tbl tblT vars z.2 = true) (hrt : frRT N eq = true) :
    ∃ xs s pats req, z.1 = Parse.frClauses s vars pats req (Parse.eqnPrio eq).2 (Parse.nonExec eq) (frAltsOf xs) ∧
      altsTrOK c tbl (Faithful.canonVars c vars) tblT (frConds eq.rhs) eq.ens.toList
        (keptAlts (frSide eq.rhs)) xs = true := by
  obtain ⟨pats, req, ens, vs0, np, ts, vs1, alts, s, vars', hhead, hsc, hal, hvars', hz⟩ := frRead_inv hrd
  rw [hvars] at hvars'
  cases hvars'
  have hn := frRead_norm hrd
  unfold frRT at hrt
  simp only [Bool.and_eq_true] at hrt
  obtain ⟨⟨hrtE, hrtC⟩, hrtK⟩ := hrt
  obtain ⟨p2, ys, rfl, r2⟩ := altsOf_inv hsy hso hA hal
  obtain ⟨p1, r1⟩ := sideConds_rt hsy hso hA hsc hn.2.1
  rw [keptAlts_eq] at hrtK ⊢
  have hpre : (ens.toList ++ ts).map (fun b => tr ⟨tbl, []⟩ (Term.kore c (Faithful.canonVars c vars) b)) =
      (eq.ens.toList ++ (frConds eq.rhs).filterMap scTrue).map (tr ⟨tblT, []⟩) := by
    rw [List.map_append, List.map_append, r1 hrtC (p2.trans (List.prefix_refl _))]
    congr 1
    rcases eqnHead_ens hhead with ⟨he, rfl⟩ | ⟨b, t, vsA, he, rfl, hc⟩
    · rw [he]; rfl
    · rw [he] at hrtE ⊢
      simp only [Option.all_some] at hrtE
      simp only [Option.toList_some, List.map_cons, List.map_nil]
      rw [condTerm_rt hsy hso hA hc hrtE (p1.trans p2)]
  refine ⟨ys.map fun y => (y.1, (ens.toList ++ ts) ++ y.2), s, pats, req, ?_,
    altsTrOK_of_all2 hpre (r2 hrtK (List.prefix_refl _))⟩
  rw [hz]
  congr 1
  simp [frAltsOf, List.map_map, Function.comp_def]

end

/-! ## The alternatives of `frClauses` -/

/-- A conjunction of conditions that Bool terms be `true` gives the terms back. -/
theorem conjTrue_inj : ∀ (l l' : List Term),
    Parse.conjC (l.map Parse.isTrueC) = Parse.conjC (l'.map Parse.isTrueC) → l = l'
  | [], [], _ => rfl
  | [], [_], h => by simp [Parse.conjC, Parse.isTrueC] at h
  | [], _ :: _ :: _, h => by simp [Parse.conjC] at h
  | [_], [], h => by simp [Parse.conjC, Parse.isTrueC] at h
  | [b], [b'], h => by
    simp only [List.map_cons, List.map_nil, Parse.conjC, Parse.isTrueC, Cond.equals.injEq] at h
    rw [h.2.1]
  | [_], _ :: _ :: _, h => by simp [Parse.conjC, Parse.isTrueC] at h
  | _ :: _ :: _, [], h => by simp [Parse.conjC] at h
  | _ :: _ :: _, [_], h => by simp [Parse.conjC, Parse.isTrueC] at h
  | b :: b2 :: l, b' :: b2' :: l', h => by
    simp only [List.map_cons, Parse.conjC, Cond.and.injEq] at h
    have h1 : b = b' := by
      have := h.1
      simp only [Parse.isTrueC, Cond.equals.injEq] at this
      exact this.2.1
    have h2 := conjTrue_inj (b2 :: l) (b2' :: l') (by simpa only [List.map_cons] using h.2)
    rw [h1, h2]

/-- An alternative's predicate gives its conditions back. -/
theorem preOf_inj {s s' : Srt} {x x' : Term × List Term} (h : preOf s x = preOf s' x') : x.2 = x'.2 := by
  unfold preOf at h
  cases h2 : x.2 with
  | nil =>
    cases h2' : x'.2 with
    | nil => rfl
    | cons _ _ => rw [h2, h2'] at h; simp [Parse.conjC] at h
  | cons b l =>
    cases h2' : x'.2 with
    | nil => rw [h2, h2'] at h; simp [Parse.conjC] at h
    | cons b' l' =>
      rw [h2, h2'] at h
      simp only [List.map_cons, Parse.conjC, Cond.and.injEq] at h
      exact conjTrue_inj (b :: l) (b' :: l') (by simpa only [List.map_cons] using h.2)

/-- **The clauses of `frClauses` give the alternatives back**, and the variables' sorts. -/
theorem frClauses_inj {s s' : Srt} {vars vars' : List Srt} {pats pats' : List Term} {req req' : Option Term}
    {prio prio' : Nat} {aside aside' : Bool} {xs xs' : List (Term × List Term)}
    (h : Parse.frClauses s vars pats req prio aside (frAltsOf xs) =
      Parse.frClauses s' vars' pats' req' prio' aside' (frAltsOf xs')) : xs = xs' ∧ vars = vars' := by
  rw [frClauses_eq, frClauses_eq] at h
  have hlen : xs.length = xs'.length := by
    have := congrArg List.length h
    simpa using this
  obtain ⟨h1, h2⟩ := List.append_inj h (by simpa using hlen)
  refine ⟨?_, ?_⟩
  · clear h h2 hlen
    induction xs generalizing xs' with
    | nil => cases xs' with
      | nil => rfl
      | cons _ _ => cases h1
    | cons x xs ih =>
      cases xs' with
      | nil => cases h1
      | cons x' xs' =>
        simp only [List.map_cons, List.cons.injEq, Clause.mk.injEq] at h1
        obtain ⟨hx, hxs⟩ := h1
        have h1 : x.1 = x'.1 := hx.2.2.2.1
        have h2 : x.2 = x'.2 := preOf_inj hx.2.2.2.2.2.2.2.2.1
        rw [ih hxs, Prod.ext h1 h2]
  · simp only [List.cons.injEq, Clause.mk.injEq] at h2
    exact h2.1.1

section
variable {N : Parse.Names} {c : Semantics} (hsy : N.syms = c.symNames) (hso : N.sorts = c.sortNames)
  {tbl tblT : VarTable} {vars : List Srt}
include hsy hso

/-- **`altsTrOK` of the alternatives of the clauses read.** `altsTrOK_of_frRead` for clauses given
as `frClauses … (frAltsOf xs)`: `xs` are the alternatives read (`frClauses_inj`). -/
theorem altsTrOK_of_clauses {eq : Parse.RawEqn} {z : List Clause × List Var}
    (hrd : Parse.frRead N eq = .ok (some z)) (hvars : Parse.varSorts N z.2 = .ok vars)
    (hA : alignOK c tbl tblT vars z.2 = true) (hrt : frRT N eq = true)
    {s : Srt} {vars' : List Srt} {pats : List Term} {req : Option Term} {prio : Nat} {aside : Bool}
    {xs : List (Term × List Term)} (hz : z.1 = Parse.frClauses s vars' pats req prio aside (frAltsOf xs)) :
    altsTrOK c tbl (Faithful.canonVars c vars) tblT (frConds eq.rhs) eq.ens.toList
      (keptAlts (frSide eq.rhs)) xs = true := by
  obtain ⟨xs0, s0, pats0, req0, hz0, hok⟩ := altsTrOK_of_frRead hsy hso (tbl := tbl) (tblT := tblT) hrd hvars hA hrt
  rw [hz] at hz0
  rw [(frClauses_inj hz0).1]
  exact hok

end

/-- **An operand read as a term of the sort s lies in s** (`inSortK_of_term`, its translation from
the round trip): `Parse.term` reads the operand q as t over variables among the first of `vsF`. -/
theorem inSortK_of_read {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} {N : Parse.Names} {c : Semantics}
    (hsy : N.syms = c.symNames) (hso : N.sorts = c.sortNames) (hTS : Faithful.TermsInSort c I)
    {tbl tblT : VarTable} {vars : List Srt} {vsF vs vs' : List Var} (hA : alignOK c tbl tblT vars vsF = true)
    {s : Srt} {t : Term} {S : Kore.KSort} {q : Kore.Pattern} {e : Valuation M}
    (hrd : Parse.term N vs q = .ok (t, vs')) (hrt : rtPat N q = true) (hp : vs' <+: vsF)
    (hs : s < nRegSorts + c.sortNames.length) (hty : sortOfTerm (c.rhsCtx (c.fns.map Fn.sig)) vars t = some s)
    (hS : trSort tblT S = trSort tbl (srtOf c s))
    (hvar : ∀ i ∈ varOccs t, Faithful.InS I (c.sortName (vars.getD i 0)) (e.evalEvar (tbl.ev (Faithful.canonKey c vars i)))) :
    InSortK I tblT e S q :=
  inSortK_of_term hTS hs hty (term_rt hsy hso hA hrd hrt hp) hS hvar

/-- The Bool terms of an `ensures` part (`ensBools`) are the `ensures` `Parse.req?` reads of it. -/
theorem ensBools_req {en : Kore.Pattern} {bs : List Kore.Pattern} {o : Option Kore.Pattern}
    (h : ensBools en = some bs) (hr : Parse.req? en = some o) : bs = o.toList := by
  unfold ensBools at h
  split at h
  · cases h
    simp only [Parse.req?] at hr
    cases hr
    rfl
  · split at h
    · cases h
      simp only [Parse.req?] at hr
      cases hr
      rfl
    · cases h
  · cases h

end TieFRRT

end KCore
