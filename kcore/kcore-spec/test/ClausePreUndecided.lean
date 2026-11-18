/-
  A clause predicate without a truth value: what `FnDet` and `FnSolves` do not say of a clause's
  own predicate. Run from the package root: `lake env lean -j1 test/ClausePreUndecided.lean`.
  Kernel-checked.

  The semantics `d`, two functions over Int, built by hand:
  - `l(X:Int) => l(X)` (`lCl`): `l` has no result at an Int (`noL`: a derivation of one would hold a
    smaller one);
  - `h(X:Int)` with two clauses of one priority, `hCl1` with `rhs := 1` and `hCl2` with `rhs := 2`,
    each with the predicate `pre := ⌈l(X)⌉ ∨ ¬⌈l(X)⌉` (`preU`).

  `Holds` gives `preU` no truth value at an Int (`noPre`): `Holds.or` reads a truth value of each
  side, `Holds.ceil` a result of `l(X)`, and there is none. So no clause of `h` applies and none
  fails, and `h` has no result at an Int (`noH`). Hence, kernel-checked here:
  - `fnDet`: every function of `d` has at most one result;
  - `fnSolves`: `FnSolves d` (no clause of `h` decides anywhere; where `l`'s clause decides, both
    sides are without a value);
  - `rest_ok`, `clause_ok`, `pre_ok`, `openLaws`: `d` meets every conjunct of `coreOK` but
    `clausesPlain`, meets CN-4 §4.9's final text of `clausesPlain` (`clauseE3`), its predicates have
    `condOK` and `Cond.bound`, and `OpenLaws d` holds;
  - `trueV`: the reading of `preU` that takes a term without a result as the empty set (`TrueV`) is
    true at every σ;
  - `sentences`: `Γ`'s sentences for the two clauses are `((⊤ ∧ X0 ∈ X) ∧ preU) → h(X0) = 1` and
    `((⊤ ∧ X0 ∈ X) ∧ preU) → h(X0) = 2`, neither under an exclusion (the clauses are of one
    priority).

  What follows from these texts, not proved here: in every interpretation `⌈φ⌉ ∨ ¬⌈φ⌉` is `⊤`, so
  the two sentences state `h(x) = 1` and `h(x) = 2` at every element x of Int. So the value model,
  in which `h(x)` is the set of `Eval`'s values of `h` at x (none), satisfies neither sentence; and
  Int is one of `distinctSorts`, whose distinct values are distinct elements in a model of `Γ`
  (`values_apart`), so no interpretation satisfies both. A statement that gives a model of `Γ` from
  `coreOK`, `FnDet`, `FnSolves` and `OpenLaws` alone is therefore false at `d` once
  `clausesPlain` admits `preU`: with a predicate in the premise it needs that each clause's own
  predicate has a truth value where its patterns match (as `holds_decided` gives where every
  function has a result, `FnTerminates`), which `PrioDecided` asks of the clauses of a smaller
  priority only. `consistent_of` asks it (`ClausePreDecided`), and `d` does not meet it
  (`not_clausePreDecided`).
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 100000

namespace KCore

namespace ClausePreUndecided

open Faithful.UndefRhsWitness (cellSorts cellCtors cellSubsorts)
open Faithful (canonVars canonClausePres eqnSentence clauseEquation prioEquation lowerClauses)
open KoreAML (R)

def iT (i : Int) : Term := .dv Srt.int (.int i)

/-- The symbols after the four cell symbols: l, h. -/
def L : Sym := nRegSyms + 4
def H : Sym := nRegSyms + 5

/-- `l(X)`, X the variable 0. -/
def lX : Term := .app L [.var 0]

/-- `l(X) => l(X)`. -/
def lCl : Clause := ⟨[Srt.int], [.var 0], none, lX, none, 50, false, [], .top, .top⟩
def lFn : Fn := ⟨L, [Srt.int], Srt.int, [lCl], false⟩

/-- `⌈l(X)⌉ ∨ ¬⌈l(X)⌉`. -/
def preU : Cond := .or (.ceil Srt.int lX) (.not (.ceil Srt.int lX))

/-- `h(X) => 1` and `h(X) => 2`, each where `preU`, of one priority. -/
def hCl1 : Clause := ⟨[Srt.int], [.var 0], none, iT 1, none, 50, false, [], preU, .top⟩
def hCl2 : Clause := ⟨[Srt.int], [.var 0], none, iT 2, none, 50, false, [], preU, .top⟩
def hFn : Fn := ⟨H, [Srt.int], Srt.int, [hCl1, hCl2], false⟩

def d : Semantics :=
  { lib := {}
    sortNames := ["KCell", "KCellOpt"]
    symNames := ["LblisKCell", "LblisKCellOpt", "Lbl'-LT-'k'-GT-'", "LblnoKCell", "Lbll", "Lblh"]
    userSorts := cellSorts
    ctors := cellCtors
    fns := [lFn, hFn]
    userSubsorts := cellSubsorts
    pgmSort := Srt.k
    rules := [] }

theorem lookups : d.lookupFn L = some lFn ∧ d.lookupFn H = some hFn := ⟨rfl, rfl⟩

theorem kinds : d.isCtor L = false ∧ isHook L = false ∧ d.isParam L = false ∧ d.isOvl L = false := by
  decide +kernel

/-! ## What `coreOK` asks, but for the predicate being `\top` -/

/-- CN-4 §4.9's final text of what `clausesPlain` asks of one clause. -/
def clauseE3 (c : Semantics) (cl : Clause) : Bool :=
  cl.exs.isEmpty && cl.post.isTop &&
  (!cl.reqOpen || cl.reqClosed || cl.openCondVars.all fun i => (cl.vars[i]?.map c.confined).getD false)

/-- `sortedOK` without `clausesPlain`. -/
def sortedRest (c : Semantics) : Bool :=
  c.subsortsOK && c.fns.all (fun f => f.clauses.all (c.clauseSorted f (c.fns.map Fn.sig))) &&
    c.rules.all c.ruleSorted && c.rulesPlain && c.paramsPlain

/-- `coreOK` without `sortedOK`. -/
def coreRest (c : Semantics) : Bool :=
  c.faithCoreOK && c.hooksApart && c.predsApart && c.idsOK && c.overloadsOK

theorem coreOK_eq (c : Semantics) : c.coreOK = ((sortedRest c && c.clausesPlain) && coreRest c) := by
  simp only [Semantics.coreOK, Semantics.sortedOK, sortedRest, coreRest, Bool.and_assoc,
    Bool.and_comm c.clausesPlain]

/-- Every conjunct of `coreOK` but `clausesPlain` holds of `d`. -/
theorem rest_ok : sortedRest d = true ∧ coreRest d = true := by decide +kernel
/-- Every clause of `d` meets CN-4 §4.9's final clause conjunct. -/
theorem clause_ok : d.fns.all (fun f => f.clauses.all (clauseE3 d)) = true := by decide +kernel
/-- Each predicate is well sorted over its clause's variables and holds no binder. -/
theorem pre_ok : d.fns.all (fun f => f.clauses.all fun cl =>
    d.condOK cl.vars cl.pre && Cond.bound d cl.vars.length cl.pre) = true := by decide +kernel
/-- `clausesPlain` refuses `d` at the predicates only. -/
theorem clausesPlain_now : d.clausesPlain = false := by decide +kernel

theorem openLaws : OpenLaws d := openLaws_of_plain (by decide +kernel)

/-! ## Matches -/

theorem match0 {σ : Subst} {vs : List GroundTerm} (h : PatVals d σ [.var 0] vs) :
    ∃ v, vs = [v] ∧ σ.lookup 0 = some v := by
  obtain ⟨v, vs', rfl, hv, hs⟩ := PatVals.cons_inv h
  rw [PatVals.nil_inv hs]
  exact ⟨v, rfl, PatVal.var_inv hv⟩

/-- A σ well sorted on a clause's one variable gives it an Int. -/
theorem int_of {σ : Subst} (hσ : d.WellSorted [Srt.int] σ) : ∃ v, σ.lookup 0 = some v ∧ d.sortOf v = some Srt.int :=
  hσ 0 Srt.int rfl

def sg (v : GroundTerm) : Subst := [(0, v)]

theorem sg_sortedAt {v : GroundTerm} (hv : d.sortOf v = some Srt.int) (is : List Nat) :
    d.WellSortedAt [Srt.int] is (sg v) := by
  intro i _ s hs
  cases i with
  | zero =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hs
    subst hs
    exact ⟨v, rfl, hv⟩
  | succ i => simp at hs

theorem sg_match (v : GroundTerm) : PatVals d (sg v) [.var 0] [v] := .cons (.var rfl) .nil

/-! ## `l` has no result at an Int -/

mutual
  /-- `l` has no result at an Int: its clause's right-hand side is `l` at the same Int. -/
  theorem noL : ∀ {f : Sym} {vs : List GroundTerm} {r : Option GroundTerm}, Eval d f vs r →
      f = L → ∀ v, vs = [v] → d.sortOf v = some Srt.int → False
    | _, _, _, .clause (fn := fn) (cl := cl) (σ := σ) hfn hcl _ hm _ _ _ _ hrhs _ _, hf, v, hvs, hv => by
      have key := noLT hrhs
      subst hf; subst hvs
      rw [lookups.1] at hfn; cases hfn
      have : cl = lCl := by simpa [lFn] using hcl
      subst this
      obtain ⟨w, hw, hl⟩ := match0 hm
      cases hw
      exact key rfl v hl hv
    | _, _, _, .rest (fn := fn) hfn hnone, hf, v, hvs, hv => by
      subst hf; subst hvs
      rw [lookups.1] at hfn; cases hfn
      cases hnone lCl (List.mem_singleton_self _) with
      | intro h =>
        cases h (sg v) (sg_sortedAt hv _) (sg_match v) with
        | intro ht _ _ => cases ht
        | pre hp => exact absurd hp.top_eq (by simp)
    | _, _, _, .ensFails (fn := fn) (cl := cl) hfn hcl _ _ _ _ _ _ ht _ _, hf, v, hvs, _ => by
      subst hf
      rw [lookups.1] at hfn; cases hfn
      have : cl = lCl := by simpa [lFn] using hcl
      subst this; cases ht
    | _, _, _, .clauseEx (fn := fn) (cl := cl) hfn hcl _ _ _ _ _ hne _ _ _ _, hf, v, hvs, _ => by
      subst hf
      rw [lookups.1] at hfn; cases hfn
      have : cl = lCl := by simpa [lFn] using hcl
      subst this; exact absurd rfl hne
    | _, _, _, .exNone (fn := fn) (cl := cl) hfn hcl hne _ _ _ _ _ _ _, hf, v, hvs, _ => by
      subst hf
      rw [lookups.1] at hfn; cases hfn
      have : cl = lCl := by simpa [lFn] using hcl
      subst this; exact absurd rfl hne
  termination_by structural _ _ _ h => h
  /-- `l(X)` has no result where X is an Int. -/
  theorem noLT : ∀ {σ : Subst} {t : Term} {r : Option GroundTerm}, EvalTerm d σ t r →
      t = lX → ∀ v, σ.lookup 0 = some v → d.sortOf v = some Srt.int → False
    | _, _, _, .var, ht, _, _, _ => by cases ht
    | _, _, _, .dv, ht, _, _, _ => by cases ht
    | _, _, _, .inj _, ht, _, _, _ => by cases ht
    | _, _, _, .ctor hk _, ht, _, _, _ => by
      cases ht; rw [kinds.1] at hk; cases hk
    | _, _, _, .hook _ hhk _ _ _, ht, _, _, _ => by
      cases ht; rw [kinds.2.1] at hhk; cases hhk
    | _, _, _, .param _ _ hp _ _, ht, _, _, _ => by
      cases ht; rw [kinds.2.2.1] at hp; cases hp
    | _, _, _, .call _ _ hts hvs hf _, ht, v, hl, hv => by
      have key := noL hf
      cases ht
      cases hts with
      | cons h1 hs =>
        cases hs; cases h1
        rw [hl] at hvs
        exact key rfl v (by simpa [allSome] using hvs.symm) hv
    | _, _, _, .callUndef _ _ hts hvs _, ht, v, hl, _ => by
      cases ht
      cases hts with
      | cons h1 hs =>
        cases hs; cases h1
        rw [hl] at hvs; simp [allSome] at hvs
    | _, _, _, .ovl _ ho _ _, ht, _, _, _ => by
      cases ht; rw [kinds.2.2.2] at ho; cases ho
    | _, _, _, .ovlFn _ ho _ _ _ _ _, ht, _, _, _ => by
      cases ht; rw [kinds.2.2.2] at ho; cases ho
  termination_by structural _ _ _ h => h
end

/-- **`preU` has no truth value** where X is an Int: `⌈l(X)⌉` has none, `l(X)` having no result. -/
theorem noPre {σ : Subst} {v : GroundTerm} (hl : σ.lookup 0 = some v) (hv : d.sortOf v = some Srt.int)
    {b : Bool} (h : Holds d 1 σ preU b) : False := by
  cases h with
  | or h1 _ =>
    cases h1 with
    | ceil he => exact noLT he rfl v hl hv

/-- **`d` does not meet `ClausePreDecided`**: the predicate of `h`'s first clause has no truth value
where its pattern matches the Int 0. -/
theorem not_clausePreDecided : ¬ ClausePreDecided d := by
  intro hp
  have hv : d.sortOf (.dv Srt.int (.int 0)) = some Srt.int := by decide +kernel
  obtain ⟨_, hb⟩ := hp hFn (by simp [d]) hCl1 (by simp [hFn]) (sg _) [_] (sg_sortedAt hv _) (sg_match _)
  exact noPre rfl hv hb

/-- No clause of `h` applies. -/
theorem not_applies {cl : Clause} (hcl : cl ∈ hFn.clauses) {σ : Subst} {vs : List GroundTerm}
    (ha : cl.AppliesAt d σ vs) : False := by
  have hc : cl = hCl1 ∨ cl = hCl2 := by simpa [hFn] using hcl
  rcases hc with rfl | rfl
  · obtain ⟨v, hl, hv⟩ := int_of ((wellSortedAt_univ rfl).mp ha.1)
    exact noPre hl hv ha.2.2.2
  · obtain ⟨v, hl, hv⟩ := int_of ((wellSortedAt_univ rfl).mp ha.1)
    exact noPre hl hv ha.2.2.2

/-- No clause of `h` has an existential variable. -/
theorem hExs {cl : Clause} (hcl : cl ∈ hFn.clauses) : cl.exs = [] := by
  have hc : cl = hCl1 ∨ cl = hCl2 := by simpa [hFn] using hcl
  rcases hc with rfl | rfl <;> rfl

/-- **`h` has no result at an Int**: no clause applies, and none fails. -/
theorem noH {v : GroundTerm} (hv : d.sortOf v = some Srt.int) {r : Option GroundTerm} (h : Eval d H [v] r) :
    False := by
  cases h with
  | clause hfn hcl hσ hm hreq hpre _ _ _ _ _ =>
    rw [lookups.2] at hfn; cases hfn
    exact not_applies hcl ⟨hσ.at _, hm, hreq, hpre⟩
  | rest hfn hnone =>
    rw [lookups.2] at hfn; cases hfn
    cases hnone hCl1 (by simp [hFn]) with
    | intro h =>
      cases h (sg v) (sg_sortedAt hv _) (sg_match v) with
      | intro ht _ _ => cases ht
      | pre hp => exact noPre (σ := sg v) rfl hv hp
  | ensFails hfn hcl hσ hm hreq hpre _ _ _ _ _ =>
    rw [lookups.2] at hfn; cases hfn
    exact not_applies hcl ⟨hσ.at _, hm, hreq, hpre⟩
  | clauseEx hfn hcl _ _ _ _ _ hne =>
    rw [lookups.2] at hfn; cases hfn
    exact absurd (hExs hcl) hne
  | exNone hfn hcl hne =>
    rw [lookups.2] at hfn; cases hfn
    exact absurd (hExs hcl) hne

/-! ## `FnDet` and `FnSolves` -/

theorem mem_fns {fn : Fn} (h : fn ∈ d.fns) : fn = lFn ∨ fn = hFn := by
  simpa [d] using h

theorem coherent_l : Coherent d lCl lCl := by
  intro vs σ σ' ha ha' _ _ _ _ _
  obtain ⟨v, rfl, hl⟩ := match0 ha.2.1
  obtain ⟨w, hw, hl'⟩ := match0 ha'.2.1
  cases hw
  refine .inl ⟨rfl, rfl, rfl, rfl, (fun i hi => ?_), (fun t ht => nomatch ht)⟩
  have : i = 0 := by simpa [lCl, lX, varOccs, varOccsList] using hi
  subst this; rw [hl, hl']

theorem coherent : CoherentAll d :=
  Faithful.coherentAll_ofCl
    (fun fn hfn cl cl' hp _ => by
      rcases mem_fns hfn with rfl | rfl
      · simp [lFn, pairs] at hp
      · have : cl = hCl1 ∧ cl' = hCl2 := by simpa [hFn, pairs] using hp
        obtain ⟨rfl, rfl⟩ := this
        exact ⟨fun _ _ _ ha _ _ _ _ _ _ => (not_applies (by simp [hFn]) ha).elim,
          fun _ _ _ ha _ _ _ _ _ _ => (not_applies (by simp [hFn]) ha).elim⟩)
    (fun fn hfn cl hcl => by
      rcases mem_fns hfn with rfl | rfl
      · have : cl = lCl := by simpa [lFn] using hcl
        subst this; exact (matchIndependent_iff_noExs rfl).mpr coherent_l
      · exact (matchIndependent_iff_noExs (hExs hcl)).mpr
          fun _ _ _ ha _ _ _ _ _ _ => (not_applies hcl ha).elim)

/-- **Every function of `d` has at most one result.** -/
theorem fnDet : FnDet d := fnDet_of_coherent coherent

/-- **Evaluation solves the equations of `d`**: no clause of `h` decides, and where `l`'s clause
decides neither `l` nor its right-hand side has a value. -/
theorem fnSolves : FnSolves d := by
  intro fn hfn vs _ cl hcl σ hdec v
  rcases mem_fns hfn with rfl | rfl
  · have : cl = lCl := by simpa [lFn] using hcl
    subst this
    obtain ⟨w, hl, hw⟩ := int_of ((wellSortedAt_univ rfl).mp hdec.1.1)
    obtain ⟨w', rfl, hl'⟩ := match0 hdec.1.2.1
    rw [hl] at hl'; cases hl'
    refine Iff.trans ?_ (Clause.gives_iff_noExs (cl := lCl) rfl rfl ((wellSortedAt_univ rfl).mp hdec.1.1) v).symm
    exact ⟨fun h => (noL h rfl w rfl hw).elim, fun h => (noLT h.1 rfl w hl hw).elim⟩
  · exact (not_applies hcl hdec.1).elim

/-! ## The predicate in the value model's reading, and the sentences -/

/-- **`preU` is true in the reading that takes a term without a result as the empty set**, at
every σ. -/
theorem trueV (σ : Subst) : TrueV d 1 σ preU := by
  show (∃ v, EvalTerm d σ lX (some v)) ∨ ¬ ∃ v, EvalTerm d σ lX (some v)
  exact Classical.em _

/-- h's argument sorts by name, and the clauses' variables (one, X:Int) as the sentences name
them. -/
def hArgs : List String := hFn.args.map d.sortName
def vs1 : List KoreAML.Var := canonVars d hCl1.vars

/-- The premise of each clause of `h`: `(⊤ ∧ X0 ∈ X) ∧ (⌈l(X)⌉ ∨ ¬⌈l(X)⌉)`. -/
def premU : Kore.Pattern :=
  .and R [premise hArgs none (Term.koreList d vs1 [.var 0]),
    .or R [.ceil (KoreAML.srt "Int") R (.app ⟨⟨"Lbll"⟩⟩ [] [KoreAML.varAt vs1 0]),
      .not R (.ceil (KoreAML.srt "Int") R (.app ⟨⟨"Lbll"⟩⟩ [] [KoreAML.varAt vs1 0]))]]

/-- **`Γ`'s sentences for the two clauses of `h`** state `h(X0) = 1` and `h(X0) = 2` under the one
premise `premU`, neither under an exclusion; both are among `h`'s equations. -/
theorem sentences :
    prioEquation d hFn hCl1 = eqnSentence d hFn premU (Term.kore d vs1 (iT 1)) (reqPat (srtOf d hFn.result) none) ∧
    prioEquation d hFn hCl2 = eqnSentence d hFn premU (Term.kore d vs1 (iT 2)) (reqPat (srtOf d hFn.result) none) ∧
    prioEquation d hFn hCl1 ∈ Faithful.fnEquationsK d hFn ∧ prioEquation d hFn hCl2 ∈ Faithful.fnEquationsK d hFn :=
  ⟨by rfl, by rfl, List.mem_map.mpr ⟨hCl1, by simp [hFn], rfl⟩, List.mem_map.mpr ⟨hCl2, by simp [hFn], rfl⟩⟩

/-! ## Axioms -/

/-- info: 'KCore.ClausePreUndecided.fnDet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms fnDet
/-- info: 'KCore.ClausePreUndecided.fnSolves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms fnSolves
/-- info: 'KCore.ClausePreUndecided.noH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms noH
/-- info: 'KCore.ClausePreUndecided.not_clausePreDecided' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms not_clausePreDecided

end ClausePreUndecided

end KCore
