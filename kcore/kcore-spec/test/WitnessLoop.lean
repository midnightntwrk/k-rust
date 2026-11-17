/-
  A clause whose witness's derivation contains a failure of the clause itself, and the text of
  `Clause.Witnessed` that cuts the loop. Run from the package root:
  `lake env lean -j1 test/WitnessLoop.lean`. Kernel-checked (`decide +kernel`).

  The semantics is the reader's for `f2-examples/opencl.kompile.kore` (Int, Bool, `S ::= a | c(Empty)`,
  Empty without a generator, `isC(c(_)) => true`, `isC(_) => false [owise]`), with `g`'s clauses
  written by hand (`c5`):
    g(0) => 0;  g(0) => 1 requires g(1) ==Int 0;
    g(1) => 1 requires isC(H:S) orBool g(0) ==Int 1   (`clC`: H open, S unconfined, conditions closed);
    g(_) => 0 [owise]
  `c5` has `sortedOKCl` and `coreOK`'s other conjuncts, and `clC` alone needs a witness (`dec`).
  `clC` fails at `[1]` (`FC`, reading `g(0)` as 0), so `g(1)` is 0 (`E10`), so `g(0)` is 1 (`E01`), so
  `clC`'s `requires` is `true` at H := a (`reqC_true`) and `g(1)` is also 1 (`E11`): `Eval` has two
  results at `g(1)` (`not_fnDet`). Values satisfying the conditions exist (`witC`, the text
  `WitnessedSome` below, without "no result but `true`"), and with it the clause hypothesis of
  `sound_at` would hold (`hc5`). Under `Clause.Witnessed` `clC` is not witnessed (`not_witDet`): at
  every value of S its `requires` also has the result `false`.

  The positive instance (`c6`): `g(1) => 1 requires H ==Int 0` (`clW`, H:Int open, Int unconfined)
  beside the text's `g(_) => 0 [owise]`. `clW` needs a witness and is `Witnessed` at H := 0, its
  second conjunct by inversion of the hook (`witW`); so `c6`'s clause hypothesis holds (`hc6`), and
  in every model of `Γc c6` each negated clause's exclusion is empty where it fails (`neg6`,
  `neg_of_coreCl`), nothing assumed of the model. A model of `Γc c6` is not exhibited here.

  `fnHyp_iff`: `FnHyp` and `FnHyp` with `WitnessedSome` in place of `Witnessed` are equivalent for
  every semantics, since `FnHyp`'s agreement and match-independence conjuncts give `FnDet`
  (`fnDet_of_agree`) and under `FnDet` the two texts agree (`Clause.witnessedDet_iff_of_fnDet`).
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

open KCore KCore.Faithful ML

namespace WitnessLoop

/-- Some values satisfy the clause's conditions (`Clause.Witnessed` without its "no result but
`true`"). -/
def WitnessedSome (c : Semantics) (cl : Clause) : Prop :=
  ∃ σ, c.WellSortedAt cl.vars cl.condVars σ ∧
    (∀ t, cl.req = some t → EvalTerm c σ t (some (bool true))) ∧ Holds c cl.vars.length σ cl.pre true

/-- `FnHyp` with `WitnessedSome` in place of `Witnessed`. -/
def FnHypSome (c : Semantics) : Prop :=
  (∀ fn ∈ c.fns, ∀ vs, c.sortsOf vs = some fn.args → ∃ r, Eval c fn.label vs r) ∧
  (∀ fn ∈ c.fns, fn.total = true → ∀ vs, c.sortsOf vs = some fn.args → ∃ v, Eval c fn.label vs (some v)) ∧
  (∀ fn ∈ c.fns, ClausesAgree c fn) ∧
  (∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, MatchIndependent c cl) ∧
  ((∀ r ∈ c.rules, r.needsWitness c = true → r.CondDecided c) ∧
    (∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, cl.needsWitness c = true → WitnessedSome c cl ∨ cl.Refuted c)) ∧
  OpenLaws c

/-- **`FnHyp` does not depend on the conjunct "no result but `true`"**, for every semantics. -/
theorem fnHyp_iff {c : Semantics} : FnHyp c ↔ FnHypSome c := by
  constructor
  · rintro ⟨h1, h2, h3, h4, ⟨hr, hcl⟩, hl⟩
    exact ⟨h1, h2, h3, h4, ⟨hr, fun fn hfn cl hcl' hw => (hcl fn hfn cl hcl' hw).imp
      (fun hd => (Clause.witnessedDet_iff_of_fnDet (fnDet_of_agree h3 h4) cl).mp hd) id⟩, hl⟩
  · rintro ⟨h1, h2, h3, h4, ⟨hr, hcl⟩, hl⟩
    exact ⟨h1, h2, h3, h4, ⟨hr, fun fn hfn cl hcl' hw => (hcl fn hfn cl hcl' hw).imp
      (fun hd => (Clause.witnessedDet_iff_of_fnDet (fnDet_of_agree h3 h4) cl).mpr hd) id⟩, hl⟩

definition_of defn from "f2-examples/opencl.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem

def i (n : Int) : Term := .dv Srt.int (.int n)

noncomputable def gText : List Clause := (c.fns.map (·.clauses)).getD 0 []
noncomputable def clO : Clause := gText.getD 0 { vars := [], pats := [], req := none, rhs := .var 0, ens := none }

def cl1 : Clause := { vars := [], pats := [i 0], req := none, rhs := i 0, ens := none }
def cl2 : Clause :=
  { vars := [], pats := [i 0], req := some (.app intEq [.app 389 [i 1], i 0]), rhs := i 1, ens := none }
def clC : Clause :=
  { vars := [32], pats := [i 1],
    req := some (.app boolOr [.app 390 [.var 0], .app intEq [.app 389 [i 0], i 1]]), rhs := i 1, ens := none }

noncomputable def g5 : Fn :=
  { label := 389, args := [Srt.int], result := Srt.int, clauses := [cl1, cl2, clC, clO] }

def ic1 : Clause :=
  { vars := [33], pats := [.app 387 [.var 0]], req := none, rhs := .dv Srt.bool (.bool true), ens := none }
def ic2 : Clause :=
  { vars := [32], pats := [.var 0], req := none, rhs := .dv Srt.bool (.bool false), ens := none, prio := 200 }
def isCF : Fn := { label := 390, args := [32], result := Srt.bool, clauses := [ic1, ic2], total := true }

noncomputable abbrev c5 : Semantics := { c with fns := g5 :: c.fns.drop 1 }

theorem hfn5 : c5.lookupFn 389 = some g5 := by rfl
theorem hfnC : c5.lookupFn 390 = some isCF := by rfl

theorem clO_facts : clO.prio = 200 ∧ clO.vars = [Srt.int] := by decide +kernel
theorem clO_pats : clO.pats = [.var 0] := by rfl
theorem clO_req : clO.req = none := by rfl
theorem clO_rhs : clO.rhs = .dv Srt.int (.int 0) := by rfl
theorem clO_ens : clO.ens = none := by rfl

/-- What `eval_den4_coreCl` asks, decided; `coreOK`'s conjuncts other than `sortedOK`; `clC` needs a
witness and no other clause does. -/
theorem dec : c5.sortedOKCl = true ∧ c5.srReady = true ∧ c5.ovls = [] ∧
    c5.subsorts.all (fun p => p.1 != p.2) = true ∧ c5.faithCoreOK = true ∧ patHooksApart c5 = true ∧
    c5.hooksApart = true ∧ c5.predsApart = true ∧ c5.idsOK = true ∧ c5.overloadsOK = true ∧
    clC.needsWitness c5 = true ∧ cl1.needsWitness c5 = false ∧ cl2.needsWitness c5 = false ∧
    clO.needsWitness c5 = false ∧ (∀ fn ∈ c.fns.drop 1, ∀ cl ∈ fn.clauses, cl.needsWitness c5 = false) ∧
    clC.reqClosed = true ∧ c5.confined 32 = false := by
  decide_cheap

instance ovl5 : OvlOK c5 := OvlOK.of_nil dec.2.2.1 dec.2.2.2.1

/-! ## No value has sort Empty -/

theorem subs_E : c5.subsorts.all (fun p => p.2 != 33) = true := by decide +kernel
theorem coll_E : c5.collOf 33 = none := by decide +kernel
theorem ctors_E : c5.ctorSigs.all (fun k => k.result != 33) = true := by decide +kernel

theorem noE (v : GroundTerm) (h : c5.sortOf v = some 33) : False := by
  cases v with
  | ctor f ts =>
    rw [Semantics.sortOf] at h
    cases hk : lookupSig c5.ctorSigs f with
    | none =>
      have : c5.lookupOvl f = none := rfl
      rw [hk, this, c5.lookupOpen_of_noRaw (by decide +kernel) f] at h; cases h
    | some k =>
      rw [hk] at h
      simp only at h
      split at h
      · have hm := List.mem_of_find?_eq_some (by rw [← lookupSig_eq]; exact hk)
        have := List.all_eq_true.mp ctors_E k hm
        simp [Option.some.inj h] at this
      · cases h
  | inj a b t =>
    rw [Semantics.sortOf] at h
    split at h
    · rename_i h'
      cases h
      simp only [Bool.and_eq_true, List.contains_iff_mem] at h'
      have := List.all_eq_true.mp subs_E _ h'.1.1
      simp at this
    · cases h
  | dv s' lit =>
    rw [Semantics.sortOf] at h
    split at h
    · rename_i h'
      cases h
      cases lit with
      | int _ => simp only [dvOK, beq_iff_eq] at h'; exact absurd h' (by decide)
      | bool _ => simp only [dvOK, beq_iff_eq] at h'; exact absurd h' (by decide)
      | float _ _ _ => simp only [dvOK, Bool.and_eq_true, beq_iff_eq] at h'; exact absurd h'.1 (by decide)
      | tok t =>
        simp only [dvOK, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h'
        rcases h' with ((h' | h') | h') | ⟨h' | h', -⟩
        · exact absurd h' (by decide)
        · exact absurd h' (by decide)
        · exact absurd h' (by decide +kernel)
        · exact absurd h' (by decide)
        · exact absurd h' (by decide +kernel)
    · cases h
  | map s' es | set s' es | list s' es =>
    have hs' : s' = 33 := by
      first
        | (obtain ⟨_, _, _, _, _, _, _, h⟩ := sortOf_mapS_fwd h; exact h.symm)
        | (obtain ⟨_, _, _, _, _, h⟩ := sortOf_setS.mp h; exact h.symm)
        | (obtain ⟨_, _, _, _, h⟩ := sortOf_listS.mp h; exact h.symm)
    subst hs'
    rw [Semantics.sortOf, coll_E] at h; cases h

/-! ## The evaluations -/

/-- `isC(v)` is `false` at every value of S: `isC(c(_))` matches no value. -/
theorem isC_false {v : GroundTerm} (hv : c5.sortOf v = some 32) :
    Eval c5 390 [v] (some (.dv Srt.bool (.bool false))) := by
  refine Eval.clause (cl := ic2) (σ := [(0, v)]) hfnC (List.mem_cons_of_mem _ (List.mem_singleton_self _))
    (fun j s hs => ?_) (.cons (.var rfl) .nil) (fun t ht => by cases ht) .top (fun cl' hcl' _ hlt => ?_) rfl .dv
    (fun t ht => by cases ht) .top
  · cases j with
    | zero => cases (show some (32 : Srt) = some s from hs); exact ⟨v, rfl, hv⟩
    | succ j => cases (show (none : Option Srt) = some s from hs)
  · rcases List.mem_cons.mp hcl' with rfl | hcl'
    · exact Fails.intro fun σ hσ _ => by
        obtain ⟨y, -, hy⟩ := hσ 0 (by decide) 33 rfl
        exact (noE y hy).elim
    · rw [List.mem_singleton.mp hcl'] at hlt; exact absurd hlt (Nat.lt_irrefl _)

theorem ev_isC {σ : Subst} {v : GroundTerm} (hl : σ.lookup 0 = some v) (hv : c5.sortOf v = some 32) :
    EvalTerm c5 σ (.app 390 [.var 0]) (some (.dv Srt.bool (.bool false))) :=
  .call (by decide +kernel) (by decide +kernel) (.cons .var .nil) (by rw [hl]; rfl) (isC_false hv)
    (by decide +kernel)

theorem ev_g {σ : Subst} {n : Int} {r : Option GroundTerm} (h : Eval c5 389 [.dv Srt.int (.int n)] r) :
    EvalTerm c5 σ (.app 389 [i n]) r :=
  .call (by decide +kernel) (by decide +kernel) (.cons .dv .nil) rfl h (by decide +kernel)

theorem g5_clauses : g5.clauses = [cl1, cl2, clC, clO] := rfl

/-- No clause of `g` has a priority below 50. -/
theorem low50 {cl' : Clause} (hcl' : cl' ∈ g5.clauses) (hlt : cl'.prio < 50) : False := by
  rw [g5_clauses] at hcl'
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hcl'
  rcases hcl' with rfl | rfl | rfl | rfl
  · exact absurd hlt (by decide)
  · exact absurd hlt (by decide)
  · exact absurd hlt (by decide)
  · rw [clO_facts.1] at hlt; exact absurd hlt (by decide)

/-- `g(0)` evaluates to 0, by `g(0) => 0`. -/
theorem E00 : Eval c5 389 [.dv Srt.int (.int 0)] (some (.dv Srt.int (.int 0))) :=
  Eval.clause (cl := cl1) (σ := []) hfn5 (by rw [g5_clauses]; simp)
    (fun j s hs => by cases (show (none : Option Srt) = some s from hs)) (.cons .dv .nil)
    (fun t ht => by cases ht) .top (fun cl' hcl' _ hlt => (low50 hcl' hlt).elim) rfl .dv (fun t ht => by cases ht)
    .top

/-- `g(1) => 1 requires isC(H) orBool g(0) ==Int 1` fails at `[1]`: at each value of S its
`requires` evaluates to `false`, reading `g(0)` as 0. -/
theorem FC : Fails c5 [.dv Srt.int (.int 1)] clC :=
  Fails.intro fun σ hσ _ => by
    obtain ⟨v, hl, hv⟩ := hσ 0 (by decide) 32 rfl
    refine ReqFails.intro (r := some (.dv Srt.bool (.bool false))) rfl ?_ (by intro h; cases h)
    exact .hook (by decide +kernel) (by decide +kernel)
      (.cons (ev_isC hl hv) (.cons (.hook (by decide +kernel) (by decide +kernel)
        (.cons (ev_g E00) (.cons .dv .nil)) (r := some (.dv Srt.bool (.bool false)))
        (fun vs hvs => by cases hvs; rfl) (fun h => by cases h)) .nil))
      (fun vs hvs => by cases hvs; rfl) (fun h => by cases h)

/-- `g(1)` evaluates to 0, by the `[owise]` clause: the other clauses fail. -/
theorem E10 : Eval c5 389 [.dv Srt.int (.int 1)] (some (.dv Srt.int (.int 0))) := by
  refine Eval.clause (cl := clO) (σ := [(0, .dv Srt.int (.int 1))]) hfn5 (by rw [g5_clauses]; simp)
    (fun j s hs => ?_) (by rw [clO_pats]; exact .cons (.var rfl) .nil)
    (fun t ht => by rw [clO_req] at ht; cases ht) (Clause.holds_preTop (by rfl) _)
    (fun cl' hcl' _ hlt => ?_) (by rfl) (by rw [clO_rhs]; exact .dv)
    (fun t ht => by rw [clO_ens] at ht; cases ht) (Clause.holds_postTop (by rfl) _)
  · rw [clO_facts.2] at hs
    cases j with
    | zero => cases hs; exact ⟨_, rfl, sortOf_int 1⟩
    | succ j => simp at hs
  · rw [g5_clauses] at hcl'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hcl'
    rcases hcl' with rfl | rfl | rfl | rfl
    · exact Fails.intro fun σ _ hpv => by
        cases hpv with
        | cons h _ => cases h
    · exact Fails.intro fun σ _ hpv => by
        cases hpv with
        | cons h _ => cases h
    · exact FC
    · exact absurd hlt (Nat.lt_irrefl _)

/-- `g(0)` evaluates to 1, by `g(0) => 1 requires g(1) ==Int 0`. -/
theorem E01 : Eval c5 389 [.dv Srt.int (.int 0)] (some (.dv Srt.int (.int 1))) :=
  Eval.clause (cl := cl2) (σ := []) hfn5 (by rw [g5_clauses]; simp)
    (fun j s hs => by cases (show (none : Option Srt) = some s from hs)) (.cons .dv .nil)
    (fun t ht => by
      cases ht
      exact .hook (by decide +kernel) (by decide +kernel) (.cons (ev_g E10) (.cons .dv .nil))
        (fun vs hvs => by cases hvs; rfl) (fun h => by cases h))
    .top (fun cl' hcl' _ hlt => (low50 hcl' hlt).elim) rfl .dv (fun t ht => by cases ht) .top

theorem a_S : c5.sortOf (.ctor 386 []) = some 32 := by decide +kernel

/-- The `requires` of `clC` evaluates to `true` at H := a, reading `g(0)` as 1. -/
theorem reqC_true : EvalTerm c5 [(0, .ctor 386 [])]
    (.app boolOr [.app 390 [.var 0], .app intEq [.app 389 [i 0], i 1]]) (some (.dv Srt.bool (.bool true))) :=
  .hook (by decide +kernel) (by decide +kernel)
    (.cons (ev_isC rfl a_S) (.cons (.hook (by decide +kernel) (by decide +kernel)
      (.cons (ev_g E01) (.cons .dv .nil)) (r := some (.dv Srt.bool (.bool true)))
      (fun vs hvs => by cases hvs; rfl) (fun h => by cases h)) .nil))
    (fun vs hvs => by cases hvs; rfl) (fun h => by cases h)

/-- **Values satisfy `clC`'s conditions**: H := a, reading `g(0)` as 1. -/
theorem witC : WitnessedSome c5 clC :=
  ⟨[(0, .ctor 386 [])], (fun j _ s hs => by
      cases j with
      | zero => cases (show some (32 : Srt) = some s from hs); exact ⟨_, rfl, a_S⟩
      | succ j => cases (show (none : Option Srt) = some s from hs)),
    (fun t ht => by cases ht; exact reqC_true), .top⟩

/-- `g(1)` evaluates to 1, by `clC` at its witness. -/
theorem E11 : Eval c5 389 [.dv Srt.int (.int 1)] (some (.dv Srt.int (.int 1))) :=
  Eval.clause (cl := clC) (σ := [(0, .ctor 386 [])]) hfn5 (by rw [g5_clauses]; simp)
    (fun j s hs => by
      cases j with
      | zero => cases (show some (32 : Srt) = some s from hs); exact ⟨_, rfl, a_S⟩
      | succ j => cases (show (none : Option Srt) = some s from hs))
    (.cons .dv .nil) (fun t ht => by cases ht; exact reqC_true)
    .top (fun cl' hcl' _ hlt => (low50 hcl' hlt).elim) rfl .dv (fun t ht => by cases ht) .top

/-- With `WitnessedSome`, every `needsWitness` clause of `c5` would be decided. -/
theorem hc5 : ∀ fn ∈ c5.fns, ∀ cl ∈ fn.clauses, cl.needsWitness c5 = true → WitnessedSome c5 cl ∨ cl.Refuted c5 := by
  intro fn hfn cl hcl hw
  rcases List.mem_cons.mp hfn with rfl | hfn
  · rw [g5_clauses] at hcl
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hcl
    rcases hcl with rfl | rfl | rfl | rfl
    · rw [dec.2.2.2.2.2.2.2.2.2.2.2.1] at hw; cases hw
    · rw [dec.2.2.2.2.2.2.2.2.2.2.2.2.1] at hw; cases hw
    · exact Or.inl witC
    · rw [dec.2.2.2.2.2.2.2.2.2.2.2.2.2.1] at hw; cases hw
  · rw [dec.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 fn hfn cl hcl] at hw; cases hw

/-- At the same values the `requires` also evaluates to `false`, reading `g(0)` as 0. -/
theorem reqC_false : EvalTerm c5 [(0, .ctor 386 [])]
    (.app boolOr [.app 390 [.var 0], .app intEq [.app 389 [i 0], i 1]]) (some (.dv Srt.bool (.bool false))) :=
  .hook (by decide +kernel) (by decide +kernel)
    (.cons (ev_isC rfl a_S) (.cons (.hook (by decide +kernel) (by decide +kernel)
      (.cons (ev_g E00) (.cons .dv .nil)) (r := some (.dv Srt.bool (.bool false)))
      (fun vs hvs => by cases hvs; rfl) (fun h => by cases h)) .nil))
    (fun vs hvs => by cases hvs; rfl) (fun h => by cases h)

theorem not_fnDet : ¬ FnDet c5 := fun h => by
  have := h _ _ _ _ E10 E11
  cases this

/-- **`clC` is not `Witnessed`**: at each value of S its `requires` also has the result `false`. -/
theorem not_witDet : ¬ clC.Witnessed c5 := by
  rintro ⟨σ, hσ, hreq, -⟩
  obtain ⟨v, hl, hv⟩ := hσ 0 (by decide +kernel) 32 rfl
  have hF : EvalTerm c5 σ (.app boolOr [.app 390 [.var 0], .app intEq [.app 389 [i 0], i 1]])
      (some (.dv Srt.bool (.bool false))) :=
    .hook (by decide +kernel) (by decide +kernel)
      (.cons (ev_isC hl hv) (.cons (.hook (by decide +kernel) (by decide +kernel)
        (.cons (ev_g E00) (.cons .dv .nil)) (r := some (.dv Srt.bool (.bool false)))
        (fun vs hvs => by cases hvs; rfl) (fun h => by cases h)) .nil))
      (fun vs hvs => by cases hvs; rfl) (fun h => by cases h)
  have := (hreq _ rfl).2 _ hF
  cases this

/-! ## A `needsWitness` clause that is `Witnessed`: `g(1) => 1 requires H ==Int 0`, H open -/

def clW : Clause :=
  { vars := [Srt.int], pats := [i 1], req := some (.app intEq [.var 0, i 0]), rhs := i 1, ens := none }

noncomputable def g6 : Fn :=
  { label := 389, args := [Srt.int], result := Srt.int, clauses := [clW, clO] }

noncomputable abbrev c6 : Semantics := { c with fns := g6 :: c.fns.drop 1 }

theorem dec6 : c6.sortedOKCl = true ∧ c6.srReady = true ∧ c6.ovls = [] ∧
    c6.subsorts.all (fun p => p.1 != p.2) = true ∧ c6.faithCoreOK = true ∧ patHooksApart c6 = true ∧
    c6.hooksApart = true ∧ c6.predsApart = true ∧ c6.idsOK = true ∧ c6.overloadsOK = true ∧
    clW.needsWitness c6 = true ∧ clO.needsWitness c6 = false ∧
    (∀ fn ∈ c.fns.drop 1, ∀ cl ∈ fn.clauses, cl.needsWitness c6 = false) ∧ c6.confined Srt.int = false := by
  decide_cheap

instance ovl6 : OvlOK c6 := OvlOK.of_nil dec6.2.2.1 dec6.2.2.2.1

/-- **`clW` is `Witnessed`** at H := 0: `0 ==Int 0` evaluates to `true`, and by inversion of the
hook to nothing else. -/
theorem witW : clW.Witnessed c6 := by
  refine ⟨[(0, .dv Srt.int (.int 0))], fun j _ s hs => ?_, fun t ht => ?_, .top⟩
  · cases j with
    | zero => cases (show some Srt.int = some s from hs); exact ⟨_, rfl, sortOf_int 0⟩
    | succ j => cases (show (none : Option Srt) = some s from hs)
  · cases ht
    refine ⟨.hook (by decide +kernel) (by decide +kernel) (.cons .var (.cons .dv .nil))
      (fun vs hvs => by cases hvs; rfl) (fun h => by cases h), fun r hr => ?_⟩
    cases hr with
    | ctor h _ => exact absurd h (by decide +kernel)
    | hook h hhk hts hh hund =>
      cases hts with
      | cons h1 hs1 =>
        cases h1
        cases hs1 with
        | cons h2 hs2 =>
          cases h2
          cases hs2
          have h3 := hh _ rfl
          have h4 : c6.hookRes intEq [.dv Srt.int (.int 0), .dv Srt.int (.int 0)] =
              some (some (.dv Srt.bool (.bool true))) := by rfl
          exact Option.some.inj (h3.symm.trans h4)
    | param h hhk hp _ _ => exact absurd hhk (by decide +kernel)
    | call h hh _ _ _ _ => exact absurd hh (by decide +kernel)
    | callUndef h hh _ _ _ => exact absurd hh (by decide +kernel)
    | ovl h ho _ => exact absurd ho (by decide +kernel)
    | ovlFn h ho => exact absurd ho (by decide +kernel)

/-- Every `needsWitness` clause of `c6` is decided: `sound_at`'s `hc` at `c6`. -/
theorem hc6 : ∀ fn ∈ c6.fns, ∀ cl ∈ fn.clauses, cl.needsWitness c6 = true → cl.CondDecided c6 := by
  intro fn hfn cl hcl hw
  rcases List.mem_cons.mp hfn with rfl | hfn
  · have hcl' : cl = clW ∨ cl = clO := by simpa [g6] using hcl
    rcases hcl' with rfl | rfl
    · exact Or.inl witW
    · rw [dec6.2.2.2.2.2.2.2.2.2.2.2.1] at hw; cases hw
  · rw [dec6.2.2.2.2.2.2.2.2.2.2.2.2.1 fn hfn cl hcl] at hw; cases hw

/-- **`neg_of_coreCl` at `c6`**, whose clause `clW` has `needsWitness`: in every model of `Γc c6`,
each negated clause's exclusion is empty where it fails, nothing assumed of the model. -/
theorem neg6 {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hI : I ⊧ᴵP Γc c6) :
    ∀ fn ∈ c6.allFns, ∀ cl ∈ fn.clauses, ClauseNeg c6 fn cl → ExclEmptyCl c6 I fn cl :=
  neg_of_coreCl hI dec6.1 dec6.2.1 dec6.2.2.2.2.1 dec6.2.2.2.2.2.1 hc6

/-- info: 'WitnessLoop.not_fnDet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms not_fnDet
/-- info: 'WitnessLoop.hc5' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hc5
/-- info: 'WitnessLoop.not_witDet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms not_witDet
/-- info: 'WitnessLoop.neg6' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms neg6
/-- info: 'WitnessLoop.fnHyp_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms fnHyp_iff
/-- info: 'KCore.Clause.witnessedDet_iff_of_fnDet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Clause.witnessedDet_iff_of_fnDet

end WitnessLoop
