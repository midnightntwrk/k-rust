/-
  The Holds lemma at an `ex` binder of a sort that is not confined, in every model of `Γc`
  (`KCore.CE.holds_binder_fixed`, `holds_den_fixed`, `holdsAt_den_fixed`, `holds_den_bound`,
  KcoreSpec/HoldsDenFixed.lean; `holds_entails_fixed`, KcoreSpec/HoldsBinderFixed.lean), and
  `fixes_value_read` (KcoreSpec/FixesValue.lean); the reading of a truth value with its terms'
  readings over `Cond.boundV` (`KCore.CE.holdsAt_ex_fixed`, `holdsReadT_holdsAt_fixed`,
  `holdsReadT_holdsAt_bound`, `HoldsShape.HoldsReadT.congr_NIR`, KcoreSpec/HoldsDenFixed.lean) and
  the constructors' lemmas over a Bool (`HoldsShape.holdsAt_notB`, …, KcoreSpec/HoldsNode.lean).
  Run from the package root: `lake env lean -j1 test/HoldsBinderFixed.lean`.

  - The lemmas at `val := c.valued`, whose sorts have a value (`Semantics.valued_value`).
  - With `val` admitting no sort, `holds_entails_fixed` is the Holds lemma over `Cond.bound`.
  - The readings with the terms' readings at `c.valued`, and over `Cond.bound`.
  - The axioms of each.
-/
import KcoreSpec.HoldsBinderFixed

open KCore ML Faithful HoldsShape

namespace HoldsBinderFixedT

variable {c : Semantics} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}

/-- The `ex` case at `c.valued`. -/
example (h : c.coreOK = true) (hrc : c.readsConfined = true) (hIc : I ⊧ᴵP Γc c) (F : AtomFacts c I)
    (s : Srt) {body : Cond} (ih : HoldsDenB (Cond.boundV c c.valued) c I body) :
    HoldsDenB (Cond.boundV c c.valued) c I (.ex s body) :=
  CE.holds_binder_fixed h hrc hIc F (fun _ => Semantics.valued_value) s ih

/-- The lemma at `c.valued`, for every condition. -/
example (h : c.coreOK = true) (hIc : I ⊧ᴵP Γc c)
    (hc : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, cl.needsWitness c = true → cl.CondDecided c)
    (p : Cond) (hrc : hasBinder p = true → c.readsConfined = true) :
    HoldsDenB (Cond.boundV c c.valued) c I p :=
  CE.holds_entails_fixed h hIc hc (fun _ => Semantics.valued_value) p hrc

/-- With `val` admitting no sort it is the lemma over `Cond.bound`. -/
example (h : c.coreOK = true) (hIc : I ⊧ᴵP Γc c)
    (hc : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, cl.needsWitness c = true → cl.CondDecided c)
    (p : Cond) (hrc : hasBinder p = true → c.readsConfined = true) : HoldsDenB (Cond.bound c) c I p := by
  have : HoldsDenB (Cond.boundV c fun _ => false) c I p :=
    CE.holds_entails_fixed h hIc hc (fun _ hs => by cases hs) p hrc
  intro vars P σ b tbl e S hok hbd
  exact this hok (by rw [Cond.boundV_none]; exact hbd)

/-- The `ex` case with the terms' readings, at `c.valued`. -/
example (h : c.coreOK = true) (hrc : c.readsConfined = true) (hIc : I ⊧ᴵP Γc c) (N : NodeFacts c I)
    {n : Nat} {σ : Subst} {s : Srt} {body : Cond} {b : Bool} (g : Subst → Bool)
    (hb : ∀ σ', Extends c n [s] σ σ' → HoldsRead c I (n + 1) σ' body (g σ'))
    (ih : ∀ σ', Extends c n [s] σ σ' → HoldsAtB (Cond.boundV c c.valued) c I (n + 1) σ' body (g σ'))
    (hr : b = true ↔ ∃ σ', Extends c n [s] σ σ' ∧ g σ' = true) :
    HoldsAtB (Cond.boundV c c.valued) c I n σ (.ex s body) b :=
  CE.holdsAt_ex_fixed h hrc hIc N (fun _ => Semantics.valued_value) g hb ih hr

/-- A truth value with its terms' readings, read over `Cond.boundV` at `c.valued`. -/
example (h : c.coreOK = true) (hrc : c.readsConfined = true) (hIc : I ⊧ᴵP Γc c) (N : NodeFacts c I)
    {n : Nat} {σ : Subst} {p : Cond} {b : Bool} (hh : HoldsRead c I n σ p b) :
    HoldsAtB (Cond.boundV c c.valued) c I n σ p b :=
  CE.holdsReadT_holdsAt_fixed h hrc hIc N (fun _ => Semantics.valued_value) hh

/-- The same over `Cond.bound`, for a semantics `coreOKEx` accepts. -/
example (h : c.coreOKEx = true) (hrc : c.readsConfined = true) (hIc : I ⊧ᴵP Γc c) (N : NodeFacts c I)
    {n : Nat} {σ : Subst} {p : Cond} {b : Bool} (hh : HoldsRead c I n σ p b) :
    HoldsAtB (Cond.bound c) c I n σ p b :=
  CE.holdsReadT_holdsAt_bound (Semantics.coreOK_iff_ex.mpr h) hrc hIc N hh

/-- The congruence at the terms' readings in I. -/
example {n : Nat} {σ σ' : Subst} {p : Cond} {b : Bool} (hh : HoldsRead c I n σ p b)
    (ha : ∀ j ∈ varOccsCond n p, σ.lookup j = σ'.lookup j) : HoldsRead c I n σ' p b :=
  hh.congr_NIR (fun hT ha => hT.congr_occ fun i hi => (ha i hi).symm) σ' ha

/-- The constructors' lemmas over `Cond.boundV`: `all`, whose binder's elements are values'. -/
example (N : NodeFacts c I) (G : BinderFacts c I) {val : Srt → Bool} {n : Nat} {σ : Subst} {s : Srt}
    {body : Cond} {b : Bool} (g : Subst → Bool)
    (ih : ∀ σ', Extends c n [s] σ σ' → HoldsAtB (Cond.boundV c val) c I (n + 1) σ' body (g σ'))
    (hr : b = true ↔ ∀ σ', Extends c n [s] σ σ' → g σ' = true) :
    HoldsAtB (Cond.boundV c val) c I n σ (.all s body) b :=
  holdsAt_allB N (fun hb => by rw [Cond.boundV, Bool.and_eq_true] at hb; exact ⟨G.elemsValues hb.1, hb.2⟩) g ih hr

#check @CE.holds_binder_fixed
#check @CE.holds_den_fixed
#check @CE.holds_entails_fixed
#check @CE.holdsAt_den_fixed
#check @CE.holds_den_bound
#check @CE.fixes_value_read
#check @CE.fixes_value

/-- info: 'KCore.CE.holdsAt_ex_fixed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.CE.holdsAt_ex_fixed
/-- info: 'KCore.CE.holdsReadT_holdsAt_fixed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.CE.holdsReadT_holdsAt_fixed
/-- info: 'KCore.CE.holdsReadT_holdsAt_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.CE.holdsReadT_holdsAt_bound
/-- info: 'KCore.HoldsShape.HoldsReadT.congr_NIR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.HoldsShape.HoldsReadT.congr_NIR
/-- info: 'KCore.HoldsShape.holdsAt_exMatchB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.HoldsShape.holdsAt_exMatchB
/-- info: 'KCore.HoldsShape.holdsAt_allB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.HoldsShape.holdsAt_allB
#print axioms KCore.CE.holds_binder_fixed
#print axioms KCore.CE.holds_den_fixed
#print axioms KCore.CE.holds_entails_fixed
#print axioms KCore.CE.holdsAt_den_fixed
#print axioms KCore.CE.holds_den_bound
#print axioms KCore.CE.fixes_value_read
#print axioms KCore.CE.fixes_value

end HoldsBinderFixedT
