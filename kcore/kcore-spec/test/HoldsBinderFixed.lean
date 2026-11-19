/-
  The Holds lemma at an `ex` binder of a sort that is not confined, in every model of `Γc`
  (`KCore.CE.holds_binder_fixed`, `holds_den_fixed`, `holdsAt_den_fixed`, `holds_den_bound`,
  KcoreSpec/HoldsDenFixed.lean; `holds_entails_fixed`, KcoreSpec/HoldsBinderFixed.lean), and
  `fixes_value_read` (KcoreSpec/FixesValue.lean); the reading of a truth value with its terms'
  readings over `Cond.boundV` (`KCore.CE.holdsAt_ex_fixed`, `holdsReadT_holdsAt_fixed`,
  `holdsReadT_holdsAt_bound`, KcoreSpec/HoldsDenFixed.lean; `HoldsShape.HoldsReadT.congr_NIR`,
  KcoreSpec/HoldsRead.lean) and
  the constructors' lemmas over a Bool (`HoldsShape.holdsAt_notB`, …, KcoreSpec/HoldsNode.lean).
  Run from the package root: `lake env lean -j1 test/HoldsBinderFixed.lean`.

  - The lemmas at `val := c.hasValue`, whose sorts have a value on `coreOK` (`hasValue_value`).
  - At `val := c.hasValue`, `holds_entails_fixed` is the Holds lemma over `Cond.bound`.
  - The readings with the terms' readings at `c.hasValue`, and over `Cond.bound`.
  - The axioms of each.
-/
import KcoreSpec.HoldsBinderFixed

open KCore ML Faithful HoldsShape

namespace HoldsBinderFixedT

variable {c : Semantics} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}

/-- The `ex` case at `c.hasValue`. -/
example (h : c.coreOK = true) (hrc : c.readsConfined = true) (hIc : I ⊧ᴵP Γc c) (F : AtomFacts c I)
    (s : Srt) {body : Cond} (ih : HoldsDenB (Cond.boundV c c.hasValue) c I body) :
    HoldsDenB (Cond.boundV c c.hasValue) c I (.ex s body) :=
  CE.holds_binder_fixed h hrc hIc F (fun _ => hasValue_value h) s ih

/-- The lemma at `c.hasValue`, for every condition. -/
example (h : c.coreOK = true) (hIc : I ⊧ᴵP Γc c)
    (hc : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, cl.needsWitness c = true → cl.CondDecided c)
    (p : Cond) (hrc : hasBinder p = true → c.readsConfined = true) :
    HoldsDenB (Cond.boundV c c.hasValue) c I p :=
  CE.holds_entails_fixed h hIc hc (fun _ => hasValue_value h) p hrc

/-- At `c.hasValue` it is the lemma over `Cond.bound` (`Cond.bound_eq_boundV`). -/
example (h : c.coreOK = true) (hIc : I ⊧ᴵP Γc c)
    (hc : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, cl.needsWitness c = true → cl.CondDecided c)
    (p : Cond) (hrc : hasBinder p = true → c.readsConfined = true) : HoldsDenB (Cond.bound c) c I p :=
  Cond.bound_eq_boundV c ▸ CE.holds_entails_fixed h hIc hc (fun _ => hasValue_value h) p hrc

/-- The `ex` case with the terms' readings, at `c.hasValue`. -/
example (h : c.coreOK = true) (hrc : c.readsConfined = true) (hIc : I ⊧ᴵP Γc c) (N : NodeFacts c I)
    {n : Nat} {σ : Subst} {s : Srt} {body : Cond} {b : Bool} (g : Subst → Bool)
    (hb : ∀ σ', Extends c n [s] σ σ' → HoldsRead c I (n + 1) σ' body (g σ'))
    (ih : ∀ σ', Extends c n [s] σ σ' → HoldsAtB (Cond.boundV c c.hasValue) c I (n + 1) σ' body (g σ'))
    (hr : b = true ↔ ∃ σ', Extends c n [s] σ σ' ∧ g σ' = true) :
    HoldsAtB (Cond.boundV c c.hasValue) c I n σ (.ex s body) b :=
  CE.holdsAt_ex_fixed h hrc hIc N (fun _ => hasValue_value h) g hb ih hr

/-- A truth value with its terms' readings, read over `Cond.boundV` at `c.hasValue`. -/
example (h : c.coreOK = true) (hrc : c.readsConfined = true) (hIc : I ⊧ᴵP Γc c) (N : NodeFacts c I)
    {n : Nat} {σ : Subst} {p : Cond} {b : Bool} (hh : HoldsRead c I n σ p b) :
    HoldsAtB (Cond.boundV c c.hasValue) c I n σ p b :=
  CE.holdsReadT_holdsAt_fixed h hrc hIc N (fun _ => hasValue_value h) hh

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
