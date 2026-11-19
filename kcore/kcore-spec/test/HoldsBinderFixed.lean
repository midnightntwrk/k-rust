/-
  The Holds lemma at an `ex` binder of a sort that is not confined, in every model of `Γc`
  (`KCore.CE.holds_binder_fixed`, `holds_den_fixed`, `holdsAt_den_fixed`, `holds_den_bound`,
  KcoreSpec/HoldsDenFixed.lean; `holds_entails_fixed`, KcoreSpec/HoldsBinderFixed.lean), and
  `fixes_value_read` (KcoreSpec/FixesValue.lean).
  Run from the package root: `lake env lean -j1 test/HoldsBinderFixed.lean`.

  - The lemmas at `val := c.valued`, whose sorts have a value (`Semantics.valued_value`).
  - With `val` admitting no sort, `holds_entails_fixed` is the Holds lemma over `Cond.bound`.
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

#check @CE.holds_binder_fixed
#check @CE.holds_den_fixed
#check @CE.holds_entails_fixed
#check @CE.holdsAt_den_fixed
#check @CE.holds_den_bound
#check @CE.fixes_value_read
#check @CE.fixes_value

#print axioms KCore.CE.holds_binder_fixed
#print axioms KCore.CE.holds_den_fixed
#print axioms KCore.CE.holds_entails_fixed
#print axioms KCore.CE.holdsAt_den_fixed
#print axioms KCore.CE.holds_den_bound
#print axioms KCore.CE.fixes_value_read
#print axioms KCore.CE.fixes_value

end HoldsBinderFixedT
