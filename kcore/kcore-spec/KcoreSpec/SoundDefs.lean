/-
  KCore. The statements of the specification (KCORE-SPEC.md §9) over the matching-logic theory of
  a semantics (`Γc`, Faithful.lean), as definitions; Sound.lean proves them.

  - `SoundC c`: `Γc c` with the step's closure (`Γstep`) has a model, and for every step of `Step`,
    by the rule r under σ (`StepBy`), in every model x has a successor among the instances of that
    application (`famEx`), and y is one of them.
  - `CompleteC c ref`: for an outcome function `ref` that lists, at each configuration, the
    successors by the rules whose left side binds every variable and a family for each unblocked
    match of the other rules (`OutIs`), with the step's closure every successor of x is in an
    outcome `ref` lists.
  - `ExactC c`: `Step` is exactly the steps some model of the theory has, at values.
  - `Consistent c`: the theory with the step's closure has a model.
-/
import KcoreSpec.FaithfulFamilies
import KcoreSpec.StepOld

set_option autoImplicit false

namespace KCore

open ML Faithful

/-! ## The statements over a semantics -/

/-- **Soundness.** The theory with the step's closure has a model; and for every step of `Step`,
by the rule r under σ: in every model, x has a successor among the instances of that application,
and y is one of those instances. -/
def SoundC (c : Semantics) : Prop :=
  (∃ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M), I ⊧ᴵP (Γc c ∪ Γstep c)) ∧
  ∀ (x y : Config c) (r : Rule) (σ : Subst), StepBy c r σ x y →
    (Γc c ⊧ (den c x.val ⇒ KoreAML.sNext (famEx c r σ))) ∧
    (Γc c ⊧ (den c y.val ⇒ famEx c r σ))

/-- `ref` lists, at x: exactly `Step`'s successors by the rules whose left side binds every
variable; and, for each other rule, a family for each unblocked match (up to the values of the
variables the left side binds) and no other family. -/
def OutIs (c : Semantics) (ref : OutFn) : Prop := ∀ x : Config c,
  (∀ y, .val y ∈ ref x.val ↔
     ∃ (hy : c.sortOf y = some topCellSort) (r : Rule) (σ : Subst),
       r.opens = [] ∧ StepBy c r σ x ⟨y, hy⟩) ∧
  (∀ r σ, .fam r σ ∈ ref x.val → r ∈ c.rules ∧ r.opens ≠ [] ∧ Unblocked c r σ x.val) ∧
  (∀ r ∈ c.rules, r.opens ≠ [] → ∀ σ, Unblocked c r σ x.val →
     ∃ σ', (∀ i ∈ varOccs r.lhs, σ'.lookup i = σ.lookup i) ∧ .fam r σ' ∈ ref x.val)

/-- **Completeness.** For `ref` listing the outcomes at each configuration, with the step's
closure every successor of x is in an outcome `ref` lists. -/
def CompleteC (c : Semantics) (ref : OutFn) : Prop :=
  OutIs c ref → ∀ x : Config c,
    (Γc c ∪ Γstep c) ⊧
      (den c x.val ⇒ KoreAML.allNext (KoreAML.disjList ((ref x.val).map (Outcome.pat c))))

/-- **Exactness.** `Step` is exactly the steps some model of the theory has, at values. -/
def ExactC (c : Semantics) : Prop := ∀ x y : Config c,
  Step c x y ↔ ∃ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M),
    (I ⊧ᴵP (Γc c ∪ Γstep c)) ∧ ¬ (I ⊧ᴵ (den c x.val ⇒ ∼ KoreAML.sNext (den c y.val)))

/-- **The theory of `c` is consistent**: `Γc c` with the step's closure has a model. `Γ` holds no
functional axiom of a function, so a function's `[total]` declaration is not read here. The theory
with those axioms (`Faithful.Model.ΓTotal`: `∃y. f(x̄) = y` for each function declared `total`) has
a model under `coreOK` and `FnHyp`: `has_model_total` (over `Γ`), `sound_total` (over `Γc`). -/
def Consistent (c : Semantics) : Prop :=
  ∃ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M), I ⊧ᴵP (Γc c ∪ Γstep c)

end KCore
