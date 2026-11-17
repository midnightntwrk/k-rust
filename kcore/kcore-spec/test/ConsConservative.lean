/-
  The registry family at detached names is conservative, and no step at values rests on it
  (KcoreSpec/ConsConservative.lean), at the decided form of `Detached`: the statements exist as
  stated and depend on no axiom but `propext`, `Classical.choice` and `Quot.sound`. Run from the
  package root: `lake env lean test/ConsConservative.lean`.
-/
import KcoreSpec.ConsConservative

open KCore KCore.Cons ML Faithful

example (c : Semantics) (ss : List Srt) (ks : List Sym) (h : c.coreOK = true) (hf : FnHyp c)
    (hd : detachedB c ss ks = true) (hraw : ∀ p ∈ c.params, p.raw = false) :
    RegistryConservative c (DetachedB.names c ss ks) :=
  registry_conservative c ss ks h hf hd hraw

example (c : Semantics) (ss : List Srt) (ks : List Sym) (h : c.coreOK = true) (hf : FnHyp c)
    (hd : detachedB c ss ks = true) (hraw : ∀ p ∈ c.params, p.raw = false) :
    ExactOwn c (DetachedB.names c ss ks) :=
  exact_own c ss ks h hf hd hraw

/-- The extension itself is the model. -/
example {c : Semantics} {ss : List Srt} {ks : List Sym} (h : c.coreOK = true) (hf : FnHyp c)
    (hd : detachedB c ss ks = true) (hraw : ∀ p ∈ c.params, p.raw = false) {M : Type} [Inhabited M]
    {I : Interpretation KoreAML.Sym M} (hI : I ⊧ᴵP Γown c (DetachedB.names c ss ks)) :
    extModel c (DetachedB.names c ss ks) I ⊧ᴵP (Γc c ∪ Γstep c) :=
  ext_model_cv h hf hd hraw hI

/-- Detaching nothing: the decided check holds of the empty lists where the theory's lists pass
it, and the statement is then `exact_hyp`'s. -/
example (c : Semantics) (h : c.coreOK = true) (hf : FnHyp c) (hd : detachedB c [] [] = true)
    (hraw : ∀ p ∈ c.params, p.raw = false) (x y : Config c) :
    Step c x y ↔ ∃ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M),
      (I ⊧ᴵP Γown c (DetachedB.names c [] [])) ∧ ¬ (I ⊧ᴵ (den c x.val ⇒ ∼ KoreAML.sNext (den c y.val))) :=
  exact_own c [] [] h hf hd hraw x y

/-- info: 'KCore.registry_conservative' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms registry_conservative

/-- info: 'KCore.exact_own' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms exact_own
