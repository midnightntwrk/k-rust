/-
  The registry family at detached names is conservative, and no step at values rests on it
  (KcoreSpec/ConsConservative.lean), at the decided form of `Detached`: the statements exist as
  stated and depend on no axiom but `propext`, `Classical.choice` and `Quot.sound`. Run from the
  package root: `lake env lean test/ConsConservative.lean`.
-/
import KcoreSpec.ConsConservative

open KCore KCore.Cons ML Faithful

example (c : Semantics) (ss : List Srt) (ks : List Sym) (h : c.coreOK = true) (hf : FnHyp c) (hpreTop : c.clausesPreTop = true)
    (hd : detachedB c ss ks = true) :
    RegistryConservative c (DetachedB.names c ss ks) :=
  registry_conservative (hpreTop := hpreTop) c ss ks h hf hd

example (c : Semantics) (ss : List Srt) (ks : List Sym) (h : c.coreOK = true) (hf : FnHyp c) (hpreTop : c.clausesPreTop = true)
    (hd : detachedB c ss ks = true) :
    ExactOwn c (DetachedB.names c ss ks) :=
  exact_own (hpreTop := hpreTop) c ss ks h hf hd

/-- The extension itself is the model. -/
example {c : Semantics} {ss : List Srt} {ks : List Sym} (h : c.coreOK = true) (hf : FnHyp c)
    (hd : detachedB c ss ks = true)
    (hpre : ∀ fn ∈ c.allFns, ∀ cl ∈ fn.clauses, cl.pre = .top)
    (hvars : ∀ fn ∈ c.allFns, ∀ cl ∈ fn.clauses, ∀ s ∈ cl.vars, s < nRegSorts + c.sortNames.length)
    {M : Type} [Inhabited M]
    {I : Interpretation KoreAML.Sym M} (hI : I ⊧ᴵP Γown c (DetachedB.names c ss ks)) :
    extModel c (DetachedB.names c ss ks) I ⊧ᴵP (Γc c ∪ Γstep c) :=
  ext_model_cv h hf hd hpre hvars hI

/-- The two facts of the clauses that `ext_model_cv` takes, from `coreOK`, `FnHyp` and
`clausesPreTop`; a clause may bind variables by `\exists`. -/
example {c : Semantics} (h : c.coreOK = true) (hf : FnHyp c) (hpreTop : c.clausesPreTop = true) :
    (∀ fn ∈ c.allFns, ∀ cl ∈ fn.clauses, cl.pre = .top) ∧
    (∀ fn ∈ c.allFns, ∀ cl ∈ fn.clauses, ∀ s ∈ cl.vars, s < nRegSorts + c.sortNames.length) :=
  clauseFacts_cv (hpreTop := hpreTop) h hf

/-- Detaching nothing: the decided check holds of the empty lists where the theory's lists pass
it, and the statement is then `exact_hyp`'s. -/
example (c : Semantics) (h : c.coreOK = true) (hf : FnHyp c) (hpreTop : c.clausesPreTop = true) (hd : detachedB c [] [] = true)
    (x y : Config c) :
    Step c x y ↔ ∃ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M),
      (I ⊧ᴵP Γown c (DetachedB.names c [] [])) ∧ ¬ (I ⊧ᴵ (den c x.val ⇒ ∼ KoreAML.sNext (den c y.val))) :=
  exact_own (hpreTop := hpreTop) c [] [] h hf hd x y

/-- A detached set of names is the names of two lists, and the two statements hold at it where
the decided check holds of such lists. -/
example {c : Semantics} {D : KoreAML.Sym → Prop} (hd : Detached c D) :
    ∃ (ss : List Srt) (ks : List Sym), (∀ s ∈ ss, s < nRegSorts) ∧ (∀ k ∈ ks, ∃ h ∈ hookSigs, h.name = k) ∧
      D = DetachedB.names c ss ks :=
  hd.eq_names_cv

example (c : Semantics) (D : KoreAML.Sym → Prop) (ss : List Srt) (ks : List Sym)
    (h : c.coreOK = true) (hf : FnHyp c) (hpreTop : c.clausesPreTop = true) (hD : D = DetachedB.names c ss ks) (hd : detachedB c ss ks = true) :
    RegistryConservative c D ∧ ExactOwn c D :=
  registry_conservative_names_cv (hpreTop := hpreTop) c D ss ks h hf hD hd

/-- info: 'KCore.registry_conservative' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms registry_conservative

/-- info: 'KCore.exact_own' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms exact_own
