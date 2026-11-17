/-
  The extension of a model of the theory without the detached names satisfies the signature's
  premises that name nothing of `D` (KcoreSpec/ConsTransferSig.lean): the statements exist as
  stated and depend on no axiom but `propext`, `Classical.choice` and `Quot.sound`. Run from the
  package root: `lake env lean test/ConsTransferSig.lean`.
-/
import KcoreSpec.ConsTransferSig

open KCore KCore.Cons ML Faithful

example {c : Semantics} {D : KoreAML.Sym → Prop} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
    (hD : ∀ σ, D σ → plainSym σ) (hI : I ⊧ᴵP Γown c D) {φ : KoreAML.P} (hφ : ΓSig c φ)
    (hn : ∀ σ ∈ psyms φ, ¬ D σ) : extModel c D I ⊧ᴵ φ :=
  sat_own_sig hD hI hφ hn

example {c : Semantics} {D : KoreAML.Sym → Prop} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
    (hD : ∀ σ, D σ → plainSym σ) (hDI : KoreAML.DefOK I) (hc : I ⊧ᴵ KoreAML.ceilDefItem.pat) :
    (extModel c D I ⊧ᴵ KoreAML.ceilDefItem.pat) ∧ (extModel c D I ⊧ᴵ KoreAML.ceilArityItem.pat) :=
  ⟨sat_ceilDef_sg hD hDI hc, sat_ceilArity_sg hD hDI hc⟩

example {D D' : KoreAML.Sym → Prop} {V : List EVar} {W : List SVar} {k : OwnKind} {φ : KoreAML.P}
    (h : OwnSorted D' V W k φ) (hn : ∀ σ ∈ psyms φ, ¬ D σ) : OwnSorted D V W k φ :=
  ownSorted_clean_sg h hn

/-- info: 'KCore.Cons.sat_own_sig' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms sat_own_sig
