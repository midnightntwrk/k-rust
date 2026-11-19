/-
  The registry family of `Γ` at a set of detached names, the theory without it, and the two
  statements that removing the family changes nothing the headlines say (`RegistryConservative`,
  `ExactOwn`). `Γ c` holds the interpreted builtin library whether or not the text of `c` imports a
  module: the sort constant of every registry sort, the arity, graph and fallback values of every
  interpreted hooked symbol, the value items and distinctness of every literal, the no-junk item
  and axioms of the library's collections. `D` names the registry sorts and hooked symbols a
  definition does not use.

  Definitions and two immediate lemmas; the two statements are not proved here.
-/
import KcoreSpec.Sound

set_option autoImplicit false

namespace KCore

open ML Faithful

/-- The symbols that occur in a pattern. -/
def psyms : KoreAML.P → List KoreAML.Sym
  | .evar _ | .svar _ | .bottom => []
  | .symbol σ => [σ]
  | .application φ ψ | .implication φ ψ => psyms φ ++ psyms ψ
  | .existential _ φ | .mu _ φ => psyms φ

/-- The registry family at the names `D`: one disjunct per place of `Γ` that writes a premise about
a registry sort or an interpreted hooked symbol, whatever the semantics' own lists hold: the sort
constant; the symbol's arity; its graph at values; the interpretation's value at a silent point;
that a value of the sort is one element of it; that two distinct values of the sort are distinct
elements; the no-junk item and the axioms of a library collection. -/
def RegistryItem (c : Semantics) (D : KoreAML.Sym → Prop) (φ : KoreAML.P) : Prop :=
  let Ds : Srt → Prop := fun s => s < nRegSorts ∧ D (.sort ("Sort" ++ c.sortName s))
  let Dk : CtorSig → Prop := fun k => k ∈ hookSigs ∧ D (.symbol (c.symName k.name))
  (∃ s, Ds s ∧ φ = (KoreAML.sortConstantItem (sortDeclOf c s)).pat) ∨
  (∃ k, Dk k ∧ φ = (symArityItem c k).pat) ∨
  (∃ (k : CtorSig) (vs : List GroundTerm) (r : Option GroundTerm),
      Dk k ∧ c.sortsOf vs = some k.args ∧ hook k.name vs = some r ∧
      (r = none → silent k.name vs = false) ∧
      φ = (KoreAML.den (symApp c k.name (GroundTerm.koreList c vs)) ≡ (match r with
        | some v => den c v
        | none => ⊥))) ∨
  (∃ (k : CtorSig) (vs : List GroundTerm),
      Dk k ∧ c.sortsOf vs = some k.args ∧ hook k.name vs = some none ∧ silent k.name vs = true ∧
      φ = (KoreAML.den (symApp c k.name (GroundTerm.koreList c vs)) ≡ (match c.fallback k.name vs with
        | some v => den c v
        | none => ⊥))) ∨
  (∃ (v : GroundTerm) (s : Srt), Ds s ∧ c.sortOf v = some s ∧
      φ = KoreAML.sExists ⟨1⟩ (sortP (c.sortName s)) (den c v ≡ .evar ⟨1⟩)) ∨
  (∃ (v w : GroundTerm) (s : Srt), Ds s ∧ (distinctSorts c).contains s = true ∧
      c.sortOf v = some s ∧ c.sortOf w = some s ∧ GroundTerm.cmp v w ≠ .eq ∧
      φ = ∼(den c v ⋀ den c w)) ∨
  (∃ k ∈ builtinColls, Ds k.sort ∧ (φ = collNoJunk c k ∨ φ ∈ collAxioms c k))

/-- The theory without the premises that name a symbol of `D`. -/
def Γown (c : Semantics) (D : KoreAML.Sym → Prop) : Premises KoreAML.Sym := fun φ =>
  (Γc c ∪ Γstep c) φ ∧ ∀ σ ∈ psyms φ, ¬ D σ

/-- `D` is detached from `c`: it names registry sorts and interpreted hooked symbols only, and every
premise of the theory that names one of them is the library's own; it names no library collection
sort that has axioms at elements (Map, Set, List). For a text that does not declare one of those
three, `D` cannot hold that sort and `Γown` keeps the library's premises about it. -/
def Detached (c : Semantics) (D : KoreAML.Sym → Prop) : Prop :=
  (∀ σ, D σ → (∃ s, s < nRegSorts ∧ σ = .sort ("Sort" ++ c.sortName s)) ∨
              (∃ k ∈ hookSigs, σ = .symbol (c.symName k.name))) ∧
  (∀ k ∈ builtinColls, D (.sort ("Sort" ++ c.sortName k.sort)) → collAxioms c k = []) ∧
  ∀ φ, (Γc c ∪ Γstep c) φ → (∃ σ ∈ psyms φ, D σ) → RegistryItem c D φ

/-- Model form: a model of the smaller theory embeds into a model of the whole theory in which a
symbol outside `D`, and application, hold of old elements what they held. The last two clauses are
one-directional on purpose: `⌈m⌉`, `⟦Sort⟧` and a literal's `dv` symbol gain new elements in `I'`. -/
def RegistryConservative (c : Semantics) (D : KoreAML.Sym → Prop) : Prop :=
  ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M), (I ⊧ᴵP Γown c D) →
    ∃ (M' : Type) (_ : Inhabited M') (I' : Interpretation KoreAML.Sym M') (ι : M → M'),
      Function.Injective ι ∧ (I' ⊧ᴵP (Γc c ∪ Γstep c)) ∧
      (∀ σ, ¬ D σ → ∀ m, ι m ∈ I'.evalSymb σ ↔ m ∈ I.evalSymb σ) ∧
      (∀ a b m, ι m ∈ I'.evalApp (ι a) (ι b) ↔ m ∈ I.evalApp a b)

/-- Sentence form at the headline's sentences: the steps at values that some model of the smaller
theory has are `Step`'s. It is the own-theory form of `ExactC` only: the entailments of `SoundC`'s
second conjunct and of `CompleteC` have own forms it does not give. -/
def ExactOwn (c : Semantics) (D : KoreAML.Sym → Prop) : Prop := ∀ x y : Config c,
  Step c x y ↔ ∃ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M),
    (I ⊧ᴵP Γown c D) ∧ ¬ (I ⊧ᴵ (den c x.val ⇒ ∼ KoreAML.sNext (den c y.val)))

/-- Detaching nothing leaves the theory. -/
theorem Γown_none (c : Semantics) : Γown c (fun _ => False) = Γc c ∪ Γstep c := by
  funext φ
  exact propext ⟨fun h => h.1, fun h => ⟨h, fun _ _ hD => hD⟩⟩

/-- A model of the theory is a model of the smaller one. -/
theorem Γown_of_model {c : Semantics} {D : KoreAML.Sym → Prop} {M : Type} {I : Interpretation KoreAML.Sym M}
    (h : I ⊧ᴵP (Γc c ∪ Γstep c)) : I ⊧ᴵP Γown c D := fun φ hφ => h φ hφ.1

/-- **The left-to-right half of `ExactOwn`**, from `exact_hyp`: a step of `Step` is one some model
of the smaller theory has, the model of the whole theory. It needs no `Detached`. -/
theorem exact_own_mp (c : Semantics) (D : KoreAML.Sym → Prop) (h : c.coreOK = true) (hf : FnHyp c)
    {x y : Config c} (hs : Step c x y) :
    ∃ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M),
      (I ⊧ᴵP Γown c D) ∧ ¬ (I ⊧ᴵ (den c x.val ⇒ ∼ KoreAML.sNext (den c y.val))) := by
  obtain ⟨M, hM, I, hI, hn⟩ := (exact_hyp c h hf x y).mp hs
  exact ⟨M, hM, I, Γown_of_model hI, hn⟩

/-- `psyms φ` followed by `acc`, built without copying a list at each application or implication
(`psymsAcc_eq`). -/
def psymsAcc : KoreAML.P → List KoreAML.Sym → List KoreAML.Sym
  | .evar _, acc | .svar _, acc | .bottom, acc => acc
  | .symbol σ, acc => σ :: acc
  | .application φ ψ, acc | .implication φ ψ, acc => psymsAcc φ (psymsAcc ψ acc)
  | .existential _ φ, acc | .mu _ φ, acc => psymsAcc φ acc

theorem psymsAcc_eq : ∀ (φ : KoreAML.P) (acc : List KoreAML.Sym), psymsAcc φ acc = psyms φ ++ acc
  | .evar _, _ | .svar _, _ | .bottom, _ | .symbol _, _ => rfl
  | .application φ ψ, acc | .implication φ ψ, acc => by
    simp only [psymsAcc, psyms, psymsAcc_eq φ, psymsAcc_eq ψ, List.append_assoc]
  | .existential _ φ, acc | .mu _ φ, acc => by simp only [psymsAcc, psyms, psymsAcc_eq φ]

/-- `psyms` computed with an accumulator. -/
def psymsByAcc (φ : KoreAML.P) : List KoreAML.Sym := psymsAcc φ []

/-- The compiled code computes `psyms` with an accumulator. -/
@[csimp] theorem psyms_eq_psymsByAcc : @psyms = @psymsByAcc := by
  funext φ
  rw [psymsByAcc, psymsAcc_eq, List.append_nil]

end KCore
