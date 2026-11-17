/-
  An equation whose right side is a union of alternatives, against its split into one equation per
  alternative: a lemma of matching logic over arbitrary patterns, in a model of definedness.

  The sentence is `prem → F = ⋁ₖ (aₖ ∧ ⌈Eₖ⌉)`: where `prem` holds, the elements of F are those of
  the alternatives aₖ whose condition Eₖ is defined. The split is, with `preₖ := ⌈aₖ⌉ ∧ ⌈Eₖ⌉`
  ("the alternative is defined and its condition holds"):
  - for each k, `prem ∧ preₖ → F = aₖ`;
  - `prem ∧ ⋀ₖ ¬preₖ → F = ⊥`.

  The split entails the sentence in every interpretation (`unionSentence_of_split`): each
  alternative whose `pre` holds is F, the others are empty or their conditions fail, and where none
  holds both sides are empty.
  The sentence entails the last equation in every interpretation (`noneClause_of_union`), and the
  equation of alternative k where F has at most one element (`altClause_of_union`): `aₖ ∧ ⌈Eₖ⌉` is
  then non-empty and inside F, so it is F. That is what the functional sentence `∃y. F = y` gives
  (`functional_one`); without it F may hold the elements of two alternatives, and then is neither.
  No alternative need be single-valued, and nothing is asked of `prem`.

  These are the unsorted connectives of matching logic (`⇒`, `≡`, `⌈_⌉`, `⋀`, `⋁`). A translated
  KORE sentence carries its sorts (`sEquals`, `sOr`, `sCeil`, the guards of its variables): it is
  not literally `unionSentence`, and reading one as the other is the work of the lemma that uses
  this one.
-/
import KcoreSpec.FaithfulTr

set_option autoImplicit false

namespace KoreAML

open ML

namespace TieUnion

/-- Alternative `(a, E)` on the right side: `a ∧ ⌈E⌉`. -/
def altBody (x : P × P) : P := x.1 ⋀ ⌈x.2⌉

/-- Alternative `(a, E)` is defined and its condition holds: `⌈a⌉ ∧ ⌈E⌉`. -/
def altPre (x : P × P) : P := ⌈x.1⌉ ⋀ ⌈x.2⌉

/-- `prem → F = ⋁ₖ (aₖ ∧ ⌈Eₖ⌉)`. -/
def unionSentence (prem F : P) (alts : List (P × P)) : P := prem ⇒ (F ≡ disjList (alts.map altBody))

/-- `prem ∧ ⌈a⌉ ∧ ⌈E⌉ → F = a`. -/
def altClause (prem F : P) (x : P × P) : P := (prem ⋀ altPre x) ⇒ (F ≡ x.1)

/-- `prem ∧ ⋀ₖ ¬(⌈aₖ⌉ ∧ ⌈Eₖ⌉) → F = ⊥`. -/
def noneClause (prem F : P) (alts : List (P × P)) : P :=
  (prem ⋀ conjList (alts.map fun x => ∼(altPre x))) ⇒ (F ≡ ⊥)

/-- `∃y. F = y`. -/
def functional (y : EVar) (F : P) : P := ∃∃ y (F ≡ .evar y)

variable {M : Type} {I : Interpretation Sym M} {e : Valuation M}

theorem interp_disjList : ∀ {φs : List P} {m : M},
    (disjList φs).interpret I e m ↔ ∃ φ ∈ φs, φ.interpret I e m
  | [], m => by simp [disjList]
  | [φ], m => by simp [disjList]
  | φ :: ψ :: φs, m => by
    show (φ ⋁ disjList (ψ :: φs)).interpret I e m ↔ _
    rw [interpret_disj, interp_disjList (φs := ψ :: φs)]
    simp only [List.mem_cons, exists_eq_or_imp]

theorem interp_conjListAll : ∀ {φs : List P} {m : M},
    (conjList φs).interpret I e m ↔ ∀ φ ∈ φs, φ.interpret I e m
  | [], m => by simp [conjList, Pattern.top]
  | [φ], m => by simp [conjList]
  | φ :: ψ :: φs, m => by
    show (φ ⋀ conjList (ψ :: φs)).interpret I e m ↔ _
    rw [interpret_conj, interp_conjListAll (φs := ψ :: φs)]
    simp only [List.mem_cons, forall_eq_or_imp]

section
variable (hD : DefOK I)
include hD

theorem interp_altBody {x : P × P} {m : M} :
    (altBody x).interpret I e m ↔ x.1.interpret I e m ∧ ∃ b, x.2.interpret I e b := by
  unfold altBody; rw [interpret_conj, interp_defined hD]

theorem interp_altPre {x : P × P} {m : M} :
    (altPre x).interpret I e m ↔ (∃ b, x.1.interpret I e b) ∧ ∃ b, x.2.interpret I e b := by
  unfold altPre; rw [interpret_conj, interp_defined hD, interp_defined hD]

theorem interp_unionSentence {prem F : P} {alts : List (P × P)} {m : M} :
    (unionSentence prem F alts).interpret I e m ↔ (prem.interpret I e m →
      ∀ a, F.interpret I e a ↔ ∃ x ∈ alts, x.1.interpret I e a ∧ ∃ b, x.2.interpret I e b) := by
  unfold unionSentence
  rw [interpret_impl, interp_equal hD]
  refine imp_congr_right fun _ => forall_congr' fun a => iff_congr Iff.rfl ?_
  rw [interp_disjList]
  constructor
  · rintro ⟨φ, hφ, ha⟩
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hφ
    exact ⟨x, hx, (interp_altBody hD).mp ha⟩
  · rintro ⟨x, hx, ha⟩
    exact ⟨_, List.mem_map.mpr ⟨x, hx, rfl⟩, (interp_altBody hD).mpr ha⟩

theorem interp_altClause {prem F : P} {x : P × P} {m : M} :
    (altClause prem F x).interpret I e m ↔ (prem.interpret I e m →
      (∃ b, x.1.interpret I e b) → (∃ b, x.2.interpret I e b) →
      ∀ a, F.interpret I e a ↔ x.1.interpret I e a) := by
  unfold altClause
  rw [interpret_impl, interpret_conj, interp_altPre hD, interp_equal hD]
  exact ⟨fun h hp ha hE => h ⟨hp, ha, hE⟩, fun h hp => h hp.1 hp.2.1 hp.2.2⟩

theorem interp_noneClause {prem F : P} {alts : List (P × P)} {m : M} :
    (noneClause prem F alts).interpret I e m ↔ (prem.interpret I e m →
      (∀ x ∈ alts, ¬ ((∃ b, x.1.interpret I e b) ∧ ∃ b, x.2.interpret I e b)) →
      ∀ a, ¬ F.interpret I e a) := by
  unfold noneClause
  rw [interpret_impl, interpret_conj, interp_equal hD]
  rw [interp_conjListAll]
  constructor
  · intro h hp hn a ha
    exact (interpret_bottom (I := I) (e := e)).mp ((h ⟨hp, fun φ hφ => by
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hφ
      rw [interpret_neg, interp_altPre hD]; exact hn x hx⟩ a).mp ha)
  · intro h hp a
    refine ⟨fun ha => (h hp.1 (fun x hx => ?_) a ha).elim, fun hb => (interpret_bottom.mp hb).elim⟩
    have := hp.2 _ (List.mem_map.mpr ⟨x, hx, rfl⟩)
    rwa [interpret_neg, interp_altPre hD] at this

/-- **The sentence gives the equation of each alternative**, at a valuation where F has at most
one element. -/
theorem altClause_of_union {prem F : P} {alts : List (P × P)} {m : M}
    (hone : ∀ a b, F.interpret I e a → F.interpret I e b → a = b)
    (h : (unionSentence prem F alts).interpret I e m) {x : P × P} (hx : x ∈ alts) :
    (altClause prem F x).interpret I e m := by
  rw [interp_altClause hD]
  rw [interp_unionSentence hD] at h
  intro hp ⟨b, hb⟩ hE a
  have hFb : F.interpret I e b := (h hp b).mpr ⟨x, hx, hb, hE⟩
  constructor
  · intro ha
    rw [hone a b ha hFb]; exact hb
  · intro ha
    exact (h hp a).mpr ⟨x, hx, ha, hE⟩

/-- **The sentence gives the last equation**: where no alternative is defined with its condition,
F is empty. -/
theorem noneClause_of_union {prem F : P} {alts : List (P × P)} {m : M}
    (h : (unionSentence prem F alts).interpret I e m) : (noneClause prem F alts).interpret I e m := by
  rw [interp_noneClause hD]
  rw [interp_unionSentence hD] at h
  intro hp hn a ha
  obtain ⟨x, hx, hxa, hE⟩ := (h hp a).mp ha
  exact hn x hx ⟨⟨a, hxa⟩, hE⟩

/-- **The equations give the sentence**, with nothing asked of F. -/
theorem unionSentence_of_split {prem F : P} {alts : List (P × P)} {m : M}
    (hk : ∀ x ∈ alts, (altClause prem F x).interpret I e m)
    (hn : (noneClause prem F alts).interpret I e m) : (unionSentence prem F alts).interpret I e m := by
  rw [interp_unionSentence hD]
  rw [interp_noneClause hD] at hn
  intro hp a
  constructor
  · intro ha
    refine Classical.byContradiction fun hno => ?_
    refine hn hp (fun x hx hae => hno ⟨x, hx, ?_, hae.2⟩) a ha
    exact ((interp_altClause hD).mp (hk x hx) hp hae.1 hae.2 a).mp ha
  · rintro ⟨x, hx, hxa, hE⟩
    exact ((interp_altClause hD).mp (hk x hx) hp ⟨a, hxa⟩ hE a).mpr hxa

/-- **What the functional sentence states**: where y is not free in F, F has at most one element
(it has exactly one). -/
theorem functional_one {y : EVar} {F : P} (hy : F.isFreeEvar y = false) {m : M}
    (h : (functional y F).interpret I e m) : ∀ a b, F.interpret I e a → F.interpret I e b → a = b := by
  unfold functional at h
  rw [interpret_exists] at h
  obtain ⟨v, hv⟩ := h
  rw [interp_equal hD] at hv
  have hF : ∀ a, F.interpret I e a ↔ a = v := fun a => by
    rw [← only_free_var_relevant (I := I) (Function.update e.evalEvar y v) e.evalEvar e.evalSvar e.evalSvar
      (fun x hx => by
        by_cases hxy : x = y
        · rw [hxy, hy] at hx; cases hx
        · simp [Function.update, hxy]) (fun _ _ => rfl) a, hv a]
    simp [Pattern.interpret, Function.update]
  intro a b ha hb
  rw [(hF a).mp ha, (hF b).mp hb]

end

/-! ## As entailments -/

/-- The sentence, F's functional sentence and definedness. -/
def TextSide (y : EVar) (prem F : P) (alts : List (P × P)) : Premises Sym :=
  fun φ => φ = unionSentence prem F alts ∨ φ = functional y F ∨ ∃ x : EVar, φ = @definedness Sym _ x

/-- The n+1 equations and definedness. -/
def SplitSide (prem F : P) (alts : List (P × P)) : Premises Sym :=
  fun φ => (∃ x ∈ alts, φ = altClause prem F x) ∨ φ = noneClause prem F alts ∨
    ∃ x : EVar, φ = @definedness Sym _ x

/-- The sentence with F's functional sentence entails the equation of each alternative. -/
theorem text_entails_alt {y : EVar} {prem F : P} {alts : List (P × P)} (hy : F.isFreeEvar y = false)
    {x : P × P} (hx : x ∈ alts) : TextSide y prem F alts ⊧ altClause prem F x := by
  intro M _ I hI e m
  have hD : DefOK I := defOK_of fun z => hI _ (.inr (.inr ⟨z, rfl⟩))
  exact altClause_of_union hD (functional_one hD hy (hI _ (.inr (.inl rfl)) e m)) (hI _ (.inl rfl) e m) hx

/-- The sentence entails the last equation (the functional sentence is not read). -/
theorem text_entails_none {y : EVar} {prem F : P} {alts : List (P × P)} :
    TextSide y prem F alts ⊧ noneClause prem F alts := by
  intro M _ I hI e m
  have hD : DefOK I := defOK_of fun z => hI _ (.inr (.inr ⟨z, rfl⟩))
  exact noneClause_of_union hD (hI _ (.inl rfl) e m)

/-- The n+1 equations entail the sentence, with no functional sentence. -/
theorem split_entails_text {prem F : P} {alts : List (P × P)} :
    SplitSide prem F alts ⊧ unionSentence prem F alts := by
  intro M _ I hI e m
  have hD : DefOK I := defOK_of fun z => hI _ (.inr (.inr ⟨z, rfl⟩))
  exact unionSentence_of_split hD (fun x hx => hI _ (.inl ⟨x, hx, rfl⟩) e m) (hI _ (.inr (.inl rfl)) e m)

end TieUnion

end KoreAML
