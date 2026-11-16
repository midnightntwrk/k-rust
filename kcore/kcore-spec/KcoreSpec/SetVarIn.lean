/-
  A function sentence whose arguments are memberships in one set variable, as kompile writes
  `rule f(@S, @S) => r`: `X₀ ∈ @S ∧ X₁ ∈ @S → f(X₀, X₁) = r`. Read as an axiom, the set variable is
  free and the sentence holds for every set `S` inside the arguments' sort. When `S` stands in no
  other part of the sentence, the two memberships state nothing: the set `{x₀, x₁}` holds both
  elements, so the sentence at every `S` is the sentence with the two memberships dropped, at every
  valuation of the element variables and every point. Stated on the translated patterns (`tr`'s
  `sImp`, `sAnd`, `sIn` and `.svar`), in every model of definedness; nothing here is about K's
  semantics beyond the translation.
-/
import KcoreSpec.FaithfulTr

set_option autoImplicit false

namespace KCore

open ML KoreAML

variable {M : Type} {I : Interpretation KoreAML.Sym M}

/-- The valuation `e` with the set variable `X` sent to `A`. -/
def svarAt_svin (e : Valuation M) (X : SVar) (A : Set M) : Valuation M :=
  ⟨e.evalEvar, Function.update e.evalSvar X A⟩

theorem interp_svarAt_svin {ψ : P} {e : Valuation M} {X : SVar} {A : Set M}
    (h : ψ.isFreeSvar X = false) (m : M) :
    ψ.interpret I (svarAt_svin e X A) m ↔ ψ.interpret I e m :=
  only_free_var_relevant _ _ _ _ (fun _ _ => rfl) (fun Y hY => by
    have hne : Y ≠ X := by rintro rfl; rw [h] at hY; cases hY
    simp [Function.update, hne]) m

/-- **The membership conjuncts over a set variable that stands nowhere else are dropped.**
A sentence `Q ∧ (x₀ ∈ X ∧ (x₁ ∈ X ∧ T)) → φ` of the result sort `R` (the shape `tr` gives a
function equation's left side `\and(Q, \and(\in(X₀, @S), \and(\in(X₁, @S), T)))`), with the
memberships `\in{S, R}`, holds at a point for every set `X` inside the sort `S` exactly where
`Q ∧ T → φ` holds there, when `X` is free in none of `S`, `R`, `Q`, `T`, `φ` and `x₀`, `x₁` are
elements of `S` (the axiom's guards). -/
theorem setvar_in_drop [Inhabited M] (hD : DefOK I) (hc : I ⊧ᴵ ceilDefItem.pat)
    {e : Valuation M} {S R Q T φ : P} {σ ρ : M} {x₀ x₁ : EVar} {X : SVar}
    (hS : ∀ a, S.interpret I e a ↔ a = σ) (hR : ∀ a, R.interpret I e a ↔ a = ρ)
    (hσ : IsSort I σ) (hρ : IsSort I ρ)
    (h₀ : Inh I σ (e.evalEvar x₀)) (h₁ : Inh I σ (e.evalEvar x₁))
    (hXS : S.isFreeSvar X = false) (hXR : R.isFreeSvar X = false) (hXQ : Q.isFreeSvar X = false)
    (hXT : T.isFreeSvar X = false) (hXφ : φ.isFreeSvar X = false) (m : M) :
    (∀ A : Set M, (∀ a, A a → Inh I σ a) →
      (sImp R (sAnd Q (sAnd (sIn S R (.evar x₀) (.svar X)) (sAnd (sIn S R (.evar x₁) (.svar X)) T)))
        φ).interpret I (svarAt_svin e X A) m) ↔
    (sImp R (sAnd Q T) φ).interpret I e m := by
  have tS := fun A => interp_svarAt_svin (I := I) (e := e) (A := A) hXS
  have tR := fun A => interp_svarAt_svin (I := I) (e := e) (A := A) hXR
  have tQ := fun A => interp_svarAt_svin (I := I) (e := e) (A := A) hXQ
  have tT := fun A => interp_svarAt_svin (I := I) (e := e) (A := A) hXT
  have tφ := fun A => interp_svarAt_svin (I := I) (e := e) (A := A) hXφ
  -- each membership `xᵢ ∈ X` at `X := A`: `xᵢ`'s value is in `A`, on the sort `ρ`
  have hin : ∀ (A : Set M) (x : EVar), Inh I σ (e.evalEvar x) →
      ((sIn S R (.evar x) (.svar X)).interpret I (svarAt_svin e X A) m ↔ A (e.evalEvar x) ∧ Inh I ρ m) := by
    intro A x hx
    rw [interp_sIn hD hc (fun a => (tS A a).trans (hS a)) (fun a => (tR A a).trans (hR a)) hσ hρ
      (fun a ha => by rw [interp_evar] at ha; rw [ha]; exact hx) m]
    have hX' : (Pattern.svar X : P).interpret I (svarAt_svin e X A) = A := by
      simp [svarAt_svin, Pattern.interpret]
    simp only [interp_evar, hX']
    exact and_congr_left fun _ => ⟨fun ⟨_, ha, h⟩ => ha ▸ h, fun h => ⟨_, rfl, h⟩⟩
  have hinh : ∀ A : Set M, (inhOf R).interpret I (svarAt_svin e X A) m ↔ Inh I ρ m :=
    fun A => interp_inhOf_of fun a => (tR A a).trans (hR a)
  simp only [interp_sImp, interp_sAnd, hinh, interp_inhOf_of hR]
  constructor
  · intro h
    let A₀ : Set M := fun a => a = e.evalEvar x₀ ∨ a = e.evalEvar x₁
    have := h A₀ (fun a ha => by rcases ha with rfl | rfl <;> assumption)
    rw [hin A₀ _ h₀, hin A₀ _ h₁, tQ, tT, tφ] at this
    refine ⟨this.1, fun ⟨hq, ht⟩ => this.2 ⟨hq, ⟨Or.inl rfl, this.1⟩, ⟨Or.inr rfl, this.1⟩, ht⟩⟩
  · rintro ⟨hm, hf⟩ A _
    rw [hin A _ h₀, hin A _ h₁, tQ, tT, tφ]
    exact ⟨hm, fun ⟨hq, _, _, ht⟩ => hf ⟨hq, ht⟩⟩

/-! ## The `[owise]` exclusion of such an equation

kompile writes the disjunct of an `[owise]` equation's exclusion for `rule f(@S, @S) => r` with one
element variable `G` in the set variable's place, `∃G. Q ∧ (x₀ ∈ G ∧ (x₁ ∈ G ∧ T))`: an element
variable denotes one element, so the disjunct holds exactly where the two arguments are equal
(`owise_diag_svin`). The equation as read (`setvar_in_drop`) applies at every pair, and its disjunct,
with two distinct bound variables, holds wherever `Q` and `T` do (`owise_split_svin`). The text's
disjunct entails the read one, so the text's `[owise]` sentence, which negates it, entails the
sentence that negates the read one (`owise_disjunct_narrower`). -/

/-- `ψ` at the valuation `e` with the element variable `x` sent to `a`, for `x` not free in `ψ`. -/
theorem interp_evarAt_svin {ψ : P} {e : Valuation M} {x : EVar} {a : M}
    (h : ψ.isFreeEvar x = false) (m : M) :
    ψ.interpret I ⟨Function.update e.evalEvar x a, e.evalSvar⟩ m ↔ ψ.interpret I e m :=
  only_free_var_relevant _ _ _ _ (fun y hy => by
    have hne : y ≠ x := by rintro rfl; rw [h] at hy; cases hy
    simp [Function.update, hne]) (fun _ _ => rfl) m

/-- A membership of an element variable in an element variable: their values are one. -/
theorem interp_sIn_evar_svin [Inhabited M] (hD : DefOK I) (hc : I ⊧ᴵ ceilDefItem.pat)
    {e : Valuation M} {S R : P} {σ ρ : M} {x y : EVar}
    (hS : ∀ a, S.interpret I e a ↔ a = σ) (hR : ∀ a, R.interpret I e a ↔ a = ρ)
    (hσ : IsSort I σ) (hρ : IsSort I ρ) (hx : Inh I σ (e.evalEvar x)) (m : M) :
    (sIn S R (.evar x) (.evar y)).interpret I e m ↔ e.evalEvar x = e.evalEvar y ∧ Inh I ρ m := by
  rw [interp_sIn hD hc hS hR hσ hρ (fun a ha => by rw [interp_evar] at ha; rw [ha]; exact hx) m]
  simp only [interp_evar]
  exact and_congr_left fun _ => ⟨fun ⟨_, h₁, h₂⟩ => h₁ ▸ h₂, fun h => ⟨_, rfl, h⟩⟩

/-- **The diagonal.** `∃G. Q ∧ (x₀ ∈ G ∧ (x₁ ∈ G ∧ T))`, `G` an element variable of the sort `S`
free in none of `S`, `R`, `Q`, `T` and neither `x₀` nor `x₁`, holds at a point exactly where the
values of `x₀` and `x₁` are one and `Q` and `T` hold, inside the sort `R`. -/
theorem owise_diag_svin [Inhabited M] (hD : DefOK I) (hc : I ⊧ᴵ ceilDefItem.pat)
    {e : Valuation M} {S R Q T : P} {σ ρ : M} {x₀ x₁ g : EVar}
    (hS : ∀ a, S.interpret I e a ↔ a = σ) (hR : ∀ a, R.interpret I e a ↔ a = ρ)
    (hσ : IsSort I σ) (hρ : IsSort I ρ)
    (h₀ : Inh I σ (e.evalEvar x₀)) (h₁ : Inh I σ (e.evalEvar x₁)) (hx₀ : x₀ ≠ g) (hx₁ : x₁ ≠ g)
    (hgS : S.isFreeEvar g = false) (hgR : R.isFreeEvar g = false)
    (hgQ : Q.isFreeEvar g = false) (hgT : T.isFreeEvar g = false) (m : M) :
    (sExists g S (sAnd Q (sAnd (sIn S R (.evar x₀) (.evar g))
      (sAnd (sIn S R (.evar x₁) (.evar g)) T)))).interpret I e m ↔
      e.evalEvar x₀ = e.evalEvar x₁ ∧ Q.interpret I e m ∧ T.interpret I e m ∧ Inh I ρ m := by
  rw [interp_sExists]
  have key : ∀ a : M,
      ((g ∈∈ inhOf S : P).interpret I ⟨Function.update e.evalEvar g a, e.evalSvar⟩ m ∧
        (sAnd Q (sAnd (sIn S R (.evar x₀) (.evar g)) (sAnd (sIn S R (.evar x₁) (.evar g)) T))).interpret
          I ⟨Function.update e.evalEvar g a, e.evalSvar⟩ m) ↔
      Inh I σ a ∧ Q.interpret I e m ∧ (e.evalEvar x₀ = a ∧ Inh I ρ m) ∧
        (e.evalEvar x₁ = a ∧ Inh I ρ m) ∧ T.interpret I e m := by
    intro a
    have hS1 := fun b => (interp_evarAt_svin (I := I) (e := e) (a := a) hgS b).trans (hS b)
    have hR1 := fun b => (interp_evarAt_svin (I := I) (e := e) (a := a) hgR b).trans (hR b)
    have e₀ : Function.update e.evalEvar g a x₀ = e.evalEvar x₀ := Function.update_noteq hx₀ _ _
    have e₁ : Function.update e.evalEvar g a x₁ = e.evalEvar x₁ := Function.update_noteq hx₁ _ _
    rw [interp_member hD, interp_inhOf_of hS1, interp_sAnd, interp_sAnd, interp_sAnd,
      interp_sIn_evar_svin hD hc hS1 hR1 hσ hρ (by simpa [e₀] using h₀),
      interp_sIn_evar_svin hD hc hS1 hR1 hσ hρ (by simpa [e₁] using h₁),
      interp_evarAt_svin hgQ, interp_evarAt_svin hgT]
    simp only [Function.update_same, e₀, e₁]
  simp only [key]
  constructor
  · rintro ⟨a, _, hq, ⟨ha₀, hm⟩, ⟨ha₁, _⟩, ht⟩
    exact ⟨ha₀.trans ha₁.symm, hq, ht, hm⟩
  · rintro ⟨h01, hq, ht, hm⟩
    exact ⟨_, h₀, hq, ⟨rfl, hm⟩, ⟨h01.symm, hm⟩, ht⟩

/-- **The disjunct as read.** `∃G. ∃G'. Q ∧ (x₀ ∈ G ∧ (x₁ ∈ G' ∧ T))`, `G` and `G'` distinct element
variables of the sort `S`, each free in none of `S`, `R`, `Q`, `T` and neither `x₀` nor `x₁`, holds
at a point exactly where `Q` and `T` hold, inside the sort `R`: at every pair of values of `x₀`
and `x₁`. -/
theorem owise_split_svin [Inhabited M] (hD : DefOK I) (hc : I ⊧ᴵ ceilDefItem.pat)
    {e : Valuation M} {S R Q T : P} {σ ρ : M} {x₀ x₁ g g' : EVar}
    (hS : ∀ a, S.interpret I e a ↔ a = σ) (hR : ∀ a, R.interpret I e a ↔ a = ρ)
    (hσ : IsSort I σ) (hρ : IsSort I ρ)
    (h₀ : Inh I σ (e.evalEvar x₀)) (h₁ : Inh I σ (e.evalEvar x₁))
    (hx₀ : x₀ ≠ g) (hx₁ : x₁ ≠ g) (hx₀' : x₀ ≠ g') (hx₁' : x₁ ≠ g') (hgg' : g ≠ g')
    (hgS : S.isFreeEvar g = false) (hgR : R.isFreeEvar g = false)
    (hgQ : Q.isFreeEvar g = false) (hgT : T.isFreeEvar g = false)
    (hgS' : S.isFreeEvar g' = false) (hgR' : R.isFreeEvar g' = false)
    (hgQ' : Q.isFreeEvar g' = false) (hgT' : T.isFreeEvar g' = false) (m : M) :
    (sExists g S (sExists g' S (sAnd Q (sAnd (sIn S R (.evar x₀) (.evar g))
      (sAnd (sIn S R (.evar x₁) (.evar g')) T))))).interpret I e m ↔
      Q.interpret I e m ∧ T.interpret I e m ∧ Inh I ρ m := by
  rw [interp_sExists]
  have key : ∀ a : M,
      ((g ∈∈ inhOf S : P).interpret I ⟨Function.update e.evalEvar g a, e.evalSvar⟩ m ∧
        (sExists g' S (sAnd Q (sAnd (sIn S R (.evar x₀) (.evar g))
          (sAnd (sIn S R (.evar x₁) (.evar g')) T)))).interpret
          I ⟨Function.update e.evalEvar g a, e.evalSvar⟩ m) ↔
      Inh I σ a ∧ ∃ a', Inh I σ a' ∧ Q.interpret I e m ∧ (e.evalEvar x₀ = a ∧ Inh I ρ m) ∧
        (e.evalEvar x₁ = a' ∧ Inh I ρ m) ∧ T.interpret I e m := by
    intro a
    let e₁ : Valuation M := ⟨Function.update e.evalEvar g a, e.evalSvar⟩
    have hS1 : ∀ b, S.interpret I e₁ b ↔ b = σ :=
      fun b => (interp_evarAt_svin (I := I) (e := e) (a := a) hgS b).trans (hS b)
    have hR1 : ∀ b, R.interpret I e₁ b ↔ b = ρ :=
      fun b => (interp_evarAt_svin (I := I) (e := e) (a := a) hgR b).trans (hR b)
    rw [interp_member hD, interp_inhOf_of hS1, interp_sExists]
    simp only [Function.update_same]
    refine and_congr_right fun _ => exists_congr fun a' => ?_
    have hS2 := fun b => (interp_evarAt_svin (I := I) (e := e₁) (a := a') hgS' b).trans (hS1 b)
    have hR2 := fun b => (interp_evarAt_svin (I := I) (e := e₁) (a := a') hgR' b).trans (hR1 b)
    have e₀ : Function.update (Function.update e.evalEvar g a) g' a' x₀ = e.evalEvar x₀ := by
      rw [Function.update_noteq hx₀', Function.update_noteq hx₀]
    have e₁' : Function.update (Function.update e.evalEvar g a) g' a' x₁ = e.evalEvar x₁ := by
      rw [Function.update_noteq hx₁', Function.update_noteq hx₁]
    have eg : Function.update (Function.update e.evalEvar g a) g' a' g = a := by
      rw [Function.update_noteq hgg', Function.update_same]
    have hQ2 := (interp_evarAt_svin (I := I) (e := e₁) (a := a') hgQ' m).trans
      (interp_evarAt_svin (I := I) (e := e) (a := a) hgQ m)
    have hT2 := (interp_evarAt_svin (I := I) (e := e₁) (a := a') hgT' m).trans
      (interp_evarAt_svin (I := I) (e := e) (a := a) hgT m)
    rw [interp_member hD, interp_inhOf_of hS2, interp_sAnd, interp_sAnd, interp_sAnd,
      interp_sIn_evar_svin hD hc hS2 hR2 hσ hρ (by simpa [e₁, e₀] using h₀),
      interp_sIn_evar_svin hD hc hS2 hR2 hσ hρ (by simpa [e₁, e₁'] using h₁), hQ2, hT2]
    simp only [e₁, Function.update_same, e₀, e₁', eg]
  simp only [key]
  constructor
  · rintro ⟨a, _, a', _, hq, ⟨_, hm⟩, _, ht⟩
    exact ⟨hq, ht, hm⟩
  · rintro ⟨hq, ht, hm⟩
    exact ⟨_, h₀, _, h₁, hq, ⟨rfl, hm⟩, ⟨rfl, hm⟩, ht⟩

/-- **The `[owise]` sentence with kompile's disjunct entails the one with the disjunct as read.**
`Q' ∧ ¬(D ∨ D₂) ∧ P → φ` at the sort `R` (the shape `tr` gives an `[owise]` equation, `D₂` the
other disjuncts), with `D` kompile's disjunct `∃G. Q ∧ (x₀ ∈ G ∧ (x₁ ∈ G ∧ T))`, entails it with
`D` replaced by `∃G. ∃G'. Q ∧ (x₀ ∈ G ∧ (x₁ ∈ G' ∧ T))`: the first disjunct entails the second
(take `G'` to be `G`), so the second premise is the narrower. `G'` is bound in the disjunct only,
so it is free in none of the disjunct's other parts. -/
theorem owise_disjunct_narrower [Inhabited M] (hD : DefOK I) (hc : I ⊧ᴵ ceilDefItem.pat)
    {e : Valuation M} {S R Q T D₂ Pr φ : P} {σ ρ : M} {x₀ x₁ g g' : EVar}
    (hS : ∀ a, S.interpret I e a ↔ a = σ) (hR : ∀ a, R.interpret I e a ↔ a = ρ)
    (hσ : IsSort I σ) (hρ : IsSort I ρ)
    (h₀ : Inh I σ (e.evalEvar x₀)) (h₁ : Inh I σ (e.evalEvar x₁))
    (hx₀ : x₀ ≠ g) (hx₁ : x₁ ≠ g) (hx₀' : x₀ ≠ g') (hx₁' : x₁ ≠ g') (hgg' : g ≠ g')
    (hgS : S.isFreeEvar g = false) (hgR : R.isFreeEvar g = false)
    (hgQ : Q.isFreeEvar g = false) (hgT : T.isFreeEvar g = false)
    (hgS' : S.isFreeEvar g' = false) (hgR' : R.isFreeEvar g' = false)
    (hgQ' : Q.isFreeEvar g' = false) (hgT' : T.isFreeEvar g' = false) (m : M) :
    (sImp R (sAnd (sNot R (sOr R (sExists g S (sAnd Q (sAnd (sIn S R (.evar x₀) (.evar g))
      (sAnd (sIn S R (.evar x₁) (.evar g)) T)))) D₂)) Pr) φ).interpret I e m →
    (sImp R (sAnd (sNot R (sOr R (sExists g S (sExists g' S (sAnd Q (sAnd (sIn S R (.evar x₀) (.evar g))
      (sAnd (sIn S R (.evar x₁) (.evar g')) T))))) D₂)) Pr) φ).interpret I e m := by
  have hw := owise_diag_svin hD hc hS hR hσ hρ h₀ h₁ hx₀ hx₁ hgS hgR hgQ hgT m
  have hr := owise_split_svin hD hc hS hR hσ hρ h₀ h₁ hx₀ hx₁ hx₀' hx₁' hgg' hgS hgR hgQ hgT
    hgS' hgR' hgQ' hgT' m
  simp only [interp_sImp, interp_sAnd, interp_sNot, interp_sOr, hw, hr]
  rintro ⟨hm, h⟩
  refine ⟨hm, fun ⟨⟨hn, hi⟩, hp⟩ => h ⟨⟨fun ⟨hi', hor⟩ => hn ⟨hi', ?_⟩, hi⟩, hp⟩⟩
  exact hor.imp_left fun ⟨_, hq, ht, hm'⟩ => ⟨hq, ht, hm'⟩

/-! ## The sentence kompile writes for `rule f(@S, @S) => r()`

test/constructs/fixtures/e3-setvar-nonlinear/kore.txt, the axiom of `f`'s rule (attributes left
out): its translation is the left side of `setvar_in_drop`, and the reading with the two memberships
dropped is the translation of the same sentence with `\and{R}(\top{R}(), \top{R}())` as its left
side. -/

section E3SetvarNonlinear
open Kore (KSort Pattern)

/-- The sort variable `R`, the sort `SortExp{}`. -/
def svinR : KSort := .var ⟨⟨⟨"R"⟩⟩⟩
def svinExp : KSort := .ctor ⟨⟨"SortExp"⟩⟩ []
/-- `X0:SortExp{}`, `X1:SortExp{}`, `@VarS:SortExp{}`. -/
def svinX0 : Kore.EVar := ⟨⟨⟨"X0"⟩⟩, svinExp⟩
def svinX1 : Kore.EVar := ⟨⟨⟨"X1"⟩⟩, svinExp⟩
def svinS : Kore.SVar := ⟨⟨⟨"VarS"⟩⟩, svinExp⟩

/-- `\equals{SortExp{},R}(Lblf{}(X0, X1), \and{SortExp{}}(Lblr{}(), \top{SortExp{}}()))`. -/
def svinEq : Pattern :=
  .equals svinExp svinR (.app ⟨⟨"Lblf"⟩⟩ [] [.var (.evar svinX0), .var (.evar svinX1)])
    (.and svinExp [.app ⟨⟨"Lblr"⟩⟩ [] [], .top svinExp])

/-- The axiom of `rule f(@S, @S) => r()`. -/
def svinAx : Pattern :=
  .implies svinR
    (.and svinR [.top svinR,
      .and svinR [.in svinExp svinR (.var (.evar svinX0)) (.var (.svar svinS)),
        .and svinR [.in svinExp svinR (.var (.evar svinX1)) (.var (.svar svinS)), .top svinR]]])
    svinEq

/-- The axiom with its two memberships dropped. -/
def svinRead : Pattern := .implies svinR (.and svinR [.top svinR, .top svinR]) svinEq

/-- The axiom's variable table (`trAxiom`'s) and translation context. -/
def svinCtx : Ctx := ⟨tableOf [⟨⟨⟨"R"⟩⟩⟩] svinAx, []⟩

/-- `setvar_in_drop` at the fixture's sentence: at every point, the translated axiom holds for
every set `@VarS` inside `SortExp` exactly where the translated sentence without the memberships
holds. -/
theorem setvar_in_drop_e3 [Inhabited M] (hD : DefOK I) (hc : I ⊧ᴵ ceilDefItem.pat)
    {e : Valuation M} {σ ρ : M}
    (hS : ∀ a, (trSort svinCtx.vars svinExp).interpret I e a ↔ a = σ)
    (hR : ∀ a, (trSort svinCtx.vars svinR).interpret I e a ↔ a = ρ)
    (hσ : IsSort I σ) (hρ : IsSort I ρ)
    (h₀ : Inh I σ (e.evalEvar (svinCtx.vars.ev (evarKey svinX0))))
    (h₁ : Inh I σ (e.evalEvar (svinCtx.vars.ev (evarKey svinX1)))) (m : M) :
    (∀ A : Set M, (∀ a, A a → Inh I σ a) →
      (tr svinCtx svinAx).interpret I (svarAt_svin e (svinCtx.vars.sv (svarKey svinS)) A) m) ↔
    (tr svinCtx svinRead).interpret I e m :=
  setvar_in_drop hD hc hS hR hσ hρ h₀ h₁ (by decide) (by decide) (by decide) (by decide) (by decide) m

end E3SetvarNonlinear

/-! ## The sentences kompile writes for `rule f(@S, @S) => one()` beside `rule f(_, _) => two() [owise]`

test/constructs/fixtures/e3-setvar-owise/kore.txt, the axioms at `//@ 202` (the first rule) and
`//@ 203` (the `[owise]` rule), attributes left out. The second's exclusion disjunct for the first
binds one element variable `Var'Unds'Gen2` at both arguments; the reader reads it with a second,
`Var'Unds'Gen2'`, at the second argument (`Parse.svinExcl?`), and that is the disjunct of the
`[owise]` sentence the reading emits (`Emit.exclusion`). Both `[owise]` sentences are translated
with the table of the read one, which holds every variable of the text's and the fresh one. -/

section E3SetvarOwise
open Kore (KSort Pattern)

/-- `Var'Unds'Gen0`, `Var'Unds'Gen1`, `Var'Unds'Gen2` (the text's) and `Var'Unds'Gen2'` (the
reader's), all of `SortExp{}`. -/
def svoGen0 : Kore.EVar := ⟨⟨⟨"Var'Unds'Gen0"⟩⟩, svinExp⟩
def svoGen1 : Kore.EVar := ⟨⟨⟨"Var'Unds'Gen1"⟩⟩, svinExp⟩
def svoGen2 : Kore.EVar := ⟨⟨⟨"Var'Unds'Gen2"⟩⟩, svinExp⟩
def svoGen2' : Kore.EVar := ⟨⟨⟨"Var'Unds'Gen2'"⟩⟩, svinExp⟩

/-- `\equals{SortExp{},R}(Lblf{}(X0, X1), \and{SortExp{}}(Lbl<c>{}(), \top{SortExp{}}()))`. -/
def svoEq (c : String) : Pattern :=
  .equals svinExp svinR (.app ⟨⟨"Lblf"⟩⟩ [] [.var (.evar svinX0), .var (.evar svinX1)])
    (.and svinExp [.app ⟨⟨c⟩⟩ [] [], .top svinExp])

/-- The axiom of `rule f(@S, @S) => one()`. -/
def svoAx : Pattern :=
  .implies svinR
    (.and svinR [.top svinR,
      .and svinR [.in svinExp svinR (.var (.evar svinX0)) (.var (.svar svinS)),
        .and svinR [.in svinExp svinR (.var (.evar svinX1)) (.var (.svar svinS)), .top svinR]]])
    (svoEq "Lblone")

/-- The axiom with its two memberships dropped. -/
def svoRead : Pattern := .implies svinR (.and svinR [.top svinR, .top svinR]) (svoEq "Lblone")

def svoCtx : Ctx := ⟨tableOf [⟨⟨⟨"R"⟩⟩⟩] svoAx, []⟩

/-- `setvar_in_drop` at the fixture's first sentence. -/
theorem setvar_in_drop_e3_owise [Inhabited M] (hD : DefOK I) (hc : I ⊧ᴵ ceilDefItem.pat)
    {e : Valuation M} {σ ρ : M}
    (hS : ∀ a, (trSort svoCtx.vars svinExp).interpret I e a ↔ a = σ)
    (hR : ∀ a, (trSort svoCtx.vars svinR).interpret I e a ↔ a = ρ)
    (hσ : IsSort I σ) (hρ : IsSort I ρ)
    (h₀ : Inh I σ (e.evalEvar (svoCtx.vars.ev (evarKey svinX0))))
    (h₁ : Inh I σ (e.evalEvar (svoCtx.vars.ev (evarKey svinX1)))) (m : M) :
    (∀ A : Set M, (∀ a, A a → Inh I σ a) →
      (tr svoCtx svoAx).interpret I (svarAt_svin e (svoCtx.vars.sv (svarKey svinS)) A) m) ↔
    (tr svoCtx svoRead).interpret I e m :=
  setvar_in_drop hD hc hS hR hσ hρ h₀ h₁ (by decide) (by decide) (by decide) (by decide) (by decide) m

/-- `\and{R}(\in{SortExp{}, R}(X0, g₀), \and{R}(\in{SortExp{}, R}(X1, g₁), \top{R}()))`. -/
def svoArgs (g₀ g₁ : Kore.EVar) : Pattern :=
  .and svinR [.in svinExp svinR (.var (.evar svinX0)) (.var (.evar g₀)),
    .and svinR [.in svinExp svinR (.var (.evar svinX1)) (.var (.evar g₁)), .top svinR]]

/-- The text's disjunct: one element variable at both arguments. -/
def svoDisj : Pattern := .exist svinR svoGen2 (.and svinR [.top svinR, svoArgs svoGen2 svoGen2])

/-- The disjunct as read: a second bound variable at the second argument. -/
def svoDisjRead : Pattern :=
  .exist svinR svoGen2 (.exist svinR svoGen2' (.and svinR [.top svinR, svoArgs svoGen2 svoGen2']))

/-- The `[owise]` axiom with the disjunct `d` in its exclusion. -/
def svoOwise (d : Pattern) : Pattern :=
  .implies svinR
    (.and svinR [.not svinR (.or svinR [d, .bottom svinR]), .and svinR [.top svinR, svoArgs svoGen0 svoGen1]])
    (svoEq "Lbltwo")

def svoOwCtx : Ctx := ⟨tableOf [⟨⟨⟨"R"⟩⟩⟩] (svoOwise svoDisjRead), []⟩

/-- `owise_diag_svin` at the text's disjunct: it holds where `X0` and `X1` have one value. -/
theorem owise_diag_e3_owise [Inhabited M] (hD : DefOK I) (hc : I ⊧ᴵ ceilDefItem.pat)
    {e : Valuation M} {σ ρ : M}
    (hS : ∀ a, (trSort svoOwCtx.vars svinExp).interpret I e a ↔ a = σ)
    (hR : ∀ a, (trSort svoOwCtx.vars svinR).interpret I e a ↔ a = ρ)
    (hσ : IsSort I σ) (hρ : IsSort I ρ)
    (h₀ : Inh I σ (e.evalEvar (svoOwCtx.vars.ev (evarKey svinX0))))
    (h₁ : Inh I σ (e.evalEvar (svoOwCtx.vars.ev (evarKey svinX1)))) (m : M) :
    (tr svoOwCtx svoDisj).interpret I e m ↔
      e.evalEvar (svoOwCtx.vars.ev (evarKey svinX0)) = e.evalEvar (svoOwCtx.vars.ev (evarKey svinX1)) ∧
      (tr svoOwCtx (.top svinR)).interpret I e m ∧ (tr svoOwCtx (.top svinR)).interpret I e m ∧
      Inh I ρ m :=
  owise_diag_svin hD hc hS hR hσ hρ h₀ h₁ (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) m

/-- `owise_split_svin` at the disjunct as read: it holds wherever its two `\top` conjuncts do. -/
theorem owise_split_e3_owise [Inhabited M] (hD : DefOK I) (hc : I ⊧ᴵ ceilDefItem.pat)
    {e : Valuation M} {σ ρ : M}
    (hS : ∀ a, (trSort svoOwCtx.vars svinExp).interpret I e a ↔ a = σ)
    (hR : ∀ a, (trSort svoOwCtx.vars svinR).interpret I e a ↔ a = ρ)
    (hσ : IsSort I σ) (hρ : IsSort I ρ)
    (h₀ : Inh I σ (e.evalEvar (svoOwCtx.vars.ev (evarKey svinX0))))
    (h₁ : Inh I σ (e.evalEvar (svoOwCtx.vars.ev (evarKey svinX1)))) (m : M) :
    (tr svoOwCtx svoDisjRead).interpret I e m ↔
      (tr svoOwCtx (.top svinR)).interpret I e m ∧ (tr svoOwCtx (.top svinR)).interpret I e m ∧
      Inh I ρ m :=
  owise_split_svin hD hc hS hR hσ hρ h₀ h₁ (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) m

/-- `owise_disjunct_narrower` at the fixture's `[owise]` sentence: the text's sentence entails the
one with the disjunct as read. -/
theorem owise_disjunct_narrower_e3_owise [Inhabited M] (hD : DefOK I) (hc : I ⊧ᴵ ceilDefItem.pat)
    {e : Valuation M} {σ ρ : M}
    (hS : ∀ a, (trSort svoOwCtx.vars svinExp).interpret I e a ↔ a = σ)
    (hR : ∀ a, (trSort svoOwCtx.vars svinR).interpret I e a ↔ a = ρ)
    (hσ : IsSort I σ) (hρ : IsSort I ρ)
    (h₀ : Inh I σ (e.evalEvar (svoOwCtx.vars.ev (evarKey svinX0))))
    (h₁ : Inh I σ (e.evalEvar (svoOwCtx.vars.ev (evarKey svinX1)))) (m : M) :
    (tr svoOwCtx (svoOwise svoDisj)).interpret I e m →
    (tr svoOwCtx (svoOwise svoDisjRead)).interpret I e m :=
  owise_disjunct_narrower hD hc hS hR hσ hρ h₀ h₁ (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) m

end E3SetvarOwise

end KCore
