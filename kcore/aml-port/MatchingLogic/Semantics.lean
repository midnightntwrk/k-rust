
import MatchingLogic.Util
import MatchingLogic.Pattern
import MatchingLogic.Proof
import MatchingLogic.PrettyPrinterOptions
import MatchingLogic.Substitution

namespace ML

set_option autoImplicit false
set_option Pattern.pp_interpret_hiding false


structure Interpretation (𝕊 : Type) (M : Type) where
  evalSymb : 𝕊 → Set M
  evalApp : M → M → Set M

structure Valuation (M : Type) where
  evalEvar : EVar → M
  evalSvar : SVar → Set M

variable {𝕊 : Type} {M : Type}

@[simp]
def Pattern.interpret (I : Interpretation 𝕊 M) (eval : Valuation M) (φ : Pattern 𝕊) : Set M :=
match φ with
| evar x => { eval.evalEvar x }
| svar i => eval.evalSvar i
| symbol σ => I.evalSymb σ
-- TODO (Andrei B): Use set notation?
| φ ⇒ ψ => fun m => (φ.interpret I eval m) → (ψ.interpret I eval m)
| ∃∃ x φ => fun m => ∃ a : M, φ.interpret I ⟨(Function.update eval.evalEvar x a), eval.evalSvar⟩ m
| μ X φ =>
  -- m ∈ ⋂ {B ⊆ M | e(X ← B)⁺ (φ) ⊆ B}
  fun m : M =>
    -- for all B ⊆ M,
    ∀ B : Set M,
      -- if e(X ← B) ⊆ B holds
      (∀ m,
        φ.interpret I ⟨eval.evalEvar, Function.update eval.evalSvar X B⟩ m → B m
      ) →
      -- then m ∈ B
      B m
| p₁ ⬝ p₂ => fun m => ∃ a : M, ∃ b : M, (p₁.interpret I eval a) ∧ (p₂.interpret I eval b) ∧ I.evalApp a b m
| ⊥ => fun _ => False

def muInterpret (I : Interpretation 𝕊 M) (eval : Valuation M) (φ : Pattern 𝕊) (X : SVar) :=
  fun m : M => ∀ B : Set M, φ.interpret I ⟨eval.evalEvar, Function.update eval.evalSvar X B⟩ m → B m

#check @muInterpret
/--
  Notation for `Pattern.interpret` which purposefully hides all the other parameters beyond the pattern
  (like the interpretation, variable valuation, etc.) as in most cases those are fixed and only obscure the view.
  The notation is never to be typed; it is just for printing purposes.
  Use `set_option pp_interpret_hiding false` to disable this pretty printing.
-/
notation "∥" φ "//" e ", " I "∥" => Pattern.interpret I e φ
notation "∥" φ "∥" => _
open Lean PrettyPrinter Delaborator SubExpr in
@[delab app.ML.Pattern.interpret]
def delabInterpret : Delab := do
  let e ← getExpr
  guard $ e.getAppNumArgs == 6 -- careful: `Pattern.interpret` has actually `6` arguments, because `Set M` means `M → Prop`.
  let ppInterpretHiding ← getBoolOption Pattern.pp_interpret_hiding.name
  guard ppInterpretHiding
  let pattern ← withAppFn $ withAppArg delab --the second last argument
  `(∥$pattern∥)

variable (φ : Pattern Empty)

def Valuation.satifies (I : Interpretation 𝕊 M) (eval : Valuation M) : Pattern 𝕊 → Prop :=
  fun φ => ∀ m : M, φ.interpret I eval m

notation I "_at_" eval "⊧ᴵ" φ => Valuation.satifies I eval φ

@[simp]
def Interpretation.satisfies (I : Interpretation 𝕊 M) : Pattern 𝕊 → Prop :=
  fun φ => ∀ eval : Valuation M, I _at_ eval ⊧ᴵ φ

infix:(arrow_precedence + 1) " ⊧ᴵ " => Interpretation.satisfies

@[simp]
def Interpretation.satisfiesAll (I : Interpretation 𝕊 M) : Premises 𝕊 → Prop :=
  fun Γ => ∀ γ ∈ Γ, I ⊧ᴵ γ

infix:(arrow_precedence + 1) " ⊧ᴵP " => Interpretation.satisfiesAll

-- todo: better names

-- TODO (Andrei B): Global semantic consequence?
@[simp]
def entails (Γ : Premises 𝕊) (φ : Pattern 𝕊) : Prop :=
  ∀ {M : Type} [Inhabited M] {I : Interpretation 𝕊 M}, I ⊧ᴵP Γ → I ⊧ᴵ φ

def substEVarValuation { M : Type } (eval : Valuation M) (x : EVar) (a : M) (arg : EVar) :=
  if arg == x then a else eval.evalEvar arg

infix:(arrow_precedence + 1) " ⊧ " => entails

attribute [local simp] or_def_imp_neg in
section

  variable {Γ : Premises 𝕊} {φ ψ : Pattern 𝕊} {I : Interpretation 𝕊 M} {e : Valuation M}

  set_option Pattern.pp_interpret_hiding true

  @[simp]
  theorem interpret_bottom : ∀ {m : M}, ⊥.interpret I e m ↔ False := by simp

  @[simp]
  theorem interpret_neg : ∀ {m : M}, (∼φ).interpret I e m ↔ ¬φ.interpret I e m := by
    intros m ; apply Iff.intro <;> (intros h ; simpa)

  @[simp]
  theorem interpret_impl : ∀ {m : M}, (φ ⇒ ψ).interpret I e m ↔ (φ.interpret I e m → ψ.interpret I e m) := by simp

  @[simp]
  theorem interpret_app : ∀ {m : M}, (φ ⬝ ψ).interpret I e m ↔ ∃ a : M, ∃ b : M, (φ.interpret I e a) ∧ (ψ.interpret I e b) ∧ I.evalApp a b m := by simp

  @[simp]
  theorem interpret_disj : ∀ {m : M}, (φ ⋁ ψ).interpret I e m ↔ φ.interpret I e m ∨ ψ.interpret I e m := by
    intros m
    apply Iff.intro <;> intros h
    . simpa
    . rw [or_def_imp_neg] at h
      exact h

  @[simp]
  theorem interpret_exists {x : EVar} : ∀ {m : M}, (∃∃ x φ).interpret I e m ↔ ∃ a : M, φ.interpret I ⟨(Function.update e.evalEvar x a), e.evalSvar⟩ m := by simp

  @[simp]
  theorem implies_false_is_neg { p : Prop } : (p → False) ↔ ¬p := by
    apply Iff.intro <;> intro h <;> intro hp <;> exact h hp

  @[simp]
  theorem equivalence { p q : Prop } : (p → q) ∧ (q → p) ↔ (p ↔ q) := by
    apply Iff.intro <;> intros h
    . cases h with | intro hLeft hRight =>
      apply Iff.intro <;> intros hLocal
      . exact hLeft (hRight (hLeft (hRight (hLeft hLocal))))
      . exact hRight (hLeft (hRight (hLeft (hRight hLocal))))
    . cases h with | intro hLeft hRight =>
      exact And.intro hLeft hRight

  @[simp]
  theorem interpret_equiv: ∀ {m : M}, (φ ⇔ ψ).interpret I e m ↔ (φ.interpret I e m ↔ ψ.interpret I e m) := by
    intros m
    apply Iff.intro <;> intros h
    . simp_all
    . simp_all

  @[simp]
  theorem interpret_conj : ∀ {m : M}, (φ ⋀ ψ).interpret I e m ↔ φ.interpret I e m ∧ ψ.interpret I e m := by
    intro m
    apply Iff.intro <;> intros h
    . simp at h
      assumption
    . simp at *
      assumption



section MirceaQuestion


  example {x : EVar} {φ : Pattern 𝕊} : Γ ⊧ ∃∃ x (x ⋀ φ) ⇒ ∀∀ x (x ⇒ φ) := by
    intros M _ I _ e m h h'
    simp_all
    rcases h with ⟨w, ⟨h₁, h₂⟩⟩
    rcases h' with ⟨w', ⟨h'₁, h'₂⟩⟩
    cases h₁
    cases h'₁
    contradiction


end MirceaQuestion
