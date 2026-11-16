/-
  kimp's noninterference through the theorem kind (KcoreSpec/Noninterference.lean): `NIFor chk`
  is the kind's statement `TINI` for every labelling and accepted program, and an unwinding
  relation per labelling and program gives it, by the kind's generic theorem and kimp's
  determinism (`Kimp.deterministic`, a kernel decision of the generated package).

  - `Start G P`: two initial configurations of P with stores that are stores and agree on G's low
    identifiers;
  - `Fin`: `<k>` is empty;
  - `Obs G`: the final stores agree on G's low identifiers.

  What is left is the relation and its conditions: `kimpNI_of_unwinding` takes them as premises.
  The unwinding condition splits by rule (`NI.unwinds_of`): a decided condition for the rules it
  covers, the others named obligations. No relation for kimp is given here.
-/
import NI.Spec
import KcoreSpec.Noninterference

set_option autoImplicit false

namespace NI

open KCore KCore.Cert

/-- Two initial configurations of P with stores that agree on the low identifiers. -/
def Start (chk : Semantics) (G P : GroundTerm) (x₁ x₂ : Config Kimp.c) : Prop :=
  ∃ E₁ E₂, Good E₁ ∧ Good E₂ ∧ LowEqIn chk G E₁ E₂ ∧ x₁.val = init P E₁ ∧ x₂.val = init P E₂

/-- A final configuration: `<k>` is empty. -/
def Fin (y : Config Kimp.c) : Prop := ∃ E n, y.val = cfg dotK E n

/-- The final stores agree on the low identifiers. -/
def Obs (chk : Semantics) (G : GroundTerm) (y₁ y₂ : Config Kimp.c) : Prop :=
  ∀ E₁ n₁ E₂ n₂, y₁.val = cfg dotK E₁ n₁ → y₂.val = cfg dotK E₂ n₂ → LowEqIn chk G E₁ E₂

theorem reach_of_star {α : Type} {r : α → α → Prop} {x y : α} (h : Star r x y) : Reach r x y := by
  induction h with
  | refl a => exact .refl a
  | step h _ ih => exact .head h ih

theorem star_of_reach {α : Type} {r : α → α → Prop} {x y : α} (h : Reach r x y) : Star r x y := by
  induction h with
  | refl a => exact .refl a
  | head h _ ih => exact .step h ih

/-- `NIFor chk` is the kind's statement for every labelling and every program `chk` accepts. -/
theorem niFor_of_tini {chk : Semantics}
    (h : ∀ G P, chk.sortOf G = some Srt.map → Kimp.c.sortOf P = some K.stmt → SecureIn chk G P →
      NI.TINI Kimp.c (Start chk G P) Fin (Obs chk G)) : NIFor chk := by
  intro G P E₁ E₂ E₁' E₂' n₁ n₂ hG hP hs hg₁ hg₂ hlo r₁ r₂
  obtain ⟨hx₁, hy₁, s₁⟩ := r₁
  obtain ⟨hx₂, hy₂, s₂⟩ := r₂
  exact h G P hG hP hs ⟨_, hx₁⟩ ⟨_, hx₂⟩ ⟨_, hy₁⟩ ⟨_, hy₂⟩ ⟨E₁, E₂, hg₁, hg₂, hlo, rfl, rfl⟩
    (reach_of_star s₁) (reach_of_star s₂) ⟨E₁', n₁, rfl⟩ ⟨E₂', n₂, rfl⟩ E₁' n₁ E₂' n₂ rfl rfl

/-- **kimp's noninterference from unwinding relations**: one per labelling and accepted program. -/
theorem niFor_of_unwinding {chk : Semantics}
    (R : GroundTerm → GroundTerm → Config Kimp.c → Config Kimp.c → Prop)
    (hu : ∀ G P, chk.sortOf G = some Srt.map → Kimp.c.sortOf P = some K.stmt → SecureIn chk G P →
      NI.Unwinding Kimp.c (Start chk G P) Fin (Obs chk G) (R G P)) : NIFor chk :=
  niFor_of_tini fun G P hG hP hs =>
    NI.tini_of_unwinding (fun _ _ _ h h' => Kimp.deterministic Kimp.c.hooks h h') (hu G P hG hP hs)

theorem kimpNI_of_unwinding (R : GroundTerm → GroundTerm → Config Kimp.c → Config Kimp.c → Prop)
    (hu : ∀ G P, ImpSec.c.sortOf G = some Srt.map → Kimp.c.sortOf P = some K.stmt → Secure G P →
      NI.Unwinding Kimp.c (Start ImpSec.c G P) Fin (Obs ImpSec.c G) (R G P)) : KimpNI :=
  niFor_of_unwinding R hu

end NI
