import KClaims.Reach
import KPrelude.Rules

/-!
# Symbolic steps through proof-carrying rule matchers

A generated rule matcher `r.run c : RuleResult A R c` returns `next c' (h : R c c')` when its
left-hand side matches `c` and its requires holds. On a configuration with symbolic parts
(a continuation variable, an unknown Boolean) the executable `step` of a generated semantics
may not reduce, because its rule index looks at positions that only some rules need; a single
matcher reduces as soon as its own left-hand side is decided. For a deterministic relation the
successor found by any one matcher is the only successor, which is all `AF` needs.
-/

namespace KClaims

open KPrelude

/-- The rule matchers of a deterministic generated semantics. -/
class RuleSet {α : Type} (A : outParam (α → Prop)) (R : α → α → Prop) where
  rules : List (Rule α A R)
  det : ∀ {a b b' : α}, R a b → R a b' → b = b'

variable {α : Type} {A : α → Prop} {R : α → α → Prop} [RuleSet A R] {P : α → Prop} {c c' : α}

theorem AF.of_rule (r : Rule α A R) (h : (r.run c).next? = some c') (k : AF R P c') : AF R P c :=
  AF.step ⟨c', RuleResult.sound_of_next? h⟩ fun _ hd =>
    (RuleSet.det (RuleResult.sound_of_next? h) hd) ▸ k

theorem AFn.of_rule {n : Nat} (r : Rule α A R) (h : (r.run c).next? = some c') (k : AFn R P n c') :
    AFn R P (n + 1) c :=
  AFn.step ⟨c', RuleResult.sound_of_next? h⟩ fun _ hd =>
    (RuleSet.det (RuleResult.sound_of_next? h) hd) ▸ k

/-- The circularity principle for one claim family given by its instances: `Inst c Q` says that
`c` is an instance of a left-hand side and `Q` is the post-condition of the same valuation. -/
theorem AF.circularity_inst {R : α → α → Prop} (Inst : α → (α → Prop) → Prop)
    (h : ∀ n, (∀ m < n, ∀ d Q, Inst d Q → AFn R Q m d) → ∀ d Q, Inst d Q → AFn R Q n d) :
    ∀ d Q, Inst d Q → AF R Q d := by
  intro d Q hd
  exact AF.circularity (ι := α → Prop) (fun Q d => Inst d Q) (fun Q => Q)
    (fun n ih Q d hd => h n (fun m hm d Q hd => ih m hm Q d hd) d Q hd) Q d hd

end KClaims
