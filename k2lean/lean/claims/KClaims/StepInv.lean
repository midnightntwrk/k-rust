import KClaims.Invariant
import KClaims.RuleStep
import KPrelude.Rules

/-!
# Rule steps under a preserved invariant, and for reachability

The step lemmas the claim tactic (`KClaims.Tactic`) applies in two modes that `KClaims.RuleStep`
does not cover.

- **Under an invariant** (`kc_auto … inv [hP]`, `k2lean claims --assume-invariant`): the claims
  are stated for configurations satisfying a preserved `P`, and their target is strengthened to
  `P d ∧ Q d`, so that the state a circularity or a proved claim leads to satisfies `P` as well.
  `AF.circularity_inst_inv` is `AF.circularity_inv` for a claim family given by its instances, and
  `AFn.of_rule_inv` takes a rule step with `P` given at the successor (`AFn.step_inv`).
  `AFn.trans_inv` continues from such a strengthened target with `P` and `Q` as two hypotheses.
- **Reachability** (`Reach`, total one-path correctness, used by the induction skeletons of
  `k2lean claims --induction`): a rule step needs no determinism, since one path suffices.
-/

namespace KClaims

open KPrelude

section

variable {α : Type} {A : α → Prop} {R : α → α → Prop} {P Q X : α → Prop} {c c' : α}

/-- A step of one rule matcher, for reachability: no determinism is needed. -/
theorem Reach.of_rule (r : Rule α A R) (h : (r.run c).next? = some c') (k : Reach R Q c') :
    Reach R Q c :=
  Reach.step (RuleResult.sound_of_next? h) k

/-- Continue from a strengthened target `P ∧ Q'`, with `P` and `Q'` as separate hypotheses. -/
theorem AFn.trans_inv {n : Nat} (h : AFn R (fun e => P e ∧ Q e) n c)
    (k : ∀ d, P d → Q d → AFn R X n d) : AFn R X n c :=
  AFn.trans h fun d hd => k d hd.1 hd.2

theorem AF.trans_inv (h : AF R (fun e => P e ∧ Q e) c) (k : ∀ d, P d → Q d → AF R X d) : AF R X c :=
  AF.trans h fun d hd => k d hd.1 hd.2

/-- Guarded circularities for a claim family given by its instances, under the invariant `P`:
each instance may assume `P` at its start, and so may each use of a circularity. -/
theorem AF.circularity_inst_inv (Inst : α → (α → Prop) → Prop)
    (h : ∀ n, (∀ m < n, ∀ d Q, P d → Inst d Q → AFn R (fun e => P e ∧ Q e) m d) →
      ∀ d Q, P d → Inst d Q → AFn R (fun e => P e ∧ Q e) n d) :
    ∀ d Q, P d → Inst d Q → AF R (fun e => P e ∧ Q e) d := by
  intro d Q hd hi
  exact AF.circularity_inv (ι := α → Prop) (fun Q d => Inst d Q) (fun Q e => P e ∧ Q e)
    (fun n ih Q d hd hi => h n (fun m hm d Q hd hi => ih m hm Q d hd hi) d Q hd hi) Q d hd hi

end

section

variable {α : Type} {A : α → Prop} {R : α → α → Prop} [RuleSet A R] {P Q : α → Prop} {c c' : α}

/-- A rule step with `P` given at the successor. -/
theorem AFn.of_rule_inv {n : Nat} (hP : Preserved R P) (hc : P c) (r : Rule α A R)
    (h : (r.run c).next? = some c') (k : P c' → AFn R Q n c') : AFn R Q (n + 1) c :=
  AFn.of_rule r h (k (hP c c' hc (RuleResult.sound_of_next? h)))

theorem AF.of_rule_inv (hP : Preserved R P) (hc : P c) (r : Rule α A R)
    (h : (r.run c).next? = some c') (k : P c' → AF R Q c') : AF R Q c :=
  AF.of_rule r h (k (hP c c' hc (RuleResult.sound_of_next? h)))

end

end KClaims
