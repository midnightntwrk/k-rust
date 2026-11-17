/-
  The tie (C14) on `f2-examples/ens.kompile.kore` for the rewrite rule, sentence 155, in the
  direction from Γ to the text (W2). Γ's axiom of the rule is the sentence with one conjunct more on
  its left side, the definedness of its right side (`rule_gamma_shape`); where that right side holds
  an element, the conjunct holds of every configuration, and Γ's axiom gives the sentence
  (`tieRule_more`). So every model of Γ, for every H, satisfies sentence 155 at those valuations
  (`rule_w2_all`), and at those that send its variables to values (`rule_w2`, `AtValues` with that
  guard; the sentence has no rule of a smaller priority, so the guard has no second part).
  Run from the package root: `lake env lean test/TieEnsW2.lean`.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.TieEns

open KCore ML Faithful KoreAML

kore_term kore from "f2-examples/ens.kompile.kore"
definition_of defn from "f2-examples/ens.kompile.kore"
user_axioms U from "f2-examples/ens.kompile.kore" module "ENS"

noncomputable abbrev c : Semantics := defn.sem
theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H
noncomputable def trS (ad : AxiomDecl) : Item := trAxiom kore.symbolDecls kore.aliasNames ad
kernel_rfl ruleItems_withHooks : ∀ (c : Semantics) (H : HookParams), ruleItems (c.withHooks H) = ruleItems c
theorem mem_Γ_rules {c : Semantics} {φ : P} (h : ΓRules c φ) : Γ c φ := Or.inl (Or.inr h)
def kAx (p : Kore.Pattern) : AxiomDecl := ⟨0, "kernel", ⟨[], p, []⟩⟩
noncomputable def r0 : Rule := c.rules[0]'(by decide +kernel)
theorem ruleItems_eq : ruleItems c = [trAxiom [] [] (kAx (prioRuleK c r0))] := by kernel_rfl
theorem coreOK : c.coreOK = true := by decide_cheap
theorem coreOKH (H : HookParams) : (cH H).coreOK = true := (Semantics.coreOK_withHooks c H).trans coreOK

/-! ## The rule (sentence 155): W2 -/

/-- The configuration sort. -/
noncomputable abbrev C0 : Kore.KSort := srtOf c topCellSort

/-- The right side of a rewrite. -/
def rightOf : Kore.Pattern → Kore.Pattern
  | .rewrites _ _ r => r
  | p => p

/-- The first conjunct of the left side of a rewrite. -/
def leftOf : Kore.Pattern → Kore.Pattern
  | .rewrites _ (.and _ (l :: _)) _ => l
  | p => p

/-- The term of a right side `\and{C}(term, \top{C}())`. -/
def rightTerm : Kore.Pattern → Kore.Pattern
  | .and _ (t :: _) => t
  | p => p

/-- Γ's axiom of the rule, and the axiom without the last conjunct of its left side. -/
noncomputable abbrev gRule : Kore.Pattern := prioRuleK c r0
noncomputable def gText : Kore.Pattern := .rewrites C0 (.and C0 [leftOf gRule, .top C0]) (rightOf gRule)

/-- Γ's axiom of the rule is `gText` with one conjunct more on its left side, the definedness of
its right side `\and{C}(r, \top{C}())`, `C` the configuration sort. -/
theorem rule_gamma_shape : gRule =
    .rewrites C0 (.and C0 ([leftOf gRule, .top C0] ++ [.ceil C0 C0 (rightOf gRule)])) (rightOf gRule) ∧
    rightOf gRule = .and C0 [rightTerm (rightOf gRule), .top C0] := by decide +kernel

theorem rule_tables : tableOf [] gRule = tableOf [] gText ∧
    (freeOf [] gRule).eraseDups = (freeOf [] gText).eraseDups := by decide +kernel

/-- `gText` is sentence 155: one translation, and one translation of the right side. -/
theorem rule_gtext : (trS U.ax155).pat = (trAxiom [] [] (kAx gText)).pat ∧
    tr ⟨tableOf U.ax155.ax.sortVars U.ax155.ax.pattern, []⟩ (rightOf U.ax155.ax.pattern) =
      tr ⟨tableOf [] gText, []⟩ (rightOf gRule) := by decide +kernel

theorem top_numbered (H : HookParams) : topCellSort < nRegSorts + (cH H).sortNames.length :=
  (by decide +kernel : topCellSort < nRegSorts + c.sortNames.length)

/-- The variable table of sentence 155. -/
noncomputable def t155 : VarTable := tableOf U.ax155.ax.sortVars U.ax155.ax.pattern

/-- The right side of sentence 155 holds an element at the valuation `e`. -/
def RightDefined {M : Type} (I : Interpretation KoreAML.Sym M) (e : Valuation M) : Prop :=
  ∃ b, (tr ⟨t155, []⟩ (rightOf U.ax155.ax.pattern)).interpret I e b

/-- **W2 for the rule, at every valuation**: in a model of Γ, for every H, sentence 155 holds at
each valuation at which its right side holds an element. Γ's axiom is the sentence with the
definedness of the right side on its left side (`rule_gamma_shape`), which holds of every
configuration there. -/
theorem rule_w2_all (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
    (hI : I ⊧ᴵP Γ (cH H)) (e : Valuation M) (hdef : RightDefined I e) (m : M) :
    (trS U.ax155).pat.interpret I e m := by
  rw [rule_gtext.1]
  haveI : OvlOK (cH H) := ovlOK_of_core (coreOKH H)
  have hD := defOK hI
  have hc := sat_sigItem hI (sig_ceilDef (c := cH H))
  obtain ⟨σ, hσ1, hσ2⟩ := sortSing hI (top_numbered H)
  have hdef' : ∃ b, (tr ⟨tableOf [] gText, []⟩ (rightOf gRule)).interpret I e b := by
    rw [← rule_gtext.2]; exact hdef
  generalize hT : tableOf [] gText = T at hdef'
  have hS : ∀ b, (trSort T C0).interpret I e b ↔ b = σ := fun b => by
    unfold C0 srtOf; rw [trSort_srt]; exact hσ1 b
  have htop : ∀ a, (tr ⟨T, []⟩ (.top C0)).interpret I e a → Inh I σ a := fun a ha => by
    rw [KoreAML.tr, interp_sTop hD (by unfold C0 srtOf; rw [trSort_srt]; rfl), interp_inhOf_of hS] at ha
    exact ha
  have hg : I ⊧ᴵ (trAxiom [] [] (kAx gRule)).pat :=
    hI _ (mem_Γ_rules (Or.inl ⟨_, by rw [ruleItems_withHooks, ruleItems_eq]; exact List.mem_singleton_self _, rfl⟩))
  refine tieRule_more hD (g := kAx gRule) (t := kAx gText) (List.cons_ne_nil _ _) rule_gamma_shape.1
    rfl rule_tables.1 rule_tables.2 hg e (fun x hx a hls => ?_) m
  rw [List.mem_singleton.mp hx]
  show (tr ⟨tableOf [] gText, []⟩ (.ceil C0 C0 (rightOf gRule))).interpret I e a
  have hls' : ∀ p ∈ [leftOf gRule, Kore.Pattern.top C0], (tr ⟨tableOf [] gText, []⟩ p).interpret I e a := hls
  rw [hT] at hls' ⊢
  rw [KoreAML.tr]
  refine (interp_sCeil hD hc hS hS hσ2 hσ2 (fun b hb => ?_) a).mpr ⟨hdef', htop a (hls' _ (by simp))⟩
  rw [rule_gamma_shape.2] at hb
  exact htop b ((interp_and (List.cons_ne_nil _ _)).mp hb _ (by simp))

/-- **W2 for the rule** (`AtValues` with the guard): in a model of Γ, for every H, sentence 155
holds at each valuation that sends its variables to values and at which its right side holds an
element. The sentence has no rule of a smaller priority, so the guard has no second part. -/
theorem rule_w2 (H : HookParams) : ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M),
    I ⊧ᴵP Γ (cH H) → ∀ e, AtValues (cH H) I e U.ax155.ax → RightDefined I e →
      ∀ m, (trS U.ax155).pat.interpret I e m :=
  fun _ _ _ hI e _ hdef m => rule_w2_all H hI e hdef m

end KCore.TieEns
#print axioms KCore.TieEns.rule_w2
