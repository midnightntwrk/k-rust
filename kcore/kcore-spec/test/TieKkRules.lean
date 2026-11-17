/-
  The rewrite rules of kore.k's text as kompile wrote it
  (`examples/ref-kk/RefKk/definition.kore`, user module `KORE`), layer 2 of the tie (C14), on the
  literals `kore` and `defn`. Nothing here reads `Parse.parse` or `emit`. Run from the package
  root: `lake env lean test/TieKkRules.lean`.

  - `ruleText`: the account's 10 rewrite sentences (408 to 417, test/TieKk.lean `classes`), in
    text order, which is the order of `c.rules`.
  - `rules_checked`: for each rule, Γ's axiom (`prioRuleK`) is a rewrite whose left side is the
    text's two conjuncts with a third more (the definedness of the right side, all the rules being
    of one priority, so no rule's negation is added), with one variable table and one list of free
    variables without it, and without it it is the text's sentence (one kernel decision).
  - `rules_from_text` (W1, and the converse for `ruleItems`): for every H, the j-th item of
    `ruleItems` is a consequence of `ruleText[j]`.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.TieKk

open KCore ML Faithful KoreAML

kore_term kore from "examples/ref-kk/RefKk/definition.kore"
definition_of defn from "examples/ref-kk/RefKk/definition.kore"
user_axioms U from "examples/ref-kk/RefKk/definition.kore" module "KORE"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

/-- `tr s`: the item `Theory.ofDefinition kore` holds for the sentence. -/
noncomputable def trS (ad : AxiomDecl) : Item := trAxiom kore.symbolDecls kore.aliasNames ad

/-- A rule axiom `\rewrites{C}(\and{C}(l, t, x), r)`, read as its parts. -/
def ruleParts : Kore.Pattern → Option (Kore.KSort × Kore.Pattern × Kore.Pattern × Kore.Pattern × Kore.Pattern)
  | .rewrites C (.and _ [l, t, x]) r => some (C, l, t, x, r)
  | _ => none

/-- The rule axiom without its left side's third conjunct. -/
def dropThird (p : Kore.Pattern) : Kore.Pattern :=
  match ruleParts p with
  | some (C, l, t, _, r) => .rewrites C (.and C [l, t]) r
  | none => p

theorem ruleParts_eq {p : Kore.Pattern} {C : Kore.KSort} {l t x r : Kore.Pattern}
    (h : ruleParts p = some (C, l, t, x, r)) : ∃ C', p = .rewrites C (.and C' [l, t, x]) r ∧ dropThird p = .rewrites C (.and C [l, t]) r := by
  unfold dropThird; rw [h]
  unfold ruleParts at h
  split at h
  · cases h; exact ⟨_, rfl, rfl⟩
  · cases h

def kAx (p : Kore.Pattern) : AxiomDecl := ⟨0, "kernel", ⟨[], p, []⟩⟩

/-- **A conjunct more on a rule's left side gives a consequence**: in a model of definedness, the
rule axiom with the left side `l ∧ t` entails the one with the left side `l ∧ t ∧ x`, where the
two have one variable table and one list of free variables. -/
theorem rewrite_weaken {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hD : DefOK I) {p : Kore.Pattern}
    {C : Kore.KSort} {l t x r : Kore.Pattern} (hq : ruleParts p = some (C, l, t, x, r))
    (ht : tableOf [] p = tableOf [] (dropThird p))
    (hf : (freeOf [] p).eraseDups = (freeOf [] (dropThird p)).eraseDups)
    (h : I ⊧ᴵ (trAxiom [] [] (kAx (dropThird p))).pat) : I ⊧ᴵ (trAxiom [] [] (kAx p)).pat := by
  obtain ⟨C', hp, hd⟩ := ruleParts_eq hq
  intro e m
  have h1 := h e m
  simp only [trAxiom, kAx, List.map_nil, List.nil_append] at h1 ⊢
  rw [ht, hf]
  rw [hd] at h1 ⊢
  rw [hp] at ⊢
  rw [interpret_impl] at h1 ⊢
  intro hg
  have h2 := h1 hg
  rw [interp_equal hD] at h2 ⊢
  intro a
  have h3 := h2 a
  simp only [sortOf, tr, trAndList, sRewrites, interp_sImp, interp_sAnd] at h3 ⊢
  exact ⟨fun hf => hf.1, fun ht' => ⟨(h3.mpr ht').1, fun hl => (h3.mpr ht').2 ⟨hl.1, hl.2.1⟩⟩⟩

/-- The account's rewrite sentences, in text order. -/
noncomputable def ruleText : List AxiomDecl :=
  [U.ax408, U.ax409, U.ax410, U.ax411, U.ax412, U.ax413, U.ax414, U.ax415, U.ax416, U.ax417]

/-- Γ's axiom of the rule is the text's sentence with a third conjunct on its left side, read as
`rewrite_weaken` asks. -/
noncomputable def ruleOKB (r : Rule) (ad : AxiomDecl) : Bool :=
  (ruleParts (prioRuleK c r)).isSome &&
    decide (tableOf [] (prioRuleK c r) = tableOf [] (dropThird (prioRuleK c r))) &&
    decide ((freeOf [] (prioRuleK c r)).eraseDups = (freeOf [] (dropThird (prioRuleK c r))).eraseDups) &&
    decide ((trS ad).pat = (trAxiom [] [] (kAx (dropThird (prioRuleK c r)))).pat)

theorem rules_length : c.rules.length = ruleText.length := by decide +kernel

theorem rules_checked : (c.rules.zip ruleText).all (fun p => ruleOKB p.1 p.2) = true := by decide +kernel

/-- **W1 for the 10 rules, and the converse for `ruleItems`**: the j-th item of Γ's rules is a
consequence of the j-th rewrite sentence of the text, for every H. -/
theorem rules_from_text (H : HookParams) :
    ∀ (j : Nat) (it : Item), (ruleItems (cH H))[j]? = some it →
      ∃ ad, ruleText[j]? = some ad ∧ (itemsPremises [trS ad] ⊧ it.pat) := by
  intro j it hj
  rw [TiePair.ruleItems_withHooks] at hj
  unfold ruleItems at hj
  rw [List.getElem?_map] at hj
  cases hr : c.rules[j]? with
  | none => rw [hr] at hj; cases hj
  | some r =>
    rw [hr] at hj
    have hjl : j < ruleText.length := rules_length ▸ (List.getElem?_eq_some_iff.mp hr).1
    refine ⟨ruleText[j], List.getElem?_eq_getElem hjl, fun {M} _ {I} hI => ?_⟩
    cases (Option.some.inj hj)
    have hz : (r, ruleText[j]) ∈ c.rules.zip ruleText :=
      List.mem_iff_getElem?.mpr ⟨j, by rw [List.getElem?_zip_eq_some]; exact ⟨hr, List.getElem?_eq_getElem hjl⟩⟩
    have hok := List.all_eq_true.mp rules_checked _ hz
    simp only [ruleOKB, Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨⟨⟨hp, ht⟩, hf⟩, htx⟩ := hok
    have hD : DefOK I := defOK_of fun x => hI _ (Or.inr ⟨x, rfl⟩)
    obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp hp
    obtain ⟨C, l, t, x, r'⟩ := q
    refine rewrite_weaken hD hq ht hf ?_
    rw [← htx]
    exact hI _ (Or.inl ⟨trS ruleText[j], List.mem_singleton_self _, rfl⟩)

end KCore.TieKk

#check @KCore.TieKk.rules_from_text
#print axioms KCore.TieKk.rules_from_text
