/-
  KCore, outside the cone: `TieRuleW2G.rule_w2_built` and `rules_w2_built` for a right side that
  also holds injections (`TieRuleCutG.builtGB`: variables, constructors and `inj{A, N}`).

  - `rightBuiltGB gs fT s xs r g`: `TieRuleW2G.rightBuiltB` with `TieRuleCutG.builtGB` for
    `TieRuleCut.builtB`: the conjuncts `g` adds are `xs` followed by `⌈r ∧ ⊤⌉` of the sort named
    `s`, `\top` of that sort is one of the text's two conjuncts, and `r` is built of the variables
    of `fT` (free in `g`) and the generators of `gs`.
  - `ruleGuard_of_builtG`, `rule_w2_builtG`, `rules_w2_builtG`: W2 with the members of `xs` as its
    only premise, under the guards. `rules_w2_builtG_nil`: with `xs = []` the sentence holds in
    every model of Γ.
  - Not covered, so `⌈right⌉` stays a premise there: a right side with an `ensures`, a domain value
    or a function call, and a rule with a `requires` (the text's second conjunct is then not
    `\top`; `TieRuleCutG.equals_top` reads the sort from an `\equals` at a companion).
-/
import KcoreSpec.TieRuleW2Guarded
import KcoreSpec.TieRuleCutGen

set_option autoImplicit false

namespace KCore

namespace TieRuleW2G

open ML Faithful KoreAML
open TieRulePair (kAx leftOf extraOf ruleTextB RuleGuard rulesTieB)

/-- The conjuncts `g` adds are `xs` and then the definedness of `r ∧ ⊤` in the sort named `s`;
`\top` of that sort is one of the first two conjuncts; the keys of `fT` are free in `g`; `r` is
built of the variables of `fT` and the generators of `gs`. -/
def rightBuiltGB (gs : List (String × KoreAML.Gen)) (fT : List VarKey) (s : String)
    (xs : List Kore.Pattern) (r : Kore.Pattern) (g : Kore.Pattern) : Bool :=
  decide (extraOf g = xs ++ [.ceil (srt s) (srt s) (.and (srt s) [r, .top (srt s)])]) &&
    (leftOf g).any (fun p => decide (p = .top (srt s))) &&
    fT.all (fun k => (freeOf [] g).eraseDups.contains k) && TieRuleCutG.builtGB gs fT r s

section
variable {M : Type} {I : Interpretation KoreAML.Sym M}

/-- **The guard from its other members.** In a model of Γ that has the Cons-Fun items of `gs`,
for `g` with `rightBuiltGB`, where the guards of `g`'s free variables hold: the conjuncts `g` adds
hold of every element its first two hold, where those of `xs` do. -/
theorem ruleGuard_of_builtG [Inhabited M] {c : Semantics} [OvlOK c] (hI : I ⊧ᴵP Γ c)
    {gs : List (String × KoreAML.Gen)} {fT : List VarKey} {N : Srt} {s : String}
    {xs : List Kore.Pattern} {r g : Kore.Pattern} (hN : N < nRegSorts + c.sortNames.length)
    (hs : c.sortName N = s) (hin : TieRuleCutG.funsInGB c gs = true)
    (hb : rightBuiltGB gs fT s xs r g = true) (e : Valuation M) (m : M) (hgd : GuardsAt g I e m)
    (hxs : ∀ x ∈ xs, ∀ a, (∀ p ∈ leftOf g, (KoreAML.tr ⟨tableOf [] g, []⟩ p).interpret I e a) →
      (KoreAML.tr ⟨tableOf [] g, []⟩ x).interpret I e a) :
    RuleGuard g I e := by
  simp only [rightBuiltGB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.any_eq_true] at hb
  obtain ⟨⟨⟨hex, p0, hp0, hp0e⟩, hsub⟩, hbuilt⟩ := hb
  have htop : Kore.Pattern.top (srt s) ∈ leftOf g := hp0e ▸ hp0
  intro x hx a hl
  rw [hex] at hx
  rcases List.mem_append.mp hx with hx | hx
  · exact hxs x hx a hl
  rw [List.mem_singleton.mp hx]
  exact TieRuleCutG.rightDefined_top hI hN hs hin hbuilt e m
    (fun k hk => hgd k (List.contains_iff_mem.mp (hsub k hk))) a (hl _ htop)

/-- **W2 for a rule whose right side is built of generators**: in a model of Γ, the text's
sentence `t` of Γ's axiom `g` holds at `(e, m)` where, the guards holding there, the conjuncts of
`xs` (those `g` adds before `⌈r ∧ ⊤⌉`) hold of every element the first two hold. -/
theorem rule_w2_builtG [Inhabited M] {c : Semantics} [OvlOK c] (hI : I ⊧ᴵP Γ c)
    {gs : List (String × KoreAML.Gen)} {fT : List VarKey} {N : Srt} {s : String}
    {xs : List Kore.Pattern} {r g : Kore.Pattern} {t : P} (h : ruleTextB t g = true)
    (hg : I ⊧ᴵ (trAxiom [] [] (kAx g)).pat) (hN : N < nRegSorts + c.sortNames.length)
    (hs : c.sortName N = s) (hin : TieRuleCutG.funsInGB c gs = true)
    (hb : rightBuiltGB gs fT s xs r g = true) (e : Valuation M) (m : M)
    (hxs : GuardsAt g I e m → ∀ x ∈ xs, ∀ a,
      (∀ p ∈ leftOf g, (KoreAML.tr ⟨tableOf [] g, []⟩ p).interpret I e a) →
        (KoreAML.tr ⟨tableOf [] g, []⟩ x).interpret I e a) :
    t.interpret I e m :=
  rule_w2_guarded (defOK hI) h hg e m fun hgd => ruleGuard_of_builtG hI hN hs hin hb e m hgd (hxs hgd)
end

section
variable {c : Semantics} {R : List P}

/-- **W2 for a rule of Γ whose right side is built of generators**: in a model of Γ, the pattern
of `R` at the rule's index holds at `(e, m)` where, the guards holding there, the conjuncts of `xs`
(the rule's `pre` and the negation of the rules of a smaller priority) hold of every element the
text's left side holds. -/
theorem rules_w2_builtG [OvlOK c] (h : rulesTieB c R = true) {j : Nat} {r : Rule} {t : P}
    (hr : c.rules[j]? = some r) (ht : R[j]? = some t) {M : Type} [Inhabited M]
    {I : Interpretation KoreAML.Sym M} (hI : I ⊧ᴵP Γ c)
    {gs : List (String × KoreAML.Gen)} {fT : List VarKey} {N : Srt} {s : String}
    {xs : List Kore.Pattern} {rr : Kore.Pattern} (hN : N < nRegSorts + c.sortNames.length)
    (hs : c.sortName N = s) (hin : TieRuleCutG.funsInGB c gs = true)
    (hb : rightBuiltGB gs fT s xs rr (prioRuleK c r) = true) (e : Valuation M) (m : M)
    (hxs : GuardsAt (prioRuleK c r) I e m → ∀ x ∈ xs, ∀ a,
      (∀ p ∈ leftOf (prioRuleK c r), (KoreAML.tr ⟨tableOf [] (prioRuleK c r), []⟩ p).interpret I e a) →
        (KoreAML.tr ⟨tableOf [] (prioRuleK c r), []⟩ x).interpret I e a) :
    t.interpret I e m := by
  obtain ⟨t', ht', hb'⟩ := TieRulePair.rulesTie_at h hr
  rw [ht] at ht'; cases ht'
  exact rule_w2_builtG hI hb'
    (hI _ (Or.inl (Or.inr (Or.inl ⟨_, List.mem_map_of_mem (List.mem_of_getElem? hr), rfl⟩))))
    hN hs hin hb e m hxs

/-- **W2 for a rule of Γ that adds `⌈r ∧ ⊤⌉` alone**: the pattern of `R` at the rule's index holds
in every model of Γ. -/
theorem rules_w2_builtG_nil [OvlOK c] (h : rulesTieB c R = true) {j : Nat} {r : Rule} {t : P}
    (hr : c.rules[j]? = some r) (ht : R[j]? = some t)
    {gs : List (String × KoreAML.Gen)} {fT : List VarKey} {N : Srt} {s : String}
    {rr : Kore.Pattern} (hN : N < nRegSorts + c.sortNames.length)
    (hs : c.sortName N = s) (hin : TieRuleCutG.funsInGB c gs = true)
    (hb : rightBuiltGB gs fT s [] rr (prioRuleK c r) = true) : Γ c ⊧ t :=
  fun {_} _ {_} hI e m => rules_w2_builtG h hr ht hI hN hs hin hb e m
    (fun _ _ hx => absurd hx List.not_mem_nil)
end

end TieRuleW2G

end KCore
