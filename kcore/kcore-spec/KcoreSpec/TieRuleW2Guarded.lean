/-
  KCore, outside the cone: W2 for a rule (`TieRulePair.rule_w2`) with its guard taken where the
  guards of the rule's variables hold, and the conjunct `⌈r ∧ ⊤⌉` of that guard from Cons-Fun.

  Γ's item of a rule is `guards → (\rewrites(l ∧ t ∧ extra, r) ≡ ⊤)`, so it is read only at the
  valuations where the guards of the rule's free variables hold (`GuardsAt`: each element variable
  holds an element of its sort). `TieRulePair.RuleGuard g I e` asks the conjuncts of `extra` at
  `e` without that premise.

  - `rule_w2_guarded`: the text's sentence `t` holds at `(e, m)` in a model of Γ's axiom `g` where
    `GuardsAt g I e m` gives `RuleGuard g I e`. `rule_w2` is the case where the guard holds outright.
  - `rightBuiltB gs fT s xs r g`: the conjuncts `g` adds are `xs` followed by
    `⌈r ∧ ⊤⌉` of the sort named `s`, `r` is built of the variables of `fT` (free in `g`) and the
    constructors of `gs` (`TieRuleCut.builtB`), and `\top` of that sort is one of the text's two
    conjuncts (a rule without `requires`), which keeps an element of the left side in the sort.
  - `ruleGuard_of_built`: then, in a model of Γ whose Cons-Fun items hold those of `gs`, where the
    guards hold, `RuleGuard` follows from its members `xs` alone: the member `⌈r ∧ ⊤⌉` holds by
    `TieRuleCut.rightDefined_of_Γ`.
  - `rule_w2_built`, `rules_w2_built`: W2 with the members of `xs` as its only premise, under the
    guards. The members that stay premises are the conjuncts of the rule's `pre` (`Cond.conj`) and
    `¬ ⋁ comps`, the negation of the rules of a smaller priority.
    `rules_w2_built_nil`: with `xs = []` (no `pre`, no rule of a smaller priority) the sentence
    holds in every model of Γ.
  - Not covered, so `⌈right⌉` stays a premise there: a right side with an `ensures`, a symbol with
    sort arguments (`inj`), a domain value or a function call (`builtB`), and a rule with a
    `requires` (the text's second conjunct is then not `\top`).
-/
import KcoreSpec.TieRulePair
import KcoreSpec.TieRuleCut

set_option autoImplicit false

namespace KCore

namespace TieRuleW2G

open ML Faithful KoreAML
open TieRulePair (kAx leftOf extraOf ruleTextB RuleGuard rulesTieB)

kernel_rfl prioRuleK_withHooksW2G : ∀ (c : Semantics) (H : HookParams) (r : Rule),
  prioRuleK (c.withHooks H) r = prioRuleK c r

/-- The conjuncts `g` adds are `xs` and then the definedness of `r ∧ ⊤` in the sort named `s`;
`\top` of that sort is one of the first two conjuncts; the keys of `fT` are free in `g`; `r` is
built of the variables of `fT` and the constructors of `gs`. -/
def rightBuiltB (gs : List (String × KoreAML.CtorSig)) (fT : List VarKey) (s : String)
    (xs : List Kore.Pattern) (r : Kore.Pattern) (g : Kore.Pattern) : Bool :=
  decide (extraOf g = xs ++ [.ceil (srt s) (srt s) (.and (srt s) [r, .top (srt s)])]) &&
    (leftOf g).any (fun p => decide (p = .top (srt s))) &&
    fT.all (fun k => (freeOf [] g).eraseDups.contains k) && TieRuleCut.builtB gs fT r s

section
variable {M : Type} {I : Interpretation KoreAML.Sym M}

/-- The guards of the free variables of `g` hold at `(e, m)`: the premise of Γ's item of `g`. -/
def GuardsAt (g : Kore.Pattern) (I : Interpretation KoreAML.Sym M) (e : Valuation M) (m : M) : Prop :=
  ∀ k ∈ (freeOf [] g).eraseDups, (guardOf (tableOf [] g) k).interpret I e m

/-- **W2 for a rule, with the guard under the variables' guards**: in a model of Γ's axiom `g`,
the text's sentence `t` holds at `(e, m)` where, the guards of `g`'s free variables holding there,
the conjuncts `g` adds hold of every element its first two hold. -/
theorem rule_w2_guarded (hD : KoreAML.DefOK I) {g : Kore.Pattern} {t : P} (h : ruleTextB t g = true)
    (hg : I ⊧ᴵ (trAxiom [] [] (kAx g)).pat) (e : Valuation M) (m : M)
    (hx : GuardsAt g I e m → RuleGuard g I e) : t.interpret I e m := by
  obtain ⟨W, S, G, X, hgp, htx, -, hXS, -, hGX⟩ := TieRulePair.rule_parts_at (I := I) h e
  have hW : W = conjList (((freeOf [] g).eraseDups).map (guardOf (tableOf [] g))) := by
    obtain ⟨C, C1, L, r, hgeq, -⟩ := TieRulePair.ruleTextB_parts h
    have h2 : (trAxiom [] [] (kAx g)).pat =
        TieRuleLhs.itemAt (tableOf [] g) (freeOf [] g).eraseDups C (.and C1 L) r := by
      rw [hgeq]; exact TieRuleLhs.trAxiom_rule C (.and C1 L) r
    rw [h2] at hgp
    unfold TieRuleLhs.itemAt at hgp
    injection hgp with h1 _
    exact h1.symm
  have h1 := hg e m
  rw [hgp, interpret_impl] at h1
  rw [htx, interpret_impl]
  intro hw
  have h2 := (KoreAML.interp_equal hD).mp (h1 hw)
  have hgd : GuardsAt g I e m := fun k hk => by
    rw [hW] at hw
    exact TieUnion.interp_conjListAll.mp hw _ (List.mem_map_of_mem hk)
  exact (KoreAML.interp_equal hD).mpr fun a => ⟨hXS a, fun hs => hGX (hx hgd) a ((h2 a).mpr hs)⟩

/-- **The guard from its other members.** In a model of Γ that has the Cons-Fun items of `gs`,
for `g` with `rightBuiltB`, where the guards of `g`'s free variables hold: the conjuncts `g` adds
hold of every element its first two hold, where those of `xs` do. The last, `⌈r ∧ ⊤⌉`, holds of
every element of the sort, which `\top` among the first two keeps the element in. -/
theorem ruleGuard_of_built [Inhabited M] {c : Semantics} [OvlOK c] (hI : I ⊧ᴵP Γ c)
    {gs : List (String × KoreAML.CtorSig)} {fT : List VarKey} {N : Srt} {s : String}
    {xs : List Kore.Pattern} {r g : Kore.Pattern} (hN : N < nRegSorts + c.sortNames.length)
    (hs : c.sortName N = s) (hin : TieRuleCut.funsInB c gs = true)
    (hb : rightBuiltB gs fT s xs r g = true) (e : Valuation M) (m : M) (hgd : GuardsAt g I e m)
    (hxs : ∀ x ∈ xs, ∀ a, (∀ p ∈ leftOf g, (KoreAML.tr ⟨tableOf [] g, []⟩ p).interpret I e a) →
      (KoreAML.tr ⟨tableOf [] g, []⟩ x).interpret I e a) :
    RuleGuard g I e := by
  subst hs
  simp only [rightBuiltB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.any_eq_true] at hb
  obtain ⟨⟨⟨hex, p0, hp0, hp0e⟩, hsub⟩, hbuilt⟩ := hb
  have htop : Kore.Pattern.top (srt (c.sortName N)) ∈ leftOf g := hp0e ▸ hp0
  intro x hx a hl
  rw [hex] at hx
  rcases List.mem_append.mp hx with hx | hx
  · exact hxs x hx a hl
  rw [List.mem_singleton.mp hx]
  have hD := defOK hI
  have h1 := hl _ htop
  have h2 : KoreAML.tr ⟨tableOf [] g, []⟩ (.top (srt (c.sortName N))) =
      sTop (trSort (tableOf [] g) (srt (c.sortName N))) := by rw [KoreAML.tr]
  rw [h2, interp_sTop hD (by rw [trSort_srt]; rfl)] at h1
  exact TieRuleCut.rightDefined_of_Γ hI hN hin hbuilt e m
    (fun k hk => hgd k (List.contains_iff_mem.mp (hsub k hk))) a h1

/-- **W2 for a rule whose right side is built of constructors**: in a model of Γ, the text's
sentence `t` of Γ's axiom `g` holds at `(e, m)` where, the guards holding there, the conjuncts of
`xs` (those `g` adds before `⌈r ∧ ⊤⌉`) hold of every element the first two hold. -/
theorem rule_w2_built [Inhabited M] {c : Semantics} [OvlOK c] (hI : I ⊧ᴵP Γ c)
    {gs : List (String × KoreAML.CtorSig)} {fT : List VarKey} {N : Srt} {s : String}
    {xs : List Kore.Pattern} {r g : Kore.Pattern} {t : P} (h : ruleTextB t g = true)
    (hg : I ⊧ᴵ (trAxiom [] [] (kAx g)).pat) (hN : N < nRegSorts + c.sortNames.length)
    (hs : c.sortName N = s) (hin : TieRuleCut.funsInB c gs = true)
    (hb : rightBuiltB gs fT s xs r g = true) (e : Valuation M) (m : M)
    (hxs : GuardsAt g I e m → ∀ x ∈ xs, ∀ a,
      (∀ p ∈ leftOf g, (KoreAML.tr ⟨tableOf [] g, []⟩ p).interpret I e a) →
        (KoreAML.tr ⟨tableOf [] g, []⟩ x).interpret I e a) :
    t.interpret I e m :=
  rule_w2_guarded (defOK hI) h hg e m fun hgd => ruleGuard_of_built hI hN hs hin hb e m hgd (hxs hgd)
end

section
variable {c : Semantics} {R : List P}

/-- **W2 for a rule of Γ whose right side is built of constructors**: in a model of Γ, the pattern
of `R` at the rule's index holds at `(e, m)` where, the guards holding there, the conjuncts of `xs`
(the rule's `pre` and the negation of the rules of a smaller priority) hold of every element the
text's left side holds. -/
theorem rules_w2_built [OvlOK c] (h : rulesTieB c R = true) {j : Nat} {r : Rule} {t : P}
    (hr : c.rules[j]? = some r) (ht : R[j]? = some t) {M : Type} [Inhabited M]
    {I : Interpretation KoreAML.Sym M} (hI : I ⊧ᴵP Γ c)
    {gs : List (String × KoreAML.CtorSig)} {fT : List VarKey} {N : Srt} {s : String}
    {xs : List Kore.Pattern} {rr : Kore.Pattern} (hN : N < nRegSorts + c.sortNames.length)
    (hs : c.sortName N = s) (hin : TieRuleCut.funsInB c gs = true)
    (hb : rightBuiltB gs fT s xs rr (prioRuleK c r) = true) (e : Valuation M) (m : M)
    (hxs : GuardsAt (prioRuleK c r) I e m → ∀ x ∈ xs, ∀ a,
      (∀ p ∈ leftOf (prioRuleK c r), (KoreAML.tr ⟨tableOf [] (prioRuleK c r), []⟩ p).interpret I e a) →
        (KoreAML.tr ⟨tableOf [] (prioRuleK c r), []⟩ x).interpret I e a) :
    t.interpret I e m := by
  obtain ⟨t', ht', hb'⟩ := TieRulePair.rulesTie_at h hr
  rw [ht] at ht'; cases ht'
  exact rule_w2_built hI hb'
    (hI _ (Or.inl (Or.inr (Or.inl ⟨_, List.mem_map_of_mem (List.mem_of_getElem? hr), rfl⟩))))
    hN hs hin hb e m hxs

/-- **W2 for a rule of Γ that adds `⌈r ∧ ⊤⌉` alone**: the pattern of `R` at the rule's index holds
in every model of Γ. -/
theorem rules_w2_built_nil [OvlOK c] (h : rulesTieB c R = true) {j : Nat} {r : Rule} {t : P}
    (hr : c.rules[j]? = some r) (ht : R[j]? = some t)
    {gs : List (String × KoreAML.CtorSig)} {fT : List VarKey} {N : Srt} {s : String}
    {rr : Kore.Pattern} (hN : N < nRegSorts + c.sortNames.length)
    (hs : c.sortName N = s) (hin : TieRuleCut.funsInB c gs = true)
    (hb : rightBuiltB gs fT s [] rr (prioRuleK c r) = true) : Γ c ⊧ t :=
  fun {_} _ {_} hI e m => rules_w2_built h hr ht hI hN hs hin hb e m
    (fun _ _ hx => absurd hx List.not_mem_nil)
end

end TieRuleW2G

end KCore
