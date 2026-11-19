/-
  W2 for the rule sentences of `f2-examples/e3-kseq.kompile.kore` (construct fixture e3-kseq;
  `test/TieE3Kseq.lean` ties its sentences and has W1 for the rules), for every interpretation H, on
  the literal `defn`. Nothing here reads `Parse.parse` or `emit`. Run from the package root:
  `lake env lean -j1 test/TieE3KseqRuleW2.lean`.

  The rules, sentences 160 to 163 in the order of `c.rules`, all of priority 50, without `requires`,
  `ensures` or `pre`:
    160  `<k> a() => b() ~> c() ... </k>`      163  `<k> d() ~> X:K => X </k>`
    161  `<k> b() => .K ... </k>`              162  `<k> c() => . ... </k>`
  - `rules_tie` (kernel): Γ's axiom of each rule (`prioRuleK`) is its sentence with one conjunct
    more on the left side, `⌈right⌉` (`extras`).
  - Rules 161, 162, 163: the right side is `<generatedTop>(<k>(V), C) ∧ ⊤`, built of the rule's
    variables and of two constructors whose Cons-Fun items Γ has (`right_built`, `right_funs`). So
    `⌈right⌉` holds where the variables' guards hold (`TieRuleCut.rightDefined_of_Γ`), the guard of
    W2 has no other member, and Γ entails each sentence (`rule161_entailed`, `rule162_entailed`,
    `rule163_entailed`, by `TieRuleW2G.rules_w2_built_nil`).
  - Rule 160: the right side holds `inj{Exp, KItem}`, a symbol with sort arguments, which
    `TieRuleCut.builtB` does not read. `rule160_w2`: the sentence holds in a model of Γ at each
    valuation where, the guards of the rule's variables holding, `⌈right⌉` holds of every element
    of the sentence's left side (`TieRuleW2G.rule_w2_guarded`).
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.TieE3KseqRuleW2

open KCore ML Faithful KoreAML

kore_term kore from "f2-examples/e3-kseq.kompile.kore"
definition_of defn from "f2-examples/e3-kseq.kompile.kore"
user_axioms U from "f2-examples/e3-kseq.kompile.kore" module "E3-KSEQ"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

/-- `tr s`: the item `Theory.ofDefinition kore` holds for the sentence. -/
noncomputable def trS (ad : AxiomDecl) : Item := trAxiom kore.symbolDecls kore.aliasNames ad

theorem coreOK : c.coreOK = true := by decide_cheap
theorem coreOKH (H : HookParams) : (cH H).coreOK = true := (Semantics.coreOK_withHooks c H).trans coreOK

/-- The rule sentences, in the order of `c.rules`. -/
noncomputable def ruleText : List AxiomDecl := [U.ax160, U.ax161, U.ax162, U.ax163]

noncomputable def rulePats : List P := ruleText.map (trS · |>.pat)

theorem rule_prios : c.rules.map (·.prio) = [50, 50, 50, 50] ∧ ruleText.map (·.index) = [160, 161, 162, 163] := by
  decide +kernel

/-- **Γ's axiom of each rule is its sentence with conjuncts more on the left side** (kernel). -/
theorem rules_tie : TieRulePair.rulesTieB c rulePats = true := by decide +kernel

theorem rules_tieH (H : HookParams) : TieRulePair.rulesTieB (cH H) rulePats = true :=
  (TieRulePair.rulesTieB_withHooks c H rulePats).trans rules_tie

noncomputable def r0 : Rule := c.rules[0]'(by decide +kernel)
noncomputable def r1 : Rule := c.rules[1]'(by decide +kernel)
noncomputable def r2 : Rule := c.rules[2]'(by decide +kernel)
noncomputable def r3 : Rule := c.rules[3]'(by decide +kernel)

/-- The term of a right side `\and{C}(t, \top{C}())`. -/
def rightTerm : Kore.Pattern → Kore.Pattern
  | .rewrites _ _ (.and _ (t :: _)) => t
  | p => p

/-- The free variables of a rule's axiom. -/
noncomputable def freeKeys (r : Rule) : List VarKey := (freeOf [] (prioRuleK c r)).eraseDups

/-- **Each rule's axiom adds one conjunct**, the definedness of its right side (kernel). -/
theorem extras : [r0, r1, r2, r3].map (fun r => (TieRulePair.extraOf (prioRuleK c r)).length) = [1, 1, 1, 1] := by
  decide +kernel

def topSrt : Srt := 17
theorem top_numbered (H : HookParams) : topSrt < nRegSorts + (cH H).sortNames.length :=
  (by decide +kernel : topSrt < nRegSorts + c.sortNames.length)
theorem top_name (H : HookParams) : (cH H).sortName topSrt = "GeneratedTopCell" :=
  (by decide +kernel : c.sortName topSrt = "GeneratedTopCell")

/-- The constructors of the right sides of rules 161, 162 and 163, each with the name of its sort. -/
def rightCtors : List (String × KoreAML.CtorSig) :=
  [("GeneratedTopCell", ⟨"Lbl'-LT-'generatedTop'-GT-'", ["KCell", "GeneratedCounterCell"], "GeneratedTopCell"⟩),
   ("KCell", ⟨"Lbl'-LT-'k'-GT-'", ["K"], "KCell"⟩)]

/-- Γ has the Cons-Fun item of each (kernel). -/
theorem right_funs : TieRuleCut.funsInB c rightCtors = true := by decide +kernel

theorem right_funsH (H : HookParams) : TieRuleCut.funsInB (cH H) rightCtors = true :=
  (TieRuleCut.funsInB_withHooks c H rightCtors).trans right_funs

/-- **The axioms of rules 161, 162 and 163 add `⌈t ∧ ⊤⌉` alone**, t built of the rule's variables
and of `rightCtors`, of the top cell's sort, which `\top` on the left side names (kernel). -/
theorem right_built : [r1, r2, r3].all (fun r => TieRuleW2G.rightBuiltB rightCtors (freeKeys r) "GeneratedTopCell" []
    (rightTerm (prioRuleK c r)) (prioRuleK c r)) = true := by decide +kernel

/-- The right side of rule 160 is not built of its variables and constructors (`kseq`, `b`, `c`
beside `rightCtors`): it applies `inj{Exp, KItem}`, a symbol with sort arguments (kernel). -/
theorem right0_not_built : TieRuleCut.builtB (rightCtors ++ [("K", ⟨"kseq", ["KItem", "K"], "K"⟩),
      ("Exp", ⟨"Lblb", [], "Exp"⟩), ("Exp", ⟨"Lblc", [], "Exp"⟩)]) (freeKeys r0)
    (rightTerm (prioRuleK c r0)) "GeneratedTopCell" = false := by decide +kernel

theorem built_at (H : HookParams) {r : Rule} (hr : r ∈ [r1, r2, r3]) :
    TieRuleW2G.rightBuiltB rightCtors (freeKeys r) "GeneratedTopCell" []
      (rightTerm (prioRuleK c r)) (prioRuleK (cH H) r) = true := by
  rw [TieRuleW2G.prioRuleK_withHooksW2G]
  exact List.all_eq_true.mp right_built r hr

/-- **W2 for a rule that adds `⌈t ∧ ⊤⌉` alone**: Γ entails its sentence, for every H. -/
theorem rule_entailed (H : HookParams) {j : Nat} {r : Rule} {ad : AxiomDecl} (hr : c.rules[j]? = some r)
    (had : ruleText[j]? = some ad) (hm : r ∈ [r1, r2, r3]) : Γ (cH H) ⊧ (trS ad).pat := by
  haveI : OvlOK (cH H) := ovlOK_of_core (coreOKH H)
  intro M _ I hI
  exact TieRuleW2G.rules_w2_built_nil (rules_tieH H) (r := r) hr
    (by unfold rulePats; rw [List.getElem?_map, had]; rfl) (top_numbered H) (top_name H) (right_funsH H)
    (built_at H hm) hI

/-- **Γ entails sentence 161** (`<k> b() => .K ... </k>`), for every H. -/
theorem rule161_entailed (H : HookParams) : Γ (cH H) ⊧ (trS U.ax161).pat :=
  rule_entailed H (j := 1) (show c.rules[1]? = some r1 from List.getElem?_eq_getElem _) rfl (by simp)

/-- **Γ entails sentence 162** (`<k> c() => . ... </k>`), for every H. -/
theorem rule162_entailed (H : HookParams) : Γ (cH H) ⊧ (trS U.ax162).pat :=
  rule_entailed H (j := 2) (show c.rules[2]? = some r2 from List.getElem?_eq_getElem _) rfl (by simp)

/-- **Γ entails sentence 163** (`<k> d() ~> X:K => X </k>`), for every H. -/
theorem rule163_entailed (H : HookParams) : Γ (cH H) ⊧ (trS U.ax163).pat :=
  rule_entailed H (j := 3) (show c.rules[3]? = some r3 from List.getElem?_eq_getElem _) rfl (by simp)

/-- **W2 for sentence 160** (`<k> a() => b() ~> c() ... </k>`), for every H: it holds in a model of Γ
at each valuation where, the guards of the rule's variables holding, the conjunct Γ's axiom adds
(`⌈right⌉`) holds of every element of the sentence's left side. -/
theorem rule160_w2 (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
    (hI : I ⊧ᴵP Γ (cH H)) (e : Valuation M) (m : M)
    (hx : TieRuleW2G.GuardsAt (prioRuleK (cH H) r0) I e m → TieRulePair.RuleGuard (prioRuleK (cH H) r0) I e) :
    (trS U.ax160).pat.interpret I e m := by
  obtain ⟨t, ht, hb⟩ := TieRulePair.rulesTie_at (rules_tieH H) (j := 0) (r := r0)
    (show c.rules[0]? = some r0 from List.getElem?_eq_getElem _)
  have ht' : rulePats[0]? = some (trS U.ax160).pat := rfl
  rw [ht'] at ht; cases ht
  exact TieRuleW2G.rule_w2_guarded (defOK hI) hb
    (hI _ (Or.inl (Or.inr (Or.inl ⟨_, List.mem_map_of_mem
      (List.mem_of_getElem? (show c.rules[0]? = some r0 from List.getElem?_eq_getElem _)), rfl⟩)))) e m hx

end KCore.TieE3KseqRuleW2

#check @KCore.TieE3KseqRuleW2.rules_tie
#check @KCore.TieE3KseqRuleW2.extras
#check @KCore.TieE3KseqRuleW2.right_built
#check @KCore.TieE3KseqRuleW2.right0_not_built
#check @KCore.TieE3KseqRuleW2.rule161_entailed
#check @KCore.TieE3KseqRuleW2.rule162_entailed
#check @KCore.TieE3KseqRuleW2.rule163_entailed
#check @KCore.TieE3KseqRuleW2.rule160_w2
#check @KCore.TieRuleW2G.rule_w2_guarded
#check @KCore.TieRuleW2G.ruleGuard_of_built
#check @KCore.TieRuleW2G.rule_w2_built
#check @KCore.TieRuleW2G.rules_w2_built
#check @KCore.TieRuleW2G.rules_w2_built_nil
#print axioms KCore.TieE3KseqRuleW2.rules_tie
#print axioms KCore.TieE3KseqRuleW2.right_built
#print axioms KCore.TieE3KseqRuleW2.rule161_entailed
#print axioms KCore.TieE3KseqRuleW2.rule162_entailed
#print axioms KCore.TieE3KseqRuleW2.rule163_entailed
#print axioms KCore.TieE3KseqRuleW2.rule160_w2
