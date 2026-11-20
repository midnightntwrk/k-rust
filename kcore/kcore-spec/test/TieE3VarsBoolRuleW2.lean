/-
  W2 for the rule sentence of `f2-examples/exvarsbool.kompile.kore` (construct fixture e3-vars-bool;
  `test/TieE3VarsBool.lean` ties its sentences and has W1 for the rule), for every interpretation H,
  on the literal `defn`. Nothing here reads `Parse.parse` or `emit`. Run from the package root:
  `lake env lean -j1 test/TieE3VarsBoolRuleW2.lean`.

  The rule, sentence 113: `<k> c() => d(?Z:Bool) </k>`, whose right side is
  `\exists Z:Bool. (<generatedTop>(<k>(inj{Exp,KItem}(d(Z)) ~> .K), C) ∧ ⊤)`.
  - `rule_tie` (kernel): Γ's axiom of the rule (`prioRuleK`) is the sentence with one conjunct more
    on the left side, `⌈right⌉` (`extras`).
  - `right_built` (kernel): that conjunct is `⌈∃Z:Bool. (t ∧ ⊤)⌉`, t built of Z, the rule's variable
    and generators whose Cons-Fun items Γ has (`right_funs`).
  - `bool_inhabited`: every model of Γ has an element of Bool, under every H: Bool has a value, and
    Γ holds `∃y:Bool. ⟦v⟧ = y` of each value.
  - `rule_entailed`: so `⌈right⌉` holds of every element of the top cell's sort (t at such a Z is
    one element), and Γ entails sentence 113 as written (`TieRuleW2G.rule_w2_exBuiltG_Γ`).
    `rule_in_step_models`: every model of `Γc` with the step's closure satisfies it.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.TieE3VarsBoolRuleW2

open KCore ML Faithful KoreAML

kore_term kore from "f2-examples/exvarsbool.kompile.kore"
definition_of defn from "f2-examples/exvarsbool.kompile.kore"
user_axioms U from "f2-examples/exvarsbool.kompile.kore" module "E3-VARS-BOOL"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

/-- `tr s`: the item `Theory.ofDefinition kore` holds for the sentence. -/
noncomputable def trS (ad : AxiomDecl) : Item := trAxiom kore.symbolDecls kore.aliasNames ad

theorem coreOK : c.coreOK = true := by decide_cheap
theorem coreOKH (H : HookParams) : (cH H).coreOK = true := (Semantics.coreOK_withHooks c H).trans coreOK

noncomputable def r0 : Rule := c.rules[0]'(by decide +kernel)

theorem rule_count : c.rules.length = 1 ∧ U.ax113.index = 113 := by decide +kernel

/-- **Γ's axiom of the rule is sentence 113 with conjuncts more on the left side** (kernel). -/
theorem rule_tie : TieRulePair.ruleTextB (trS U.ax113).pat (prioRuleK c r0) = true := by decide +kernel

/-- **The axiom adds one conjunct** (kernel). -/
theorem extras : (TieRulePair.extraOf (prioRuleK c r0)).length = 1 := by decide +kernel

/-- The free variables of the rule's axiom. -/
noncomputable def freeKeys : List VarKey := (freeOf [] (prioRuleK c r0)).eraseDups

theorem top_numbered (H : HookParams) : topCellSort < nRegSorts + (cH H).sortNames.length :=
  (by decide +kernel : topCellSort < nRegSorts + c.sortNames.length)
theorem top_name (H : HookParams) : (cH H).sortName topCellSort = "GeneratedTopCell" :=
  (by decide +kernel : c.sortName topCellSort = "GeneratedTopCell")

/-- The generators of the right side, each with the name of its sort. -/
def rightGens : List (String × KoreAML.Gen) :=
  [("GeneratedTopCell", .ctor ⟨"Lbl'-LT-'generatedTop'-GT-'", ["KCell", "GeneratedCounterCell"], "GeneratedTopCell"⟩),
   ("KCell", .ctor ⟨"Lbl'-LT-'k'-GT-'", ["K"], "KCell"⟩),
   ("K", .ctor ⟨"kseq", ["KItem", "K"], "K"⟩),
   ("K", .ctor ⟨"dotk", [], "K"⟩),
   ("KItem", .inj "Exp"),
   ("Exp", .ctor ⟨"Lbld", ["Bool"], "Exp"⟩)]

/-- Γ has the Cons-Fun item of each (kernel). -/
theorem right_funs : TieRuleCutG.funsInGB c rightGens = true := by decide +kernel

/-- **The conjunct the axiom adds is `⌈∃Z:Bool. (t ∧ ⊤)⌉`**, t built of Z, the rule's variables
and `rightGens`, of the top cell's sort, which `\top` on the left side names (kernel). -/
theorem right_built : TieRuleW2G.rightExBuiltGB rightGens freeKeys "GeneratedTopCell" "Bool"
    (prioRuleK c r0) = true := by decide +kernel

/-- The reader exhibits a value of Bool (kernel). -/
theorem bool_value : (Parse.exhibit? c Srt.bool).isSome = true := by decide +kernel

/-- **Every model of Γ has an element of Bool**, for every H: Bool has a value, which applies no
parameter, and Γ holds `∃y:Bool. ⟦v⟧ = y` of each value. -/
theorem bool_inhabited (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
    (hI : I ⊧ᴵP Γ (cH H)) : ∃ w, InS I "Bool" w := by
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp bool_value
  obtain ⟨a, ha⟩ := inhabited_of_exhibit_withHooks H hI hv KoreAML.val0
  have hn : (c.withHooks H).sortName Srt.bool = "Bool" := (by decide +kernel : c.sortName Srt.bool = "Bool")
  rw [hn] at ha
  exact ⟨a, ha⟩

/-- **Γ entails sentence 113** (`<k> c() => d(?Z:Bool) </k>`) as written, for every H: Bool has an
element, at which the right side's term is one element of the top cell's sort (the Cons-Fun items
of its generators), so the conjunct `⌈right⌉` of Γ's axiom holds wherever the sentence's left side
does. -/
theorem rule_entailed (H : HookParams) : Γ (cH H) ⊧ (trS U.ax113).pat := by
  haveI : OvlOK (cH H) := ovlOK_of_core (coreOKH H)
  intro M _ I hI
  exact TieRuleW2G.rule_w2_exBuiltG_Γ (c := cH H) (r := r0) (List.getElem_mem _)
    (by rw [TieRuleW2G.prioRuleK_withHooksW2G]; exact rule_tie) (top_numbered H) (top_name H)
    ((TieRuleCutG.funsInGB_withHooks c H rightGens).trans right_funs)
    (by rw [TieRuleW2G.prioRuleK_withHooksW2G]; exact right_built) (fun _ _ _ hI' => bool_inhabited H hI') hI

/-- `Γc` entails the sentence too: it holds `Γ`. -/
theorem rule_entailed_c (H : HookParams) : Γc (cH H) ⊧ (trS U.ax113).pat :=
  fun hI => rule_entailed H fun φ hφ => hI φ (Or.inl hφ)

/-- **Every model of `Γc` with the step's closure satisfies sentence 113**, for every H. -/
theorem rule_in_step_models (H : HookParams) : Γc (cH H) ∪ Γstep (cH H) ⊧ (trS U.ax113).pat :=
  fun hI => rule_entailed_c H fun φ hφ => hI φ (Or.inl hφ)

end KCore.TieE3VarsBoolRuleW2

#check @KCore.TieE3VarsBoolRuleW2.rule_tie
#check @KCore.TieE3VarsBoolRuleW2.extras
#check @KCore.TieE3VarsBoolRuleW2.right_funs
#check @KCore.TieE3VarsBoolRuleW2.right_built
#check @KCore.TieE3VarsBoolRuleW2.bool_inhabited
#check @KCore.TieE3VarsBoolRuleW2.rule_entailed
#check @KCore.TieE3VarsBoolRuleW2.rule_entailed_c
#check @KCore.TieE3VarsBoolRuleW2.rule_in_step_models
#check @KCore.TieRuleW2G.ruleGuard_of_exBuiltG
#check @KCore.TieRuleW2G.rule_w2_exBuiltG
#check @KCore.TieRuleW2G.rule_w2_exBuiltG_Γ
#print axioms KCore.TieE3VarsBoolRuleW2.rule_entailed
#print axioms KCore.TieE3VarsBoolRuleW2.rule_in_step_models
