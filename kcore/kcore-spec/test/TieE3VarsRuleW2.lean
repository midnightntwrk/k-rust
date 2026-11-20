/-
  W2 for the rule sentence 170 of `f2-examples/e3-vars.kompile.kore` (construct fixture e3-vars;
  `test/TieE3Vars.lean` ties its sentences and has W1 for the rules), for every interpretation H,
  on the literal `defn`. Nothing here reads `Parse.parse` or `emit`. Run from the package root:
  `lake env lean -j1 test/TieE3VarsRuleW2.lean`.

  The rule, sentence 170, the third of `c.rules`: `<k> c(_, _Y) => d(?Z:Int) ... </k>`, whose right
  side is `\exists Z:Int. (<generatedTop>(<k>(inj{Exp,KItem}(d(Z)) ~> K), N, C) ∧ ⊤)`. Sentences 168
  and 169 (`a(X) => d(X)`, `b() => d(!N:Int)`) are not read here.
  - `rule_tie` (kernel): Γ's axiom of the rule (`prioRuleK`) is the sentence with one conjunct more
    on the left side, `⌈right⌉` (`extras`).
  - `right_built` (kernel): that conjunct is `⌈∃Z:Int. (t ∧ ⊤)⌉`, t built of Z, the rule's variables
    and generators whose Cons-Fun items Γ has (`right_funs`).
  - `int_inhabited`: every model of Γ has an element of Int, under every H: Int has a value, and
    Γ holds `∃y:Int. ⟦v⟧ = y` of each value.
  - `rule_entailed`: so `⌈right⌉` holds of every element of the top cell's sort (t at such a Z is
    one element), and Γ entails sentence 170 as written (`TieRuleW2G.rule_w2_exBuiltG_Γ`).
    `rule_in_step_models`: every model of `Γc` with the step's closure satisfies it.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.TieE3VarsRuleW2

open KCore ML Faithful KoreAML

kore_term kore from "f2-examples/e3-vars.kompile.kore"
definition_of defn from "f2-examples/e3-vars.kompile.kore"
user_axioms U from "f2-examples/e3-vars.kompile.kore" module "E3-VARS"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

/-- `tr s`: the item `Theory.ofDefinition kore` holds for the sentence. -/
noncomputable def trS (ad : AxiomDecl) : Item := trAxiom kore.symbolDecls kore.aliasNames ad

theorem coreOK : c.coreOK = true := by decide_cheap
theorem coreOKH (H : HookParams) : (cH H).coreOK = true := (Semantics.coreOK_withHooks c H).trans coreOK

noncomputable def r2 : Rule := c.rules[2]'(by decide +kernel)

theorem rule_count : c.rules.length = 3 ∧ U.ax170.index = 170 := by decide +kernel

/-- **Γ's axiom of the rule is sentence 170 with conjuncts more on the left side** (kernel). -/
theorem rule_tie : TieRulePair.ruleTextB (trS U.ax170).pat (prioRuleK c r2) = true := by decide +kernel

/-- **The axiom adds one conjunct** (kernel). -/
theorem extras : (TieRulePair.extraOf (prioRuleK c r2)).length = 1 := by decide +kernel

/-- The free variables of the rule's axiom. -/
noncomputable def freeKeys : List VarKey := (freeOf [] (prioRuleK c r2)).eraseDups

theorem top_numbered (H : HookParams) : topCellSort < nRegSorts + (cH H).sortNames.length :=
  (by decide +kernel : topCellSort < nRegSorts + c.sortNames.length)
theorem top_name (H : HookParams) : (cH H).sortName topCellSort = "GeneratedTopCell" :=
  (by decide +kernel : c.sortName topCellSort = "GeneratedTopCell")

/-- The generators of the right side, each with the name of its sort. -/
def rightGens : List (String × KoreAML.Gen) :=
  [("GeneratedTopCell", .ctor ⟨"Lbl'-LT-'generatedTop'-GT-'", ["KCell", "NCell", "GeneratedCounterCell"], "GeneratedTopCell"⟩),
   ("KCell", .ctor ⟨"Lbl'-LT-'k'-GT-'", ["K"], "KCell"⟩),
   ("K", .ctor ⟨"kseq", ["KItem", "K"], "K"⟩),
   ("KItem", .inj "Exp"),
   ("Exp", .ctor ⟨"Lbld", ["Int"], "Exp"⟩)]

/-- Γ has the Cons-Fun item of each (kernel). -/
theorem right_funs : TieRuleCutG.funsInGB c rightGens = true := by decide +kernel

/-- **The conjunct the axiom adds is `⌈∃Z:Int. (t ∧ ⊤)⌉`**, t built of Z, the rule's variables
and `rightGens`, of the top cell's sort, which `\top` on the left side names (kernel). -/
theorem right_built : TieRuleW2G.rightExBuiltGB rightGens freeKeys "GeneratedTopCell" "Int"
    (prioRuleK c r2) = true := by decide +kernel

/-- The reader exhibits a value of Int (kernel). -/
theorem int_value : (Parse.exhibit? c Srt.int).isSome = true := by decide +kernel

/-- **Every model of Γ has an element of Int**, for every H: Int has a value, which applies no
parameter, and Γ holds `∃y:Int. ⟦v⟧ = y` of each value. -/
theorem int_inhabited (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
    (hI : I ⊧ᴵP Γ (cH H)) : ∃ w, InS I "Int" w := by
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp int_value
  obtain ⟨a, ha⟩ := inhabited_of_exhibit_withHooks H hI hv KoreAML.val0
  have hn : (c.withHooks H).sortName Srt.int = "Int" := (by decide +kernel : c.sortName Srt.int = "Int")
  rw [hn] at ha
  exact ⟨a, ha⟩

/-- **Γ entails sentence 170** (`<k> c(_, _Y) => d(?Z:Int) ... </k>`) as written, for every H: Int has an
element, at which the right side's term is one element of the top cell's sort (the Cons-Fun items
of its generators), so the conjunct `⌈right⌉` of Γ's axiom holds wherever the sentence's left side
does. -/
theorem rule_entailed (H : HookParams) : Γ (cH H) ⊧ (trS U.ax170).pat := by
  haveI : OvlOK (cH H) := ovlOK_of_core (coreOKH H)
  intro M _ I hI
  exact TieRuleW2G.rule_w2_exBuiltG_Γ (c := cH H) (r := r2) (List.getElem_mem _)
    (by rw [TieRuleW2G.prioRuleK_withHooksW2G]; exact rule_tie) (top_numbered H) (top_name H)
    ((TieRuleCutG.funsInGB_withHooks c H rightGens).trans right_funs)
    (by rw [TieRuleW2G.prioRuleK_withHooksW2G]; exact right_built) (fun _ _ _ hI' => int_inhabited H hI') hI

/-- `Γc` entails the sentence too: it holds `Γ`. -/
theorem rule_entailed_c (H : HookParams) : Γc (cH H) ⊧ (trS U.ax170).pat :=
  fun hI => rule_entailed H fun φ hφ => hI φ (Or.inl hφ)

/-- **Every model of `Γc` with the step's closure satisfies sentence 170**, for every H. -/
theorem rule_in_step_models (H : HookParams) : Γc (cH H) ∪ Γstep (cH H) ⊧ (trS U.ax170).pat :=
  fun hI => rule_entailed_c H fun φ hφ => hI φ (Or.inl hφ)

end KCore.TieE3VarsRuleW2

#check @KCore.TieE3VarsRuleW2.rule_tie
#check @KCore.TieE3VarsRuleW2.extras
#check @KCore.TieE3VarsRuleW2.right_funs
#check @KCore.TieE3VarsRuleW2.right_built
#check @KCore.TieE3VarsRuleW2.int_inhabited
#check @KCore.TieE3VarsRuleW2.rule_entailed
#check @KCore.TieE3VarsRuleW2.rule_entailed_c
#check @KCore.TieE3VarsRuleW2.rule_in_step_models
#check @KCore.TieRuleW2G.ruleGuard_of_exBuiltG
#check @KCore.TieRuleW2G.rule_w2_exBuiltG
#check @KCore.TieRuleW2G.rule_w2_exBuiltG_Γ
#print axioms KCore.TieE3VarsRuleW2.rule_entailed
#print axioms KCore.TieE3VarsRuleW2.rule_in_step_models
