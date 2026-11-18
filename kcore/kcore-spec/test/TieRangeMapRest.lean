/-
  The function equations and the rule of the fixture e6-rangemap-rest tied to its sentences (C14),
  and its expectation (C7 form (a)), for every interpretation H. The text is
  `f2-examples/e6rmrest.kompile.kore`, the kompiled text of `test/constructs/fixtures/e6-rangemap-rest`
  (equal to it after `kfix.stripped`): no user function, and the one rule (sentence 176)
  `<k> go => res(.RangeMap, M1 <=RangeMap M, M <=RangeMap M1, removeAll(M10, SetItem([3, 5))),
  updateRangeMap(M10, ([3, 5) r|-> b))) </k>`, with `M1 := [0, 3) r|-> a`,
  `M := ([0, 3) r|-> a) ([5, 7) r|-> b)` and `M10 := [0, 10) r|-> a`. Run from the package root:
  `lake env lean -j1 test/TieRangeMapRest.lean`. Every statement is on the literal `defn`; nothing
  reads `Parse.parse` or `emit`. The declarations of RANGEMAP and the `functional` sentences of its
  interpreted symbols are tied on e6-rangemap (test/TieRangeMapDecls.lean).

  - Function equations (`fnText`: the sort predicates'): each of Γ's items is the translation of
    its sentence (`shape`), so Γ entails each (`fns_entailed`) and each item is a consequence of its
    sentence (`fns_from_text`).
  - The rule (sentence 176): Γ's axiom of the rule (`prioRuleK`) is the sentence with conjuncts more
    on its left side, among them the definedness of the right side (`rules_tie`), so Γ's item is a
    consequence of the sentence (`rules_from_text`, W1) and the sentence holds where those conjuncts
    hold (`rules_w2`, W2).
  - `consistent`: Γ with the step's closure has a model, for every H; the text owes no fact.

  The values the right side's applications take (`hook_values`, by the interpreted symbols' graphs;
  domains.md, K 7.1.337):
  - `.RangeMap` is the map with no range (513: "The `RangeMap` with zero elements");
  - `M1 <=RangeMap M` is true and `M <=RangeMap M1` false (665-671: inclusion; `M1` is a proper part of
    `M` and `[5, 7)` is no key of `M1`, so the two hold under inclusion and under strict inclusion
    alike);
  - `removeAll(M10, SetItem([3, 5)))` is `[0, 3) ↦ a, [5, 10) ↦ a` (611-613: every part of a range of
    the Set present in the map is removed; `[3, 5)` lies in `M10`, so the point is in the domain);
  - `updateRangeMap(M10, [3, 5) ↦ b)` is `[0, 3) ↦ a, [3, 5) ↦ b, [5, 10) ↦ a` (596-605: the second
    map's value overwrites the first's where their ranges overlap).
  The expectation (C7 form (a), through the reading: Γ's item of rule 176 holds only where its right
  side is defined, ruleRightDefined):
  - `go_step`: `go` steps to `res` of those five values, from `Pre` (the function sentences as
    written, Γ's rule items and the families: here the graphs of the interpreted symbols), which has
    a model (`pre_model`): Γ's item of the rule (a consequence of sentence 176, `rules_from_text`)
    where its left side matches, each application on its right side at its value by its interpreted
    symbol's graph; so the right side is defined there.
  The symbol numbers are the reader's for this text, each checked by its name (`syms_named`).
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.TieRangeMapRest

open KCore ML Faithful KoreAML

kore_term kore from "f2-examples/e6rmrest.kompile.kore"
definition_of defn from "f2-examples/e6rmrest.kompile.kore"
user_axioms U from "f2-examples/e6rmrest.kompile.kore" module "E6-RANGEMAP-REST"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

/-- No parameter of the definition is an open generator. -/
theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel

/-- `tr s`: the item `Theory.ofDefinition kore` holds for the sentence. -/
noncomputable def trS (ad : AxiomDecl) : Item := trAxiom kore.symbolDecls kore.aliasNames ad

theorem coreOK : c.coreOK = true := by decide_cheap
theorem coreOKH (H : HookParams) : (cH H).coreOK = true := (Semantics.coreOK_withHooks c H).trans coreOK

/-! ## The function equations -/

/-- The text sentences of Γ's equations, in `fnItems`'s order: found by head symbol and priority
(`TiePair.fnTextOf`); `shape` is what makes them the equations' sentences. -/
noncomputable def fnText : List AxiomDecl := TiePair.fnTextOf c U.all

/-- Their axiom indices: the sort predicates' (the text has no user function). -/
theorem fnText_index : fnText.map (·.index) = [247, 255, 254, 253, 252, 259, 258, 263, 262, 261, 260, 265,
    264, 257, 256, 236, 235, 246, 245, 242, 241, 244, 243, 249, 248, 251, 250, 238, 237, 240, 239] := by
  decide +kernel

/-- The translations of the text's sentences, in that order. -/
noncomputable def textPats : List P := fnText.map (trS · |>.pat)

/-- **Each of Γ's equations is the translation of its text sentence**, pattern for pattern or with
one variable renamed (`TiePair.sameB`; kernel). -/
theorem shape : TiePair.shapeB (TiePair.gammaPats c) textPats = true := by decide +kernel

theorem shapeH (H : HookParams) : TiePair.shapeB (TiePair.gammaPats (cH H)) textPats = true := by
  rw [TiePair.gammaPats_withHooks]; exact shape

/-- **E for the function equations**: Γ entails each, for every H. -/
theorem fns_entailed (H : HookParams) : ∀ ad ∈ fnText, Γ (cH H) ⊧ (trS ad).pat :=
  fun ad had => TiePair.entailed (shapeH H) _ (List.mem_map_of_mem had)

/-- **The converse for `fnItems`**: each item is a consequence of a text sentence, the j-th of
`fnText[j]`. -/
theorem fns_from_text (H : HookParams) :
    ∀ (j : Nat) (it : Item), (fnItems (cH H))[j]? = some it →
      ∃ ad, fnText[j]? = some ad ∧ (TiePair.Texts [(trS ad).pat] ⊧ it.pat) := by
  intro j it hj
  obtain ⟨t, ht, hent⟩ := TiePair.from_text (shapeH H) j it hj
  unfold textPats at ht
  rw [List.getElem?_map] at ht
  cases hf : fnText[j]? with
  | none => rw [hf] at ht; cases ht
  | some ad => rw [hf] at ht; cases ht; exact ⟨ad, rfl, hent⟩

/-! ## The rule sentence -/

/-- The rule sentences, in the order of `c.rules`: the one rule, sentence 176. -/
noncomputable def ruleText : List AxiomDecl := [U.ax176]

noncomputable def rulePats : List P := ruleText.map (trS · |>.pat)

/-- **Γ's axiom of the rule is its sentence with conjuncts more on the left side** (kernel). -/
theorem rules_tie : TieRulePair.rulesTieB c rulePats = true := by decide +kernel

theorem rules_tieH (H : HookParams) : TieRulePair.rulesTieB (cH H) rulePats = true :=
  (TieRulePair.rulesTieB_withHooks c H rulePats).trans rules_tie

/-- **W1 for the rule**: Γ's rule item is a consequence of its sentence, for every H. -/
theorem rules_from_text (H : HookParams) :
    ∀ (j : Nat) (it : Item), (ruleItems (cH H))[j]? = some it →
      ∃ ad, ruleText[j]? = some ad ∧ (TiePair.Texts [(trS ad).pat] ⊧ it.pat) := by
  intro j it hj
  obtain ⟨t, ht, hent⟩ := TieRulePair.rules_from_text (rules_tieH H) j it hj
  unfold rulePats at ht
  rw [List.getElem?_map] at ht
  cases hf : ruleText[j]? with
  | none => rw [hf] at ht; cases ht
  | some ad => rw [hf] at ht; cases ht; exact ⟨ad, rfl, hent⟩

/-- **W2 for the rule, with the guard**: in a model of Γ, for every H, the rule's sentence holds at
each valuation at which the conjuncts Γ's axiom of the rule adds (the definedness of the right
side) hold of every element the sentence's left side and `requires` hold. -/
theorem rules_w2 (H : HookParams) {j : Nat} {r : Rule} {ad : AxiomDecl} (hr : (cH H).rules[j]? = some r)
    (had : ruleText[j]? = some ad) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
    (hI : I ⊧ᴵP Γ (cH H)) (e : Valuation M) (hx : TieRulePair.RuleGuard (prioRuleK (cH H) r) I e) (m : M) :
    (trS ad).pat.interpret I e m :=
  TieRulePair.rules_w2 (rules_tieH H) hr (by unfold rulePats; rw [List.getElem?_map, had]; rfl) hI e hx m

/-! ## Consistency for every H -/

def kCell : Sym := 382
def aS : Sym := 384
def bS : Sym := 385
def goS : Sym := 386
def resS : Sym := 387

theorem syms_named : c.symName kCell = "Lbl'-LT-'k'-GT-'" ∧ c.symName aS = "Lbla" ∧ c.symName bS = "Lblb" ∧
    c.symName goS = "Lblgo" ∧ c.symName resS = "Lblres" ∧ c.symName rmUnit = "Lbl'Stop'RangeMap" ∧
    c.symName rmInclusion = "Lbl'Unds-LT-Eqls'RangeMap'UndsUnds'RANGEMAP'Unds'Bool'Unds'RangeMap'Unds'RangeMap" ∧
    c.symName rmRemoveAll = "LblremoveAll'LParUndsCommUndsRParUnds'RANGEMAP'Unds'RangeMap'Unds'RangeMap'Unds'Set" ∧
    c.symName rmUpdateAll = "LblupdateRangeMap'LParUndsCommUndsRParUnds'RANGEMAP'Unds'RangeMap'Unds'RangeMap'Unds'RangeMap" := by
  decide +kernel

theorem hok : c.ok = true := by decide +kernel
theorem hsr : c.srReady = true := by decide +kernel
theorem hmr : c.matchReady = true := by decide +kernel
theorem readsConfined_c : c.readsConfined = false := by decide +kernel
theorem readsConfinedH (H : HookParams) : (cH H).readsConfined = false :=
  (Semantics.readsConfined_withHooks c H).trans readsConfined_c

def callOrder : List Nat := []

theorem term_named : c.rankObligations callOrder ++ c.decObligationsL = [] := by decide +kernel
theorem total_named : c.totalObligationsRP callOrder [] = [] := by decide +kernel
theorem agree_named : c.agreeObligationsI = [] := by decide +kernel
theorem match_named : c.matchObligationsL = ([] : List (Nat × Nat)) := by decide +kernel

theorem obl_nil (H : HookParams) : FnObligations (cH H) callOrder [] :=
  FnObligations.of_nil
    (by rw [Semantics.rankObligations_withHooks, Semantics.decObligationsL_withHooks]; exact term_named)
    ((Semantics.totalObligationsRP_withHooks _ H _ _).trans total_named)
    ((Det.Semantics.agreeObligationsI_withHooks _ H).trans agree_named)
    ((Det.Semantics.matchObligationsL_withHooks _ H).trans match_named)

/-- `FnHyp` under every interpretation: the text owes no fact (no user function, nothing open). -/
theorem fnHypH (H : HookParams) : FnHyp (cH H) :=
  fnHyp_withHooks coreOK (Semantics.rightHeld_of_valued (by decide +kernel)) H ParamsTotal.nil (obl_nil H)

/-- **Γ with the step's closure has a model, for every H** (C14 closure (a)). -/
theorem consistent (H : HookParams) : Consistent (cH H) := consistent_of_fnHyp _ (coreOKH H) (fnHypH H)

/-! ## The expectation (C7 form (a)) -/

/-- The premises of the derivation: the function sentences as written, Γ's rule items, and the
families (the parts of Γ no sentence states: here the interpreted symbols' graphs and the values). -/
noncomputable abbrev Pre (H : HookParams) : Premises KoreAML.Sym := TiePair.Pre (cH H) textPats

/-- **`Pre` with the step's closure has a model, for every H.** -/
theorem pre_model (H : HookParams) :
    ∃ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M), I ⊧ᴵP (Pre H ∪ Γstep (cH H)) :=
  TiePair.pre_model (shapeH H) (consistent H)

def a : GroundTerm := .ctor aS []
def b : GroundTerm := .ctor bS []

def elem (x y : Int) (v : GroundTerm) : GroundTerm := rmV [(rangeT x y, v)]

/-- `M1`, `M`, `M10` and `[3, 5) ↦ b`: the canonical values of the maps the rule writes. -/
def M1 : GroundTerm := elem 0 3 a
def M : GroundTerm := rmV [(rangeT 0 3, a), (rangeT 5 7, b)]
def M10 : GroundTerm := elem 0 10 a
def M35b : GroundTerm := elem 3 5 b
/-- `SetItem([3, 5))`: the range injected into KItem. -/
def S35 : GroundTerm := .set Srt.set [.inj Srt.range Srt.kitem (rangeT 3 5)]

/-- The map with no range. -/
def unitV : GroundTerm := rmV []
/-- `M10` less `[3, 5)`. -/
def removedV : GroundTerm := rmV [(rangeT 0 3, a), (rangeT 5 10, a)]
/-- `M10` with `[3, 5)` bound to `b`. -/
def updatedV : GroundTerm := rmV [(rangeT 0 3, a), (rangeT 3 5, b), (rangeT 5 10, a)]

/-- **The values of the four applications** (domains.md 513, 665-671, 611-613, 596-605), by the
interpreted symbols' graphs: `hook` gives each a value, so no interpretation is read there. -/
theorem hook_values : hook rmUnit [] = some (some unitV) ∧
    hook rmInclusion [M1, M] = some (some (bool true)) ∧ hook rmInclusion [M, M1] = some (some (bool false)) ∧
    hook rmRemoveAll [M10, S35] = some (some removedV) ∧ hook rmUpdateAll [M10, M35b] = some (some updatedV) := by
  decide +kernel

def resV : GroundTerm := .ctor resS [unitV, bool true, bool false, removedV, updatedV]

/-- The configuration `<k> t </k>` with the generated counter at 0. -/
def cfg (t : GroundTerm) : GroundTerm :=
  .ctor topLabel [.ctor kCell [.ctor kseq [t, .ctor dotk []]], .ctor counterLabel [int 0]]

/-- A configuration of the data under the interpretation H. -/
noncomputable abbrev XH (x : Config c) (H : HookParams) : Config (cH H) := TieRulePair.cfgH noRaw x H
noncomputable def Go : Config c := ⟨cfg (.ctor goS []), by decide +kernel⟩
noncomputable def Res : Config c := ⟨cfg resV, by decide +kernel⟩

/-- **`go` steps to `res(.RangeMap's value, true, false, [0,3) ↦ a, [5,10) ↦ a, [0,3) ↦ a,
[3,5) ↦ b, [5,10) ↦ a)`**, for every H: derived from `Pre`, through Γ's item of rule 176, each
application on its right side at its value by its interpreted symbol's graph. -/
theorem go_step (H : HookParams) :
    Pre H ⊧ (den (cH H) (XH Go H).val ⇒ KoreAML.sNext (den (cH H) (XH Res H).val)) :=
  TiePair.cut (shapeH H)
    (sound_at_step (cH H) (coreOKH H) (readsConfinedH H) _ _
      (TieRulePair.step_withHooks hok hsr hmr noRaw (n := 50) (by decide +kernel) H))

end KCore.TieRangeMapRest

#check @KCore.TieRangeMapRest.go_step
#print axioms KCore.TieRangeMapRest.hook_values
#print axioms KCore.TieRangeMapRest.shape
#print axioms KCore.TieRangeMapRest.fns_entailed
#print axioms KCore.TieRangeMapRest.fns_from_text
#print axioms KCore.TieRangeMapRest.rules_tie
#print axioms KCore.TieRangeMapRest.rules_from_text
#print axioms KCore.TieRangeMapRest.rules_w2
#print axioms KCore.TieRangeMapRest.consistent
#print axioms KCore.TieRangeMapRest.pre_model
#print axioms KCore.TieRangeMapRest.go_step
