/-
  The function equations and the rule of the fixture e6-rangemap-keys tied to its sentences (C14),
  and its expectation (C7 form (a)), for every interpretation H. The text is
  `f2-examples/e6rmkeys.kompile.kore`, the kompiled text of `test/constructs/fixtures/e6-rangemap-keys`
  (equal to it after `kfix.stripped`): the one rule (sentence 176)
  `<k> go => res(keys(([0, 3) r|-> a) ([5, 7) r|-> b))) </k>`, and no user function. Run from the
  package root: `lake env lean -j1 test/TieRangeMapKeys.lean`. Every statement is on the literal
  `defn`; nothing reads `Parse.parse` or `emit`. The declarations of RANGEMAP and the `functional`
  sentences of its interpreted symbols are tied on e6-rangemap (test/TieRangeMapDecls.lean);
  test/RangeMapKeysFixture.lean shows the step on the reading and that it is the only one.

  - Function equations (`fnText`: the sort predicates'): each of Γ's items is the translation of
    its sentence (`shape`), so Γ entails each (`fns_entailed`) and each item is a consequence of its
    sentence (`fns_from_text`).
  - The rule (sentence 176): Γ's axiom of the rule (`prioRuleK`) is the sentence with conjuncts more
    on its left side, among them the definedness of the right side (`rules_tie`), so Γ's item is a
    consequence of the sentence (`rules_from_text`, W1) and the sentence holds where those conjuncts
    hold (`rules_w2`, W2).
  - `consistent`: Γ with the step's closure has a model, for every H; the text owes no fact.

  The expectation (C7 form (a), through the reading: Γ's item of rule 176 holds only where its right
  side is defined, ruleRightDefined):
  - `go_step`: `go` steps to `res(SetItem([0,3)) SetItem([5,7)))`, the Set of the map's two ranges
    each injected into KItem, from `Pre` (the function sentences as written, Γ's rule items and the
    families: here the graphs of the interpreted symbols), which has a model (`pre_model`): Γ's item
    of the rule (a consequence of sentence 176, `rules_from_text`) where its left side matches, and
    `keys` at the map `([0, 3) r|-> a) ([5, 7) r|-> b)` at its value by the graphs of `r|->`,
    `_RangeMap_` and `keys`; so the right side is defined there.
  The symbol numbers are the reader's for this text, each checked by its name (`syms_named`).
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.TieRangeMapKeys

open KCore ML Faithful KoreAML

kore_term kore from "f2-examples/e6rmkeys.kompile.kore"
definition_of defn from "f2-examples/e6rmkeys.kompile.kore"
user_axioms U from "f2-examples/e6rmkeys.kompile.kore" module "E6-RANGEMAP-KEYS"

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
    c.symName goS = "Lblgo" ∧ c.symName resS = "Lblres" ∧
    c.symName rmKeys = "Lblkeys'LParUndsRParUnds'RANGEMAP'Unds'Set'Unds'RangeMap" := by
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

/-- The Set of the ranges `[0,3)` and `[5,7)`, each injected into KItem, in the Set's order: `keys`
of `([0, 3) r|-> a) ([5, 7) r|-> b)` (domains.md 620-625: the Set of all the ranges of the map). -/
def keysM : GroundTerm :=
  .set Srt.set [.inj Srt.range Srt.kitem (rangeT 0 3), .inj Srt.range Srt.kitem (rangeT 5 7)]

/-- The configuration `<k> t </k>` with the generated counter at 0. -/
def cfg (t : GroundTerm) : GroundTerm :=
  .ctor topLabel [.ctor kCell [.ctor kseq [t, .ctor dotk []]], .ctor counterLabel [int 0]]

/-- A configuration of the data under the interpretation H. -/
noncomputable abbrev XH (x : Config c) (H : HookParams) : Config (cH H) := TieRulePair.cfgH noRaw x H
noncomputable def Go : Config c := ⟨cfg (.ctor goS []), by decide +kernel⟩
noncomputable def Res : Config c := ⟨cfg (.ctor resS [keysM]), by decide +kernel⟩

/-- **`go` steps to `res` of the Set of the map's two ranges**, for every H: derived from `Pre`,
through Γ's item of rule 176, `keys` at the map's value by its interpreted symbol's graph. -/
theorem go_step (H : HookParams) :
    Pre H ⊧ (den (cH H) (XH Go H).val ⇒ KoreAML.sNext (den (cH H) (XH Res H).val)) :=
  TiePair.cut (shapeH H)
    (sound_at_step (cH H) (coreOKH H) (readsConfinedH H) _ _
      (TieRulePair.step_withHooks hok hsr hmr noRaw (n := 50) (by decide +kernel) H))

end KCore.TieRangeMapKeys

#check @KCore.TieRangeMapKeys.go_step
#print axioms KCore.TieRangeMapKeys.shape
#print axioms KCore.TieRangeMapKeys.fns_entailed
#print axioms KCore.TieRangeMapKeys.fns_from_text
#print axioms KCore.TieRangeMapKeys.rules_tie
#print axioms KCore.TieRangeMapKeys.rules_from_text
#print axioms KCore.TieRangeMapKeys.rules_w2
#print axioms KCore.TieRangeMapKeys.consistent
#print axioms KCore.TieRangeMapKeys.pre_model
#print axioms KCore.TieRangeMapKeys.go_step
