/-
  The tie (C14) of the fixture e6-rangemap and its expectations (C7 form (a)), for every
  interpretation H. The text is `f2-examples/e6rm.kompile.kore`, the kompiled text of
  `test/constructs/fixtures/e6-rangemap` (equal to it after `kfix.stripped`):
  `m => ([0, 3) r|-> a) ([5, 7) r|-> b)` (`m` a total function of no argument, sentence 274) and the
  rule (sentence 182) `<k> go => res(size(m), m[1], m[3] orDefault c, 2 in_keys(m), 3 in_keys(m),
  size(M2), find_range(M2, 4), size(([0, 10) r|-> a) [ [3, 5) <- b ]),
  size(([0, 10) r|-> a) [ [3, 5) <- undef ]), ([0, 10) r|-> a) -RangeMap ([3, 5) r|-> a)) </k>`, with
  `M2 := ([0, 3) r|-> a) ([3, 5) r|-> a)`. Run from the package root:
  `lake env lean -j1 test/TieRangeMap.lean`. Every statement is on the literal `defn`; nothing reads
  `Parse.parse` or `emit`. The declarations of RANGEMAP and the `functional` sentences of its
  interpreted symbols: test/TieRangeMapDecls.lean.

  Layer 2.
  - Function equations (`fnText`: `m`'s, sentence 274, and the sort predicates'): each of Γ's
    items is the translation of its sentence (`shape`), so Γ entails each (`fns_entailed`) and each
    item is a consequence of its sentence (`fns_from_text`).
  - Constructor sentences, and the account of the classes tied: test/TieRangeMapCons.lean.
  - The rule (sentence 182): Γ's axiom of the rule (`prioRuleK`) is the sentence with conjuncts more
    on its left side, among them the definedness of the right side (`rules_tie`), so Γ's item is a
    consequence of the sentence (`rules_from_text`, W1) and the sentence holds where those conjuncts
    hold (`rules_w2`, W2).
  - `consistent`: Γ with the step's closure has a model, for every H; `FnHyp` with `m`'s totality,
    the one fact the deciders leave, from `m`'s value.

  The expectations (C7 form (a)):
  - `m_eq` (from sentences): `m` is `M := [0,3) ↦ a, [5,7) ↦ b`, from `Pre` (the function sentences as written, Γ's
    rule items and the families: here the graphs of the interpreted symbols), which has a model
    (`pre_model`): sentence 274 with the graphs of `r|->` and `_RangeMap_` at its right side.
  - `go_step` (through the reading: Γ's item of rule 182 holds only where its right side is
    defined, ruleRightDefined): `go` steps to `res(2, a, c, true, false, 1, [0,5), 3, 2,
    [0,3) ↦ a, [5,10) ↦ a)`, from `Pre`: Γ's item of the rule (a consequence of sentence 182,
    `rules_from_text`) where its left side matches, `m`'s value from 274, each application on its
    right side at its value by the graph of its interpreted symbol: `size` (2, 1, 3, 2), `m[1] = a`
    and `m[3] orDefault c = c` (a range holds its lower bound, not its upper), `in_keys` (true at 2,
    false at 3), `M2` merged into `[0,5)`, `find_range(M2, 4) = [0,5)`, the update, the removal and
    the difference; so the right side is defined there.
  The symbol numbers are the reader's for this text, each checked by its name (`syms_named`).
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.TieRangeMap

open KCore ML Faithful KoreAML

kore_term kore from "f2-examples/e6rm.kompile.kore"
definition_of defn from "f2-examples/e6rm.kompile.kore"
user_axioms U from "f2-examples/e6rm.kompile.kore" module "E6-RANGEMAP"

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

/-- Their axiom indices: `m`'s (274), then the sort predicates'. -/
theorem fnText_index : fnText.map (·.index) = [274, 253, 261, 260, 259, 258, 265, 264, 269, 268, 267, 266, 271,
    270, 263, 262, 242, 241, 252, 251, 248, 247, 250, 249, 255, 254, 257, 256, 244, 243, 246, 245] := by
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

/-- The rule sentences, in the order of `c.rules`: the one rule, sentence 182. -/
noncomputable def ruleText : List AxiomDecl := [U.ax182]

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

/-! ## The facts the deciders leave -/

def kCell : Sym := 382
def aS : Sym := 384
def bS : Sym := 385
def cS : Sym := 386
def goS : Sym := 387
def resS : Sym := 388
def mS : Sym := 389

theorem syms_named : c.symName kCell = "Lbl'-LT-'k'-GT-'" ∧ c.symName aS = "Lbla" ∧ c.symName bS = "Lblb" ∧
    c.symName cS = "Lblc" ∧ c.symName goS = "Lblgo" ∧ c.symName resS = "Lblres" ∧ c.symName mS = "Lblm" := by
  decide +kernel

theorem hok : c.ok = true := by decide +kernel
theorem hsr : c.srReady = true := by decide +kernel
theorem hmr : c.matchReady = true := by decide +kernel
theorem hokH (H : HookParams) : (cH H).ok = true := (Semantics.ok_withHooks c H).trans hok
theorem readsConfined_c : c.readsConfined = false := by decide +kernel
theorem readsConfinedH (H : HookParams) : (cH H).readsConfined = false :=
  (Semantics.readsConfined_withHooks c H).trans readsConfined_c

noncomputable abbrev fnM : Fn := c.fns[0]'(by decide +kernel)

theorem hfn : c.lookupFn mS = some fnM := rfl
theorem hfnH (H : HookParams) : (cH H).lookupFn mS = some fnM := by rw [Semantics.lookupFn_withHooks]; exact hfn
theorem hvsH (H : HookParams) : (cH H).sortsOf [] = some fnM.args := by
  rw [Semantics.sortsOf_withHooks _ _ noRaw]; decide +kernel

/-- Three KItem values. -/
def a : GroundTerm := .ctor aS []
def b : GroundTerm := .ctor bS []
def cv : GroundTerm := .ctor cS []

def elem (x y : Int) (v : GroundTerm) : GroundTerm := rmV [(rangeT x y, v)]

/-- `M`, the canonical value of `([0,3) r|-> a) ([5,7) r|-> b)`. -/
def M : GroundTerm := rmV [(rangeT 0 3, a), (rangeT 5 7, b)]
/-- `M10 -RangeMap ([3,5) r|-> a)`. -/
def Mdiff : GroundTerm := rmV [(rangeT 0 3, a), (rangeT 5 10, a)]

/-- **`m`'s one equation gives `M` under every interpretation**: `evalFC` reads none. -/
theorem m_value (H : HookParams) : Eval (cH H) mS [] (some M) :=
  TiePair.eval_withHooks hok hsr hmr noRaw H hfn (by decide +kernel) (n := 50) (by decide +kernel)

/-- `FnHyp` under every interpretation: the one obligation the deciders name is `m`'s totality,
which `m_value` gives; the rest are decided on the data. -/
theorem fnHypH (H : HookParams) : FnHyp (cH H) := by
  have hpl : (cH H).plain = true := (Semantics.plain_withHooks c H).trans (by decide +kernel)
  refine fnHyp_of_core (t := defn.cert) (coreOKH H)
    (Semantics.rightHeld_withHooks (Semantics.rightHeld_of_valued (by decide +kernel)) H (by decide +kernel))
    ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro f hf
    rw [orderObligations_withHooks, certObligations_withHooks,
      show c.orderObligations ++ defn.cert.obligations c = [] by decide +kernel] at hf
    exact absurd hf List.not_mem_nil
  · intro f hf fn hlook vs hvs
    rw [Semantics.totalObligations_withHooks, show c.totalObligations = [mS] by decide +kernel] at hf
    rw [List.mem_singleton] at hf
    subst hf
    rw [hfnH, Option.some.injEq] at hlook
    subst hlook
    have hargs : fnM.args = [] := by decide +kernel
    rw [hargs] at hvs
    cases vs with
    | nil => exact ⟨M, m_value H⟩
    | cons v vs =>
      rw [Semantics.sortsOf_withHooks _ _ noRaw] at hvs; unfold Semantics.sortsOf at hvs
      split at hvs <;> simp at hvs
  · intro f hf
    rw [Semantics.agreeObligations_withHooks, show c.agreeObligations = [] by decide +kernel] at hf
    exact absurd hf List.not_mem_nil
  · intro p hp
    rw [Semantics.matchObligations_withHooks, show c.matchObligations = [] by decide +kernel] at hp
    exact absurd hp List.not_mem_nil
  · intro o ho
    rw [Semantics.lazyObligations_withHooks, show c.lazyObligations = [] by decide +kernel] at ho
    exact absurd ho List.not_mem_nil
  · exact openDecided_of_plain (fun r hr => needsWitness_of_binds ((Semantics.plain_parts hpl).1 r hr))
      (fun fn hfn cl hcl => Clause.needsWitness_of_binds ((Semantics.plain_parts hpl).2.1 fn hfn cl hcl))
  · exact openLaws_of_plain (Semantics.plain_parts hpl).2.2

/-- **Γ with the step's closure has a model, for every H** (C14 closure (a)). -/
theorem consistent (H : HookParams) : Consistent (cH H) := consistent_of_fnHyp _ (coreOKH H) (fnHypH H)

/-! ## The expectations (C7 form (a)) -/

/-- The premises of the derivations: the function sentences as written, Γ's rule items, and the
families (the parts of Γ no sentence states: here the interpreted symbols' graphs and the values). -/
noncomputable abbrev Pre (H : HookParams) : Premises KoreAML.Sym := TiePair.Pre (cH H) textPats

/-- **`Pre` with the step's closure has a model, for every H.** -/
theorem pre_model (H : HookParams) :
    ∃ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M), I ⊧ᴵP (Pre H ∪ Γstep (cH H)) :=
  TiePair.pre_model (shapeH H) (consistent H)

/-- **`m` is `[0,3) ↦ a, [5,7) ↦ b`, derived from `Pre`**, for every H: sentence 274 as written, its
right side `([0, 3) r|-> a) ([5, 7) r|-> b)` at its value by the graphs of `r|->` and `_RangeMap_`. -/
theorem m_eq (H : HookParams) : Pre H ⊧ (TiePair.app (cH H) mS [] ≡ den (cH H) M) :=
  TiePair.value (shapeH H) (coreOKH H) (hokH H) (m_value H) (hfnH H) (hvsH H)

/-- The configuration `<k> t </k>` with the generated counter at 0. -/
def cfg (t : GroundTerm) : GroundTerm :=
  .ctor topLabel [.ctor kCell [.ctor kseq [t, .ctor dotk []]], .ctor counterLabel [int 0]]

def resV : GroundTerm :=
  .ctor resS [int 2, a, cv, bool true, bool false, int 1, rangeT 0 5, int 3, int 2, Mdiff]

/-- A configuration of the data under the interpretation H. -/
noncomputable abbrev XH (x : Config c) (H : HookParams) : Config (cH H) := TieRulePair.cfgH noRaw x H
noncomputable def Go : Config c := ⟨cfg (.ctor goS []), by decide +kernel⟩
noncomputable def Res : Config c := ⟨cfg resV, by decide +kernel⟩

/-- **`go` steps to `res(2, a, c, true, false, 1, [0,5), 3, 2, [0,3) ↦ a, [5,10) ↦ a)`**, for every H:
derived from `Pre`, through Γ's item of rule 182 (`m`'s equation 274 as written), each application
on the rule's right side at its value by its interpreted symbol's graph. -/
theorem go_step (H : HookParams) :
    Pre H ⊧ (den (cH H) (XH Go H).val ⇒ KoreAML.sNext (den (cH H) (XH Res H).val)) :=
  TiePair.cut (shapeH H)
    (sound_at_step (cH H) (coreOKH H) (readsConfinedH H) _ _
      (TieRulePair.step_withHooks hok hsr hmr noRaw (n := 50) (by decide +kernel) H))

end KCore.TieRangeMap

#check @KCore.TieRangeMap.m_eq
#check @KCore.TieRangeMap.go_step
#print axioms KCore.TieRangeMap.shape
#print axioms KCore.TieRangeMap.fns_entailed
#print axioms KCore.TieRangeMap.fns_from_text
#print axioms KCore.TieRangeMap.rules_tie
#print axioms KCore.TieRangeMap.rules_from_text
#print axioms KCore.TieRangeMap.rules_w2
#print axioms KCore.TieRangeMap.consistent
#print axioms KCore.TieRangeMap.pre_model
#print axioms KCore.TieRangeMap.m_eq
#print axioms KCore.TieRangeMap.go_step
