/-
  The tie (C14) of the fixture e2-rule on `f2-examples/rulecool.kompile.kore`: nine rules over
  `a(Int)`, `b(Int)`, `c(Int)`, among them a labelled one, three of priorities 10, 50 and 60 at
  `a(X)`, an `[owise]` one beside `b(0) => c(0)`, `c(X) => b(X)` with `preserves-definedness` and a
  label, and the `[cool]` and `[heat]` rules `<k> c(1) => b(1) ... </k>` and
  `<k> c(2) => b(2) ... </k>`, whose `requires` `true andBool isKResult(HOLE)` and
  `true andBool notBool isKResult(HOLE)` hold HOLE:K, bound by no side. Every statement is on the
  literal `defn`, for every interpretation H; nothing reads `Parse.parse` or `emit`.
  Run from the package root: `lake env lean -j1 test/TieRuleCool.lean`.

  The tie.
  - Function equations (`fnText`, the sort predicates'): each of Γ's items is the translation of its
    sentence (`shape`), so Γ entails each (`fns_entailed`) and each item is a consequence of its
    sentence (`TiePair.from_text`).
  - The rule sentences (`ruleText`, 164 to 172, in the order of `c.rules`): Γ's axiom of each rule
    (`prioRuleK`) is its sentence with conjuncts more on the left side, the definedness of the right
    side and, beside a rule of a smaller priority, the negation of that rule's left side and
    `requires` (`rules_tie`, kernel), so each of Γ's rule items is a consequence of its sentence
    (`rules_from_text`, W1). HOLE, free in the sentence and in Γ's item, is universal over the
    whole sentence in both.
  - The definition reads a confined sort (`readsConfined_c`), so its theory is `Γc = Γ ∪ Γcl`, and
    `Γcl` holds one item, `boolClosed` (`gammaCl_eq`), a family of the reading that no sentence
    states.
  - The facts `FnHyp` asks, for every H (`obl_nil`): no obligation is named, and the two rules that
    need a witness, the `[cool]` and `[heat]` rules, are `Witnessed` (`witnessed6H`, `witnessed7H`:
    HOLE := `kseq(inj{Int,KItem}(0), dotk)` and HOLE := `dotk`, the `requires` evaluated by
    `Exec.evalT_sound` at `c.withHooks H`, whose evaluation of these terms reads no interpretation).
    So `Γc` with the step's closure has a model (`consistent`), and so has `Pre` (`pre_model`): the
    function sentences as written, Γ's rule items (each a consequence of its sentence by W1), the
    families and `Γcl`; every premise of `Γc` is a consequence of `Pre` (`gamma_from`).

  The steps, for every H, each built by hand (`StepBy`): the priority premise of a rule is shown
  by `NotApplies` of each rule of a smaller priority number, at its left side or (at `b(0)`, for
  the `[owise]` rule) at its match. The inversions: every rule's left side is
  `<k> f(p) ~> R </k>` with the counter cell (`lhsOf`), so a match fixes `f` and `p`'s value
  (`lhs_inv`), and a right side `<k> g(X) ~> R </k>` evaluates to one configuration (`rhs_inv`).

  The expectations (C7 form (a)), from `Pre` (with the step's closure for the successor sets):
  - `a5_step`, `a5_succs`: `a(5)` steps to `c(5)` (sentence 165, priority 10), and `c(5)` is its only
    successor: the rules of priorities 50 and 60 at `a(X)` (164, 166, 167; the labelled one among
    them) are blocked there by the one of priority 10.
  - `b5_step`, `b5_succs`: `b(5)` steps to `c(5)` by the `[owise]` rule (169), its only successor.
  - `b0_step`, `b0_succs`: `b(0)` steps to `c(0)` by `b(0) => c(0)` (168), its only successor: the
    `[owise]` rule is blocked there.
  - `c5_step`, `c5_succs`: `c(5)` steps to `b(5)` by the rule with `preserves-definedness` and the
    label `r2` (172), its only successor: the `[cool]` and `[heat]` rules do not match there.
  - `c1_step`: `c(1)` steps to `b(1)` by the `[cool]` rule (170), HOLE := `kseq(inj{Int,KItem}(0), dotk)`.
  - `c2_step`: `c(2)` steps to `b(2)` by the `[heat]` rule (171), HOLE := `dotk`.
  The rule labelled `r2` (172) steps `c(1)` and `c(2)` to `b(1)` and `b(2)` too; `c1_step` and
  `c2_step` are derived through the `[cool]` and `[heat]` steps. No successor set is stated at `c(1)`
  or `c(2)`, where an outcome is the family of a rule with HOLE open.

  Not tied here: the constructor sentences, no junk, the hooked functional, collection law, library
  and set-variable classes, and the account of the user module (on e2-unbound,
  test/TieUnbound.lean and test/TieUnboundAtValues.lean tie them).
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.TieRuleCool

open KCore ML Faithful KoreAML

kore_term kore from "f2-examples/rulecool.kompile.kore"
definition_of defn from "f2-examples/rulecool.kompile.kore"
user_axioms U from "f2-examples/rulecool.kompile.kore" module "E2-RULE"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

/-- No parameter of the definition is an open generator. -/
theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel

/-- `tr s`: the item `Theory.ofDefinition kore` holds for the sentence. -/
noncomputable def trS (ad : AxiomDecl) : Item := trAxiom kore.symbolDecls kore.aliasNames ad

set_option maxHeartbeats 1000000 in
theorem coreOK : c.coreOK = true := by decide_cheap
theorem coreOKH (H : HookParams) : (cH H).coreOK = true := (Semantics.coreOK_withHooks c H).trans coreOK

/-- HOLE is left open: the definition reads a confined sort, so its theory is `Γc`. -/
theorem readsConfined_c : c.readsConfined = true := by decide +kernel

/-- Bool holds only its literals here, and the definition reads a confined sort: `Γcl` holds its
one item, `boolClosed`. -/
theorem gammaCl_eq (H : HookParams) (φ : P) : Γcl (cH H) φ ↔ φ = boolClosed (cH H) :=
  ⟨fun h => h.2.2, fun h => ⟨readsConfined_c, (by decide +kernel : c.litSort Srt.bool = true), h⟩⟩

/-! ## The function equations (the sort predicates') -/

noncomputable def fnText : List AxiomDecl := TiePair.fnTextOf c U.all

noncomputable def textPats : List P := fnText.map (trS · |>.pat)

/-- **Each of Γ's equations is the translation of its text sentence** (`TiePair.sameB`; kernel). -/
theorem shape : TiePair.shapeB (TiePair.gammaPats c) textPats = true := by decide +kernel

theorem shapeH (H : HookParams) : TiePair.shapeB (TiePair.gammaPats (cH H)) textPats = true := by
  rw [TiePair.gammaPats_withHooks]; exact shape

/-- **E for the function equations**: Γ entails each, for every H. -/
theorem fns_entailed (H : HookParams) : ∀ ad ∈ fnText, Γ (cH H) ⊧ (trS ad).pat :=
  fun _ had => TiePair.entailed (shapeH H) _ (List.mem_map_of_mem had)

/-! ## The rule sentences -/

/-- The rule sentences, in the order of `c.rules`. -/
noncomputable def ruleText : List AxiomDecl :=
  [U.ax164, U.ax165, U.ax166, U.ax167, U.ax168, U.ax169, U.ax170, U.ax171, U.ax172]

noncomputable def rulePats : List P := ruleText.map (trS · |>.pat)

/-- The rules' priorities (the text's `priority` and `owise` attributes) and their sentences'
indices. -/
theorem rule_prios : c.rules.map (·.prio) = [50, 10, 50, 60, 50, 200, 50, 50, 50] ∧
    ruleText.map (·.index) = [164, 165, 166, 167, 168, 169, 170, 171, 172] := by
  decide +kernel

/-- **Γ's axiom of each rule is its sentence with conjuncts more on the left side** (kernel). -/
theorem rules_tie : TieRulePair.rulesTieB c rulePats = true := by decide +kernel

theorem rules_tieH (H : HookParams) : TieRulePair.rulesTieB (cH H) rulePats = true :=
  (TieRulePair.rulesTieB_withHooks c H rulePats).trans rules_tie

/-- **W1 for the rules**: each of Γ's rule items is a consequence of its sentence, for every H. -/
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

/-! ## The rules -/

def sExp : Srt := 32
def isKResult : Sym := 383
def kCell : Sym := 384
def symA : Sym := 386
def symB : Sym := 387
def symC : Sym := 388
def andBool : Sym := 4
def notBool : Sym := 3

theorem names_ok : c.sortName sExp = "Exp" ∧ c.symName isKResult = "LblisKResult" ∧
    c.symName kCell = "Lbl'-LT-'k'-GT-'" ∧ c.symName symA = "Lbla" ∧ c.symName symB = "Lblb" ∧
    c.symName symC = "Lblc" ∧ c.symName andBool = "Lbl'Unds'andBool'Unds'" ∧
    c.symName notBool = "LblnotBool'Unds'" := by
  decide +kernel

noncomputable def r0 : Rule := c.rules[0]'(by decide +kernel)
noncomputable def r1 : Rule := c.rules[1]'(by decide +kernel)
noncomputable def r2 : Rule := c.rules[2]'(by decide +kernel)
noncomputable def r3 : Rule := c.rules[3]'(by decide +kernel)
noncomputable def r4 : Rule := c.rules[4]'(by decide +kernel)
noncomputable def r5 : Rule := c.rules[5]'(by decide +kernel)
noncomputable def r6 : Rule := c.rules[6]'(by decide +kernel)
noncomputable def r7 : Rule := c.rules[7]'(by decide +kernel)
noncomputable def r8 : Rule := c.rules[8]'(by decide +kernel)

theorem rules_len : c.rules.length = 9 := by decide +kernel

theorem rules_eq : c.rules = [r0, r1, r2, r3, r4, r5, r6, r7, r8] := by
  apply List.ext_getElem (by rw [rules_len]; rfl)
  intro i h1 _
  rw [rules_len] at h1
  match i, h1 with
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | 4, _ => rfl
  | 5, _ => rfl
  | 6, _ => rfl
  | 7, _ => rfl
  | 8, _ => rfl

theorem rulesH (H : HookParams) : (cH H).rules = [r0, r1, r2, r3, r4, r5, r6, r7, r8] := rules_eq

/-- The left side of every rule, and the right side of those without a function: `<k> f(p) ~> R </k>`
with the counter cell, R and the counter the variables 1 and 2. -/
def lhsOf (f : Sym) (p : Term) : Term :=
  .app topLabel [.app kCell [.app kseq [.inj sExp Srt.kitem (.app f [p]), .var 1]], .var 2]

/-- The literal n bound to the variable 0. -/
def litAs (n : Int) : Term := .as (.dv Srt.int (.int n)) 0

theorem r0_parts : r0.vars = [Srt.int, Srt.k, 19] ∧ r0.lhs = lhsOf symA (.var 0) ∧ r0.req = none ∧
    r0.pre = .top ∧ r0.prio = 50 := ⟨rfl, rfl, rfl, rfl, rfl⟩
theorem r1_parts : r1.vars = [Srt.int, Srt.k, 19] ∧ r1.lhs = lhsOf symA (.var 0) ∧
    r1.rhs = lhsOf symC (.var 0) ∧ r1.req = none ∧ r1.ens = none ∧ r1.pre = .top ∧ r1.post = .top ∧
    r1.prio = 10 := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
theorem r2_parts : r2.lhs = lhsOf symA (.var 0) ∧ r2.prio = 50 := ⟨rfl, rfl⟩
theorem r3_parts : r3.lhs = lhsOf symA (.var 0) ∧ r3.prio = 60 := ⟨rfl, rfl⟩
theorem r4_parts : r4.vars = [Srt.int, Srt.k, 19] ∧ r4.lhs = lhsOf symB (litAs 0) ∧
    r4.rhs = lhsOf symC (.var 0) ∧ r4.req = none ∧ r4.ens = none ∧ r4.pre = .top ∧ r4.post = .top ∧
    r4.prio = 50 := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
theorem r5_parts : r5.vars = [Srt.int, Srt.k, 19] ∧ r5.lhs = lhsOf symB (.var 0) ∧
    r5.rhs = lhsOf symC (.var 0) ∧ r5.req = none ∧ r5.ens = none ∧ r5.pre = .top ∧ r5.post = .top ∧
    r5.prio = 200 := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
theorem r6_parts : r6.vars = [Srt.int, Srt.k, 19, Srt.k] ∧ r6.lhs = lhsOf symC (litAs 1) ∧
    r6.rhs = lhsOf symB (.var 0) ∧
    r6.req = some (.app andBool [.dv Srt.bool (.bool true), .app isKResult [.var 3]]) ∧ r6.ens = none ∧
    r6.pre = .top ∧ r6.post = .top ∧ r6.prio = 50 := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
theorem r7_parts : r7.vars = [Srt.int, Srt.k, 19, Srt.k] ∧ r7.lhs = lhsOf symC (litAs 2) ∧
    r7.rhs = lhsOf symB (.var 0) ∧
    r7.req = some (.app andBool [.dv Srt.bool (.bool true), .app notBool [.app isKResult [.var 3]]]) ∧
    r7.ens = none ∧ r7.pre = .top ∧ r7.post = .top ∧ r7.prio = 50 := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
theorem r8_parts : r8.vars = [Srt.int, Srt.k, 19] ∧ r8.lhs = lhsOf symC (.var 0) ∧
    r8.rhs = lhsOf symB (.var 0) ∧ r8.req = none ∧ r8.ens = none ∧ r8.pre = .top ∧ r8.post = .top ∧
    r8.prio = 50 := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
theorem r_exs : r1.exs = [] ∧ r4.exs = [] ∧ r5.exs = [] ∧ r6.exs = [] ∧ r7.exs = [] ∧ r8.exs = [] :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **The `[cool]` and `[heat]` rules are the rules that need a witness, and the ones with an
open variable** (HOLE, variable 3). -/
theorem witness_rules : r6.needsWitness c = true ∧ r7.needsWitness c = true ∧ r6.opens = [3] ∧ r7.opens = [3] ∧
    r0.needsWitness c = false ∧ r1.needsWitness c = false ∧ r2.needsWitness c = false ∧
    r3.needsWitness c = false ∧ r4.needsWitness c = false ∧ r5.needsWitness c = false ∧
    r8.needsWitness c = false ∧ r0.opens = [] ∧ r1.opens = [] ∧ r2.opens = [] ∧ r3.opens = [] ∧
    r4.opens = [] ∧ r5.opens = [] ∧ r8.opens = [] := by
  decide +kernel

/-! ## The facts `FnHyp` asks, for every H -/

theorem sortOfH (H : HookParams) (v : GroundTerm) : (cH H).sortOf v = c.sortOf v := by
  rw [Semantics.sortOf_withHooks _ _ noRaw]

/-- `kseq(inj{Int,KItem}(0), dotk)`: a K whose one item is a `KResult`. -/
def holeCool : GroundTerm := .ctor kseq [.inj Srt.int Srt.kitem (int 0), .ctor dotk []]
/-- `dotk`: the empty K, not a `KResult`. -/
def holeHeat : GroundTerm := .ctor dotk []

def dotK : GroundTerm := .ctor dotk []
def cnt0 : GroundTerm := .ctor counterLabel [.dv Srt.int (.int 0)]

theorem base_sorts : c.sortOf holeCool = some Srt.k ∧ c.sortOf holeHeat = some Srt.k ∧
    c.sortOf dotK = some Srt.k ∧ c.sortOf cnt0 = some 19 := by
  decide +kernel

/-- The substitution at `<k> f(n) </k>`. -/
def σn (n : Int) : Subst := [(0, int n), (1, dotK), (2, cnt0)]
/-- The substitution of the `[cool]` and `[heat]` rules at `<k> c(n) </k>`, HOLE := h. -/
def σAt (n : Int) (h : GroundTerm) : Subst := σn n ++ [(3, h)]

theorem σn_sorted (H : HookParams) (n : Int) : (cH H).WellSorted [Srt.int, Srt.k, 19] (σn n) := fun j s hs => by
  match j, hs with
  | 0, hs => cases hs; exact ⟨_, rfl, by rw [sortOfH]; exact sortOf_int n⟩
  | 1, hs => cases hs; exact ⟨_, rfl, by rw [sortOfH]; exact base_sorts.2.2.1⟩
  | 2, hs => cases hs; exact ⟨_, rfl, by rw [sortOfH]; exact base_sorts.2.2.2⟩

theorem σAt_sorted (H : HookParams) {n : Int} {h : GroundTerm} (hh : c.sortOf h = some Srt.k) :
    (cH H).WellSorted [Srt.int, Srt.k, 19, Srt.k] (σAt n h) := fun j s hs => by
  match j, hs with
  | 0, hs => cases hs; exact ⟨_, rfl, by rw [sortOfH]; exact sortOf_int n⟩
  | 1, hs => cases hs; exact ⟨_, rfl, by rw [sortOfH]; exact base_sorts.2.2.1⟩
  | 2, hs => cases hs; exact ⟨_, rfl, by rw [sortOfH]; exact base_sorts.2.2.2⟩
  | 3, hs => cases hs; exact ⟨_, rfl, by rw [sortOfH]; exact hh⟩

theorem fnsH (H : HookParams) : (cH H).fns = [] := (by decide +kernel : c.fns = [])

/-- The functions are the generated sort predicates (`fns` is empty), whose clauses `sortPreds_ctx`
reads: the executable evaluation is sound here although `ok` is false (an open rule variable). -/
theorem clauseCtx (H : HookParams) : Exec.ClauseCtx (cH H) := by
  intro fn hfn'
  rcases List.mem_append.mp hfn' with hfn | hfn
  · rw [fnsH] at hfn; cases hfn
  · exact ⟨[], fun k hk => (nomatch hk), fun cl hcl =>
      ⟨(sortPreds_ctx hfn cl hcl).1, (sortPreds_ctx hfn cl hcl).2.1, (sortPreds_ctx hfn cl hcl).2.2.1,
        (sortPreds_ctx hfn cl hcl).2.2.2.1, (sortPreds_ctx hfn cl hcl).2.2.2.2.1,
        (sortPreds_ctx hfn cl hcl).2.2.2.2.2, Semantics.sortPreds_pre hfn cl hcl,
        Semantics.sortPreds_exs hfn cl hcl, Semantics.sortPreds_post hfn cl hcl⟩⟩

theorem sortCtx (H : HookParams) : SortCtx (cH H) := by
  obtain ⟨hok, hsr, -, -, -, -, -, -, hno⟩ := hypSound_of_core (coreOKH H)
  haveI : OvlOK (cH H) := hno
  exact sortCtx_of_all hok hsr (OvlOK.ovlCase hno)

theorem matchCtx (H : HookParams) : Exec.MatchCtx (cH H) :=
  Exec.matchCtx_of ((Semantics.matchReady_withHooks c H).trans (by decide +kernel))

-- The `requires` of the `[cool]` rule evaluates to `true` at HOLE := `holeCool`, for every H:
-- the evaluation reads no interpretation of the parameters.
kernel_rfl evalCool : ∀ H : HookParams, Exec.evalT (c.withHooks H) 10 (σAt 1 holeCool)
  (.app andBool [.dv Srt.bool (.bool true), .app isKResult [.var 3]]) = some (some (bool true))
-- The `requires` of the `[heat]` rule evaluates to `true` at HOLE := `holeHeat`, for every H.
kernel_rfl evalHeat : ∀ H : HookParams, Exec.evalT (c.withHooks H) 10 (σAt 2 holeHeat)
  (.app andBool [.dv Srt.bool (.bool true), .app notBool [.app isKResult [.var 3]]]) = some (some (bool true))

theorem reqCool (H : HookParams) : EvalTerm (cH H) (σAt 1 holeCool)
    (.app andBool [.dv Srt.bool (.bool true), .app isKResult [.var 3]]) (some (bool true)) :=
  Exec.evalT_sound (sortCtx H) (clauseCtx H) (matchCtx H) 10 (evalCool H) (headsOK_fns (cH H))
    (σAt_sorted H base_sorts.1) (s := Srt.bool) (by rw [fnsH]; exact (by decide +kernel :
      sortOfTerm (c.rhsCtx []) [Srt.int, Srt.k, 19, Srt.k]
        (.app andBool [.dv Srt.bool (.bool true), .app isKResult [.var 3]]) = some Srt.bool))

theorem reqHeat (H : HookParams) : EvalTerm (cH H) (σAt 2 holeHeat)
    (.app andBool [.dv Srt.bool (.bool true), .app notBool [.app isKResult [.var 3]]]) (some (bool true)) :=
  Exec.evalT_sound (sortCtx H) (clauseCtx H) (matchCtx H) 10 (evalHeat H) (headsOK_fns (cH H))
    (σAt_sorted H base_sorts.2.1) (s := Srt.bool) (by rw [fnsH]; exact (by decide +kernel :
      sortOfTerm (c.rhsCtx []) [Srt.int, Srt.k, 19, Srt.k]
        (.app andBool [.dv Srt.bool (.bool true), .app notBool [.app isKResult [.var 3]]]) = some Srt.bool))

/-- **The `[cool]` rule is `Witnessed`, for every H**, HOLE := `kseq(inj{Int,KItem}(0), dotk)`. -/
theorem witnessed6H (H : HookParams) : r6.Witnessed (cH H) :=
  ⟨σAt 1 holeCool, fun i _ s hs => σAt_sorted H base_sorts.1 i s (by rw [← r6_parts.1]; exact hs),
   fun t ht => by rw [r6_parts.2.2.2.1] at ht; cases ht; exact reqCool H,
   by rw [r6_parts.2.2.2.2.2.1]; exact .top⟩

/-- **The `[heat]` rule is `Witnessed`, for every H**, HOLE := `dotk`. -/
theorem witnessed7H (H : HookParams) : r7.Witnessed (cH H) :=
  ⟨σAt 2 holeHeat, fun i _ s hs => σAt_sorted H base_sorts.2.1 i s (by rw [← r7_parts.1]; exact hs),
   fun t ht => by rw [r7_parts.2.2.2.1] at ht; cases ht; exact reqHeat H,
   by rw [r7_parts.2.2.2.2.2.1]; exact .top⟩

kernel_rfl needsWitnessH : ∀ (H : HookParams) (r : Rule), r.needsWitness (c.withHooks H) = r.needsWitness c

/-- **Every closed open condition is decided, for every H**: the two rules that need a witness are
`Witnessed`; there is no function clause but the sort predicates'. -/
theorem openDecidedH (H : HookParams) : OpenDecided (cH H) := by
  refine ⟨fun r hr hw => ?_, fun fn hfn => by rw [fnsH] at hfn; cases hfn⟩
  rw [rulesH] at hr
  rw [needsWitnessH] at hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  obtain ⟨h6, h7, -, -, h0, h1, h2, h3, h4, h5, h8, -⟩ := witness_rules
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [h0] at hw; cases hw
  · rw [h1] at hw; cases hw
  · rw [h2] at hw; cases hw
  · rw [h3] at hw; cases hw
  · rw [h4] at hw; cases hw
  · rw [h5] at hw; cases hw
  · exact .inl (witnessed6H H)
  · exact .inl (witnessed7H H)
  · rw [h8] at hw; cases hw

theorem term_named : c.rankObligations [] ++ c.decObligationsL = [] := by decide +kernel
theorem total_named : c.totalObligationsRP [] [] = [] := by decide +kernel
theorem agree_named : c.agreeObligationsI = [] := by decide +kernel
theorem match_named : c.matchObligationsL = ([] : List (Nat × Nat)) := by decide +kernel

/-- The obligations, for every H: none is named, and the two owed conditions are witnessed. -/
theorem obl_nil (H : HookParams) : FnObligations (cH H) [] [] := by
  have h1 : (cH H).rankObligations [] ++ (cH H).decObligationsL = [] := by
    rw [Semantics.rankObligations_withHooks, Semantics.decObligationsL_withHooks]; exact term_named
  have h2 : (cH H).totalObligationsRP [] [] = [] := (Semantics.totalObligationsRP_withHooks _ H _ _).trans total_named
  have h3 : (cH H).agreeObligationsI = [] := (Det.Semantics.agreeObligationsI_withHooks _ H).trans agree_named
  have h4 : (cH H).matchObligationsL = [] := (Det.Semantics.matchObligationsL_withHooks _ H).trans match_named
  refine ⟨fun f hf => ?_, fun f hf => ?_, fun f hf => ?_, fun p hp => ?_, openDecidedH H, openLaws_of_plain noRaw⟩
  · rw [h1] at hf; exact absurd hf List.not_mem_nil
  · rw [h2] at hf; exact absurd hf List.not_mem_nil
  · rw [h3] at hf; exact absurd hf List.not_mem_nil
  · rw [h4] at hp; exact absurd hp List.not_mem_nil

/-- **`FnHyp` for every H.** -/
theorem fnHypH (H : HookParams) : FnHyp (cH H) :=
  fnHyp_withHooks coreOK (Semantics.rightHeld_of_valued (by decide +kernel)) H ParamsTotal.nil (obl_nil H)

/-- **`Γc` with the step's closure has a model, for every H.** -/
theorem consistent (H : HookParams) : Consistent (cH H) := consistent_of_fnHyp _ (coreOKH H) (fnHypH H)

/-! ## The premises of the derivations -/

/-- The function sentences as written, Γ's rule items (each a consequence of its sentence,
`rules_from_text`), the families, and `Γcl` (`boolClosed`, a family of the reading). -/
def Pre (H : HookParams) : Premises KoreAML.Sym := TiePair.Pre (cH H) textPats ∪ Γcl (cH H)

/-- **Every premise of `Γc` is a consequence of `Pre`.** -/
theorem gamma_from (H : HookParams) : ∀ φ, Γc (cH H) φ → Pre H ⊧ φ := by
  intro φ h M _ I hI
  rcases h with h | h
  · exact TiePair.gamma_from (shapeH H) φ h (I := I) fun ψ hψ => hI ψ (Or.inl hψ)
  · exact hI φ (Or.inr h)

/-- **`Pre` with the step's closure has a model, for every H**: every model of `Γc` with it is one. -/
theorem pre_model (H : HookParams) :
    ∃ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M), I ⊧ᴵP (Pre H ∪ Γstep (cH H)) := by
  obtain ⟨M, hM, I, hI⟩ := consistent H
  have hΓ : I ⊧ᴵP Γ (cH H) := fun φ h => hI φ (Or.inl (Or.inl h))
  refine ⟨M, hM, I, fun φ h => ?_⟩
  rcases h with (h | h) | h
  · rcases h with ((h1 | h1) | h1)
    · rcases h1 with ht | ⟨x, rfl⟩
      · exact TiePair.entailed (shapeH H) φ ht hΓ
      · exact hΓ _ (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨x, rfl⟩))))))))
    · exact hΓ _ (Or.inl (Or.inr h1))
    · rcases h1 with (((h1 | h1) | h1) | h1) | h1
      · exact hΓ _ (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl h1))))))
      · exact hΓ _ (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h1))))))
      · exact hΓ _ (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h1)))))
      · exact hΓ _ (Or.inl (Or.inl (Or.inl (Or.inr h1))))
      · exact hΓ _ (Or.inr h1)
  · exact hI _ (Or.inl (Or.inr h))
  · exact hI _ (Or.inr h)

/-- The cut: what `Γc` entails, `Pre` entails. -/
theorem cutC (H : HookParams) {ψ : P} (hψ : Γc (cH H) ⊧ ψ) : Pre H ⊧ ψ :=
  fun hT => hψ fun φ hφ => gamma_from H φ hφ hT

/-- The cut with the step's closure on both sides. -/
theorem cutStep (H : HookParams) {ψ : P} (hψ : (Γc (cH H) ∪ Γstep (cH H)) ⊧ ψ) : (Pre H ∪ Γstep (cH H)) ⊧ ψ :=
  fun hT => hψ fun φ hφ => by
    rcases hφ with hφ | hφ
    · exact gamma_from H φ hφ (fun χ hχ => hT χ (Or.inl hχ))
    · exact hT φ (Or.inr hφ)

/-! ## The configurations and the inversions -/

section Steps
variable (H : HookParams)

theorem syms_ok : (cH H).isCtor topLabel = true ∧ (cH H).isCtor kCell = true ∧ (cH H).isCtor kseq = true ∧
    (cH H).isCtor symA = true ∧ (cH H).isCtor symB = true ∧ (cH H).isCtor symC = true :=
  (by decide +kernel : c.isCtor topLabel = true ∧ c.isCtor kCell = true ∧ c.isCtor kseq = true ∧
    c.isCtor symA = true ∧ c.isCtor symB = true ∧ c.isCtor symC = true)
theorem hooks_ok : patternHooks.contains topLabel = false ∧ patternHooks.contains kCell = false ∧
    patternHooks.contains kseq = false ∧ patternHooks.contains symA = false ∧
    patternHooks.contains symB = false ∧ patternHooks.contains symC = false := by
  decide +kernel

/-- The three constructors of Exp that take an Int. -/
def ABC (f : Sym) : Prop := f = symA ∨ f = symB ∨ f = symC

theorem abc_ok {f : Sym} (hf : ABC f) : (cH H).isCtor f = true ∧ patternHooks.contains f = false := by
  rcases hf with rfl | rfl | rfl
  · exact ⟨(syms_ok H).2.2.2.1, hooks_ok.2.2.2.1⟩
  · exact ⟨(syms_ok H).2.2.2.2.1, hooks_ok.2.2.2.2.1⟩
  · exact ⟨(syms_ok H).2.2.2.2.2, hooks_ok.2.2.2.2.2⟩

theorem abcA : ABC symA := .inl rfl
theorem abcB : ABC symB := .inr (.inl rfl)
theorem abcC : ABC symC := .inr (.inr rfl)

/-- The configuration `<k> f(v) ~> w </k>` with the counter cell u. -/
def cfgOf (f : Sym) (v w u : GroundTerm) : GroundTerm :=
  .ctor topLabel [.ctor kCell [.ctor kseq [.inj sExp Srt.kitem (.ctor f [v]), w]], u]

/-- The constructor, its argument, the rest of the k cell and the counter cell of a configuration
`cfgOf f v w u`. -/
def partsOf : GroundTerm → Option (Sym × GroundTerm × GroundTerm × GroundTerm)
  | .ctor _ [.ctor _ [.ctor _ [.inj _ _ (.ctor f [v]), w]], u] => some (f, v, w, u)
  | _ => none

omit H in
theorem cfgOf_inj {f g : Sym} {v v' w w' u u' : GroundTerm} (h : cfgOf f v w u = cfgOf g v' w' u') :
    f = g ∧ v = v' ∧ w = w' ∧ u = u' := by
  have h' := congrArg partsOf h
  simp only [partsOf, cfgOf, Option.some.injEq, Prod.mk.injEq] at h'
  exact h'

/-- **What a left side denotes**: `<k> f(v) ~> w </k>` with the counter cell u, where p denotes v
and σ gives the variables 1 and 2 the values w and u. -/
theorem lhs_inv {f : Sym} {p : Term} {σ : Subst} {x : GroundTerm} (hf : ABC f)
    (h : PatVal (cH H) σ (lhsOf f p) x) :
    ∃ v w u, x = cfgOf f v w u ∧ PatVal (cH H) σ p v ∧ σ.lookup 1 = some w ∧ σ.lookup 2 = some u := by
  obtain ⟨hc, hh⟩ := abc_ok H hf
  unfold lhsOf at h
  obtain ⟨-, vs, rfl, hvs⟩ := PatVal.app_inv hooks_ok.1 h (syms_ok H).1
  obtain ⟨v1, vs1, rfl, h1, hvs1⟩ := hvs.cons_inv
  obtain ⟨u, vs2, rfl, h2, hvs2⟩ := hvs1.cons_inv
  cases hvs2.nil_inv
  obtain ⟨-, ws, rfl, hws⟩ := PatVal.app_inv hooks_ok.2.1 h1 (syms_ok H).2.1
  obtain ⟨w1, ws1, rfl, h11, hws1⟩ := hws.cons_inv
  cases hws1.nil_inv
  obtain ⟨-, zs, rfl, hzs⟩ := PatVal.app_inv hooks_ok.2.2.1 h11 (syms_ok H).2.2.1
  obtain ⟨z1, zs1, rfl, hz1, hzs1⟩ := hzs.cons_inv
  obtain ⟨w, zs2, rfl, hz2, hzs2⟩ := hzs1.cons_inv
  cases hzs2.nil_inv
  obtain ⟨a, ha, rfl⟩ := PatVal.inj_inv hz1
  obtain ⟨-, as, rfl, has⟩ := PatVal.app_inv hh ha hc
  obtain ⟨v, as1, rfl, hv, has1⟩ := has.cons_inv
  cases has1.nil_inv
  exact ⟨v, w, u, rfl, hv, PatVal.var_inv hz2, PatVal.var_inv h2⟩

/-- A left side whose constructor is not the configuration's does not match it. -/
theorem mismatch {f g : Sym} {p : Term} {σ : Subst} {v w u : GroundTerm} (hf : ABC f) (hfg : f ≠ g)
    (h : PatVal (cH H) σ (lhsOf f p) (cfgOf g v w u)) : False := by
  obtain ⟨_, _, _, hx, -⟩ := lhs_inv H hf h
  exact hfg (cfgOf_inj hx).1.symm

/-- A left side at the literal k does not match the configuration at n ≠ k. -/
theorem mismatch_lit {f : Sym} {k n : Int} {σ : Subst} {w u : GroundTerm} (hf : ABC f) (hne : n ≠ k)
    (h : PatVal (cH H) σ (lhsOf f (litAs k)) (cfgOf f (int n) w u)) : False := by
  obtain ⟨v, _, _, hx, hp, -⟩ := lhs_inv H hf h
  obtain rfl := (cfgOf_inj hx).2.1
  have := PatVal.dv_inv (PatVal.as_inv hp).1
  simp only [int, GroundTerm.dv.injEq, Lit.int.injEq, true_and] at this
  exact hne this

/-- **What a right side `<k> f(X) ~> R </k>` evaluates to.** -/
theorem rhs_inv {f : Sym} {σ : Subst} {y v w u : GroundTerm} (hf : ABC f)
    (h : EvalTerm (cH H) σ (lhsOf f (.var 0)) (some y))
    (h0 : σ.lookup 0 = some v) (h1 : σ.lookup 1 = some w) (h2 : σ.lookup 2 = some u) :
    y = cfgOf f v w u := by
  obtain ⟨hc, -⟩ := abc_ok H hf
  unfold lhsOf at h
  obtain ⟨rs, hrs, he⟩ := EvalTerm.ctor_inv (syms_ok H).1 h
  obtain ⟨q1, rs1, rfl, hq1, hrs1⟩ := hrs.cons_inv
  obtain ⟨q2, rs2, rfl, hq2, hrs2⟩ := hrs1.cons_inv
  cases hrs2.nil_inv
  rw [hq2.var_inv, h2] at he
  obtain ⟨ps, hps, rfl⟩ := EvalTerm.ctor_inv (syms_ok H).2.1 hq1
  obtain ⟨p1, ps1, rfl, hp1, hps1⟩ := hps.cons_inv
  cases hps1.nil_inv
  obtain ⟨ks, hks, rfl⟩ := EvalTerm.ctor_inv (syms_ok H).2.2.1 hp1
  obtain ⟨k1, ks1, rfl, hk1, hks1⟩ := hks.cons_inv
  obtain ⟨k2, ks2, rfl, hk2, hks2⟩ := hks1.cons_inv
  cases hks2.nil_inv
  rw [hk2.var_inv, h1] at he
  obtain ⟨b1, hb1, rfl⟩ := EvalTerm.inj_inv hk1
  obtain ⟨bs, hbs, rfl⟩ := EvalTerm.ctor_inv hc hb1
  obtain ⟨d1, ds1, rfl, hd1, hds1⟩ := hbs.cons_inv
  cases hds1.nil_inv
  rw [hd1.var_inv, h0] at he
  simp only [allSome, Option.bind, Option.map, injNormal, Option.some.injEq] at he
  exact he

omit H in
/-- A rule without `requires` and with the predicate `\top` applies wherever it matches. -/
theorem not_reqFails {c' : Semantics} {r : Rule} {σ : Subst} (hreq : r.req = none) (hpre : r.pre = .top) :
    ¬ RuleReqFails c' σ r := by
  intro h
  cases h with
  | intro ht _ _ => rw [hreq] at ht; cases ht
  | pre h => rw [hpre] at h; cases h

/-- The left side at the variable 0 matches `<k> f(n) </k>` at `σn n`. -/
theorem match_var {f : Sym} (hf : ABC f) (n : Int) :
    PatVal (cH H) (σn n) (lhsOf f (.var 0)) (cfgOf f (int n) dotK cnt0) :=
  .ctor (syms_ok H).1 (.cons (.ctor (syms_ok H).2.1 (.cons (.ctor (syms_ok H).2.2.1
    (.cons (.inj (.ctor (abc_ok H hf).1 (.cons (.var rfl) .nil))) (.cons (.var rfl) .nil))) .nil))
    (.cons (.var rfl) .nil))

/-- The left side at the literal n matches `<k> f(n) </k>` at `σn n`. -/
theorem match_lit {f : Sym} (hf : ABC f) (n : Int) :
    PatVal (cH H) (σn n) (lhsOf f (litAs n)) (cfgOf f (int n) dotK cnt0) :=
  .ctor (syms_ok H).1 (.cons (.ctor (syms_ok H).2.1 (.cons (.ctor (syms_ok H).2.2.1
    (.cons (.inj (.ctor (abc_ok H hf).1 (.cons (.as .dv rfl) .nil))) (.cons (.var rfl) .nil))) .nil))
    (.cons (.var rfl) .nil))

/-- The same at `σAt n h`. -/
theorem match_litAt {f : Sym} (hf : ABC f) (n : Int) (h : GroundTerm) :
    PatVal (cH H) (σAt n h) (lhsOf f (litAs n)) (cfgOf f (int n) dotK cnt0) :=
  .ctor (syms_ok H).1 (.cons (.ctor (syms_ok H).2.1 (.cons (.ctor (syms_ok H).2.2.1
    (.cons (.inj (.ctor (abc_ok H hf).1 (.cons (.as .dv rfl) .nil))) (.cons (.var rfl) .nil))) .nil))
    (.cons (.var rfl) .nil))

/-- The right side `<k> f(X) ~> R </k>` at `σn n`. -/
theorem eval_var {f : Sym} (hf : ABC f) (n : Int) :
    EvalTerm (cH H) (σn n) (lhsOf f (.var 0)) (some (cfgOf f (int n) dotK cnt0)) :=
  .ctor (syms_ok H).1 (.cons (.ctor (syms_ok H).2.1 (.cons (.ctor (syms_ok H).2.2.1
    (.cons (.inj (.ctor (abc_ok H hf).1 (.cons .var .nil))) (.cons .var .nil))) .nil)) (.cons .var .nil))

/-- The same at `σAt n h`. -/
theorem eval_varAt {f : Sym} (hf : ABC f) (n : Int) (h : GroundTerm) :
    EvalTerm (cH H) (σAt n h) (lhsOf f (.var 0)) (some (cfgOf f (int n) dotK cnt0)) :=
  .ctor (syms_ok H).1 (.cons (.ctor (syms_ok H).2.1 (.cons (.ctor (syms_ok H).2.2.1
    (.cons (.inj (.ctor (abc_ok H hf).1 (.cons .var .nil))) (.cons .var .nil))) .nil)) (.cons .var .nil))

/-- A configuration of the data under the interpretation H. -/
def X {f : Sym} {n : Int} (hs : c.sortOf (cfgOf f (int n) dotK cnt0) = some topCellSort) : Config (cH H) :=
  ⟨cfgOf f (int n) dotK cnt0, by rw [sortOfH]; exact hs⟩

/-- `<k> a(5) </k>`, `<k> b(5) </k>`, `<k> b(0) </k>`, `<k> c(5) </k>`, `<k> c(1) </k>`, `<k> c(2) </k>`, and the
successors `<k> c(5) </k>`, `<k> c(0) </k>`, `<k> b(5) </k>`, `<k> b(1) </k>`, `<k> b(2) </k>`. -/
def A5 : Config (cH H) := X H (f := symA) (n := 5) (by decide +kernel)
def B5 : Config (cH H) := X H (f := symB) (n := 5) (by decide +kernel)
def B0 : Config (cH H) := X H (f := symB) (n := 0) (by decide +kernel)
def C5 : Config (cH H) := X H (f := symC) (n := 5) (by decide +kernel)
def C1 : Config (cH H) := X H (f := symC) (n := 1) (by decide +kernel)
def C2 : Config (cH H) := X H (f := symC) (n := 2) (by decide +kernel)
def C0 : Config (cH H) := X H (f := symC) (n := 0) (by decide +kernel)
def B1 : Config (cH H) := X H (f := symB) (n := 1) (by decide +kernel)
def B2 : Config (cH H) := X H (f := symB) (n := 2) (by decide +kernel)

omit H in
theorem ne_syms : symA ≠ symB ∧ symA ≠ symC ∧ symB ≠ symC ∧ symB ≠ symA ∧ symC ≠ symA ∧ symC ≠ symB := by
  decide +kernel

theorem mem_r1 : r1 ∈ (cH H).rules := by rw [rulesH]; exact .tail _ (.head _)
theorem mem_r4 : r4 ∈ (cH H).rules := by
  rw [rulesH]; exact .tail _ (.tail _ (.tail _ (.tail _ (.head _))))

/-- At `<k> a(n) </k>` the rule of priority 10 applies, so none of a larger priority number does. -/
theorem blockedA {n : Int} {r : Rule} {τ : Subst} {x y : Config (cH H)} (hx : x.val = cfgOf symA (int n) dotK cnt0)
    (hb : StepBy (cH H) r τ x y) (hp : 10 < r.prio) : False := by
  have hna := hb.hprio r1 (mem_r1 H) (by rw [r1_parts.2.2.2.2.2.2.2]; exact hp) (σn n)
    (fun i _ s hs => σn_sorted H n i s (by rw [← r1_parts.1]; exact hs))
    (by rw [r1_parts.2.1, hx]; exact match_var H abcA n)
  exact not_reqFails r1_parts.2.2.2.1 r1_parts.2.2.2.2.2.1 hna

/-- At `<k> b(0) </k>` the rule `b(0) => c(0)` applies, so the `[owise]` rule does not. -/
theorem blockedB0 {r : Rule} {τ : Subst} {x y : Config (cH H)} (hx : x.val = cfgOf symB (int 0) dotK cnt0)
    (hb : StepBy (cH H) r τ x y) (hp : 50 < r.prio) : False := by
  have hna := hb.hprio r4 (mem_r4 H) (by rw [r4_parts.2.2.2.2.2.2.2]; exact hp) (σn 0)
    (fun i _ s hs => σn_sorted H 0 i s (by rw [← r4_parts.1]; exact hs))
    (by rw [r4_parts.2.1, hx]; exact match_lit H abcB 0)
  exact not_reqFails r4_parts.2.2.2.1 r4_parts.2.2.2.2.2.1 hna

/-- A step by a rule `<k> f(X) => g(X) </k>` from `<k> f(n) </k>` ends at `<k> g(n) </k>`. -/
theorem step_end {f g : Sym} {p : Term} {n : Int} {r : Rule} {τ : Subst} {x y : Config (cH H)}
    (hf : ABC f) (hg : ABC g) (hl : r.lhs = lhsOf f p) (hr : r.rhs = lhsOf g (.var 0))
    (hp : ∀ v, PatVal (cH H) τ p v → τ.lookup 0 = some v)
    (hx : x.val = cfgOf f (int n) dotK cnt0) (hb : StepBy (cH H) r τ x y) : y.val = cfgOf g (int n) dotK cnt0 := by
  have hm := hb.hmatch
  rw [hl, hx] at hm
  obtain ⟨v, w, u, he, hpv, h1, h2⟩ := lhs_inv H hf hm
  obtain ⟨-, rfl, rfl, rfl⟩ := cfgOf_inj he
  have hev := hb.heval
  rw [hr] at hev
  exact rhs_inv H hg hev (hp _ hpv) h1 h2

/-- The no-priority form of the premise: no rule has a priority number below 10. -/
theorem prio_min : ∀ r' ∈ (cH H).rules, ¬ r'.prio < 10 := by
  intro r' hr'
  rw [rulesH] at hr'
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
  rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

/-- The rules of a priority number below 50: the rule of priority 10 only. -/
theorem prio_lt50 : ∀ r' ∈ (cH H).rules, r'.prio < 50 → r' = r1 := by
  intro r' hr' hlt
  rw [rulesH] at hr'
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
  rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | rfl | exact absurd hlt (by decide +kernel)

/-! ## The steps -/

/-- `a(5)` steps to `c(5)` by the rule of priority 10 (sentence 165). -/
theorem stepA5 : StepBy (cH H) r1 (σn 5) (A5 H) (C5 H) where
  mem := mem_r1 H
  hσ := fun j s hs => σn_sorted H 5 j s (by rw [← r1_parts.1]; exact hs)
  hmatch := by rw [r1_parts.2.1]; exact match_var H abcA 5
  hreq := fun t ht => by rw [r1_parts.2.2.2.1] at ht; cases ht
  hpre := by rw [r1_parts.2.2.2.2.2.1]; exact .top
  heval := by rw [r1_parts.2.2.1]; exact eval_var H abcC 5
  hens := fun t ht => by rw [r1_parts.2.2.2.2.1] at ht; cases ht
  hpost := by rw [r1_parts.2.2.2.2.2.2.1]; exact .top
  hprio := fun r' hr' hlt => absurd (by rw [r1_parts.2.2.2.2.2.2.2] at hlt; exact hlt) (prio_min H r' hr')

/-- `b(5)` steps to `c(5)` by the `[owise]` rule (sentence 169): every other rule's left side
fails to match `b(5)`. -/
theorem stepB5 : StepBy (cH H) r5 (σn 5) (B5 H) (C5 H) where
  mem := by rw [rulesH]; exact .tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))
  hσ := fun j s hs => σn_sorted H 5 j s (by rw [← r5_parts.1]; exact hs)
  hmatch := by rw [r5_parts.2.1]; exact match_var H abcB 5
  hreq := fun t ht => by rw [r5_parts.2.2.2.1] at ht; cases ht
  hpre := by rw [r5_parts.2.2.2.2.2.1]; exact .top
  heval := by rw [r5_parts.2.2.1]; exact eval_var H abcC 5
  hens := fun t ht => by rw [r5_parts.2.2.2.2.1] at ht; cases ht
  hpost := by rw [r5_parts.2.2.2.2.2.2.1]; exact .top
  hprio := fun r' hr' _ σ _ hm => by
    exfalso
    rw [rulesH] at hr'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [r0_parts.2.1] at hm; exact mismatch H abcA ne_syms.1 hm
    · rw [r1_parts.2.1] at hm; exact mismatch H abcA ne_syms.1 hm
    · rw [r2_parts.1] at hm; exact mismatch H abcA ne_syms.1 hm
    · rw [r3_parts.1] at hm; exact mismatch H abcA ne_syms.1 hm
    · rw [r4_parts.2.1] at hm; exact mismatch_lit H abcB (by decide) hm
    · exact absurd ‹r5.prio < r5.prio› (Nat.lt_irrefl _)
    · rw [r6_parts.2.1] at hm; exact mismatch H abcC ne_syms.2.2.2.2.2 hm
    · rw [r7_parts.2.1] at hm; exact mismatch H abcC ne_syms.2.2.2.2.2 hm
    · rw [r8_parts.2.1] at hm; exact mismatch H abcC ne_syms.2.2.2.2.2 hm

/-- The premise of a rule of priority 50 at `<k> g(n) </k>`, g not `a`: the rule of priority 10
does not match. -/
theorem prio50 {g : Sym} (hg : g ≠ symA) (v w u : GroundTerm) :
    ∀ r' ∈ (cH H).rules, r'.prio < 50 → NotApplies (cH H) r' (cfgOf g v w u) := by
  intro r' hr' hlt σ _ hm
  obtain rfl := prio_lt50 H r' hr' hlt
  rw [r1_parts.2.1] at hm
  exact absurd (mismatch H abcA (Ne.symm hg) hm) id

/-- `b(0)` steps to `c(0)` by `b(0) => c(0)` (sentence 168). -/
theorem stepB0 : StepBy (cH H) r4 (σn 0) (B0 H) (C0 H) where
  mem := mem_r4 H
  hσ := fun j s hs => σn_sorted H 0 j s (by rw [← r4_parts.1]; exact hs)
  hmatch := by rw [r4_parts.2.1]; exact match_lit H abcB 0
  hreq := fun t ht => by rw [r4_parts.2.2.2.1] at ht; cases ht
  hpre := by rw [r4_parts.2.2.2.2.2.1]; exact .top
  heval := by rw [r4_parts.2.2.1]; exact eval_var H abcC 0
  hens := fun t ht => by rw [r4_parts.2.2.2.2.1] at ht; cases ht
  hpost := by rw [r4_parts.2.2.2.2.2.2.1]; exact .top
  hprio := by rw [r4_parts.2.2.2.2.2.2.2]; exact prio50 H ne_syms.2.2.2.1 _ _ _

/-- `c(5)` steps to `b(5)` by the rule with `preserves-definedness` and the label `r2` (sentence 172). -/
theorem stepC5 : StepBy (cH H) r8 (σn 5) (C5 H) (B5 H) where
  mem := by rw [rulesH]; exact .tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))))
  hσ := fun j s hs => σn_sorted H 5 j s (by rw [← r8_parts.1]; exact hs)
  hmatch := by rw [r8_parts.2.1]; exact match_var H abcC 5
  hreq := fun t ht => by rw [r8_parts.2.2.2.1] at ht; cases ht
  hpre := by rw [r8_parts.2.2.2.2.2.1]; exact .top
  heval := by rw [r8_parts.2.2.1]; exact eval_var H abcB 5
  hens := fun t ht => by rw [r8_parts.2.2.2.2.1] at ht; cases ht
  hpost := by rw [r8_parts.2.2.2.2.2.2.1]; exact .top
  hprio := by rw [r8_parts.2.2.2.2.2.2.2]; exact prio50 H ne_syms.2.2.2.2.1 _ _ _

/-- `c(1)` steps to `b(1)` by the `[cool]` rule (sentence 170), HOLE := `holeCool`. -/
theorem stepC1 : StepBy (cH H) r6 (σAt 1 holeCool) (C1 H) (B1 H) where
  mem := by rw [rulesH]; exact .tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))
  hσ := fun j s hs => σAt_sorted H base_sorts.1 j s (by rw [← r6_parts.1]; exact hs)
  hmatch := by rw [r6_parts.2.1]; exact match_litAt H abcC 1 holeCool
  hreq := fun t ht => by rw [r6_parts.2.2.2.1] at ht; cases ht; exact reqCool H
  hpre := by rw [r6_parts.2.2.2.2.2.1]; exact .top
  heval := by rw [r6_parts.2.2.1]; exact eval_varAt H abcB 1 holeCool
  hens := fun t ht => by rw [r6_parts.2.2.2.2.1] at ht; cases ht
  hpost := by rw [r6_parts.2.2.2.2.2.2.1]; exact .top
  hprio := by rw [r6_parts.2.2.2.2.2.2.2]; exact prio50 H ne_syms.2.2.2.2.1 _ _ _

/-- `c(2)` steps to `b(2)` by the `[heat]` rule (sentence 171), HOLE := `holeHeat`. -/
theorem stepC2 : StepBy (cH H) r7 (σAt 2 holeHeat) (C2 H) (B2 H) where
  mem := by rw [rulesH]; exact .tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))))
  hσ := fun j s hs => σAt_sorted H base_sorts.2.1 j s (by rw [← r7_parts.1]; exact hs)
  hmatch := by rw [r7_parts.2.1]; exact match_litAt H abcC 2 holeHeat
  hreq := fun t ht => by rw [r7_parts.2.2.2.1] at ht; cases ht; exact reqHeat H
  hpre := by rw [r7_parts.2.2.2.2.2.1]; exact .top
  heval := by rw [r7_parts.2.2.1]; exact eval_varAt H abcB 2 holeHeat
  hens := fun t ht => by rw [r7_parts.2.2.2.2.1] at ht; cases ht
  hpost := by rw [r7_parts.2.2.2.2.2.2.1]; exact .top
  hprio := by rw [r7_parts.2.2.2.2.2.2.2]; exact prio50 H ne_syms.2.2.2.2.1 _ _ _

/-- **In every model of `Γc`, a step by a rule without existential variables is a successor**,
for every H: the pinned `sound_at` (every competitor that needs a witness is `Witnessed`,
`openDecidedH`) and `famEx_closed`. -/
theorem sound_of {x y : Config (cH H)} {r : Rule} {σ : Subst} (hb : StepBy (cH H) r σ x y) (hex : r.exs = []) :
    Γc (cH H) ⊧ (den (cH H) x.val ⇒ KoreAML.sNext (den (cH H) y.val)) := by
  have hc := (openDecidedH H).2
  obtain ⟨h1, -⟩ := sound_at (cH H) (coreOKH H) x y r σ hb (fun r' hr' _ hw _ => (openDecidedH H).1 r' hr' hw) hc
  have hcl : Γc (cH H) ⊧ (famEx (cH H) r σ ≡ den (cH H) y.val) := famEx_closed (cH H) (coreOKH H) hb hex hc
  intro M _ I hI e m
  have hst := h1 hI e m
  rw [interpret_impl] at hst ⊢
  intro hx
  exact sNext_congr ((KoreAML.interp_equal (defOK fun φ hφ => hI φ (Or.inl hφ))).mp (hcl hI e m)) (hst hx)

/-! ## The inversions: every successor -/

theorem mem_rules {r : Rule} (hr : r ∈ (cH H).rules) :
    r = r0 ∨ r = r1 ∨ r = r2 ∨ r = r3 ∨ r = r4 ∨ r = r5 ∨ r = r6 ∨ r = r7 ∨ r = r8 := by
  rw [rulesH] at hr
  simpa only [List.mem_cons, List.not_mem_nil, or_false] using hr

/-- **Every successor of `a(5)` is `c(5)`**: the rules at `b` and `c` do not match; of the four at
`a`, the one of priority 10 gives `c(5)` and blocks the others. -/
theorem succ_A5 {y : Config (cH H)} (hs : Step (cH H) (A5 H) y) : y = C5 H := by
  obtain ⟨r, τ, hb⟩ := step_iff_by.mp hs
  have hx : (A5 H).val = cfgOf symA (int 5) dotK cnt0 := rfl
  have hm := hb.hmatch
  rcases mem_rules H hb.mem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd (blockedA H hx hb (by rw [r0_parts.2.2.2.2]; decide)) id
  · exact Subtype.ext (step_end H abcA abcC r1_parts.2.1 r1_parts.2.2.1 (fun _ h => PatVal.var_inv h) hx hb)
  · exact absurd (blockedA H hx hb (by rw [r2_parts.2]; decide)) id
  · exact absurd (blockedA H hx hb (by rw [r3_parts.2]; decide)) id
  · rw [r4_parts.2.1] at hm; exact absurd (mismatch H abcB ne_syms.2.2.2.1 hm) id
  · rw [r5_parts.2.1] at hm; exact absurd (mismatch H abcB ne_syms.2.2.2.1 hm) id
  · rw [r6_parts.2.1] at hm; exact absurd (mismatch H abcC ne_syms.2.2.2.2.1 hm) id
  · rw [r7_parts.2.1] at hm; exact absurd (mismatch H abcC ne_syms.2.2.2.2.1 hm) id
  · rw [r8_parts.2.1] at hm; exact absurd (mismatch H abcC ne_syms.2.2.2.2.1 hm) id

/-- **Every successor of `b(5)` is `c(5)`**, by the `[owise]` rule: `b(0) => c(0)` does not match. -/
theorem succ_B5 {y : Config (cH H)} (hs : Step (cH H) (B5 H) y) : y = C5 H := by
  obtain ⟨r, τ, hb⟩ := step_iff_by.mp hs
  have hx : (B5 H).val = cfgOf symB (int 5) dotK cnt0 := rfl
  have hm := hb.hmatch
  rcases mem_rules H hb.mem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [r0_parts.2.1] at hm; exact absurd (mismatch H abcA ne_syms.1 hm) id
  · rw [r1_parts.2.1] at hm; exact absurd (mismatch H abcA ne_syms.1 hm) id
  · rw [r2_parts.1] at hm; exact absurd (mismatch H abcA ne_syms.1 hm) id
  · rw [r3_parts.1] at hm; exact absurd (mismatch H abcA ne_syms.1 hm) id
  · rw [r4_parts.2.1] at hm; exact absurd (mismatch_lit H abcB (by decide) hm) id
  · exact Subtype.ext (step_end H abcB abcC r5_parts.2.1 r5_parts.2.2.1 (fun _ h => PatVal.var_inv h) hx hb)
  · rw [r6_parts.2.1] at hm; exact absurd (mismatch H abcC ne_syms.2.2.2.2.2 hm) id
  · rw [r7_parts.2.1] at hm; exact absurd (mismatch H abcC ne_syms.2.2.2.2.2 hm) id
  · rw [r8_parts.2.1] at hm; exact absurd (mismatch H abcC ne_syms.2.2.2.2.2 hm) id

/-- **Every successor of `b(0)` is `c(0)`**: `b(0) => c(0)` gives it and blocks the `[owise]` rule. -/
theorem succ_B0 {y : Config (cH H)} (hs : Step (cH H) (B0 H) y) : y = C0 H := by
  obtain ⟨r, τ, hb⟩ := step_iff_by.mp hs
  have hx : (B0 H).val = cfgOf symB (int 0) dotK cnt0 := rfl
  have hm := hb.hmatch
  rcases mem_rules H hb.mem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [r0_parts.2.1] at hm; exact absurd (mismatch H abcA ne_syms.1 hm) id
  · rw [r1_parts.2.1] at hm; exact absurd (mismatch H abcA ne_syms.1 hm) id
  · rw [r2_parts.1] at hm; exact absurd (mismatch H abcA ne_syms.1 hm) id
  · rw [r3_parts.1] at hm; exact absurd (mismatch H abcA ne_syms.1 hm) id
  · exact Subtype.ext (step_end H abcB abcC r4_parts.2.1 r4_parts.2.2.1 (fun _ h => (PatVal.as_inv h).2) hx hb)
  · exact absurd (blockedB0 H hx hb (by rw [r5_parts.2.2.2.2.2.2.2]; decide)) id
  · rw [r6_parts.2.1] at hm; exact absurd (mismatch H abcC ne_syms.2.2.2.2.2 hm) id
  · rw [r7_parts.2.1] at hm; exact absurd (mismatch H abcC ne_syms.2.2.2.2.2 hm) id
  · rw [r8_parts.2.1] at hm; exact absurd (mismatch H abcC ne_syms.2.2.2.2.2 hm) id

/-- **Every successor of `c(5)` is `b(5)`**: the `[cool]` and `[heat]` rules match `c(1)` and
`c(2)` only. -/
theorem succ_C5 {y : Config (cH H)} (hs : Step (cH H) (C5 H) y) : y = B5 H := by
  obtain ⟨r, τ, hb⟩ := step_iff_by.mp hs
  have hx : (C5 H).val = cfgOf symC (int 5) dotK cnt0 := rfl
  have hm := hb.hmatch
  rcases mem_rules H hb.mem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [r0_parts.2.1] at hm; exact absurd (mismatch H abcA ne_syms.2.1 hm) id
  · rw [r1_parts.2.1] at hm; exact absurd (mismatch H abcA ne_syms.2.1 hm) id
  · rw [r2_parts.1] at hm; exact absurd (mismatch H abcA ne_syms.2.1 hm) id
  · rw [r3_parts.1] at hm; exact absurd (mismatch H abcA ne_syms.2.1 hm) id
  · rw [r4_parts.2.1] at hm; exact absurd (mismatch H abcB ne_syms.2.2.1 hm) id
  · rw [r5_parts.2.1] at hm; exact absurd (mismatch H abcB ne_syms.2.2.1 hm) id
  · rw [r6_parts.2.1] at hm; exact absurd (mismatch_lit H abcC (by decide) hm) id
  · rw [r7_parts.2.1] at hm; exact absurd (mismatch_lit H abcC (by decide) hm) id
  · exact Subtype.ext (step_end H abcC abcB r8_parts.2.1 r8_parts.2.2.1 (fun _ h => PatVal.var_inv h) hx hb)

/-- The rules with an open variable, the `[cool]` and `[heat]` rules, have their left side at `c(1)`
and `c(2)`: where neither matches, no outcome is a family. -/
theorem fam_none {x : Config (cH H)} (h6 : ∀ σ, ¬ PatVal (cH H) σ r6.lhs x.val) (h7 : ∀ σ, ¬ PatVal (cH H) σ r7.lhs x.val) :
    ∀ r ∈ (cH H).rules, r.opens ≠ [] → ∀ σ, Unblocked (cH H) r σ x.val → False := by
  intro r hr hne σ hu
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, h0, h1, h2, h3, h4, h5, h8⟩ := witness_rules
  rcases mem_rules H hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hne h0
  · exact hne h1
  · exact hne h2
  · exact hne h3
  · exact hne h4
  · exact hne h5
  · exact h6 σ hu.2.1
  · exact h7 σ hu.2.1
  · exact hne h8

/-- **Completeness at a configuration where neither rule with an open variable matches**: with the
step's closure, every successor is one of `ys`, where every `Step` successor is. -/
theorem complete_of {x : Config (cH H)} (h6 : ∀ σ, ¬ PatVal (cH H) σ r6.lhs x.val)
    (h7 : ∀ σ, ¬ PatVal (cH H) σ r7.lhs x.val) (ys : List GroundTerm) (hys : ∀ y, Step (cH H) x y → y.val ∈ ys) :
    (Γc (cH H) ∪ Γstep (cH H)) ⊧ (den (cH H) x.val ⇒ KoreAML.allNext (KoreAML.disjList (ys.map (den (cH H))))) := by
  have hm : (ys.map Outcome.val).map (Outcome.pat (cH H)) = ys.map (den (cH H)) := by rw [List.map_map]; rfl
  rw [← hm]
  intro M _ I hI
  exact complete_at (cH H) (coreOKH H) x (stepDecided_of_fnHyp (coreOKH H) (fnHypH H) x) (ys.map Outcome.val)
    (fun y r σ _ hs => List.mem_map_of_mem (hys y (step_iff_by.mpr ⟨r, σ, hs⟩)))
    (fun r hr hne σ hu => absurd (fam_none H h6 h7 r hr hne σ hu) id) (openDecidedH H).2 hI

theorem nomatch_cool {g : Sym} {n : Int} (hg : g ≠ symC ∨ n ≠ 1) (σ : Subst) :
    ¬ PatVal (cH H) σ r6.lhs (cfgOf g (int n) dotK cnt0) := fun hm => by
  rw [r6_parts.2.1] at hm
  rcases hg with hg | hn
  · exact mismatch H abcC (Ne.symm hg) hm
  · obtain ⟨v, _, _, hx, hp, -⟩ := lhs_inv H abcC hm
    obtain ⟨-, rfl, -, -⟩ := cfgOf_inj hx
    have := PatVal.dv_inv (PatVal.as_inv hp).1
    simp only [int, GroundTerm.dv.injEq, Lit.int.injEq, true_and] at this
    exact hn this
theorem nomatch_heat {g : Sym} {n : Int} (hg : g ≠ symC ∨ n ≠ 2) (σ : Subst) :
    ¬ PatVal (cH H) σ r7.lhs (cfgOf g (int n) dotK cnt0) := fun hm => by
  rw [r7_parts.2.1] at hm
  rcases hg with hg | hn
  · exact mismatch H abcC (Ne.symm hg) hm
  · obtain ⟨v, _, _, hx, hp, -⟩ := lhs_inv H abcC hm
    obtain ⟨-, rfl, -, -⟩ := cfgOf_inj hx
    have := PatVal.dv_inv (PatVal.as_inv hp).1
    simp only [int, GroundTerm.dv.injEq, Lit.int.injEq, true_and] at this
    exact hn this

end Steps

/-! ## The fixture's expectations (C7 form (a)) -/

/-- **`a(5)` steps to `c(5)`, from the sentence of the rule of priority 10** (165), for every H:
derived from `Pre` (Γ's item of the sentence by W1, `rules_from_text`). -/
theorem a5_step (H : HookParams) : Pre H ⊧ (den (cH H) (A5 H).val ⇒ KoreAML.sNext (den (cH H) (C5 H).val)) :=
  cutC H (sound_of H (stepA5 H) r_exs.1)

/-- **`c(5)` is `a(5)`'s only successor**, for every H: the rule of priority 10 blocks the labelled
rule `r-label` (164) and those of priorities 50 and 60 (166, 167). From `Pre` with the step's closure. -/
theorem a5_succs (H : HookParams) :
    (Pre H ∪ Γstep (cH H)) ⊧ (den (cH H) (A5 H).val ⇒
      KoreAML.allNext (KoreAML.disjList (([(C5 H).val] : List GroundTerm).map (den (cH H))))) :=
  cutStep H (complete_of H (nomatch_cool H (.inl ne_syms.2.1)) (nomatch_heat H (.inl ne_syms.2.1)) _
    fun y hs => by rw [succ_A5 H hs]; exact List.mem_singleton_self _)

/-- **`b(5)` steps to `c(5)`, from the sentence of the `[owise]` rule** (169), for every H. -/
theorem b5_step (H : HookParams) : Pre H ⊧ (den (cH H) (B5 H).val ⇒ KoreAML.sNext (den (cH H) (C5 H).val)) :=
  cutC H (sound_of H (stepB5 H) r_exs.2.2.1)

/-- **`c(5)` is `b(5)`'s only successor**, for every H (the `[owise]` rule; `b(0) => c(0)` does not
match). -/
theorem b5_succs (H : HookParams) :
    (Pre H ∪ Γstep (cH H)) ⊧ (den (cH H) (B5 H).val ⇒
      KoreAML.allNext (KoreAML.disjList (([(C5 H).val] : List GroundTerm).map (den (cH H))))) :=
  cutStep H (complete_of H (nomatch_cool H (.inl ne_syms.2.2.1)) (nomatch_heat H (.inl ne_syms.2.2.1)) _
    fun y hs => by rw [succ_B5 H hs]; exact List.mem_singleton_self _)

/-- **`b(0)` steps to `c(0)`, from the sentence `b(0) => c(0)`** (168), for every H. -/
theorem b0_step (H : HookParams) : Pre H ⊧ (den (cH H) (B0 H).val ⇒ KoreAML.sNext (den (cH H) (C0 H).val)) :=
  cutC H (sound_of H (stepB0 H) r_exs.2.1)

/-- **`c(0)` is `b(0)`'s only successor**, for every H: `b(0) => c(0)` blocks the `[owise]` rule. -/
theorem b0_succs (H : HookParams) :
    (Pre H ∪ Γstep (cH H)) ⊧ (den (cH H) (B0 H).val ⇒
      KoreAML.allNext (KoreAML.disjList (([(C0 H).val] : List GroundTerm).map (den (cH H))))) :=
  cutStep H (complete_of H (nomatch_cool H (.inl ne_syms.2.2.1)) (nomatch_heat H (.inl ne_syms.2.2.1)) _
    fun y hs => by rw [succ_B0 H hs]; exact List.mem_singleton_self _)

/-- **`c(5)` steps to `b(5)`, from the sentence of the rule with `preserves-definedness` and the
label `r2`** (172), for every H. -/
theorem c5_step (H : HookParams) : Pre H ⊧ (den (cH H) (C5 H).val ⇒ KoreAML.sNext (den (cH H) (B5 H).val)) :=
  cutC H (sound_of H (stepC5 H) r_exs.2.2.2.2.2)

/-- **`b(5)` is `c(5)`'s only successor**, for every H: the `[cool]` and `[heat]` rules do not match. -/
theorem c5_succs (H : HookParams) :
    (Pre H ∪ Γstep (cH H)) ⊧ (den (cH H) (C5 H).val ⇒
      KoreAML.allNext (KoreAML.disjList (([(B5 H).val] : List GroundTerm).map (den (cH H))))) :=
  cutStep H (complete_of H (nomatch_cool H (.inr (by decide))) (nomatch_heat H (.inr (by decide))) _
    fun y hs => by rw [succ_C5 H hs]; exact List.mem_singleton_self _)

/-- **`c(1)` steps to `b(1)`, from the sentence of the `[cool]` rule** (170), for every H: its
`requires` `true andBool isKResult(HOLE)` holds at HOLE := `kseq(inj{Int,KItem}(0), dotk)`. -/
theorem c1_step (H : HookParams) : Pre H ⊧ (den (cH H) (C1 H).val ⇒ KoreAML.sNext (den (cH H) (B1 H).val)) :=
  cutC H (sound_of H (stepC1 H) r_exs.2.2.2.1)

/-- **`c(2)` steps to `b(2)`, from the sentence of the `[heat]` rule** (171), for every H: its
`requires` `true andBool notBool isKResult(HOLE)` holds at HOLE := `dotk`. -/
theorem c2_step (H : HookParams) : Pre H ⊧ (den (cH H) (C2 H).val ⇒ KoreAML.sNext (den (cH H) (B2 H).val)) :=
  cutC H (sound_of H (stepC2 H) r_exs.2.2.2.2.1)

end KCore.TieRuleCool

#print axioms KCore.TieRuleCool.shape
#print axioms KCore.TieRuleCool.rules_tie
#print axioms KCore.TieRuleCool.rules_from_text
#print axioms KCore.TieRuleCool.witnessed6H
#print axioms KCore.TieRuleCool.witnessed7H
#print axioms KCore.TieRuleCool.fnHypH
#print axioms KCore.TieRuleCool.consistent
#print axioms KCore.TieRuleCool.gamma_from
#print axioms KCore.TieRuleCool.pre_model
#print axioms KCore.TieRuleCool.a5_step
#print axioms KCore.TieRuleCool.a5_succs
#print axioms KCore.TieRuleCool.b5_step
#print axioms KCore.TieRuleCool.b5_succs
#print axioms KCore.TieRuleCool.b0_step
#print axioms KCore.TieRuleCool.b0_succs
#print axioms KCore.TieRuleCool.c5_step
#print axioms KCore.TieRuleCool.c5_succs
#print axioms KCore.TieRuleCool.c1_step
#print axioms KCore.TieRuleCool.c2_step
