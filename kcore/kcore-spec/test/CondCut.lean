/-
  Two readings of a rule's or an equation's condition `\equals{SortBool{},S}(B, true)`, on K 7.1.337
  kompile's KORE of the construct fixtures (test/constructs/fixtures). Run from the package root:
  `lake env lean -j1 test/CondCut.lean`.

  - `notAsCondition` (`Parse.notCondTerm?`, `Parse.condCuts`): B is `\not{SortBool{}}(B')`, B' a
    Bool term. `\not{SortBool{}}(B')` is the complement of B' in the elements of Bool, which are its
    two literals where the text gives Bool no element of its own; the complement is `{true}` exactly
    where B' is `{false}`. Read as no `requires` and the condition `B' = false` (`Cond.equals`), in
    a rule's `pre` and an equation's `Clause.pre`. A text that gives Bool a constructor of its own
    is refused `openExtent` (Bool). A `\not` that is one conjunct of several is refused: there
    `\and{SortBool{}}(true, \not(B'))` holds where B' has no element, and `B' = false` does not.
  - `andUnderAppCut` (`Parse.condAndCutT`): a conjunct of B holds, under applications, a
    conjunction `t₁ ∧ … ∧ tₙ` of `singleValued` terms. Each has at most one element, so the
    conjunction is t₁ where every `t₁ ∈ tⱼ` holds and nothing elsewhere, where the application, and
    B with it, is nothing. Read with t₁ in the conjunction's place and the memberships `t₁ ∈ tⱼ`
    (`Cond.mem`) beside it. A conjunction one of whose conjuncts is no `singleValued` term (a
    conjunction among them) is refused `patternConnective` (`\and`).

  The texts (f2-examples, from the fixtures of the same name):
  - `mlreqnot` (e3-ml-req-not): `go(X) => done requires #Not(X >Int 0)`.
  - `mleqreqnot` (e3-ml-eq-req-not): `f(X) => 1 requires #Not(X >Int 0)`, `f(_) => 0 [owise]`.
  - `mlreqandapp` (e3-ml-req-and-under-app): `go(X, Y) => done requires f(X #And Y) ==Int 0`,
    `f(X) => X -Int 1`.
  - `mleqreqandapp` (e3-ml-eq-req-and-under-app): `g(X, Y) => 1 requires f(X #And Y) ==Int 0`,
    `g(_, _) => 0 [owise]`, f as above.

  Kernel-checked, at the parsed semantics:
  - `ReqNot.step_iff`: for every integer i, `<k> go(i) </k>` steps to `<k> done </k>` exactly where
    i ≤ 0, and `ReqNot.step_le`: it has no successor where i > 0. (Under every interpretation at
    three points: test/Guards.lean `DevNotCond`.)
  - `ReqAndApp`: `go(1, 1)` steps to `done`; `go(1, 2)`, `go(2, 2)` and `go(0, 0)` have no
    successor: the rule applies exactly where X = Y and f(X) = 0.

  The same, for every interpretation H, at `c.withHooks H` (the expectations through the reading):
  `ReqNot.step_iffH`, `ReqNot.stuckH`; `ReqAndApp.step_go11H`, `ReqAndApp.stuckH`. Neither reading
  has a parameter: the rule, the sorts of values and the graphs of the registry's hooks it calls are
  the same under every H, and `ReqAndApp.coherentH` gives evaluation one result under every H.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

open KCore

namespace CondCut

/-- The reader's verdict on the text at `path`, edited by `edit`: read, with `coreOK` and the notes
of the user module's sentences read through one, or the refusal. -/
def verdict (path : String) (edit : String → String := id) : IO String := do
  match Kore.parseDefinition (edit (← IO.FS.readFile path)) with
  | .error e => return s!"KORE read error {e}"
  | .ok k => match Parse.parse k with
    | .error r => return s!"{r.reason.name} {r.detail}"
    | .ok d =>
      let N := Parse.namesOf k
      let notes := (k.modules.getLast?.toList.flatMap (·.sentences)).filterMap fun s => match s with
        | .axiom a => let ns := Parse.connNotes N a; if ns.isEmpty then none else some (ns.map (·.name))
        | _ => none
      return s!"read; unaccounted {(Parse.unconsumed k d).length}; coreOK {d.sem.coreOK}; notes {notes}"

/-- The rule's `requires` of `mlreqnot`, as kompile writes it. -/
def notReq : String :=
  "\\not{SortBool{}}(Lbl'Unds-GT-'Int'Unds'{}(VarX:SortInt{},\\dv{SortInt{}}(\"0\")))"

/-- The conjunction of `mlreqandapp`'s `requires`, as kompile writes it. -/
def andArg : String := "\\and{SortInt{}}(VarX:SortInt{},VarY:SortInt{})"

/-- notAsCondition and andUnderAppCut: the four texts read, each with its note; Bool given a
constructor of the text's own; the `\not` one conjunct of two; a conjunction among the conjuncts of
a conjunction under an application. -/
def verdicts : IO Unit := do
  IO.println (← verdict "f2-examples/mlreqnot.kompile.kore")
  IO.println (← verdict "f2-examples/mleqreqnot.kompile.kore")
  IO.println (← verdict "f2-examples/mlreqandapp.kompile.kore")
  IO.println (← verdict "f2-examples/mleqreqandapp.kompile.kore")
  IO.println (← verdict "f2-examples/mlreqnot.kompile.kore" fun s =>
    s.replace "  sort SortExp{} []"
      "  sort SortExp{} []\n  symbol Lblmaybe{}() : SortBool{} [constructor{}(), functional{}(), injective{}()]")
  IO.println (← verdict "f2-examples/mlreqnot.kompile.kore" fun s =>
    s.replace notReq s!"\\and\{SortBool\{}}(\\dv\{SortBool\{}}(\"true\"), {notReq})")
  IO.println (← verdict "f2-examples/mlreqandapp.kompile.kore" fun s =>
    s.replace andArg "\\and{SortInt{}}(VarX:SortInt{},\\and{SortInt{}}(VarY:SortInt{},VarX:SortInt{}))")

/--
info: read; unaccounted 0; coreOK true; notes [[notAsCondition]]
read; unaccounted 0; coreOK true; notes [[notAsCondition]]
read; unaccounted 0; coreOK true; notes [[andUnderAppCut]]
read; unaccounted 0; coreOK true; notes [[andUnderAppCut]]
openExtent Bool
patternConnective \not
patternConnective \and
-/
#guard_msgs in
#eval verdicts

/-! ## Inversions and configurations -/

theorem holds_equals_inv {c : Semantics} {n : Nat} {σ : Subst} {s : Srt} {t u : Term} {b : Bool}
    (h : Holds c n σ (.equals s t u) b) :
    ∃ r r', EvalTerm c σ t r ∧ EvalTerm c σ u r' ∧ b = sameResult r r' := by
  generalize hq : Cond.equals s t u = q at h
  cases h with
  | equals h h' => cases hq; exact ⟨_, _, h, h', rfl⟩
  | _ => cases hq

/-- `sameResult` of two results is their equality. -/
theorem sameResult_some {v w : GroundTerm} : sameResult (some v) (some w) = decide (v = w) := by
  unfold sameResult
  by_cases h : v = w
  · subst h; simp [cmp_eq_iff]
  · simp [cmp_eq_iff, h]

theorem patVal_ctor2 {c : Semantics} {σ : Subst} {f : Sym} {p q : Term} {v w : GroundTerm}
    (hf : patternHooks.contains f = false) (hc : c.isCtor f = true)
    (h : PatVal c σ (.app f [p, q]) (.ctor f [v, w])) : PatVal c σ p v ∧ PatVal c σ q w := by
  obtain ⟨-, vs, he, hs⟩ := PatVal.app_inv hf h hc
  cases he
  obtain ⟨_, _, he1, h1, hs1⟩ := PatVals.cons_inv hs
  cases he1
  obtain ⟨_, _, he2, h2, _⟩ := PatVals.cons_inv hs1
  cases he2
  exact ⟨h1, h2⟩

theorem patVal_ctor1 {c : Semantics} {σ : Subst} {f : Sym} {p : Term} {v : GroundTerm}
    (hf : patternHooks.contains f = false) (hc : c.isCtor f = true)
    (h : PatVal c σ (.app f [p]) (.ctor f [v])) : PatVal c σ p v := by
  obtain ⟨-, vs, he, hs⟩ := PatVal.app_inv hf h hc
  cases he
  obtain ⟨_, _, he1, h1, _⟩ := PatVals.cons_inv hs
  cases he1
  exact h1

/-- An Int literal, as a value. -/
def iv (i : Int) : GroundTerm := .dv Srt.int (.int i)

/-- The configuration `<generatedTop>(<k>(kseq(inj{s,KItem}(st), dotk)), <generatedCounter>(0))`,
the k cell's symbol `kCell`. -/
def cfgOf (kCell : Sym) (s : Srt) (st : GroundTerm) : GroundTerm :=
  .ctor topLabel [.ctor kCell [.ctor kseq [.inj s Srt.kitem st, .ctor dotk []]], .ctor counterLabel [iv 0]]

/-- The configuration pattern `<generatedTop>(<k>(kseq(inj{s,KItem}(p), Vk)), Vc)`. -/
def cfgPat (kCell : Sym) (s : Srt) (p : Term) (k c : Nat) : Term :=
  .app topLabel [.app kCell [.app kseq [.inj s Srt.kitem p, .var k]], .var c]

theorem sortOf_ctor_congr {c : Semantics} {f : Sym} {ts ts0 : List GroundTerm}
    (hl : (lookupSig c.ctorSigs f).isSome = true)
    (h : c.sortsOf ts = c.sortsOf ts0) : c.sortOf (.ctor f ts) = c.sortOf (.ctor f ts0) := by
  obtain ⟨k, hk⟩ := Option.isSome_iff_exists.mp hl
  simp only [Semantics.sortOf, hk, h]

theorem sortsOf_head_congr {c : Semantics} {t t0 : GroundTerm} {ts : List GroundTerm}
    (h : c.sortOf t = c.sortOf t0) : c.sortsOf (t :: ts) = c.sortsOf (t0 :: ts) := by
  simp only [Semantics.sortsOf, h]

theorem sortOf_inj_congr {c : Semantics} {a b : Srt} {t t0 : GroundTerm} (h : c.sortOf t = c.sortOf t0)
    (hi : t.isInj = t0.isInj) : c.sortOf (.inj a b t) = c.sortOf (.inj a b t0) := by
  simp only [Semantics.sortOf, h, hi]

theorem sortOf_cfgOf_congr {c : Semantics} {kCell : Sym} {s : Srt} {st st0 : GroundTerm}
    (hl : (lookupSig c.ctorSigs topLabel).isSome = true ∧ (lookupSig c.ctorSigs kCell).isSome = true ∧
      (lookupSig c.ctorSigs kseq).isSome = true)
    (h : c.sortOf st = c.sortOf st0) (hi : st.isInj = st0.isInj) :
    c.sortOf (cfgOf kCell s st) = c.sortOf (cfgOf kCell s st0) :=
  sortOf_ctor_congr hl.1 (sortsOf_head_congr (sortOf_ctor_congr hl.2.1 (sortsOf_head_congr
    (sortOf_ctor_congr hl.2.2 (sortsOf_head_congr (sortOf_inj_congr h hi))))))

/-! ## `notAsCondition`: `go(X) => done requires #Not(X >Int 0)` -/

namespace ReqNot

definition_of defn from "f2-examples/mlreqnot.kompile.kore"
noncomputable abbrev c : Semantics := defn.sem

def exp : Srt := 32
def kCell : Sym := 383
def symDone : Sym := 385
def symGo : Sym := 386

theorem names_ok : c.sortName exp = "Exp" ∧ c.symName kCell = "Lbl'-LT-'k'-GT-'" ∧
    c.symName symDone = "Lbldone" ∧ c.symName symGo = "Lblgo" ∧ c.symName intGt = "Lbl'Unds-GT-'Int'Unds'" := by
  decide +kernel

theorem coreOK : c.coreOK = true := by decide +kernel
theorem prios : c.rules.length = 1 := by decide +kernel

/-- The reading has no open variable and no binder, so the definition reads no confined sort and
its theory `Γc` is `Γ`, without `boolClosed`. -/
theorem readsConfined_false : c.readsConfined = false := by decide +kernel

noncomputable def r0 : Rule := c.rules[0]'(by decide +kernel)
theorem r0_mem : r0 ∈ c.rules := List.getElem_mem _
theorem rule_eq {r : Rule} (hr : r ∈ c.rules) : r = r0 := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hr
  have : i = 0 := by have := prios; omega
  subst this
  rfl

/-- The rule as read: no `requires`, and `pre` the condition `X >Int 0 = false`. -/
theorem r0_vars : r0.vars = [Srt.int, Srt.k, 19] := by decide +kernel
theorem r0_lhs : r0.lhs = cfgPat kCell exp (.app symGo [.var 0]) 1 2 := rfl
theorem r0_rhs : r0.rhs = cfgPat kCell exp (.app symDone []) 1 2 := rfl
theorem r0_shape : r0.req = none ∧ r0.ens = none ∧ r0.post = .top ∧
    r0.pre = .equals Srt.bool (.app intGt [.var 0, .dv Srt.int (.int 0)]) (.dv Srt.bool (.bool false)) :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem syms_ok : c.isCtor topLabel = true ∧ c.isCtor kCell = true ∧ c.isCtor kseq = true ∧
    c.isCtor symGo = true ∧ c.isCtor symDone = true := by
  decide +kernel
theorem hooks_ok : patternHooks.contains topLabel = false ∧ patternHooks.contains kCell = false ∧
    patternHooks.contains kseq = false ∧ patternHooks.contains symGo = false := by
  decide +kernel
theorem kinds : isHook intGt = true ∧ c.isCtor intGt = false ∧ c.isOvl intGt = false := by
  decide +kernel
theorem lookups_ok : (lookupSig c.ctorSigs topLabel).isSome = true ∧ (lookupSig c.ctorSigs kCell).isSome = true ∧
    (lookupSig c.ctorSigs kseq).isSome = true ∧ (lookupSig c.ctorSigs symGo).isSome = true := by
  decide +kernel

def ctr : GroundTerm := .ctor counterLabel [iv 0]
def cfg (st : GroundTerm) : GroundTerm := cfgOf kCell exp st

theorem sortOf_go (i : Int) : c.sortOf (cfg (.ctor symGo [iv i])) = some topCellSort := by
  have h0 : c.sortOf (cfg (.ctor symGo [iv 0])) = some topCellSort := by decide +kernel
  rw [← h0]
  exact sortOf_cfgOf_congr ⟨lookups_ok.1, lookups_ok.2.1, lookups_ok.2.2.1⟩
    (sortOf_ctor_congr lookups_ok.2.2.2 (sortsOf_head_congr ((sortOf_int i).trans (sortOf_int 0).symm))) rfl

/-- `<k> go(i) </k>` and `<k> done </k>`. -/
def Go (i : Int) : Config c := ⟨cfg (.ctor symGo [iv i]), sortOf_go i⟩
def Done : Config c := ⟨cfg (.ctor symDone []), by decide +kernel⟩

/-- X := i, the K rest `.K`, the counter cell. -/
def σ (i : Int) : Subst := [(0, iv i), (1, .ctor dotk []), (2, ctr)]

/-! ### `X >Int 0` at an Int -/

theorem gt_res (i : Int) : c.hookRes intGt [iv i, iv 0] = some (some (bool (decide (i > 0)))) :=
  Semantics.hookRes_of_value (by rw [Det.hook_intGt]; rfl)

theorem allSome2 (a b : GroundTerm) : allSome [some a, some b] = some [a, b] := rfl

/-- `X >Int 0` has the result `i > 0` where X is the Int i. -/
theorem evalGt_mk {τ : Subst} {i : Int} (hl : τ.lookup 0 = some (iv i)) :
    EvalTerm c τ (.app intGt [.var 0, .dv Srt.int (.int 0)]) (some (bool (decide (i > 0)))) :=
  .hook kinds.2.1 kinds.1 (.cons .var (.cons .dv .nil))
    (fun vs hvs => by
      rw [hl] at hvs
      have hv : vs = [iv i, iv 0] := Option.some.inj (hvs.symm.trans (allSome2 _ _))
      subst hv; exact gt_res i)
    (fun hn => by rw [hl] at hn; exact absurd (hn.symm.trans (allSome2 _ _)) (by simp))

/-- `X >Int 0` has no other result. -/
theorem evalGt_inv {τ : Subst} {i : Int} (hl : τ.lookup 0 = some (iv i))
    {w : Option GroundTerm} (h : EvalTerm c τ (.app intGt [.var 0, .dv Srt.int (.int 0)]) w) :
    w = some (bool (decide (i > 0))) := by
  cases h with
  | ctor hk _ => exact absurd (kinds.2.1.symm.trans hk) (by simp)
  | hook _ _ hts hh _ =>
    cases hts with
    | cons h1 hs =>
      cases hs with
      | cons h2 hs2 =>
        cases hs2; cases h1; cases h2
        rw [hl] at hh
        have := (hh _ (allSome2 _ _)).symm.trans (gt_res i)
        exact (Option.some.inj this)
  | param _ hhk _ _ _ => exact absurd (kinds.1.symm.trans hhk) (by simp)
  | call _ hhk _ _ _ _ => exact absurd (kinds.1.symm.trans hhk) (by simp)
  | callUndef _ hhk _ _ _ => exact absurd (kinds.1.symm.trans hhk) (by simp)
  | ovl _ ho _ _ => exact absurd (kinds.2.2.symm.trans ho) (by simp)
  | ovlFn _ ho _ _ _ _ _ => exact absurd (kinds.2.2.symm.trans ho) (by simp)

/-- **`pre` holds exactly where X is an Int i ≤ 0.** -/
theorem pre_iff {τ : Subst} {i : Int} (hl : τ.lookup 0 = some (iv i)) :
    Holds c r0.vars.length τ r0.pre true ↔ i ≤ 0 := by
  rw [r0_shape.2.2.2]
  constructor
  · intro h
    obtain ⟨r, r', e, e', hb⟩ := holds_equals_inv h
    rw [evalGt_inv hl e] at hb
    cases e'
    rw [sameResult_some] at hb
    cases hd : decide (i > 0) with
    | false => have := of_decide_eq_false hd; omega
    | true => rw [hd] at hb; exact absurd hb (by decide)
  · intro hi
    have h := Holds.equals (n := r0.vars.length) (s := Srt.bool) (evalGt_mk hl)
      (EvalTerm.dv (c := c) (σ := τ) (s := Srt.bool) (lit := .bool false))
    have hd : decide (i > 0) = false := decide_eq_false (by omega)
    rw [hd] at h
    have hs : sameResult (some (bool false)) (some (GroundTerm.dv Srt.bool (.bool false))) = true := by
      rw [sameResult_some]; rfl
    rw [hs] at h
    exact h

theorem prio_none {r' : Rule} (hr' : r' ∈ c.rules) (hlt : r'.prio < r0.prio) : False := by
  rw [rule_eq hr'] at hlt
  exact Nat.lt_irrefl _ hlt

/-- A match of the left side at `<k> go(i) </k>` gives X the value i. -/
theorem lookup0 {τ : Subst} {i : Int} (hm : PatVal c τ r0.lhs (cfg (.ctor symGo [iv i]))) :
    τ.lookup 0 = some (iv i) := by
  rw [r0_lhs] at hm
  have h1 := (patVal_ctor2 hooks_ok.1 syms_ok.1 hm).1
  have h2 := patVal_ctor1 hooks_ok.2.1 syms_ok.2.1 h1
  have h3 := (patVal_ctor2 hooks_ok.2.2.1 syms_ok.2.2.1 h2).1
  obtain ⟨w, hw, he⟩ := PatVal.inj_inv h3
  obtain ⟨-, vs, rfl, hs⟩ := PatVal.app_inv hooks_ok.2.2.2 hw syms_ok.2.2.2.1
  have he' : GroundTerm.inj exp Srt.kitem (.ctor symGo [iv i]) = .inj exp Srt.kitem (.ctor symGo vs) := he
  cases he'
  obtain ⟨_, _, he1, h4, _⟩ := PatVals.cons_inv hs
  cases he1
  exact PatVal.var_inv h4

theorem stepBy {i : Int} (hi : i ≤ 0) : StepBy c r0 (σ i) (Go i) Done where
  mem := r0_mem
  hσ := fun j s hs => by
    rw [r0_vars] at hs
    match j, hs with
    | 0, hs => cases hs; exact ⟨_, rfl, sortOf_int i⟩
    | 1, hs => cases hs; exact ⟨_, rfl, by decide +kernel⟩
    | 2, hs => cases hs; exact ⟨_, rfl, by decide +kernel⟩
  hmatch := by
    rw [r0_lhs]
    have hig : injNormal exp Srt.kitem (.ctor symGo [iv i]) = .inj exp Srt.kitem (.ctor symGo [iv i]) := rfl
    exact .ctor syms_ok.1 (.cons (.ctor syms_ok.2.1 (.cons (.ctor syms_ok.2.2.1
      (.cons (hig ▸ .inj (.ctor syms_ok.2.2.2.1 (.cons (.var rfl) .nil))) (.cons (.var rfl) .nil))) .nil))
      (.cons (.var rfl) .nil))
  hreq := fun t ht => by rw [r0_shape.1] at ht; cases ht
  hpre := (pre_iff rfl).mpr hi
  heval := by
    rw [r0_rhs]
    have he : EvalTerm c (σ i) (.inj exp Srt.kitem (.app symDone []))
        (some (.inj exp Srt.kitem (.ctor symDone []))) :=
      .inj (.ctor syms_ok.2.2.2.2 .nil)
    exact .ctor syms_ok.1 (.cons (.ctor syms_ok.2.1 (.cons (.ctor syms_ok.2.2.1
      (.cons he (.cons .var .nil))) .nil)) (.cons .var .nil))
  hens := fun t ht => by rw [r0_shape.2.1] at ht; cases ht
  hpost := by rw [r0_shape.2.2.1]; exact .top
  hprio := fun r' hr' hlt => (prio_none hr' hlt).elim

/-- **A step from `<k> go(i) </k>` is at an i ≤ 0**: the rule's `pre` holds there only. -/
theorem step_le {i : Int} {y : Config c} (h : Step c (Go i) y) : i ≤ 0 := by
  obtain ⟨r, τ, hs⟩ := step_iff_by.mp h
  have hr := rule_eq hs.mem
  subst hr
  exact (pre_iff (lookup0 hs.hmatch)).mp hs.hpre

/-- **`<k> go(i) </k>` steps to `<k> done </k>` exactly where i ≤ 0**, for every integer i. -/
theorem step_iff (i : Int) : Step c (Go i) Done ↔ i ≤ 0 :=
  ⟨step_le, fun hi => step_iff_by.mpr ⟨r0, σ i, stepBy hi⟩⟩

/-- **Where i > 0, `<k> go(i) </k>` has no successor.** -/
theorem stuck {i : Int} (hi : 0 < i) (y : Config c) : ¬ Step c (Go i) y :=
  fun h => absurd (step_le h) (by omega)

/-- info: 'CondCut.ReqNot.step_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms step_iff
/-- info: 'CondCut.ReqNot.stuck' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms stuck

/-! ### Under every interpretation H

The same steps at `c.withHooks H`: the reading has no parameter, so a value's sort, the rule and
the graph of `_>Int_` (a registry hook) are the same under every H. -/

noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

/-- No parameter of the definition is an open generator. -/
theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel

theorem sortOfH (H : HookParams) (v : GroundTerm) : (cH H).sortOf v = c.sortOf v := by
  rw [Semantics.sortOf_withHooks _ _ noRaw]

/-- `<k> go(i) </k>` and `<k> done </k>` under H. -/
def GoH (H : HookParams) (i : Int) : Config (cH H) := ⟨cfg (.ctor symGo [iv i]), by rw [sortOfH]; exact sortOf_go i⟩
def DoneH (H : HookParams) : Config (cH H) := ⟨cfg (.ctor symDone []), by rw [sortOfH]; exact Done.property⟩

theorem symsH (H : HookParams) : (cH H).isCtor topLabel = true ∧ (cH H).isCtor kCell = true ∧
    (cH H).isCtor kseq = true ∧ (cH H).isCtor symGo = true ∧ (cH H).isCtor symDone = true := syms_ok

theorem r0_memH (H : HookParams) : r0 ∈ (cH H).rules := r0_mem
theorem rule_eqH (H : HookParams) {r : Rule} (hr : r ∈ (cH H).rules) : r = r0 := rule_eq hr

/-- `X >Int 0` has the result `i > 0` under H where X is the Int i. -/
theorem evalGt_mkH (H : HookParams) {τ : Subst} {i : Int} (hl : τ.lookup 0 = some (iv i)) :
    EvalTerm (cH H) τ (.app intGt [.var 0, .dv Srt.int (.int 0)]) (some (bool (decide (i > 0)))) :=
  .hook kinds.2.1 kinds.1 (.cons .var (.cons .dv .nil))
    (fun vs hvs => by
      rw [hl] at hvs
      have hv : vs = [iv i, iv 0] := Option.some.inj (hvs.symm.trans (allSome2 _ _))
      subst hv; exact Semantics.hookRes_of_value (by rw [Det.hook_intGt]; rfl))
    (fun hn => by rw [hl] at hn; exact absurd (hn.symm.trans (allSome2 _ _)) (by simp))

/-- `X >Int 0` has no other result under H. -/
theorem evalGt_invH (H : HookParams) {τ : Subst} {i : Int} (hl : τ.lookup 0 = some (iv i))
    {w : Option GroundTerm} (h : EvalTerm (cH H) τ (.app intGt [.var 0, .dv Srt.int (.int 0)]) w) :
    w = some (bool (decide (i > 0))) := by
  cases h with
  | ctor hk _ => exact absurd (kinds.2.1.symm.trans hk) (by simp)
  | hook _ _ hts hh _ =>
    cases hts with
    | cons h1 hs =>
      cases hs with
      | cons h2 hs2 =>
        cases hs2; cases h1; cases h2
        rw [hl] at hh
        have := (hh _ (allSome2 _ _)).symm.trans
          (Semantics.hookRes_of_value (c := cH H) (by rw [Det.hook_intGt]; rfl))
        exact (Option.some.inj this)
  | param _ hhk _ _ _ => exact absurd (kinds.1.symm.trans hhk) (by simp)
  | call _ hhk _ _ _ _ => exact absurd (kinds.1.symm.trans hhk) (by simp)
  | callUndef _ hhk _ _ _ => exact absurd (kinds.1.symm.trans hhk) (by simp)
  | ovl _ ho _ _ => exact absurd (kinds.2.2.symm.trans ho) (by simp)
  | ovlFn _ ho _ _ _ _ _ => exact absurd (kinds.2.2.symm.trans ho) (by simp)

/-- `pre` holds under H exactly where X is an Int i ≤ 0. -/
theorem pre_iffH (H : HookParams) {τ : Subst} {i : Int} (hl : τ.lookup 0 = some (iv i)) :
    Holds (cH H) r0.vars.length τ r0.pre true ↔ i ≤ 0 := by
  rw [r0_shape.2.2.2]
  constructor
  · intro h
    obtain ⟨r, r', e, e', hb⟩ := holds_equals_inv h
    rw [evalGt_invH H hl e] at hb
    cases e'
    rw [sameResult_some] at hb
    cases hd : decide (i > 0) with
    | false => have := of_decide_eq_false hd; omega
    | true => rw [hd] at hb; exact absurd hb (by decide)
  · intro hi
    have h := Holds.equals (n := r0.vars.length) (s := Srt.bool) (evalGt_mkH H hl)
      (EvalTerm.dv (c := cH H) (σ := τ) (s := Srt.bool) (lit := .bool false))
    have hd : decide (i > 0) = false := decide_eq_false (by omega)
    rw [hd] at h
    have hs : sameResult (some (bool false)) (some (GroundTerm.dv Srt.bool (.bool false))) = true := by
      rw [sameResult_some]; rfl
    rw [hs] at h
    exact h

/-- A match of the left side under H at `<k> go(i) </k>` gives X the value i. -/
theorem lookup0H (H : HookParams) {τ : Subst} {i : Int} (hm : PatVal (cH H) τ r0.lhs (cfg (.ctor symGo [iv i]))) :
    τ.lookup 0 = some (iv i) := by
  rw [r0_lhs] at hm
  have h1 := (patVal_ctor2 hooks_ok.1 (symsH H).1 hm).1
  have h2 := patVal_ctor1 hooks_ok.2.1 (symsH H).2.1 h1
  have h3 := (patVal_ctor2 hooks_ok.2.2.1 (symsH H).2.2.1 h2).1
  obtain ⟨w, hw, he⟩ := PatVal.inj_inv h3
  obtain ⟨-, vs, rfl, hs⟩ := PatVal.app_inv hooks_ok.2.2.2 hw (symsH H).2.2.2.1
  have he' : GroundTerm.inj exp Srt.kitem (.ctor symGo [iv i]) = .inj exp Srt.kitem (.ctor symGo vs) := he
  cases he'
  obtain ⟨_, _, he1, h4, _⟩ := PatVals.cons_inv hs
  cases he1
  exact PatVal.var_inv h4

theorem stepByH (H : HookParams) {i : Int} (hi : i ≤ 0) : StepBy (cH H) r0 (σ i) (GoH H i) (DoneH H) where
  mem := r0_memH H
  hσ := fun j s hs => by
    rw [r0_vars] at hs
    match j, hs with
    | 0, hs => cases hs; exact ⟨_, rfl, by rw [sortOfH]; exact sortOf_int i⟩
    | 1, hs => cases hs; exact ⟨_, rfl, by rw [sortOfH]; decide +kernel⟩
    | 2, hs => cases hs; exact ⟨_, rfl, by rw [sortOfH]; decide +kernel⟩
  hmatch := by
    rw [r0_lhs]
    have hig : injNormal exp Srt.kitem (.ctor symGo [iv i]) = .inj exp Srt.kitem (.ctor symGo [iv i]) := rfl
    exact .ctor (symsH H).1 (.cons (.ctor (symsH H).2.1 (.cons (.ctor (symsH H).2.2.1
      (.cons (hig ▸ .inj (.ctor (symsH H).2.2.2.1 (.cons (.var rfl) .nil))) (.cons (.var rfl) .nil))) .nil))
      (.cons (.var rfl) .nil))
  hreq := fun t ht => by rw [r0_shape.1] at ht; cases ht
  hpre := (pre_iffH H rfl).mpr hi
  heval := by
    rw [r0_rhs]
    have he : EvalTerm (cH H) (σ i) (.inj exp Srt.kitem (.app symDone []))
        (some (.inj exp Srt.kitem (.ctor symDone []))) :=
      .inj (.ctor (symsH H).2.2.2.2 .nil)
    exact .ctor (symsH H).1 (.cons (.ctor (symsH H).2.1 (.cons (.ctor (symsH H).2.2.1
      (.cons he (.cons .var .nil))) .nil)) (.cons .var .nil))
  hens := fun t ht => by rw [r0_shape.2.1] at ht; cases ht
  hpost := by rw [r0_shape.2.2.1]; exact .top
  hprio := fun r' hr' hlt => (prio_none hr' hlt).elim

/-- **A step from `<k> go(i) </k>` is at an i ≤ 0, for every H**: the rule's `pre` holds there
only. -/
theorem step_leH (H : HookParams) {i : Int} {y : Config (cH H)} (h : Step (cH H) (GoH H i) y) : i ≤ 0 := by
  obtain ⟨r, τ, hs⟩ := step_iff_by.mp h
  have hr := rule_eqH H hs.mem
  subst hr
  exact (pre_iffH H (lookup0H H hs.hmatch)).mp hs.hpre

/-- **`<k> go(i) </k>` steps to `<k> done </k>` exactly where i ≤ 0, for every H** and every
integer i. -/
theorem step_iffH (H : HookParams) (i : Int) : Step (cH H) (GoH H i) (DoneH H) ↔ i ≤ 0 :=
  ⟨step_leH H, fun hi => step_iff_by.mpr ⟨r0, σ i, stepByH H hi⟩⟩

/-- **Where i > 0, `<k> go(i) </k>` has no successor, for every H.** -/
theorem stuckH (H : HookParams) {i : Int} (hi : 0 < i) (y : Config (cH H)) : ¬ Step (cH H) (GoH H i) y :=
  fun h => absurd (step_leH H h) (by omega)

/-- info: 'CondCut.ReqNot.step_iffH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms step_iffH
/-- info: 'CondCut.ReqNot.stuckH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms stuckH

end ReqNot

/-! ## `andUnderAppCut`: `go(X, Y) => done requires f(X #And Y) ==Int 0`, `f(X) => X -Int 1` -/

namespace ReqAndApp

definition_of defn from "f2-examples/mlreqandapp.kompile.kore"
noncomputable abbrev c : Semantics := defn.sem

def exp : Srt := 32
def symDone : Sym := 385
def symGo : Sym := 386
def symF : Sym := 387

theorem names_ok : c.symName symDone = "Lbldone" ∧ c.symName symGo = "Lblgo" ∧ c.symName symF = "Lblf" := by
  decide +kernel

/-- The rule as read: the `requires` `f(X) ==Int 0`, and `pre` the membership `X ∈ Y` at Int. -/
theorem read_shape : c.rules.map (fun r => (r.req, r.pre)) =
    [(some (.app intEq [.app symF [.var 0], .dv Srt.int (.int 0)]), .mem Srt.int (.var 0) (.var 1))] :=
  rfl

theorem coreOK : c.coreOK = true := by decide +kernel

/-- The definition without its rule, whose `ok` gives the clauses' context. -/
noncomputable abbrev cNoRules : Semantics := { c with rules := [] }
theorem sortedOK : c.sortedOK = true := by decide +kernel
theorem srReady : c.srReady = true := by decide +kernel
theorem matchReady : c.matchReady = true := by decide +kernel

/-- Evaluation has one result: the deciders confirm coherence. -/
theorem coherent : CoherentAll c := by
  have hag : c.agreeObligations = [] := by decide +kernel
  have hcf : c.clausesFixed = true := by decide +kernel
  refine coherentAll_of_parts (matchIndependentAll_of_sortedOK sortedOK (Semantics.fnsNoExs_of_all (by decide +kernel)) matchReady
    (.of_fixed hcf (Exec.matchCtx_of matchReady).noOvl)) fun f fn hfn => ?_
  obtain ⟨hmem, -⟩ := lookupFn_spec hfn
  rcases List.mem_append.mp hmem with h | h
  · exact clausesAgree_of_sortedOK sortedOK (Semantics.fnsNoExs_of_all (by decide +kernel)) srReady matchReady (fun f hf => by rw [hag] at hf; nomatch hf) fn h
  · exact sortPreds_agree h

theorem fnDet : FnDet c := fnDet_of_coherent coherent

private theorem hready : CExec.execReady c = true := by decide +kernel

def cfg (e : GroundTerm) : GroundTerm := cfgOf 383 exp e
def go (i j : Int) : GroundTerm := .ctor symGo [iv i, iv j]
def Go11 : Config c := ⟨cfg (go 1 1), by decide +kernel⟩
def Go12 : Config c := ⟨cfg (go 1 2), by decide +kernel⟩
def Go22 : Config c := ⟨cfg (go 2 2), by decide +kernel⟩
def Go00 : Config c := ⟨cfg (go 0 0), by decide +kernel⟩
def Done : Config c := ⟨cfg (.ctor symDone []), by decide +kernel⟩

/-- **`go(1, 1)` steps to `done`**: X and Y are both 1 and f(1) = 0. -/
theorem step_go11 : Step c Go11 Done := by
  have hy : Done.val ∈ CExec.successorsN c 50 Go11.val := by decide +kernel
  obtain ⟨_, h⟩ := CExec.successorsN_step_ready hready (x := Go11) hy
  exact h

/-- **`go(1, 2)`, `go(2, 2)` and `go(0, 0)` have no successor**: at the first X and Y differ, and
`1 #And 2` is nothing; at the others f(X) is not 0. -/
theorem stuck : (∀ y, ¬ Step c Go12 y) ∧ (∀ y, ¬ Step c Go22 y) ∧ (∀ y, ¬ Step c Go00 y) :=
  ⟨CExec.noStep_at hready fnDet (n := 50) (x := Go12) (by decide +kernel) (by decide +kernel),
   CExec.noStep_at hready fnDet (n := 50) (x := Go22) (by decide +kernel) (by decide +kernel),
   CExec.noStep_at hready fnDet (n := 50) (x := Go00) (by decide +kernel) (by decide +kernel)⟩

/-- info: 'CondCut.ReqAndApp.stuck' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms stuck

/-! ### Under every interpretation H

The same steps at `c.withHooks H`: the reading has no parameter, so the executable step at these
configurations (f's clause, the registry's `_-Int_` and `_==Int_`, the membership of `pre`) reads no
interpretation, and evaluation has one result under every H. -/

noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

/-- No parameter of the definition is an open generator. -/
theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel

kernel_rfl sortedOK_withHooksL : ∀ H : HookParams, (c.withHooks H).sortedOK = c.sortedOK

/-- Evaluation has one result under every H: the deciders on the data confirm coherence. -/
theorem coherentH (H : HookParams) : CoherentAll (cH H) := by
  have hag : (cH H).agreeObligations = [] := (Semantics.agreeObligations_withHooks c H).trans (by decide +kernel)
  have hcf : (cH H).clausesFixed = true := (Semantics.clausesFixed_withHooks c H).trans (by decide +kernel)
  have hso : (cH H).sortedOK = true := (sortedOK_withHooksL H).trans sortedOK
  have hsr' : (cH H).srReady = true := (Semantics.srReady_withHooks c H).trans srReady
  have hmr' : (cH H).matchReady = true := (Semantics.matchReady_withHooks c H).trans matchReady
  have hnx : (cH H).FnsNoExs := (Semantics.fnsNoExs_withHooks c H).mpr (Semantics.fnsNoExs_of_all (by decide +kernel))
  refine coherentAll_of_parts (matchIndependentAll_of_sortedOK hso hnx hmr'
    (.of_fixed hcf (Exec.matchCtx_of hmr').noOvl)) fun f fn hfn => ?_
  obtain ⟨hmem, -⟩ := lookupFn_spec hfn
  rcases List.mem_append.mp hmem with h | h
  · exact clausesAgree_of_sortedOK hso hnx hsr' hmr' (fun f hf => by rw [hag] at hf; nomatch hf) fn h
  · exact sortPreds_agree h

theorem fnDetH (H : HookParams) : FnDet (cH H) := fnDet_of_coherent (coherentH H)

/-- A configuration of the reading is one under every H (no open generator). -/
def cfgH (x : Config c) (H : HookParams) : Config (cH H) :=
  ⟨x.val, by rw [Semantics.sortOf_withHooks _ _ noRaw]; exact x.property⟩

kernel_rfl succsGo11_withHooks : ∀ H : HookParams,
  CExec.successorsN (c.withHooks H) 50 Go11.val = CExec.successorsN c 50 Go11.val
kernel_rfl succsGo12_withHooks : ∀ H : HookParams,
  CExec.successorsN (c.withHooks H) 50 Go12.val = CExec.successorsN c 50 Go12.val
kernel_rfl succsGo22_withHooks : ∀ H : HookParams,
  CExec.successorsN (c.withHooks H) 50 Go22.val = CExec.successorsN c 50 Go22.val
kernel_rfl succsGo00_withHooks : ∀ H : HookParams,
  CExec.successorsN (c.withHooks H) 50 Go00.val = CExec.successorsN c 50 Go00.val
kernel_rfl fuelGo12_withHooks : ∀ H : HookParams,
  CExec.outOfFuel (c.withHooks H) 50 Go12.val = CExec.outOfFuel c 50 Go12.val
kernel_rfl fuelGo22_withHooks : ∀ H : HookParams,
  CExec.outOfFuel (c.withHooks H) 50 Go22.val = CExec.outOfFuel c 50 Go22.val
kernel_rfl fuelGo00_withHooks : ∀ H : HookParams,
  CExec.outOfFuel (c.withHooks H) 50 Go00.val = CExec.outOfFuel c 50 Go00.val

theorem listed :
    Done.val ∈ CExec.successorsN c 50 Go11.val ∧
    CExec.successorsN c 50 Go12.val = [] ∧ CExec.outOfFuel c 50 Go12.val = false ∧
    CExec.successorsN c 50 Go22.val = [] ∧ CExec.outOfFuel c 50 Go22.val = false ∧
    CExec.successorsN c 50 Go00.val = [] ∧ CExec.outOfFuel c 50 Go00.val = false := by
  decide +kernel

/-- **`go(1, 1)` steps to `done`, for every H.** -/
theorem step_go11H (H : HookParams) : Step (cH H) (cfgH Go11 H) (cfgH Done H) := by
  have hy : Done.val ∈ CExec.successorsN (cH H) 50 (cfgH Go11 H).val := by
    show Done.val ∈ CExec.successorsN (c.withHooks H) 50 Go11.val
    rw [succsGo11_withHooks]; exact listed.1
  obtain ⟨_, h⟩ := CExec.successorsN_step_ready ((CExec.execReady_withHooks c H).trans hready)
    (x := cfgH Go11 H) hy
  exact h

/-- **`go(1, 2)`, `go(2, 2)` and `go(0, 0)` have no successor, for every H.** -/
theorem stuckH (H : HookParams) : (∀ y, ¬ Step (cH H) (cfgH Go12 H) y) ∧ (∀ y, ¬ Step (cH H) (cfgH Go22 H) y) ∧
    (∀ y, ¬ Step (cH H) (cfgH Go00 H) y) :=
  have hr := (CExec.execReady_withHooks c H).trans hready
  ⟨CExec.noStep_at (n := 50) (x := cfgH Go12 H) hr (fnDetH H)
      (by show CExec.outOfFuel (c.withHooks H) 50 Go12.val = false; rw [fuelGo12_withHooks]; exact listed.2.2.1)
      (by show CExec.successorsN (c.withHooks H) 50 Go12.val = []; rw [succsGo12_withHooks]; exact listed.2.1),
   CExec.noStep_at (n := 50) (x := cfgH Go22 H) hr (fnDetH H)
      (by show CExec.outOfFuel (c.withHooks H) 50 Go22.val = false; rw [fuelGo22_withHooks]; exact listed.2.2.2.2.1)
      (by show CExec.successorsN (c.withHooks H) 50 Go22.val = []; rw [succsGo22_withHooks]; exact listed.2.2.2.1),
   CExec.noStep_at (n := 50) (x := cfgH Go00 H) hr (fnDetH H)
      (by show CExec.outOfFuel (c.withHooks H) 50 Go00.val = false; rw [fuelGo00_withHooks]; exact listed.2.2.2.2.2.2)
      (by show CExec.successorsN (c.withHooks H) 50 Go00.val = []; rw [succsGo00_withHooks]; exact listed.2.2.2.2.2.1)⟩

/-- info: 'CondCut.ReqAndApp.step_go11H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms step_go11H
/-- info: 'CondCut.ReqAndApp.stuckH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms stuckH

end ReqAndApp

end CondCut
