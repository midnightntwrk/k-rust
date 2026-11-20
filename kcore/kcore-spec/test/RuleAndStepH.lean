/-
  The steps of the rules read through `andTermsCut` (test/PredFixtures.lean's `RhsAnd.MlAndT` and
  `RhsAnd.MlAndV`), under every interpretation of the parameters: K 7.1.337 kompile's texts of the
  fixtures e3-ml-rule-rhs-and-term and e3-ml-rule-rhs-and-var, read by the reader, each statement
  over `c0.withHooks H` for every `H : HookParams`, `c0` the reading. Run from the package root:
  `lake env lean -j1 test/RuleAndStepH.lean`.

  - `MlAndT` (`f2-examples/e3-ml-rule-rhs-and-term.kompile.kore`: `rule f(X) => X`,
    `rule g(X) => 0 -Int X`, `rule <k> go(X) => f(X) #And g(X) ... </k>`): sentence 157 is read in
    the fresh form, `go(X) => ?Z` with `post := Z ∈ f(X) ∧ Z ∈ g(X)` (`r0_shape`); sentences 155
    and 156 are the equations of f and g. `step_go0_iff`: the successor of `<k> go(0) </k>` is
    `<k> 0 </k>`, and only it: f(0) and g(0) are both 0. `stuck_go1`: `<k> go(1) </k>` has no
    successor: f(1) = 1 and g(1) = -1 have no common value.
    The rule has a `post` and an existential variable, which `ok` and `execReady` refuse, so the
    steps are proved from `StepBy` and `Holds`, as in test/PredFixtures.lean. The interpretation is
    not read: the evaluation of f and g on the parsed data (`Cert.evalTC`) reads none
    (`Cert.evalTC_withHooks`: no parameter is an open generator, and `_-Int_` has a value at every
    pair of Ints, so no point is a silent one), and the deciders that give one result to every
    evaluation (`coherent`) are of the parsed data.
  - `MlAndV` (`f2-examples/e3-ml-rule-rhs-and-var.kompile.kore`,
    `rule <k> c(X) => a() #And X ... </k>`): sentence 99 is read in the variable form, `c(X) => X`
    with `post := X ∈ a()` (`read_shape`). `andVar_steps`: `<k> c(a) </k>` steps to `<k> a </k>`,
    and `<k> c(b) </k>` has no successor. The rule binds its variables on the left side and its
    `post` is a membership, so the executable step lists its successors (`CExec.execReady`), and
    the list at the two configurations is the same under every H (`ca_withHooks`, `cb_withHooks`,
    checked by the kernel: the text declares no function).

  test/TieE3MlRuleRhsAndTerm157.lean and test/TieE3MlRuleRhsAndVar99.lean tie Γ's item of each rule
  to its sentence for every H (`rule_from_text_sig`). The steps of e3-ml-rule-rhs-and-ctor
  (`c(X) => X #And a()`) for every H are test/Guards.lean's `DevAndCut.andCut_steps`.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

open KCore
open ML Faithful

namespace RuleAndStepH
/-! ## Inversions -/

theorem holds_not_inv {c : Semantics} {n : Nat} {σ : Subst} {p : Cond} {b : Bool}
    (h : Holds c n σ (.not p) b) : ∃ b', Holds c n σ p b' ∧ b = !b' := by
  generalize hq : Cond.not p = q at h
  cases h with
  | not h => cases hq; exact ⟨_, h, rfl⟩
  | _ => cases hq

theorem holds_and_inv {c : Semantics} {n : Nat} {σ : Subst} {p q : Cond} {b : Bool}
    (h : Holds c n σ (.and p q) b) : ∃ b₁ b₂, Holds c n σ p b₁ ∧ Holds c n σ q b₂ ∧ b = (b₁ && b₂) := by
  generalize hq : Cond.and p q = r at h
  cases h with
  | and h h' => cases hq; exact ⟨_, _, h, h', rfl⟩
  | _ => cases hq

theorem holds_or_inv {c : Semantics} {n : Nat} {σ : Subst} {p q : Cond} {b : Bool}
    (h : Holds c n σ (.or p q) b) : ∃ b₁ b₂, Holds c n σ p b₁ ∧ Holds c n σ q b₂ ∧ b = (b₁ || b₂) := by
  generalize hq : Cond.or p q = r at h
  cases h with
  | or h h' => cases hq; exact ⟨_, _, h, h', rfl⟩
  | _ => cases hq

theorem holds_mem_inv {c : Semantics} {n : Nat} {σ : Subst} {s : Srt} {t u : Term} {b : Bool}
    (h : Holds c n σ (.mem s t u) b) :
    ∃ r r', EvalTerm c σ t r ∧ EvalTerm c σ u r' ∧ b = (r.isSome && sameResult r r') := by
  generalize hq : Cond.mem s t u = q at h
  cases h with
  | mem h h' => cases hq; exact ⟨_, _, h, h', rfl⟩
  | _ => cases hq

/-- A nullary constructor evaluates to itself. -/
theorem evalTerm_const {c : Semantics} {σ : Subst} {f : Sym} {r : Option GroundTerm}
    (hc : c.isCtor f = true) (h : EvalTerm c σ (.app f []) r) : r = some (.ctor f []) := by
  obtain ⟨rs, hrs, rfl⟩ := EvalTerm.ctor_inv hc h
  cases EvalTerms.nil_inv hrs
  rfl

/-- `sameResult` of two results is their equality. -/
theorem sameResult_some {v w : GroundTerm} : sameResult (some v) (some w) = decide (v = w) := by
  unfold sameResult
  by_cases h : v = w
  · subst h; simp [cmp_eq_iff]
  · simp [cmp_eq_iff, h]

/-- An injection's normal form is the injection of a term that is no injection. -/
theorem injNormal_of_not_inj {a b : Srt} {v : GroundTerm} (h : v.isInj = false) :
    injNormal a b v = .inj a b v := by
  cases v <;> first | rfl | cases h

/-- A value of a sort no sort lies below is no injection. -/
theorem isInj_of_sort {c : Semantics} {s : Srt} (hs : ∀ p ∈ c.subsorts, p.2 ≠ s) {v : GroundTerm}
    (hv : c.sortOf v = some s) : v.isInj = false := by
  cases v with
  | inj a b w =>
    simp only [Semantics.sortOf] at hv
    split at hv
    · rename_i hc
      simp only [Bool.and_eq_true, List.contains_iff_mem] at hc
      cases hv
      exact absurd rfl (hs _ hc.1.1)
    · cases hv
  | _ => rfl

theorem allSome_cons {r : Option GroundTerm} {rs : List (Option GroundTerm)} {v : GroundTerm}
    {vs : List GroundTerm} (h : allSome (r :: rs) = some (v :: vs)) : r = some v ∧ allSome rs = some vs := by
  cases r with
  | none => cases h
  | some w =>
    simp only [allSome, Option.bind_some] at h
    cases hr : allSome rs with
    | none => rw [hr] at h; cases h
    | some ws => rw [hr] at h; cases h; exact ⟨rfl, rfl⟩

/-- A constructor application evaluating to a constructor term of two arguments: the two
arguments' results. -/
theorem evalTerm_ctor2 {c : Semantics} {σ : Subst} {f : Sym} {t u : Term} {v w : GroundTerm}
    (hc : c.isCtor f = true) (h : EvalTerm c σ (.app f [t, u]) (some (.ctor f [v, w]))) :
    EvalTerm c σ t (some v) ∧ EvalTerm c σ u (some w) := by
  obtain ⟨rs, hrs, he⟩ := EvalTerm.ctor_inv hc h
  obtain ⟨r1, rs1, rfl, h1, hrs1⟩ := EvalTerms.cons_inv hrs
  obtain ⟨r2, rs2, rfl, h2, hrs2⟩ := EvalTerms.cons_inv hrs1
  cases EvalTerms.nil_inv hrs2
  cases ha : allSome [r1, r2] with
  | none => rw [ha] at he; cases he
  | some vs =>
    rw [ha] at he
    cases he
    obtain ⟨rfl, h'⟩ := allSome_cons ha
    obtain ⟨rfl, -⟩ := allSome_cons h'
    exact ⟨h1, h2⟩

/-- A constructor application evaluating to a constructor term of one argument. -/
theorem evalTerm_ctor1 {c : Semantics} {σ : Subst} {f : Sym} {t : Term} {v : GroundTerm}
    (hc : c.isCtor f = true) (h : EvalTerm c σ (.app f [t]) (some (.ctor f [v]))) :
    EvalTerm c σ t (some v) := by
  obtain ⟨rs, hrs, he⟩ := EvalTerm.ctor_inv hc h
  obtain ⟨r1, rs1, rfl, h1, hrs1⟩ := EvalTerms.cons_inv hrs
  cases EvalTerms.nil_inv hrs1
  cases ha : allSome [r1] with
  | none => rw [ha] at he; cases he
  | some vs =>
    rw [ha] at he
    cases he
    obtain ⟨rfl, -⟩ := allSome_cons ha
    exact h1

/-- The pattern of a constructor application of two arguments at a constructor term. -/
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

/-- The configuration `<generatedTop>(<k>(kseq(inj{s,KItem}(st), dotk)), <generatedCounter>(0))`,
the k cell's symbol `kCell`. -/
def cfgOf (kCell : Sym) (s : Srt) (st : GroundTerm) : GroundTerm :=
  .ctor topLabel [.ctor kCell [.ctor kseq [.inj s Srt.kitem st, .ctor dotk []]], .ctor counterLabel [int 0]]

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

/-- `cfgOf kCell s st` has the sort of `cfgOf kCell s st0` where st and st0 have one sort and
neither is an injection. -/
theorem sortOf_cfgOf_congr {c : Semantics} {kCell : Sym} {s : Srt} {st st0 : GroundTerm}
    (hl : (lookupSig c.ctorSigs topLabel).isSome = true ∧ (lookupSig c.ctorSigs kCell).isSome = true ∧
      (lookupSig c.ctorSigs kseq).isSome = true)
    (h : c.sortOf st = c.sortOf st0) (hi : st.isInj = st0.isInj) :
    c.sortOf (cfgOf kCell s st) = c.sortOf (cfgOf kCell s st0) :=
  sortOf_ctor_congr hl.1 (sortsOf_head_congr (sortOf_ctor_congr hl.2.1 (sortsOf_head_congr
    (sortOf_ctor_congr hl.2.2 (sortsOf_head_congr (sortOf_inj_congr h hi))))))


/-- A constructor application of two arguments with a result: the constructor term of the two
arguments' results. -/
theorem evalTerm_ctor2_ex {c : Semantics} {σ : Subst} {f : Sym} {t u : Term} {v : GroundTerm}
    (hc : c.isCtor f = true) (h : EvalTerm c σ (.app f [t, u]) (some v)) :
    ∃ v₁ v₂, v = .ctor f [v₁, v₂] ∧ EvalTerm c σ t (some v₁) ∧ EvalTerm c σ u (some v₂) := by
  obtain ⟨rs, hrs, he⟩ := EvalTerm.ctor_inv hc h
  obtain ⟨r1, rs1, rfl, h1, hrs1⟩ := EvalTerms.cons_inv hrs
  obtain ⟨r2, rs2, rfl, h2, hrs2⟩ := EvalTerms.cons_inv hrs1
  cases EvalTerms.nil_inv hrs2
  cases r1 with
  | none => cases he
  | some v₁ =>
    cases r2 with
    | none => cases he
    | some v₂ => cases he; exact ⟨v₁, v₂, rfl, h1, h2⟩

/-- A constructor application of one argument with a result. -/
theorem evalTerm_ctor1_ex {c : Semantics} {σ : Subst} {f : Sym} {t : Term} {v : GroundTerm}
    (hc : c.isCtor f = true) (h : EvalTerm c σ (.app f [t]) (some v)) :
    ∃ v₁, v = .ctor f [v₁] ∧ EvalTerm c σ t (some v₁) := by
  obtain ⟨rs, hrs, he⟩ := EvalTerm.ctor_inv hc h
  obtain ⟨r1, rs1, rfl, h1, hrs1⟩ := EvalTerms.cons_inv hrs
  cases EvalTerms.nil_inv hrs1
  cases r1 with
  | none => cases he
  | some v₁ => cases he; exact ⟨v₁, rfl, h1⟩

/-- An evaluation of `cfgPat kCell s p k c` to a value: the value is `cfgOf kCell s w` where p
evaluates to w, V_k is `.` and V_c the counter at 0. -/
theorem evalTerm_cfgPat {c : Semantics} {σ : Subst} {kCell : Sym} {s : Srt} {p : Term} {k i : Nat}
    {v : GroundTerm} (hc : c.isCtor topLabel = true ∧ c.isCtor kCell = true ∧ c.isCtor kseq = true)
    (hk : σ.lookup k = some (.ctor dotk [])) (hi : σ.lookup i = some (.ctor counterLabel [int 0]))
    (h : EvalTerm c σ (cfgPat kCell s p k i) (some v)) :
    ∃ w, EvalTerm c σ p (some w) ∧ v = .ctor topLabel [.ctor kCell [.ctor kseq
      [injNormal s Srt.kitem w, .ctor dotk []]], .ctor counterLabel [int 0]] := by
  obtain ⟨v₁, v₂, rfl, h1, h2⟩ := evalTerm_ctor2_ex hc.1 h
  obtain ⟨u, rfl, h3⟩ := evalTerm_ctor1_ex hc.2.1 h1
  obtain ⟨u₁, u₂, rfl, h4, h5⟩ := evalTerm_ctor2_ex hc.2.2 h3
  obtain ⟨r', h6, hr⟩ := EvalTerm.inj_inv h4
  have e5 := EvalTerm.var_inv h5
  have e2 := EvalTerm.var_inv h2
  rw [hk] at e5
  rw [hi] at e2
  cases e5
  cases e2
  cases r' with
  | none => cases hr
  | some w =>
    simp only [Option.map_some, Option.some.injEq] at hr
    subst hr
    exact ⟨w, h6, rfl⟩

/-- A match of `cfgPat kCell s p k i` at `cfgOf kCell s st`: p matches a w whose injection is st's, and
V_k, V_c are `.` and the counter. -/
theorem patVal_cfgPat {c : Semantics} {σ : Subst} {kCell : Sym} {s : Srt} {p : Term} {k i : Nat}
    {st : GroundTerm} (hc : c.isCtor topLabel = true ∧ c.isCtor kCell = true ∧ c.isCtor kseq = true)
    (hh : patternHooks.contains topLabel = false ∧ patternHooks.contains kCell = false ∧
      patternHooks.contains kseq = false)
    (h : PatVal c σ (cfgPat kCell s p k i) (cfgOf kCell s st)) :
    (∃ w, PatVal c σ p w ∧ injNormal s Srt.kitem w = .inj s Srt.kitem st) ∧
      σ.lookup k = some (.ctor dotk []) ∧ σ.lookup i = some (.ctor counterLabel [int 0]) := by
  have ⟨h1, hc'⟩ := patVal_ctor2 hh.1 hc.1 h
  have h2 := patVal_ctor1 hh.2.1 hc.2.1 h1
  have ⟨h3, hk'⟩ := patVal_ctor2 hh.2.2 hc.2.2 h2
  obtain ⟨w, hw, he⟩ := PatVal.inj_inv h3
  exact ⟨⟨w, hw, he.symm⟩, PatVal.var_inv hk', PatVal.var_inv hc'⟩

/-! ## The fixtures' symbols and configurations -/

def exp : Srt := 32
def kCell : Sym := 383
def symA : Sym := 385
def symB : Sym := 386
def symC : Sym := 387
def symD : Sym := 388

def aT : GroundTerm := .ctor symA []
def bT : GroundTerm := .ctor symB []
def dotkT : GroundTerm := .ctor dotk []
def ctr : GroundTerm := .ctor counterLabel [int 0]
def cfg (st : GroundTerm) : GroundTerm := cfgOf kCell exp st

/-! ## e3-ml-rule-rhs-and-term -/

namespace MlAndT

definition_of defn from "f2-examples/e3-ml-rule-rhs-and-term.kompile.kore"

noncomputable abbrev c0 : Semantics := defn.sem

theorem noRaw0 : ∀ k ∈ c0.params, k.raw = false := by decide +kernel

theorem isCtor_wh (H : HookParams) (f : Sym) : (c0.withHooks H).isCtor f = c0.isCtor f := rfl
theorem rules_wh (H : HookParams) : (c0.withHooks H).rules = c0.rules := rfl
theorem fns_wh (H : HookParams) : (c0.withHooks H).fns = c0.fns := rfl
theorem params_wh (H : HookParams) : (c0.withHooks H).params = c0.params := rfl
theorem subsorts_wh (H : HookParams) : (c0.withHooks H).subsorts = c0.subsorts := rfl
theorem ctorSigs_wh (H : HookParams) : (c0.withHooks H).ctorSigs = c0.ctorSigs := rfl

variable {H : HookParams}

/-- A value has the sort the parsed data gives it, under every interpretation: no parameter is an
open generator. -/
theorem sortOf_eq : (c0.withHooks H).sortOf = c0.sortOf := Semantics.sortOf_withHooks c0 H noRaw0

/-- Decides a condition of the parsed data stated of `c0.withHooks H`: the condition does not read
the interpretation, so it is rewritten to `c0`'s and decided there. -/
local macro "whd" : tactic => `(tactic| first | decide +kernel | (rw [sortOf_eq]; decide +kernel) |
  (simp only [isCtor_wh, rules_wh, fns_wh, params_wh, subsorts_wh, ctorSigs_wh]; decide +kernel))

def symGo : Sym := 386
def symF : Sym := 388
def symG : Sym := 389

theorem names_ok : c0.sortName exp = "Exp" ∧ c0.symName symGo = "Lblgo" ∧ c0.symName symF = "Lblf" ∧
    c0.symName symG = "Lblg" := by
  decide +kernel
theorem prios : c0.rules.length = 1 ∧ ∀ r ∈ c0.rules, r.prio = 50 := by decide +kernel

noncomputable def r0 : Rule := c0.rules[0]'(by decide +kernel)
theorem r0_mem : r0 ∈ (c0.withHooks H).rules := List.getElem_mem _
theorem rule_eq {r : Rule} (hr : r ∈ (c0.withHooks H).rules) : r = r0 := by
  rw [rules_wh] at hr
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hr
  have : i = 0 := by have := prios.1; omega
  subst this
  rfl

def fX : Term := .app symF [.var 0]
def gX : Term := .app symG [.var 0]

/-- The fresh form: `go(X) => ?Z` with `post := and (mem Z f(X)) (mem Z g(X))`, Z the variable 3. -/
theorem r0_vars : r0.vars = [Srt.int, Srt.k, 19, Srt.int] := by whd
theorem r0_lhs : r0.lhs = cfgPat kCell exp (.app symGo [.var 0]) 1 2 := rfl
theorem r0_rhs : r0.rhs = cfgPat kCell Srt.int (.var 3) 1 2 := rfl
theorem r0_shape : r0.req = none ∧ r0.ens = none ∧ r0.pre = .top ∧ r0.exs = [3] ∧
    r0.post = .and (.mem Srt.int (.var 3) fX) (.mem Srt.int (.var 3) gX) :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem syms_ok : (c0.withHooks H).isCtor topLabel = true ∧ (c0.withHooks H).isCtor kCell = true ∧ (c0.withHooks H).isCtor kseq = true ∧
    (c0.withHooks H).isCtor symGo = true := by
  whd
theorem hooks_ok : patternHooks.contains topLabel = false ∧ patternHooks.contains kCell = false ∧
    patternHooks.contains kseq = false ∧ patternHooks.contains symGo = false := by
  whd

/-! #### The evaluation of the conjuncts -/

/-- The definition without its rule: the rule has a predicate and an existential variable, which
`ok` and `okM` refuse; the clauses' context does not read the rules. -/
noncomputable abbrev cNoRules : Semantics := { c0 with rules := [] }
theorem okL : cNoRules.ok = true := by decide +kernel
theorem sortedOK0 : c0.sortedOK = true := by decide +kernel
kernel_rfl sortedOK_wh : ∀ H : HookParams, (c0.withHooks H).sortedOK = c0.sortedOK
theorem sortedOK : (c0.withHooks H).sortedOK = true := (sortedOK_wh H).trans sortedOK0
theorem srReady : (c0.withHooks H).srReady = true :=
  (Semantics.srReady_withHooks c0 H).trans (by decide +kernel)
theorem matchReady : (c0.withHooks H).matchReady = true :=
  (Semantics.matchReady_withHooks c0 H).trans (by decide +kernel)

theorem hsc : SortCtx (c0.withHooks H) := sortCtx_of_all sortedOK srReady (Exec.ovlCase_of matchReady)
/-- The clauses are the definition's: `ok` of the definition without its rule gives their context,
under every interpretation. -/
theorem hcc : Exec.ClauseCtx (c0.withHooks H) :=
  have h : Exec.ClauseCtx (cNoRules.withHooks H) := Exec.clauseCtx_of ((Semantics.ok_withHooks cNoRules H).trans okL)
  h
theorem hmc : Exec.MatchCtx (c0.withHooks H) := Exec.matchCtx_of matchReady

theorem fnsNoExs : (c0.withHooks H).FnsNoExs :=
  (Semantics.fnsNoExs_withHooks _ _).mpr (Semantics.fnsNoExs_of_all (by decide +kernel))

/-- Evaluation has one result under every interpretation: the deciders confirm coherence on the
parsed data. -/
theorem coherent : CoherentAll (c0.withHooks H) := by
  have hag : (c0.withHooks H).agreeObligations = [] :=
    (Semantics.agreeObligations_withHooks c0 H).trans (by decide +kernel)
  have hcf : (c0.withHooks H).clausesFixed = true :=
    (Semantics.clausesFixed_withHooks c0 H).trans (by decide +kernel)
  refine coherentAll_of_parts (matchIndependentAll_of_sortedOK sortedOK fnsNoExs matchReady
    (.of_fixed hcf (Exec.matchCtx_of matchReady).noOvl)) fun f fn hfn => ?_
  obtain ⟨hmem, -⟩ := lookupFn_spec hfn
  rcases List.mem_append.mp hmem with h | h
  · exact clausesAgree_of_sortedOK sortedOK fnsNoExs srReady matchReady (fun f hf => by rw [hag] at hf; nomatch hf) fn h
  · exact sortPreds_agree h

theorem fnDet : FnDet (c0.withHooks H) := fnDet_of_coherent coherent

theorem headsOK : HeadsOK (c0.withHooks H) ((c0.withHooks H).fns.map Fn.sig) := fun k hk => by
  obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hk
  exact ⟨g, List.mem_append_left _ hg, rfl⟩

def σn (n : Int) : Subst := [(0, int n)]

theorem wsn (n : Int) : (c0.withHooks H).WellSorted [Srt.int] (σn n) := fun j s hs => by
  match j, hs with
  | 0, hs => cases hs; exact ⟨_, rfl, sortOf_int n⟩

/-- A term over X evaluated at `X := n` gives its result at any σ that gives X the value n. -/
theorem at_τ {t : Term} (ht : varOccs t = [0]) {n : Int} {r : Option GroundTerm} (h : EvalTerm (c0.withHooks H) (σn n) t r)
    {τ : Subst} (h0 : τ.lookup 0 = some (int n)) : EvalTerm (c0.withHooks H) τ t r :=
  Exec.EvalTerm.congr h fun i hi => by
    rw [ht, List.mem_singleton] at hi
    subst hi
    exact h0.symm

/-- The executable evaluation on the parsed data reads no interpretation (`Cert.evalTC_withHooks`):
its result is the evaluation's under every H. -/
theorem evalAt {n : Nat} {σ : Subst} {t : Term} {r : Option GroundTerm} (h : Cert.evalTC c0 n σ t = some r) :
    Exec.evalT (c0.withHooks H) n σ t = some r :=
  Cert.evalTC_sound n ((Cert.evalTC_withHooks c0 H noRaw0 n σ t).trans h)

/-- The sort of a term in the definition's context does not read the interpretation. -/
theorem sortAt {vars : List Srt} {t : Term} {s : Srt}
    (h : sortOfTerm (c0.rhsCtx (c0.fns.map Fn.sig)) vars t = some s) :
    sortOfTerm ((c0.withHooks H).rhsCtx ((c0.withHooks H).fns.map Fn.sig)) vars t = some s := h

theorem f0 : EvalTerm (c0.withHooks H) (σn 0) fX (some (int 0)) :=
  Exec.evalT_sound hsc hcc hmc 20 (evalAt (by decide +kernel)) headsOK (wsn 0) (s := Srt.int) (sortAt (by decide +kernel))
theorem g0 : EvalTerm (c0.withHooks H) (σn 0) gX (some (int 0)) :=
  Exec.evalT_sound hsc hcc hmc 20 (evalAt (by decide +kernel)) headsOK (wsn 0) (s := Srt.int) (sortAt (by decide +kernel))
theorem f1 : EvalTerm (c0.withHooks H) (σn 1) fX (some (int 1)) :=
  Exec.evalT_sound hsc hcc hmc 20 (evalAt (by decide +kernel)) headsOK (wsn 1) (s := Srt.int) (sortAt (by decide +kernel))
theorem g1 : EvalTerm (c0.withHooks H) (σn 1) gX (some (int (-1))) :=
  Exec.evalT_sound hsc hcc hmc 20 (evalAt (by decide +kernel)) headsOK (wsn 1) (s := Srt.int) (sortAt (by decide +kernel))

/-! #### The steps -/

/-- `<k> go(n) </k>`; `<k> n </k>`. -/
def goCfg (n : Int) : GroundTerm := cfgOf kCell exp (.ctor symGo [int n])
def resCfg (n : Int) : GroundTerm := cfgOf kCell Srt.int (int n)

def Go0 : Config (c0.withHooks H) := ⟨goCfg 0, by whd⟩
def Go1 : Config (c0.withHooks H) := ⟨goCfg 1, by whd⟩
def Zero : Config (c0.withHooks H) := ⟨resCfg 0, by whd⟩

def σ0 : Subst := [(0, int 0), (1, dotkT), (2, ctr), (3, int 0)]

/-- **`go(0)` steps to `0`**: X := 0, Z := 0, the value both conjuncts have there. -/
theorem stepBy0 : StepBy (c0.withHooks H) r0 σ0 Go0 Zero where
  mem := r0_mem
  hσ := fun j s hs => by
    rw [r0_vars] at hs
    match j, hs with
    | 0, hs => cases hs; exact ⟨_, rfl, sortOf_int 0⟩
    | 1, hs => cases hs; exact ⟨_, rfl, by whd⟩
    | 2, hs => cases hs; exact ⟨_, rfl, by whd⟩
    | 3, hs => cases hs; exact ⟨_, rfl, sortOf_int 0⟩
  hmatch := by
    rw [r0_lhs]
    have hi : injNormal exp Srt.kitem (.ctor symGo [int 0]) = .inj exp Srt.kitem (.ctor symGo [int 0]) := rfl
    exact .ctor syms_ok.1 (.cons (.ctor syms_ok.2.1 (.cons (.ctor syms_ok.2.2.1
      (.cons (hi ▸ .inj (.ctor syms_ok.2.2.2 (.cons (.var rfl) .nil))) (.cons (.var rfl) .nil))) .nil))
      (.cons (.var rfl) .nil))
  hreq := fun t ht => by rw [r0_shape.1] at ht; cases ht
  hpre := by rw [r0_shape.2.2.1]; exact .top
  heval := by
    rw [r0_rhs]
    have he : EvalTerm (c0.withHooks H) σ0 (.inj Srt.int Srt.kitem (.var 3)) (some (.inj Srt.int Srt.kitem (int 0))) := .inj .var
    exact .ctor syms_ok.1 (.cons (.ctor syms_ok.2.1 (.cons (.ctor syms_ok.2.2.1
      (.cons he (.cons .var .nil))) .nil)) (.cons .var .nil))
  hens := fun t ht => by rw [r0_shape.2.1] at ht; cases ht
  hpost := by
    rw [r0_shape.2.2.2.2]
    have h : Holds (c0.withHooks H) r0.vars.length σ0 (.and (.mem Srt.int (.var 3) fX) (.mem Srt.int (.var 3) gX))
        (((σ0.lookup 3).isSome && sameResult (σ0.lookup 3) (some (int 0))) &&
          ((σ0.lookup 3).isSome && sameResult (σ0.lookup 3) (some (int 0)))) :=
      .and (.mem .var (at_τ rfl f0 rfl)) (.mem .var (at_τ rfl g0 rfl))
    have hb : (((σ0.lookup 3).isSome && sameResult (σ0.lookup 3) (some (int 0))) &&
        ((σ0.lookup 3).isSome && sameResult (σ0.lookup 3) (some (int 0)))) = true := by
      show ((true && sameResult (some (int 0)) (some (int 0))) && (true && sameResult (some (int 0)) (some (int 0)))) = true
      rw [sameResult_some]; simp
    rwa [hb] at h
  hprio := fun r' hr' hlt => by
    rw [prios.2 r' hr', prios.2 r0 r0_mem] at hlt; exact absurd hlt (Nat.lt_irrefl _)

theorem step_go0 : Step (c0.withHooks H) Go0 Zero := step_iff_by.mpr ⟨r0, σ0, stepBy0⟩

/-- **A step by the rule from `go(n)`**, where f(n) is n and g(n) is m: n = m, and the successor
is `n`. -/
theorem go_inv {n m : Int} (hf : EvalTerm (c0.withHooks H) (σn n) fX (some (int n))) (hg : EvalTerm (c0.withHooks H) (σn n) gX (some (int m)))
    {τ : Subst} {x y : Config (c0.withHooks H)} (hx : x.val = goCfg n) (hs : StepBy (c0.withHooks H) r0 τ x y) :
    n = m ∧ y.val = resCfg n := by
  have hm := hs.hmatch
  rw [r0_lhs, hx] at hm
  obtain ⟨⟨w, hw, hwe⟩, hk, hc⟩ := patVal_cfgPat ⟨syms_ok.1, syms_ok.2.1, syms_ok.2.2.1⟩
    ⟨hooks_ok.1, hooks_ok.2.1, hooks_ok.2.2.1⟩ hm
  obtain ⟨-, vs, rfl, hvs⟩ := PatVal.app_inv hooks_ok.2.2.2 hw syms_ok.2.2.2
  have hwe' : GroundTerm.inj exp Srt.kitem (.ctor symGo vs) = .inj exp Srt.kitem (.ctor symGo [int n]) := hwe
  cases hwe'
  obtain ⟨_, _, he1, h0, _⟩ := PatVals.cons_inv hvs
  cases he1
  have hl0 := PatVal.var_inv h0
  obtain ⟨v, hl3, -⟩ := hs.hσ 3 Srt.int (by rw [r0_vars]; rfl)
  have hp := hs.hpost
  rw [r0_shape.2.2.2.2] at hp
  obtain ⟨b₁, b₂, h₁, h₂, hb⟩ := holds_and_inv hp
  obtain ⟨r₁, r₁', e₁, e₁', rfl⟩ := holds_mem_inv h₁
  obtain ⟨r₂, r₂', e₂, e₂', rfl⟩ := holds_mem_inv h₂
  rw [EvalTerm.var_inv e₁, EvalTerm.var_inv e₂, hl3, EvalTerm.functional_of_fnDet fnDet e₁' (at_τ rfl hf hl0),
    EvalTerm.functional_of_fnDet fnDet e₂' (at_τ rfl hg hl0)] at hb
  simp only [Option.isSome_some, Bool.true_and, sameResult_some] at hb
  have hv : v = int n ∧ v = int m := by simpa using hb.symm
  obtain ⟨rfl, hvm⟩ := hv
  have he := hs.heval
  rw [r0_rhs] at he
  obtain ⟨w', hw', hy⟩ := evalTerm_cfgPat ⟨syms_ok.1, syms_ok.2.1, syms_ok.2.2.1⟩ hk hc he
  have hw'' : some w' = some (int n) := (EvalTerm.var_inv hw').trans hl3
  cases hw''
  have hnm : n = m := by simpa [int] using hvm
  exact ⟨hnm, hy⟩

/-- **The successor of `go(0)` is `0`, and only it.** -/
theorem step_go0_iff (y : Config (c0.withHooks H)) : Step (c0.withHooks H) Go0 y ↔ y = Zero := by
  constructor
  · intro h
    obtain ⟨r, τ, hs⟩ := step_iff_by.mp h
    rw [rule_eq hs.mem] at hs
    exact Subtype.ext (go_inv f0 g0 rfl hs).2
  · rintro rfl; exact step_go0

/-- **`go(1)` has no successor**: f(1) = 1 and g(1) = -1 have no common value. -/
theorem stuck_go1 : ∀ y, ¬ Step (c0.withHooks H) Go1 y := fun y h => by
  obtain ⟨r, τ, hs⟩ := step_iff_by.mp h
  rw [rule_eq hs.mem] at hs
  exact absurd (go_inv f1 g1 rfl hs).1 (by decide)


/-- info: 'RuleAndStepH.MlAndT.step_go0_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms step_go0_iff
/-- info: 'RuleAndStepH.MlAndT.stuck_go1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms stuck_go1

end MlAndT

/-! ## e3-ml-rule-rhs-and-var -/

namespace MlAndV
open KCore.TieRuleLhs (cfgH)

definition_of defn from "f2-examples/e3-ml-rule-rhs-and-var.kompile.kore"

noncomputable abbrev c0 : Semantics := defn.sem

theorem noRaw0 : ∀ k ∈ c0.params, k.raw = false := by decide +kernel

theorem names_ok : c0.sortName exp = "Exp" ∧ c0.symName kCell = "Lbl'-LT-'k'-GT-'" ∧
    c0.symName symA = "Lbla" ∧ c0.symName symB = "Lblb" ∧ c0.symName symC = "Lblc" := by
  decide +kernel

/-- The rule as read: `c(X) => X`, X the variable 0, no `ensures`, no existential variable, and
`post` the membership `X ∈ a()`. -/
theorem read_shape : c0.rules.map (fun r => (r.lhs, r.rhs, r.ens.isNone, r.exs, r.post)) =
    [(cfgPat kCell exp (.app symC [.var 0]) 1 2, cfgPat kCell exp (.var 0) 1 2, true, [],
      .mem exp (.var 0) (.app symA []))] := rfl

theorem hready : CExec.execReady c0 = true := by decide +kernel
theorem noFns : c0.fns = [] := by decide +kernel
/-- The text declares no function, so evaluation has one result under every interpretation. -/
theorem fnDetH (H : HookParams) : FnDet (c0.withHooks H) :=
  fnDet_of_agree (fun _ h => by rw [show (c0.withHooks H).fns = c0.fns from rfl, noFns] at h; cases h)
    (fun _ h => by rw [show (c0.withHooks H).fns = c0.fns from rfl, noFns] at h; cases h)

def CA : Config c0 := ⟨cfg (.ctor symC [aT]), by decide +kernel⟩
def CB : Config c0 := ⟨cfg (.ctor symC [bT]), by decide +kernel⟩
def A : Config c0 := ⟨cfg aT, by decide +kernel⟩

kernel_rfl ca_withHooks : ∀ H : HookParams,
  CExec.successorsN (c0.withHooks H) 50 CA.val = CExec.successorsN c0 50 CA.val
kernel_rfl cb_withHooks : ∀ H : HookParams,
  CExec.successorsN (c0.withHooks H) 50 CB.val = CExec.successorsN c0 50 CB.val
kernel_rfl cb_fuel_withHooks : ∀ H : HookParams,
  CExec.outOfFuel (c0.withHooks H) 50 CB.val = CExec.outOfFuel c0 50 CB.val

/-- **`andTermsCut` in the variable form, for every interpretation**: `<k> c(a) </k>` steps to
`<k> a </k>` and `<k> c(b) </k>` has no successor: `a() ∧ X` is X where X is `a` and is empty
elsewhere. -/
theorem andVar_steps (H : HookParams) :
    Step (c0.withHooks H) (cfgH noRaw0 CA H) (cfgH noRaw0 A H) ∧
    ∀ y, ¬ Step (c0.withHooks H) (cfgH noRaw0 CB H) y := by
  have hr := (CExec.execReady_withHooks c0 H).trans hready
  refine ⟨?_, CExec.noStep_at hr (fnDetH H) (n := 50) (x := cfgH noRaw0 CB H)
    ((cb_fuel_withHooks H).trans (by decide +kernel)) ((cb_withHooks H).trans (by decide +kernel))⟩
  have hy : A.val ∈ CExec.successorsN (c0.withHooks H) 50 CA.val := by
    rw [ca_withHooks]; decide +kernel
  obtain ⟨_, h⟩ := CExec.successorsN_step_ready hr (x := cfgH noRaw0 CA H) hy
  exact h

/-- info: 'RuleAndStepH.MlAndV.andVar_steps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms andVar_steps

end MlAndV

end RuleAndStepH

