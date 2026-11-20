/-
  The steps of the rules read through `connectiveCut` (test/PredFixtures.lean's `LhsNot`,
  `LhsNotOther` and `RhsOr`), under every interpretation of the parameters: K 7.1.337 kompile's
  texts of the fixtures e3-ml-rule-lhs-not, e3-ml-rule-lhs-not-other and e3-ml-rule-rhs-or, read by
  the reader, each statement over `c0.withHooks H` for every `H : HookParams`, `c0` the reading.
  Run from the package root: `lake env lean -j1 test/RuleConnStepH.lean`.

  ## Why no statement depends on H
  An interpretation enters evaluation in three places: a parameter symbol without a registry hook
  (`Semantics.paramVal`), an interpreted symbol at a silent point (`Semantics.hookRes`), and the
  sort of an open generator's application (`Semantics.sortOf`). The three texts declare no function
  and no parameter that is an open generator (`noRaw0`), and the rules' sides and the memberships
  of `pre` and `post` apply constructors only (`syms_ok`), so matching and evaluation read no hook
  and every value has the sort the parsed data gives it (`sortOf_eq`). The proofs are those of
  test/PredFixtures.lean with the semantics `c0.withHooks H`.

  - `LhsNot` (`f2-examples/e3-ml-rule-lhs-not.kompile.kore`, `rule <k> c(#Not(a())) => a() ... </k>`,
    kompiled as `c(\not(\and(a(), _Gen5))) => _Gen5`): sentence 104 is read as `c(Z) => G` with
    `pre := ¬(Z ∈ a() ∧ Z ∈ G)` (`r0_shape`). `step_iff`: for all values z and g of Exp,
    `<k> c(z) </k>` steps to `<k> g </k>` exactly where not (z = a and g = a).
  - `LhsNotOther` (`f2-examples/e3-ml-rule-lhs-not-other.kompile.kore`,
    `rule <k> c(#Not(a())) => b() ... </k>`): sentence 104 is read as `c(Z) => b` with
    `pre := ¬(Z ∈ a())` (`r0_shape`). `step_iff`: for every value z of Exp and every configuration
    y, `<k> c(z) </k>` steps to y exactly where z is not `a` and y is `<k> b </k>`.
  - `RhsOr` (`f2-examples/e3-ml-rule-rhs-or.kompile.kore`, `rule <k> go => a() #Or b() ... </k>`):
    sentence 109 is read as `go => ?Z` with `post := Z ∈ a() ∨ Z ∈ b()` (`r0_shape`). `step_iff`:
    the successors of `<k> go </k>` are `<k> a </k>` and `<k> b </k>`, and nothing else.

  test/TieRuleConn.lean ties Γ's item of each rule to its sentence for every H
  (`LhsNot.rule_from_text_sig`, `LhsNotOther.rule_from_text_sig`, `RhsOr.rule_from_text_sig`, on
  f2-examples/mlnot, mlnoto and mlror, which are these three files byte for byte).
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

open KCore
open ML Faithful

namespace RuleConnStepH
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

/-! ## e3-ml-rule-lhs-not -/

namespace LhsNot

definition_of defn from "f2-examples/e3-ml-rule-lhs-not.kompile.kore"

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

def exp : Srt := 32
def kCell : Sym := 383
def symA : Sym := 385
def symC : Sym := 387

theorem names_ok : c0.sortName exp = "Exp" ∧ c0.symName kCell = "Lbl'-LT-'k'-GT-'" ∧
    c0.symName symA = "Lbla" ∧ c0.symName symC = "Lblc" := by
  decide +kernel
noncomputable def r0 : Rule := c0.rules[0]'(by decide +kernel)

theorem r0_mem : r0 ∈ (c0.withHooks H).rules := List.getElem_mem _

/-- The text has the one rule. -/
theorem rule_eq {r : Rule} (hr : r ∈ (c0.withHooks H).rules) : r = r0 := by
  rw [rules_wh] at hr
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hr
  have h1 : c0.rules.length = 1 := by decide +kernel
  have : i = 0 := by omega
  subst this
  rfl

theorem r0_vars : r0.vars = [exp, Srt.k, 19, exp] := by whd
theorem r0_lhs : r0.lhs = cfgPat kCell exp (.app symC [.var 0]) 1 2 := rfl
theorem r0_rhs : r0.rhs = cfgPat kCell exp (.var 3) 1 2 := rfl
/-- `pre := not (and (mem Z a) (mem Z G))`, Z the variable 0, G the variable 3. -/
theorem r0_shape : r0.req = none ∧ r0.ens = none ∧ r0.exs = [] ∧ r0.post = .top ∧
    r0.pre = .not (.and (.mem exp (.var 0) (.app symA [])) (.mem exp (.var 0) (.var 3))) :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem syms_ok : (c0.withHooks H).isCtor topLabel = true ∧ (c0.withHooks H).isCtor kCell = true ∧ (c0.withHooks H).isCtor kseq = true ∧
    (c0.withHooks H).isCtor symA = true ∧ (c0.withHooks H).isCtor symC = true ∧ (c0.withHooks H).isCtor dotk = true ∧ (c0.withHooks H).isCtor counterLabel = true := by
  whd

theorem hooks_ok : patternHooks.contains topLabel = false ∧ patternHooks.contains kCell = false ∧
    patternHooks.contains kseq = false ∧ patternHooks.contains symC = false := by
  whd

theorem lookups_ok : (lookupSig (c0.withHooks H).ctorSigs topLabel).isSome = true ∧ (lookupSig (c0.withHooks H).ctorSigs kCell).isSome = true ∧
    (lookupSig (c0.withHooks H).ctorSigs kseq).isSome = true ∧ (lookupSig (c0.withHooks H).ctorSigs symC).isSome = true := by
  whd

/-- No sort lies below Exp. -/
theorem exp_bottom : ∀ p ∈ (c0.withHooks H).subsorts, p.2 ≠ exp := by
  intro p hp
  have h : (c0.withHooks H).subsorts.all (fun p => p.2 != exp) = true := by whd
  simpa using List.all_eq_true.mp h p hp

/-! ### The configurations -/

def A : GroundTerm := .ctor symA []
def ctr : GroundTerm := .ctor counterLabel [int 0]
def cfg (st : GroundTerm) : GroundTerm := cfgOf kCell exp st

theorem sortOf_A : (c0.withHooks H).sortOf A = some exp := by whd

theorem sortOf_cfg {g : GroundTerm} (hg : (c0.withHooks H).sortOf g = some exp) : (c0.withHooks H).sortOf (cfg g) = some topCellSort := by
  have h0 : (c0.withHooks H).sortOf (cfg A) = some topCellSort := by whd
  rw [← h0]
  exact sortOf_cfgOf_congr ⟨lookups_ok.1, lookups_ok.2.1, lookups_ok.2.2.1⟩ (by rw [hg, sortOf_A])
    (by rw [isInj_of_sort exp_bottom hg]; rfl)

theorem sortOf_cfgC {z : GroundTerm} (hz : (c0.withHooks H).sortOf z = some exp) :
    (c0.withHooks H).sortOf (cfg (.ctor symC [z])) = some topCellSort := by
  have h0 : (c0.withHooks H).sortOf (cfg (.ctor symC [A])) = some topCellSort := by whd
  rw [← h0]
  exact sortOf_cfgOf_congr ⟨lookups_ok.1, lookups_ok.2.1, lookups_ok.2.2.1⟩
    (sortOf_ctor_congr lookups_ok.2.2.2 (sortsOf_head_congr (by rw [hz, sortOf_A]))) rfl

/-- `<k> (c0.withHooks H)(z) </k>`. -/
def C (z : GroundTerm) (hz : (c0.withHooks H).sortOf z = some exp) : Config (c0.withHooks H) := ⟨cfg (.ctor symC [z]), sortOf_cfgC hz⟩
/-- `<k> g </k>`. -/
def G (g : GroundTerm) (hg : (c0.withHooks H).sortOf g = some exp) : Config (c0.withHooks H) := ⟨cfg g, sortOf_cfg hg⟩

/-! ### The step -/

def σ (z g : GroundTerm) : Subst := [(0, z), (1, .ctor dotk []), (2, ctr), (3, g)]

/-- `pre` under any σ: false exactly where σ gives Z the value `a` and G the value Z has. -/
theorem pre_holds (τ : Subst) : Holds (c0.withHooks H) r0.vars.length τ r0.pre
    (!(((τ.lookup 0).isSome && sameResult (τ.lookup 0) (some A)) &&
      ((τ.lookup 0).isSome && sameResult (τ.lookup 0) (τ.lookup 3)))) := by
  rw [r0_shape.2.2.2.2]
  exact .not (.and (.mem .var (.ctor syms_ok.2.2.2.1 .nil)) (.mem .var .var))

/-- The truth value of `pre` under any σ is `pre_holds`'s. -/
theorem pre_val {τ : Subst} {b : Bool} (h : Holds (c0.withHooks H) r0.vars.length τ r0.pre b) :
    b = (!(((τ.lookup 0).isSome && sameResult (τ.lookup 0) (some A)) &&
      ((τ.lookup 0).isSome && sameResult (τ.lookup 0) (τ.lookup 3)))) := by
  rw [r0_shape.2.2.2.2] at h
  obtain ⟨b', hp, rfl⟩ := holds_not_inv h
  obtain ⟨b₁, b₂, h₁, h₂, rfl⟩ := holds_and_inv hp
  obtain ⟨r₁, r₁', e₁, e₁', rfl⟩ := holds_mem_inv h₁
  obtain ⟨r₂, r₂', e₂, e₂', rfl⟩ := holds_mem_inv h₂
  rw [EvalTerm.var_inv e₁, evalTerm_const syms_ok.2.2.2.1 e₁', EvalTerm.var_inv e₂, EvalTerm.var_inv e₂']
  rfl

/-- `pre` where σ gives Z the value z and G the value g. -/
theorem pre_at {τ : Subst} {z g : GroundTerm} (h0 : τ.lookup 0 = some z) (h3 : τ.lookup 3 = some g) {b : Bool} :
    Holds (c0.withHooks H) r0.vars.length τ r0.pre b ↔ b = !(decide (z = A) && decide (z = g)) := by
  constructor
  · intro h
    rw [pre_val h, h0, h3]
    simp only [Option.isSome_some, Bool.true_and, sameResult_some]
  · intro hb
    have h := pre_holds (H := H) τ
    rw [h0, h3] at h
    simp only [Option.isSome_some, Bool.true_and, sameResult_some] at h
    rw [hb]; exact h

theorem prio_none {r' : Rule} (hr' : r' ∈ (c0.withHooks H).rules) (hlt : r'.prio < r0.prio) : False := by
  rw [rule_eq hr'] at hlt
  exact Nat.lt_irrefl _ hlt

theorem stepBy {z g : GroundTerm} (hz : (c0.withHooks H).sortOf z = some exp) (hg : (c0.withHooks H).sortOf g = some exp)
    (hne : ¬ (z = A ∧ g = A)) : StepBy (c0.withHooks H) r0 (σ z g) (C z hz) (G g hg) where
  mem := r0_mem
  hσ := fun j s hs => by
    rw [r0_vars] at hs
    match j, hs with
    | 0, hs => cases hs; exact ⟨_, rfl, hz⟩
    | 1, hs => cases hs; exact ⟨_, rfl, by whd⟩
    | 2, hs => cases hs; exact ⟨_, rfl, by whd⟩
    | 3, hs => cases hs; exact ⟨_, rfl, hg⟩
  hmatch := by
    rw [r0_lhs]
    have hiz : injNormal exp Srt.kitem (.ctor symC [z]) = .inj exp Srt.kitem (.ctor symC [z]) := rfl
    exact .ctor syms_ok.1 (.cons (.ctor syms_ok.2.1 (.cons (.ctor syms_ok.2.2.1
      (.cons (hiz ▸ .inj (.ctor syms_ok.2.2.2.2.1 (.cons (.var rfl) .nil))) (.cons (.var rfl) .nil))) .nil))
      (.cons (.var rfl) .nil))
  hreq := fun t ht => by rw [r0_shape.1] at ht; cases ht
  hpre := (pre_at rfl rfl).mpr (by
    by_cases ha : z = A
    · subst ha
      have : g ≠ A := fun h => hne ⟨rfl, h⟩
      simp [Ne.symm this]
    · simp [ha])
  heval := by
    rw [r0_rhs]
    have hig : injNormal exp Srt.kitem g = .inj exp Srt.kitem g := injNormal_of_not_inj (isInj_of_sort exp_bottom hg)
    have he : EvalTerm (c0.withHooks H) (σ z g) (.inj exp Srt.kitem (.var 3)) (((σ z g).lookup 3).map (injNormal exp Srt.kitem)) :=
      .inj .var
    have hv : ((σ z g).lookup 3).map (injNormal exp Srt.kitem) = some (.inj exp Srt.kitem g) := by
      show (some g).map _ = _
      rw [Option.map_some, hig]
    rw [hv] at he
    exact .ctor syms_ok.1 (.cons (.ctor syms_ok.2.1 (.cons (.ctor syms_ok.2.2.1
      (.cons he (.cons .var .nil))) .nil)) (.cons .var .nil))
  hens := fun t ht => by rw [r0_shape.2.1] at ht; cases ht
  hpost := by rw [r0_shape.2.2.2.1]; exact .top
  hprio := fun r' hr' hlt => (prio_none hr' hlt).elim

/-- A match of the left side at `<k> (c0.withHooks H)(z) </k>` gives Z the value z. -/
theorem lookup0 {τ : Subst} {z : GroundTerm} (hm : PatVal (c0.withHooks H) τ r0.lhs (cfg (.ctor symC [z]))) :
    τ.lookup 0 = some z := by
  rw [r0_lhs] at hm
  have h1 := (patVal_ctor2 hooks_ok.1 syms_ok.1 hm).1
  have h2 := patVal_ctor1 hooks_ok.2.1 syms_ok.2.1 h1
  have h3 := (patVal_ctor2 hooks_ok.2.2.1 syms_ok.2.2.1 h2).1
  obtain ⟨w, hw, he⟩ := PatVal.inj_inv h3
  obtain ⟨-, vs, rfl, hs⟩ := PatVal.app_inv hooks_ok.2.2.2 hw syms_ok.2.2.2.2.1
  have he' : GroundTerm.inj exp Srt.kitem (.ctor symC [z]) = .inj exp Srt.kitem (.ctor symC vs) := he
  cases he'
  obtain ⟨_, _, he1, h4, _⟩ := PatVals.cons_inv hs
  cases he1
  exact PatVal.var_inv h4

/-- An evaluation of the right side to `<k> g </k>` gives G the value g. -/
theorem lookup3 {τ : Subst} {g : GroundTerm} (hτ : (c0.withHooks H).WellSorted r0.vars τ)
    (he : EvalTerm (c0.withHooks H) τ r0.rhs (some (cfg g))) : τ.lookup 3 = some g := by
  obtain ⟨v₃, hl₃, hv₃⟩ := hτ 3 exp (by rw [r0_vars]; rfl)
  rw [r0_rhs] at he
  have h1 := (evalTerm_ctor2 syms_ok.1 he).1
  have h2 := evalTerm_ctor1 syms_ok.2.1 h1
  have h3 := (evalTerm_ctor2 syms_ok.2.2.1 h2).1
  obtain ⟨r', h4, hr⟩ := EvalTerm.inj_inv h3
  rw [EvalTerm.var_inv h4] at hr
  cases hl : τ.lookup 3 with
  | none => rw [hl] at hr; cases hr
  | some v =>
    rw [hl] at hr
    simp only [Option.map_some, Option.some.injEq] at hr
    cases v with
    | inj a b w =>
      rw [hl] at hl₃
      cases hl₃
      cases isInj_of_sort exp_bottom hv₃
    | _ => simp only [injNormal] at hr; cases hr; rfl

/-- **`<k> (c0.withHooks H)(z) </k>` steps to `<k> g </k>` exactly where not (z = a and g = a)**, for all values z
and g of Exp. -/
theorem step_iff {z g : GroundTerm} (hz : (c0.withHooks H).sortOf z = some exp) (hg : (c0.withHooks H).sortOf g = some exp) :
    Step (c0.withHooks H) (C z hz) (G g hg) ↔ ¬ (z = A ∧ g = A) := by
  constructor
  · intro h ⟨hza, hga⟩
    obtain ⟨r, τ, hs⟩ := step_iff_by.mp h
    have hr := rule_eq hs.mem
    subst hr
    have h0 := lookup0 hs.hmatch
    have h3 := lookup3 hs.hσ hs.heval
    have hf := (pre_at h0 h3).mp hs.hpre
    rw [hza, hga] at hf
    simp at hf
  · intro hne
    exact step_iff_by.mpr ⟨r0, σ z g, stepBy hz hg hne⟩


/-- info: 'RuleConnStepH.LhsNot.step_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms step_iff

end LhsNot

/-! ## e3-ml-rule-lhs-not-other -/

namespace LhsNotOther

definition_of defn from "f2-examples/e3-ml-rule-lhs-not-other.kompile.kore"

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

def exp : Srt := 32
def kCell : Sym := 383
def symA : Sym := 385
def symB : Sym := 386
def symC : Sym := 387

theorem names_ok : c0.sortName exp = "Exp" ∧ c0.symName kCell = "Lbl'-LT-'k'-GT-'" ∧
    c0.symName symA = "Lbla" ∧ c0.symName symB = "Lblb" ∧ c0.symName symC = "Lblc" := by
  decide +kernel

noncomputable def r0 : Rule := c0.rules[0]'(by decide +kernel)

theorem r0_mem : r0 ∈ (c0.withHooks H).rules := List.getElem_mem _

/-- The text has the one rule. -/
theorem rule_eq {r : Rule} (hr : r ∈ (c0.withHooks H).rules) : r = r0 := by
  rw [rules_wh] at hr
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hr
  have h1 : c0.rules.length = 1 := by decide +kernel
  have : i = 0 := by omega
  subst this
  rfl

theorem r0_vars : r0.vars = [exp, Srt.k, 19] := by whd
theorem r0_lhs : r0.lhs = cfgPat kCell exp (.app symC [.var 0]) 1 2 := rfl
theorem r0_rhs : r0.rhs = cfgPat kCell exp (.app symB []) 1 2 := rfl
/-- `pre := not (mem Z a)`, Z the variable 0. -/
theorem r0_shape : r0.req = none ∧ r0.ens = none ∧ r0.exs = [] ∧ r0.post = .top ∧
    r0.pre = .not (.mem exp (.var 0) (.app symA [])) :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem syms_ok : (c0.withHooks H).isCtor topLabel = true ∧ (c0.withHooks H).isCtor kCell = true ∧ (c0.withHooks H).isCtor kseq = true ∧
    (c0.withHooks H).isCtor symA = true ∧ (c0.withHooks H).isCtor symB = true ∧ (c0.withHooks H).isCtor symC = true := by
  whd

theorem hooks_ok : patternHooks.contains topLabel = false ∧ patternHooks.contains kCell = false ∧
    patternHooks.contains kseq = false ∧ patternHooks.contains symC = false := by
  whd

theorem lookups_ok : (lookupSig (c0.withHooks H).ctorSigs topLabel).isSome = true ∧ (lookupSig (c0.withHooks H).ctorSigs kCell).isSome = true ∧
    (lookupSig (c0.withHooks H).ctorSigs kseq).isSome = true ∧ (lookupSig (c0.withHooks H).ctorSigs symC).isSome = true := by
  whd

/-! ### The configurations -/

def A : GroundTerm := .ctor symA []
def B : GroundTerm := .ctor symB []
def cfg (st : GroundTerm) : GroundTerm := cfgOf kCell exp st

theorem sortOf_A : (c0.withHooks H).sortOf A = some exp := by whd

theorem sortOf_cfgC {z : GroundTerm} (hz : (c0.withHooks H).sortOf z = some exp) :
    (c0.withHooks H).sortOf (cfg (.ctor symC [z])) = some topCellSort := by
  have h0 : (c0.withHooks H).sortOf (cfg (.ctor symC [A])) = some topCellSort := by whd
  rw [← h0]
  exact sortOf_cfgOf_congr ⟨lookups_ok.1, lookups_ok.2.1, lookups_ok.2.2.1⟩
    (sortOf_ctor_congr lookups_ok.2.2.2 (sortsOf_head_congr (by rw [hz, sortOf_A]))) rfl

/-- `<k> (c0.withHooks H)(z) </k>`. -/
def C (z : GroundTerm) (hz : (c0.withHooks H).sortOf z = some exp) : Config (c0.withHooks H) := ⟨cfg (.ctor symC [z]), sortOf_cfgC hz⟩
/-- `<k> b </k>`. -/
def Bc : Config (c0.withHooks H) := ⟨cfg B, by whd⟩

/-! ### The step -/

def σ (z : GroundTerm) : Subst := [(0, z), (1, .ctor dotk []), (2, .ctor counterLabel [int 0])]

/-- `pre` where σ gives Z the value z: true exactly where z is not `a`. -/
theorem pre_at {τ : Subst} {z : GroundTerm} (h0 : τ.lookup 0 = some z) {b : Bool} :
    Holds (c0.withHooks H) r0.vars.length τ r0.pre b ↔ b = !(decide (z = A)) := by
  rw [r0_shape.2.2.2.2]
  constructor
  · intro h
    obtain ⟨b', hp, rfl⟩ := holds_not_inv h
    obtain ⟨r₁, r₁', e₁, e₁', rfl⟩ := holds_mem_inv hp
    rw [EvalTerm.var_inv e₁, evalTerm_const syms_ok.2.2.2.1 e₁', h0]
    simp only [Option.isSome_some, Bool.true_and, sameResult_some]
    rfl
  · intro hb
    have h : Holds (c0.withHooks H) r0.vars.length τ (.not (.mem exp (.var 0) (.app symA [])))
        (!((τ.lookup 0).isSome && sameResult (τ.lookup 0) (some A))) :=
      .not (.mem .var (.ctor syms_ok.2.2.2.1 .nil))
    rw [h0] at h
    simp only [Option.isSome_some, Bool.true_and, sameResult_some] at h
    rw [hb]; exact h

theorem stepBy {z : GroundTerm} (hz : (c0.withHooks H).sortOf z = some exp) (hne : z ≠ A) :
    StepBy (c0.withHooks H) r0 (σ z) (C z hz) Bc where
  mem := r0_mem
  hσ := fun j s hs => by
    rw [r0_vars] at hs
    match j, hs with
    | 0, hs => cases hs; exact ⟨_, rfl, hz⟩
    | 1, hs => cases hs; exact ⟨_, rfl, by whd⟩
    | 2, hs => cases hs; exact ⟨_, rfl, by whd⟩
  hmatch := by
    rw [r0_lhs]
    have hiz : injNormal exp Srt.kitem (.ctor symC [z]) = .inj exp Srt.kitem (.ctor symC [z]) := rfl
    exact .ctor syms_ok.1 (.cons (.ctor syms_ok.2.1 (.cons (.ctor syms_ok.2.2.1
      (.cons (hiz ▸ .inj (.ctor syms_ok.2.2.2.2.2 (.cons (.var rfl) .nil))) (.cons (.var rfl) .nil))) .nil))
      (.cons (.var rfl) .nil))
  hreq := fun t ht => by rw [r0_shape.1] at ht; cases ht
  hpre := (pre_at rfl).mpr (by simp [hne])
  heval := by
    rw [r0_rhs]
    have he : EvalTerm (c0.withHooks H) (σ z) (.inj exp Srt.kitem (.app symB [])) (some (.inj exp Srt.kitem B)) :=
      .inj (.ctor syms_ok.2.2.2.2.1 .nil)
    exact .ctor syms_ok.1 (.cons (.ctor syms_ok.2.1 (.cons (.ctor syms_ok.2.2.1
      (.cons he (.cons .var .nil))) .nil)) (.cons .var .nil))
  hens := fun t ht => by rw [r0_shape.2.1] at ht; cases ht
  hpost := by rw [r0_shape.2.2.2.1]; exact .top
  hprio := fun r' hr' hlt => absurd hlt (by rw [rule_eq hr']; exact Nat.lt_irrefl _)

/-- A match of the left side at `<k> (c0.withHooks H)(z) </k>` gives Z the value z. -/
theorem lookup0 {τ : Subst} {z : GroundTerm} (hm : PatVal (c0.withHooks H) τ r0.lhs (cfg (.ctor symC [z]))) :
    τ.lookup 0 = some z := by
  rw [r0_lhs] at hm
  have h1 := (patVal_ctor2 hooks_ok.1 syms_ok.1 hm).1
  have h2 := patVal_ctor1 hooks_ok.2.1 syms_ok.2.1 h1
  have h3 := (patVal_ctor2 hooks_ok.2.2.1 syms_ok.2.2.1 h2).1
  obtain ⟨w, hw, he⟩ := PatVal.inj_inv h3
  obtain ⟨-, vs, rfl, hs⟩ := PatVal.app_inv hooks_ok.2.2.2 hw syms_ok.2.2.2.2.2
  have he' : GroundTerm.inj exp Srt.kitem (.ctor symC [z]) = .inj exp Srt.kitem (.ctor symC vs) := he
  cases he'
  obtain ⟨_, _, he1, h4, _⟩ := PatVals.cons_inv hs
  cases he1
  exact PatVal.var_inv h4

/-- **`<k> (c0.withHooks H)(z) </k>` steps to y exactly where z is not `a` and y is `<k> b </k>`**, for every
value z of Exp and every configuration y. -/
theorem step_iff {z : GroundTerm} (hz : (c0.withHooks H).sortOf z = some exp) (y : Config (c0.withHooks H)) :
    Step (c0.withHooks H) (C z hz) y ↔ z ≠ A ∧ y = Bc := by
  constructor
  · intro h
    obtain ⟨r, τ, hs⟩ := step_iff_by.mp h
    have hr := rule_eq hs.mem
    subst hr
    have h0 := lookup0 hs.hmatch
    have hp := (pre_at h0).mp hs.hpre
    refine ⟨fun hza => by rw [hza] at hp; simp at hp, ?_⟩
    have hm := hs.hmatch
    rw [r0_lhs] at hm
    obtain ⟨-, hk, hc⟩ := patVal_cfgPat ⟨syms_ok.1, syms_ok.2.1, syms_ok.2.2.1⟩
      ⟨hooks_ok.1, hooks_ok.2.1, hooks_ok.2.2.1⟩ hm
    have he := hs.heval
    rw [r0_rhs] at he
    obtain ⟨w', hw', hy⟩ := evalTerm_cfgPat ⟨syms_ok.1, syms_ok.2.1, syms_ok.2.2.1⟩ hk hc he
    have hw := evalTerm_const syms_ok.2.2.2.2.1 hw'
    cases hw
    exact Subtype.ext hy
  · rintro ⟨hne, rfl⟩
    exact step_iff_by.mpr ⟨r0, σ z, stepBy hz hne⟩

/-- `(c0.withHooks H)(b)` and `(c0.withHooks H)((c0.withHooks H)(a))` step to `b`; `(c0.withHooks H)(a)` has no successor. -/
theorem step_cb : Step (c0.withHooks H) (C B (by whd)) Bc :=
  (step_iff _ _).mpr ⟨by whd, rfl⟩
theorem step_cca : Step (c0.withHooks H) (C (.ctor symC [A]) (by whd)) Bc :=
  (step_iff _ _).mpr ⟨by whd, rfl⟩
theorem stuck_ca : ∀ y, ¬ Step (c0.withHooks H) (C A sortOf_A) y :=
  fun y h => ((step_iff _ y).mp h).1 rfl

/-- info: 'RuleConnStepH.LhsNotOther.step_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms step_iff

end LhsNotOther

/-! ## e3-ml-rule-rhs-or -/

namespace RhsOr

definition_of defn from "f2-examples/e3-ml-rule-rhs-or.kompile.kore"

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

def exp : Srt := 32
def kCell : Sym := 383
def symA : Sym := 385
def symB : Sym := 386
def symGo : Sym := 389

theorem names_ok : c0.sortName exp = "Exp" ∧ c0.symName kCell = "Lbl'-LT-'k'-GT-'" ∧
    c0.symName symA = "Lbla" ∧ c0.symName symB = "Lblb" ∧ c0.symName symGo = "Lblgo" := by
  decide +kernel

noncomputable def r0 : Rule := c0.rules[0]'(by decide +kernel)

theorem r0_mem : r0 ∈ (c0.withHooks H).rules := List.getElem_mem _

/-- The text has the one rule. -/
theorem rule_eq {r : Rule} (hr : r ∈ (c0.withHooks H).rules) : r = r0 := by
  rw [rules_wh] at hr
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hr
  have h1 : c0.rules.length = 1 := by decide +kernel
  have : i = 0 := by omega
  subst this
  rfl

theorem r0_vars : r0.vars = [Srt.k, 19, exp] := by whd
theorem r0_lhs : r0.lhs = cfgPat kCell exp (.app symGo []) 0 1 := rfl
theorem r0_rhs : r0.rhs = cfgPat kCell exp (.var 2) 0 1 := rfl
/-- `go => ?Z` with `post := or (mem Z a) (mem Z b)`, Z the variable 2. -/
theorem r0_shape : r0.req = none ∧ r0.ens = none ∧ r0.exs = [2] ∧ r0.pre = .top ∧
    r0.post = .or (.mem exp (.var 2) (.app symA [])) (.mem exp (.var 2) (.app symB [])) :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem syms_ok : (c0.withHooks H).isCtor topLabel = true ∧ (c0.withHooks H).isCtor kCell = true ∧ (c0.withHooks H).isCtor kseq = true ∧
    (c0.withHooks H).isCtor symA = true ∧ (c0.withHooks H).isCtor symB = true ∧ (c0.withHooks H).isCtor symGo = true ∧ (c0.withHooks H).isCtor dotk = true := by
  whd

theorem hooks_ok : patternHooks.contains topLabel = false ∧ patternHooks.contains kCell = false ∧
    patternHooks.contains kseq = false ∧ patternHooks.contains symGo = false := by
  whd


/-! ### The configurations -/

def dotkT : GroundTerm := .ctor dotk []
def ctr : GroundTerm := .ctor counterLabel [int 0]
def cfg (st : GroundTerm) : GroundTerm := cfgOf kCell exp st
def a : GroundTerm := .ctor symA []
def b : GroundTerm := .ctor symB []

/-- `<k> go </k>`. -/
def Go : Config (c0.withHooks H) := ⟨cfg (.ctor symGo []), by whd⟩
/-- `<k> a </k>`, `<k> b </k>`. -/
def A : Config (c0.withHooks H) := ⟨cfg a, by whd⟩
def B : Config (c0.withHooks H) := ⟨cfg b, by whd⟩

theorem A_ne_B : (A : Config (c0.withHooks H)) ≠ B :=
  fun h => absurd (congrArg Subtype.val h) (by show cfg a ≠ cfg b; decide +kernel)

/-! ### `Step` from `go` to `a` and to `b` -/

/-- `post` where σ gives Z the value v. -/
theorem post_at {τ : Subst} {v : GroundTerm} (h2 : τ.lookup 2 = some v) {bv : Bool} :
    Holds (c0.withHooks H) r0.vars.length τ r0.post bv ↔ bv = (decide (v = a) || decide (v = b)) := by
  rw [r0_shape.2.2.2.2]
  constructor
  · intro h
    obtain ⟨b₁, b₂, h₁, h₂, rfl⟩ := holds_or_inv h
    obtain ⟨r₁, r₁', e₁, e₁', rfl⟩ := holds_mem_inv h₁
    obtain ⟨r₂, r₂', e₂, e₂', rfl⟩ := holds_mem_inv h₂
    rw [EvalTerm.var_inv e₁, evalTerm_const syms_ok.2.2.2.1 e₁', EvalTerm.var_inv e₂,
      evalTerm_const syms_ok.2.2.2.2.1 e₂', h2]
    simp only [Option.isSome_some, Bool.true_and, sameResult_some]; rfl
  · intro hb
    have h : Holds (c0.withHooks H) r0.vars.length τ (.or (.mem exp (.var 2) (.app symA [])) (.mem exp (.var 2) (.app symB [])))
        (((τ.lookup 2).isSome && sameResult (τ.lookup 2) (some a)) ||
          ((τ.lookup 2).isSome && sameResult (τ.lookup 2) (some b))) :=
      .or (.mem .var (.ctor syms_ok.2.2.2.1 .nil)) (.mem .var (.ctor syms_ok.2.2.2.2.1 .nil))
    rw [h2] at h
    simp only [Option.isSome_some, Bool.true_and, sameResult_some] at h
    rw [hb]; exact h

/-- The right side under σ that gives V0, V1 and Z the values `.`, the counter and v. -/
theorem rhs_eval {τ : Subst} {v : GroundTerm} (h0 : τ.lookup 0 = some dotkT) (h1 : τ.lookup 1 = some ctr)
    (h2 : τ.lookup 2 = some v) (hv : v.isInj = false) : EvalTerm (c0.withHooks H) τ r0.rhs (some (cfg v)) := by
  rw [r0_rhs]
  have he : EvalTerm (c0.withHooks H) τ (.inj exp Srt.kitem (.var 2)) ((τ.lookup 2).map (injNormal exp Srt.kitem)) := .inj .var
  rw [h2, Option.map_some, injNormal_of_not_inj hv] at he
  have e0 : EvalTerm (c0.withHooks H) τ (.var 0) (some dotkT) := h0 ▸ .var
  have e1 : EvalTerm (c0.withHooks H) τ (.var 1) (some ctr) := h1 ▸ .var
  exact .ctor syms_ok.1 (.cons (.ctor syms_ok.2.1 (.cons (.ctor syms_ok.2.2.1
    (.cons he (.cons e0 .nil))) .nil)) (.cons e1 .nil))

theorem prio_none {r' : Rule} (hr' : r' ∈ (c0.withHooks H).rules) (hlt : r'.prio < r0.prio) : False := by
  rw [rule_eq hr'] at hlt
  exact Nat.lt_irrefl _ hlt

/-- The text declares no function, so evaluation has one result under every interpretation. -/
theorem fns_nil0 : c0.fns = [] := by decide +kernel
theorem fnDet : FnDet (c0.withHooks H) :=
  fnDet_of_agree (fun _ h => by rw [fns_wh, fns_nil0] at h; cases h)
    (fun _ h => by rw [fns_wh, fns_nil0] at h; cases h)

/-- A step by the rule at any σ that gives V0, V1 the values of `<k> go </k>` and Z a or b. -/
theorem stepBy_at {τ : Subst} {v : GroundTerm} (h0 : τ.lookup 0 = some dotkT) (h1 : τ.lookup 1 = some ctr)
    (h2 : τ.lookup 2 = some v) (hv : v = a ∨ v = b) (y : Config (c0.withHooks H)) (hy : y.val = cfg v) :
    StepBy (c0.withHooks H) r0 τ Go y where
  mem := r0_mem
  hσ := fun j s hs => by
    rw [r0_vars] at hs
    match j, hs with
    | 0, hs => cases hs; exact ⟨_, h0, by whd⟩
    | 1, hs => cases hs; exact ⟨_, h1, by whd⟩
    | 2, hs => cases hs; exact ⟨_, h2, by rcases hv with rfl | rfl <;> whd⟩
  hmatch := by
    rw [r0_lhs]
    have hi : injNormal exp Srt.kitem (.ctor symGo []) = .inj exp Srt.kitem (.ctor symGo []) := rfl
    exact .ctor syms_ok.1 (.cons (.ctor syms_ok.2.1 (.cons (.ctor syms_ok.2.2.1
      (.cons (hi ▸ .inj (.ctor syms_ok.2.2.2.2.2.1 .nil)) (.cons (.var h0) .nil))) .nil))
      (.cons (.var h1) .nil))
  hreq := fun t ht => by rw [r0_shape.1] at ht; cases ht
  hpre := by rw [r0_shape.2.2.2.1]; exact .top
  heval := by
    rw [hy]
    exact rhs_eval h0 h1 h2 (by rcases hv with rfl | rfl <;> rfl)
  hens := fun t ht => by rw [r0_shape.2.1] at ht; cases ht
  hpost := (post_at h2).mpr (by rcases hv with rfl | rfl <;> whd)
  hprio := fun r' hr' hlt => (prio_none hr' hlt).elim

def σ (v : GroundTerm) : Subst := [(0, dotkT), (1, ctr), (2, v)]

/-- **`go` steps to `a` and to `b`.** -/
theorem stepBy_a : StepBy (c0.withHooks H) r0 (σ a) Go A := stepBy_at rfl rfl rfl (.inl rfl) A rfl
theorem stepBy_b : StepBy (c0.withHooks H) r0 (σ b) Go B := stepBy_at rfl rfl rfl (.inr rfl) B rfl
theorem step_a : Step (c0.withHooks H) Go A := step_iff_by.mpr ⟨r0, σ a, stepBy_a⟩
theorem step_b : Step (c0.withHooks H) Go B := step_iff_by.mpr ⟨r0, σ b, stepBy_b⟩

/-- A match at `<k> go </k>` gives V0 and V1 the values `.` and the counter. -/
theorem lookups {τ : Subst} (hm : PatVal (c0.withHooks H) τ r0.lhs (cfg (.ctor symGo []))) :
    τ.lookup 0 = some dotkT ∧ τ.lookup 1 = some ctr := by
  rw [r0_lhs] at hm
  have ⟨h1, hc⟩ := patVal_ctor2 hooks_ok.1 syms_ok.1 hm
  have h2 := patVal_ctor1 hooks_ok.2.1 syms_ok.2.1 h1
  have h3 := (patVal_ctor2 hooks_ok.2.2.1 syms_ok.2.2.1 h2).2
  exact ⟨PatVal.var_inv h3, PatVal.var_inv hc⟩

/-- **Every step by the rule from `go` is to `a` or to `b`**, and Z has that value. -/
theorem step_inv {τ : Subst} {x y : Config (c0.withHooks H)} (hs : StepBy (c0.withHooks H) r0 τ x y) (hx : x = Go) :
    ∃ v, τ.lookup 2 = some v ∧ (v = a ∨ v = b) ∧ (y = A ∨ y = B) := by
  subst hx
  obtain ⟨h0, h1⟩ := lookups hs.hmatch
  obtain ⟨v, h2, -⟩ := hs.hσ 2 exp (by rw [r0_vars]; rfl)
  have hp := (post_at h2).mp hs.hpost
  have hv : v = a ∨ v = b := by
    by_cases ha : v = a
    · exact .inl ha
    · by_cases hb : v = b
      · exact .inr hb
      · simp [ha, hb] at hp
  refine ⟨v, h2, hv, ?_⟩
  have he := EvalTerm.functional_of_fnDet fnDet hs.heval (rhs_eval h0 h1 h2 (by rcases hv with rfl | rfl <;> rfl))
  rcases hv with rfl | rfl
  · exact .inl (Subtype.ext (Option.some.inj he))
  · exact .inr (Subtype.ext (Option.some.inj he))


/-- **The successors of `<k> go </k>` are `<k> a </k>` and `<k> b </k>`, and nothing else**, under
every interpretation. -/
theorem step_iff (y : Config (c0.withHooks H)) : Step (c0.withHooks H) Go y ↔ y = A ∨ y = B := by
  constructor
  · intro h
    obtain ⟨r, τ, hs⟩ := step_iff_by.mp h
    have hr := rule_eq hs.mem
    subst hr
    obtain ⟨_, _, _, hy⟩ := step_inv hs rfl
    exact hy
  · rintro (rfl | rfl)
    · exact step_a
    · exact step_b

/-- info: 'RuleConnStepH.RhsOr.step_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms step_iff

end RhsOr

end RuleConnStepH

