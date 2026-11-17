/-
  The fixtures of rules with predicates (CN-4 §4.8, R3 fixture table), read from K 7.1.337 kompile's
  KORE with a connective at a term position cut (`Parse.connRuleOf`, `Parse.andRuleOf`;
  test/PredReader.lean prints the readings). Run from the package root:
  `lake env lean -j1 test/PredFixtures.lean`.

  `definition_read NAME from "file.kore" by conn` (or `by and`) adds the definition
  `Parse.parseWith` builds with that reading function, as `definition_of` adds `Parse.parse`'s.

  ## e3-ml-rule-lhs-not
  `f2-examples/mlnot.kompile.kore` (`test/constructs/fixtures/e3-ml-rule-lhs-not/kore.txt:51-56`):
  `c(#Not(a())) => a()`, kompiled to `<k> c(\not{Exp}(\and{Exp}(a(), _Gen5))) => _Gen5 </k>`, _Gen5
  bound only under `\not`. Read as `c(Z) => G` with `pre := not (and (mem Z a) (mem Z G))`, Z
  (variable 0) bound by the left side, G (variable 3) open and held by the right side under
  constructors. The text's only rule, so the definition has `coreOK` (`coreOK`). For all values z
  and g of Exp, `<k> c(z) </k>` steps to `<k> g </k>` exactly where not (z = a and g = a)
  (`step_iff`): the sentence `c(¬(a ∧ G)) → •G` holds at every G with z outside `a ∧ G`.
  Beside a rule of a larger priority (the definition with the rule `c(Z) => b`, `pre := not (mem Z
  a)`, of priority 200 appended: `cLarger`), G is an open variable of a condition with the variable Z the left side binds, of the
  sort Exp the text leaves unconfined, in a rule that competes with a larger one: `rulesPlain` and
  `coreOK` fail (`larger_refused`) and the reader's message is `openRequires` at Exp.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

open KCore
open ML Faithful

namespace PredFixtures

open Lean Elab Command in
/-- `definition_read NAME from "file.kore" by conn|and`: `def NAME : Definition`, the definition
`Parse.parseWith` builds from the file with the rules read by `Parse.connRuleOf` (`conn`) or
`Parse.andRuleOf` (`and`), added as a term (not compiled). -/
elab "definition_read " id:ident " from " path:str " by " rd:ident : command => do
  let f ← match rd.getId.toString with
    | "conn" => pure Parse.connRuleOf
    | "and" => pure Parse.andRuleOf
    | s => throwError "definition_read: no reading function {s}"
  let input ← IO.FS.readFile path.getString
  let k ← match Kore.parseDefinition input with
    | .error e => throwError "definition_read: {path.getString}: KORE read error {e}"
    | .ok k => pure k
  let d ← match Parse.parseWith f k with
    | .ok d => pure d
    | .error r => throwError "definition_read: {path.getString}: refused: {r.toText}"
  let name := (← getCurrNamespace) ++ id.getId
  liftCoreM <| addDecl <| .defnDecl {
    name, levelParams := [], type := mkConst ``Definition, value := definitionExpr d,
    hints := .regular 0, safety := .safe }

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

/-- The configuration pattern `<generatedTop>(<k>(kseq(inj{s,KItem}(p), V1)), V2)`. -/
def cfgPat (kCell : Sym) (s : Srt) (p : Term) : Term :=
  .app topLabel [.app kCell [.app kseq [.inj s Srt.kitem p, .var 1]], .var 2]

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

/-! ## e3-ml-rule-lhs-not -/

namespace LhsNot

definition_read defn from "f2-examples/mlnot.kompile.kore" by conn

noncomputable abbrev c : Semantics := defn.sem

def exp : Srt := 32
def kCell : Sym := 383
def symA : Sym := 385
def symC : Sym := 387

theorem names_ok : c.sortName exp = "Exp" ∧ c.symName kCell = "Lbl'-LT-'k'-GT-'" ∧
    c.symName symA = "Lbla" ∧ c.symName symC = "Lblc" := by
  decide +kernel

/-- **Admitted as the only rule**: the definition with the rule `c(Z) => G` has `coreOK`. -/
theorem coreOK : c.coreOK = true := by decide +kernel

noncomputable def r0 : Rule := c.rules[0]'(by decide +kernel)

theorem r0_mem : r0 ∈ c.rules := List.getElem_mem _

/-- The text has the one rule. -/
theorem rule_eq {r : Rule} (hr : r ∈ c.rules) : r = r0 := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hr
  have h1 : c.rules.length = 1 := by decide +kernel
  have : i = 0 := by omega
  subst this
  rfl

theorem r0_vars : r0.vars = [exp, Srt.k, 19, exp] := by decide +kernel
theorem r0_lhs : r0.lhs = cfgPat kCell exp (.app symC [.var 0]) := rfl
theorem r0_rhs : r0.rhs = cfgPat kCell exp (.var 3) := rfl
/-- `pre := not (and (mem Z a) (mem Z G))`, Z the variable 0, G the variable 3. -/
theorem r0_shape : r0.req = none ∧ r0.ens = none ∧ r0.exs = [] ∧ r0.post = .top ∧
    r0.pre = .not (.and (.mem exp (.var 0) (.app symA [])) (.mem exp (.var 0) (.var 3))) :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem syms_ok : c.isCtor topLabel = true ∧ c.isCtor kCell = true ∧ c.isCtor kseq = true ∧
    c.isCtor symA = true ∧ c.isCtor symC = true ∧ c.isCtor dotk = true ∧ c.isCtor counterLabel = true := by
  decide +kernel

theorem hooks_ok : patternHooks.contains topLabel = false ∧ patternHooks.contains kCell = false ∧
    patternHooks.contains kseq = false ∧ patternHooks.contains symC = false := by
  decide +kernel

theorem lookups_ok : (lookupSig c.ctorSigs topLabel).isSome = true ∧ (lookupSig c.ctorSigs kCell).isSome = true ∧
    (lookupSig c.ctorSigs kseq).isSome = true ∧ (lookupSig c.ctorSigs symC).isSome = true := by
  decide +kernel

/-- No sort lies below Exp. -/
theorem exp_bottom : ∀ p ∈ c.subsorts, p.2 ≠ exp := by
  intro p hp
  have h : c.subsorts.all (fun p => p.2 != exp) = true := by decide +kernel
  simpa using List.all_eq_true.mp h p hp

/-! ### The configurations -/

def A : GroundTerm := .ctor symA []
def ctr : GroundTerm := .ctor counterLabel [int 0]
def cfg (st : GroundTerm) : GroundTerm := cfgOf kCell exp st

theorem sortOf_A : c.sortOf A = some exp := by decide +kernel

theorem sortOf_cfg {g : GroundTerm} (hg : c.sortOf g = some exp) : c.sortOf (cfg g) = some topCellSort := by
  have h0 : c.sortOf (cfg A) = some topCellSort := by decide +kernel
  rw [← h0]
  exact sortOf_cfgOf_congr ⟨lookups_ok.1, lookups_ok.2.1, lookups_ok.2.2.1⟩ (by rw [hg, sortOf_A])
    (by rw [isInj_of_sort exp_bottom hg]; rfl)

theorem sortOf_cfgC {z : GroundTerm} (hz : c.sortOf z = some exp) :
    c.sortOf (cfg (.ctor symC [z])) = some topCellSort := by
  have h0 : c.sortOf (cfg (.ctor symC [A])) = some topCellSort := by decide +kernel
  rw [← h0]
  exact sortOf_cfgOf_congr ⟨lookups_ok.1, lookups_ok.2.1, lookups_ok.2.2.1⟩
    (sortOf_ctor_congr lookups_ok.2.2.2 (sortsOf_head_congr (by rw [hz, sortOf_A]))) rfl

/-- `<k> c(z) </k>`. -/
def C (z : GroundTerm) (hz : c.sortOf z = some exp) : Config c := ⟨cfg (.ctor symC [z]), sortOf_cfgC hz⟩
/-- `<k> g </k>`. -/
def G (g : GroundTerm) (hg : c.sortOf g = some exp) : Config c := ⟨cfg g, sortOf_cfg hg⟩

/-! ### The step -/

def σ (z g : GroundTerm) : Subst := [(0, z), (1, .ctor dotk []), (2, ctr), (3, g)]

/-- `pre` under any σ: false exactly where σ gives Z the value `a` and G the value Z has. -/
theorem pre_holds (τ : Subst) : Holds c r0.vars.length τ r0.pre
    (!(((τ.lookup 0).isSome && sameResult (τ.lookup 0) (some A)) &&
      ((τ.lookup 0).isSome && sameResult (τ.lookup 0) (τ.lookup 3)))) := by
  rw [r0_shape.2.2.2.2]
  exact .not (.and (.mem .var (.ctor syms_ok.2.2.2.1 .nil)) (.mem .var .var))

/-- The truth value of `pre` under any σ is `pre_holds`'s. -/
theorem pre_val {τ : Subst} {b : Bool} (h : Holds c r0.vars.length τ r0.pre b) :
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
    Holds c r0.vars.length τ r0.pre b ↔ b = !(decide (z = A) && decide (z = g)) := by
  constructor
  · intro h
    rw [pre_val h, h0, h3]
    simp only [Option.isSome_some, Bool.true_and, sameResult_some]
  · intro hb
    have h := pre_holds τ
    rw [h0, h3] at h
    simp only [Option.isSome_some, Bool.true_and, sameResult_some] at h
    rw [hb]; exact h

theorem prio_none {r' : Rule} (hr' : r' ∈ c.rules) (hlt : r'.prio < r0.prio) : False := by
  rw [rule_eq hr'] at hlt
  exact Nat.lt_irrefl _ hlt

theorem stepBy {z g : GroundTerm} (hz : c.sortOf z = some exp) (hg : c.sortOf g = some exp)
    (hne : ¬ (z = A ∧ g = A)) : StepBy c r0 (σ z g) (C z hz) (G g hg) where
  mem := r0_mem
  hσ := fun j s hs => by
    rw [r0_vars] at hs
    match j, hs with
    | 0, hs => cases hs; exact ⟨_, rfl, hz⟩
    | 1, hs => cases hs; exact ⟨_, rfl, by decide +kernel⟩
    | 2, hs => cases hs; exact ⟨_, rfl, by decide +kernel⟩
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
    have he : EvalTerm c (σ z g) (.inj exp Srt.kitem (.var 3)) (((σ z g).lookup 3).map (injNormal exp Srt.kitem)) :=
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

/-- A match of the left side at `<k> c(z) </k>` gives Z the value z. -/
theorem lookup0 {τ : Subst} {z : GroundTerm} (hm : PatVal c τ r0.lhs (cfg (.ctor symC [z]))) :
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
theorem lookup3 {τ : Subst} {g : GroundTerm} (hτ : c.WellSorted r0.vars τ)
    (he : EvalTerm c τ r0.rhs (some (cfg g))) : τ.lookup 3 = some g := by
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

/-- **`<k> c(z) </k>` steps to `<k> g </k>` exactly where not (z = a and g = a)**, for all values z
and g of Exp. -/
theorem step_iff {z g : GroundTerm} (hz : c.sortOf z = some exp) (hg : c.sortOf g = some exp) :
    Step c (C z hz) (G g hg) ↔ ¬ (z = A ∧ g = A) := by
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

/-! ### Beside a rule of a larger priority -/

def symB : Sym := 386

/-- `c(Z) => b` with `pre := not (mem Z a)` at the priority 200: the shape of
e3-ml-rule-lhs-not-other's `c(#Not(a())) => b()`, written by hand. -/
def rOther : Rule :=
  { vars := [exp, Srt.k, 19], lhs := cfgPat kCell exp (.app symC [.var 0]), req := none,
    rhs := cfgPat kCell exp (.app symB []), ens := none, prio := 200,
    pre := .not (.mem exp (.var 0) (.app symA [])) }

/-- The definition's semantics with `rOther` appended. -/
noncomputable def cLarger : Semantics := { c with rules := c.rules ++ [rOther] }

/-- **Beside a rule of a larger priority the rule is refused**: in `cLarger` the rule `c(Z) => G`
competes with `rOther`, and G (variable 3), of the unconfined sort Exp, is open in `pre`, which
also reads Z, bound by the left side: the rule's conjunct of `rulesPlain` fails, and `coreOK`
with it. `rOther` alone is well sorted with the conjunct. -/
theorem larger_refused : c.confined exp = false ∧ r0.opens = [3] ∧ cLarger.rulePlainPP r0 = false ∧
    cLarger.ruleSorted rOther = true ∧ cLarger.rulePlainPP rOther = true ∧
    cLarger.rulesPlain = false ∧ cLarger.coreOK = false := by
  decide +kernel

/-- The reader's message for the rule in `cLarger`. -/
def largerMessage : IO Unit := do
  match Kore.parseDefinition (← IO.FS.readFile "f2-examples/mlnot.kompile.kore") with
  | .error e => IO.println s!"KORE read error {e}"
  | .ok k => match Parse.parseWith Parse.connRuleOf k with
    | .error r => IO.println s!"refused {r.reason.name}"
    | .ok d =>
      let c' : Semantics := { d.sem with rules := d.sem.rules ++ [rOther] }
      match d.sem.rules.head?, d.pres.rules.head? with
      | some r, some p => IO.println s!"{(Parse.openRefusal c' r p.names).map fun x => (x.1.name, x.2)}"
      | _, _ => IO.println "no rule"

/--
info: (some (openRequires, Var'Unds'Gen5:Exp: in a condition with a variable the left side binds, of a sort the text leaves unconfined, in a rule of a priority below another's))
-/
#guard_msgs in
#eval largerMessage

/-- info: 'PredFixtures.LhsNot.step_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms step_iff
/-- info: 'PredFixtures.LhsNot.larger_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms larger_refused

end LhsNot

end PredFixtures
