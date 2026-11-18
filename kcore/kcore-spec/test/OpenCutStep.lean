/-
  The steps of a rule read through the cut of an open generator, on K 7.1.337 kompile's text of
  fixture e2-open-mixed (`f2-examples/openmixed.kompile.kore`: `syntax A ::= "x" | "y"`,
  `syntax B ::= A "&" A [comm]`, `syntax KItem ::= c(B) | d(A)`, `rule <k> c(X & Y) => d(X) </k>`).
  Run from the package root: `lake env lean -j1 test/OpenCutStep.lean`.

  `&` is the open generator `and : A A → B` (a raw parameter without a law; kompile writes no
  sentence for `comm`). The reader reads the rule's left side through the cut (`Parse.ovlCut`;
  test/OpenGenerator.lean prints the reading): the rule `r0` is `c(Open0) => d(X)` with
  `pre := Open0 ∈ and(X, Y)` (`r0_shape`), whose term is evaluated through the interpretation's
  value of `and` (`EvalTerm.param`, `Semantics.paramVal`), not matched.

  - `step_iff`: **for every interpretation H of the parameters**, a configuration `<k> c(v) </k>`
    steps to y exactly when y is `<k> d(a) </k>` for values a, b of A with `paramVal and [a, b] =
    some v`. Every H satisfies `OpenLaws` here (`and` has no law: `openLaws_any`), so `FnHyp`
    holds at every H (`fnHyp`); `OpenTotal` is not used.
  - `none_iff`: at `HookParams.none`, where `and` keeps its raw application, `<k> c(x & y) </k>`
    steps to `<k> d(x) </k>` and to nothing else.
  - `swap_x`, `swap_y`: at `Hswap`, which answers `and(x, y)` at `and [y, x]`, it steps both to
    `<k> d(x) </k>` and to `<k> d(y) </k>`.

  The other branches of the cut (beside an `[owise]` rule; every argument variable held elsewhere in
  the left side; an `#as` under the generator) are test/OpenGenerator.lean's.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

open KCore

namespace OpenCutStep

definition_of defn from "f2-examples/openmixed.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem

/-- The text read at the interpretation H of its parameters. -/
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

def sB : Srt := 32
def sA : Srt := 33
def kCell : Sym := 384
def symC : Sym := 386
def symD : Sym := 387
def symX : Sym := 388
def symY : Sym := 389
def andS : Sym := 390

def andP : ParamSig := { sig := ⟨andS, [sA, sA], sB⟩, raw := true }

theorem names_ok : c.sortName sB = "B" ∧ c.sortName sA = "A" ∧ c.symName kCell = "Lbl'-LT-'k'-GT-'" ∧
    c.symName symC = "Lblc" ∧ c.symName symD = "Lbld" ∧ c.symName symX = "Lblx" ∧
    c.symName symY = "Lbly" ∧ c.symName andS = "Lbland" := by
  decide +kernel

theorem coreOK : c.coreOK = true := by decide_cheap

theorem coreOK_H (H : HookParams) : (cH H).coreOK = true :=
  (Semantics.coreOK_withHooks c H).trans coreOK

noncomputable def r0 : Rule := c.rules[0]'(by decide +kernel)

theorem r0_mem (H : HookParams) : r0 ∈ (cH H).rules := List.getElem_mem _

/-- The text has the one rule. -/
theorem rule_eq (H : HookParams) {r : Rule} (hr : r ∈ (cH H).rules) : r = r0 := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hr
  have h1 : c.rules.length = 1 := by decide +kernel
  have : i = 0 := by change i < c.rules.length at hi; omega
  subst this
  rfl

theorem r0_vars : r0.vars = [sA, sA, 19, sB] := by decide +kernel
theorem r0_lhs : r0.lhs = .app topLabel [.app kCell [.app kseq [.app symC [.var 3], .app dotk []]],
    .var 2] := rfl
theorem r0_rhs : r0.rhs = .app topLabel [.app kCell [.app kseq [.app symD [.var 0], .app dotk []]],
    .var 2] := rfl
/-- The cut's reading: no `requires` or `ensures`, `pre` the membership of `Open0` (variable 3) in
`and(X, Y)`, `post` true, no existential variable. -/
theorem r0_shape : r0.req = none ∧ r0.ens = none ∧
    r0.pre = .mem sB (.var 3) (.app andS [.var 0, .var 1]) ∧ r0.post = .top ∧ r0.exs = [] :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem facts : c.ruleSorted r0 = true ∧ r0.prio = 50 ∧ c.fns = [] ∧
    c.params.filter (·.raw) = [andP] := by
  decide +kernel

/-- The condition holds Open0, which the left side binds: the rule's condition is not closed, so
the rule needs no witness at any interpretation. -/
theorem r0_reqClosed : r0.reqClosed = false := by decide +kernel

theorem lhs_vars : ∀ j ∈ varOccs r0.lhs, j < 4 := by decide +kernel
theorem rhs_vars : ∀ j ∈ varOccs r0.rhs, j < 4 := by decide +kernel

theorem syms_ok (H : HookParams) : (cH H).isCtor topLabel = true ∧ (cH H).isCtor kCell = true ∧
    (cH H).isCtor kseq = true ∧ (cH H).isCtor symC = true ∧ (cH H).isCtor dotk = true ∧
    (cH H).isCtor symD = true := by
  change c.isCtor topLabel = true ∧ c.isCtor kCell = true ∧ c.isCtor kseq = true ∧
    c.isCtor symC = true ∧ c.isCtor dotk = true ∧ c.isCtor symD = true
  decide +kernel

theorem hooks_ok : patternHooks.contains topLabel = false ∧ patternHooks.contains kCell = false ∧
    patternHooks.contains kseq = false ∧ patternHooks.contains symC = false := by
  decide +kernel

/-- `and` is a parameter, neither a constructor nor a hooked symbol, read as the open generator
`andP` with no registry hook. -/
theorem and_ok (H : HookParams) : (cH H).isCtor andS = false ∧ isHook andS = false ∧
    (cH H).isParam andS = true ∧ (cH H).lookupParam andS = some andP := by
  change c.isCtor andS = false ∧ isHook andS = false ∧ c.isParam andS = true ∧
    c.lookupParam andS = some andP
  decide +kernel

/-- `and` has no law: `OpenLaws` holds under every interpretation. -/
theorem openLaws_any (H : HookParams) : OpenLaws (cH H) := fun k hk hr => by
  have hk' : k ∈ c.params.filter (·.raw) := List.mem_filter.mpr ⟨hk, hr⟩
  rw [facts.2.2.2, List.mem_singleton] at hk'
  subst hk'
  exact ⟨fun h => (by cases h), fun h => (by cases h)⟩

/-- The hypothesis on the functions holds at every H: the text declares none, no rule needs a
witness (its condition holds Open0, which the left side binds), and `OpenLaws` holds. -/
theorem fnHyp (H : HookParams) : FnHyp (cH H) :=
  have hn : ∀ fn, fn ∈ (cH H).fns → False := fun fn hfn => by
    change fn ∈ c.fns at hfn
    rw [facts.2.2.1] at hfn
    cases hfn
  ⟨fun fn hfn => (hn fn hfn).elim, fun fn hfn => (hn fn hfn).elim, fun fn hfn => (hn fn hfn).elim,
    fun fn hfn => (hn fn hfn).elim,
    openDecided_of_plain (fun r hr => by
        rw [rule_eq H hr]
        simp [Rule.needsWitness, r0_reqClosed]) (fun fn hfn => (hn fn hfn).elim),
    openLaws_any H⟩

theorem fnDet (H : HookParams) : FnDet (cH H) := (fnModel_of_fnHyp (coreOK_H H) (fnHyp H)).1

/-! ## The configurations -/

def ctr : GroundTerm := .ctor counterLabel [int 0]
def dk : GroundTerm := .ctor dotk []
def x : GroundTerm := .ctor symX []
def y : GroundTerm := .ctor symY []

/-- `<k> st ~> . </k>` with the counter 0. -/
def cfg (st : GroundTerm) : GroundTerm := .ctor topLabel [.ctor kCell [.ctor kseq [st, dk]], ctr]

theorem ctr_sort (H : HookParams) : (cH H).sortOf ctr = some 19 :=
  (Semantics.sortOf_withHooks_rawFree c H (by decide +kernel)).trans (by decide +kernel)

/-! ## `step_iff`: the steps at `<k> c(v) </k>`, for every H -/

/-- The substitution of the rule's variables X, Y, the counter and Open0. -/
def σ (a b v : GroundTerm) : Subst := [(0, a), (1, b), (2, ctr), (3, v)]

theorem prio_none (H : HookParams) {r' : Rule} (hr' : r' ∈ (cH H).rules) (hlt : r'.prio < r0.prio) :
    False := by
  rw [rule_eq H hr'] at hlt
  exact absurd hlt (Nat.lt_irrefl _)

theorem matchX (H : HookParams) (a b v : GroundTerm) :
    PatVal (cH H) (σ a b v) r0.lhs (cfg (.ctor symC [v])) := by
  rw [r0_lhs]
  have hs := syms_ok H
  exact .ctor hs.1 (.cons (.ctor hs.2.1 (.cons (.ctor hs.2.2.1
    (.cons (.ctor hs.2.2.2.1 (.cons (.var rfl) .nil)) (.cons (.ctor hs.2.2.2.2.1 .nil) .nil))) .nil))
    (.cons (.var rfl) .nil))

theorem evalD (H : HookParams) (a b v : GroundTerm) :
    EvalTerm (cH H) (σ a b v) r0.rhs (some (cfg (.ctor symD [a]))) := by
  rw [r0_rhs]
  have hs := syms_ok H
  exact .ctor hs.1 (.cons (.ctor hs.2.1 (.cons (.ctor hs.2.2.1
    (.cons (.ctor hs.2.2.2.2.2 (.cons .var .nil)) (.cons (.ctor hs.2.2.2.2.1 .nil) .nil))) .nil))
    (.cons .var .nil))

/-- `pre` at any substitution: its truth value is whether the value of Open0 is the value
`paramVal` gives `and` at the values of X and Y. -/
theorem pre_at (H : HookParams) (τ : Subst) :
    Holds (cH H) r0.vars.length τ r0.pre ((τ.lookup 3).isSome &&
      sameResult (τ.lookup 3) ((allSome [τ.lookup 0, τ.lookup 1]).bind ((cH H).paramVal andS))) := by
  rw [r0_shape.2.2.1]
  have ha := and_ok H
  exact .mem .var (.param ha.1 ha.2.1 ha.2.2.1 (.cons .var (.cons .var .nil)) rfl)

theorem sameResult_some_iff (v : GroundTerm) (r : Option GroundTerm) :
    sameResult (some v) r = true ↔ r = some v := by
  cases r with
  | none => simp [sameResult]
  | some w =>
    simp only [sameResult, beq_iff_eq, Option.some.injEq]
    exact ⟨fun h => (cmp_eq_iff.mp h).symm, fun h => cmp_eq_iff.mpr h.symm⟩

/-- The value `paramVal` gives `and` is of sort B. -/
theorem val_sort (H : HookParams) {a b v : GroundTerm} (hv : (cH H).paramVal andS [a, b] = some v) :
    (cH H).sortOf v = some sB :=
  ((paramVal_raw_sorted (and_ok H).2.2.2 rfl rfl).mp hv).2

/-- The step by the rule at `σ a b v`, where `and` is v at (a, b). -/
theorem stepBy (H : HookParams) {a b v : GroundTerm} (ha : (cH H).sortOf a = some sA)
    (hb : (cH H).sortOf b = some sA) (hv : (cH H).paramVal andS [a, b] = some v)
    (X Y : Config (cH H)) (hX : X.val = cfg (.ctor symC [v])) (hY : Y.val = cfg (.ctor symD [a])) :
    StepBy (cH H) r0 (σ a b v) X Y where
  mem := r0_mem H
  hσ := fun j s hs => by
    rw [r0_vars] at hs
    match j, hs with
    | 0, hs => cases hs; exact ⟨_, rfl, ha⟩
    | 1, hs => cases hs; exact ⟨_, rfl, hb⟩
    | 2, hs => cases hs; exact ⟨_, rfl, ctr_sort H⟩
    | 3, hs => cases hs; exact ⟨_, rfl, val_sort H hv⟩
  hmatch := hX ▸ matchX H a b v
  hreq := fun t ht => by rw [r0_shape.1] at ht; cases ht
  hpre := by
    have hp := pre_at H (σ a b v)
    have h3 : (σ a b v).lookup 3 = some v := rfl
    have hab : (allSome [(σ a b v).lookup 0, (σ a b v).lookup 1]) = some [a, b] := rfl
    rw [h3, hab, Option.bind_some, hv] at hp
    have ht : ((some v).isSome && sameResult (some v) (some v)) = true := by
      simp [(sameResult_some_iff v (some v)).mpr rfl]
    exact ht ▸ hp
  heval := hY ▸ evalD H a b v
  hens := fun t ht => by rw [r0_shape.2.1] at ht; cases ht
  hpost := by rw [r0_shape.2.2.2.1]; exact .top
  hprio := fun r' hr' hlt => (prio_none H hr' hlt).elim

/-- A substitution under which the left side denotes `<k> c(v) </k>` gives Open0 the value v and
the counter cell its value. -/
theorem lookups {H : HookParams} {τ : Subst} {v : GroundTerm}
    (hm : PatVal (cH H) τ r0.lhs (cfg (.ctor symC [v]))) :
    τ.lookup 3 = some v ∧ τ.lookup 2 = some ctr := by
  rw [r0_lhs] at hm
  have hs := syms_ok H
  obtain ⟨-, vs, hv, hs1⟩ := PatVal.app_inv hooks_ok.1 hm hs.1
  injection hv with _ hv
  subst hv
  cases hs1 with
  | cons hk hs2 =>
    cases hs2 with
    | cons h2 _ =>
      obtain ⟨-, vs, hv, hs3⟩ := PatVal.app_inv hooks_ok.2.1 hk hs.2.1
      injection hv with _ hv
      subst hv
      cases hs3 with
      | cons hq _ =>
        obtain ⟨-, vs, hv, hs4⟩ := PatVal.app_inv hooks_ok.2.2.1 hq hs.2.2.1
        injection hv with _ hv
        subst hv
        cases hs4 with
        | cons hcv _ =>
          obtain ⟨-, vs, hv, hs5⟩ := PatVal.app_inv hooks_ok.2.2.2 hcv hs.2.2.2.1
          injection hv with _ hv
          subst hv
          cases hs5 with
          | cons h3 _ => exact ⟨PatVal.var_inv h3, PatVal.var_inv h2⟩

/-- **For every interpretation H, `<k> c(v) </k>` steps to Y exactly when Y is `<k> d(a) </k>` for
values a, b of A at which the interpretation's `and` is v.** -/
theorem step_iff (H : HookParams) (X Y : Config (cH H)) (v : GroundTerm)
    (hX : X.val = cfg (.ctor symC [v])) :
    Step (cH H) X Y ↔ ∃ a b, (cH H).sortOf a = some sA ∧ (cH H).sortOf b = some sA ∧
      (cH H).paramVal andS [a, b] = some v ∧ Y.val = cfg (.ctor symD [a]) := by
  constructor
  · intro hs
    obtain ⟨r, τ, hst⟩ := step_iff_by.mp hs
    have hr := rule_eq H hst.mem
    subst hr
    have hm : PatVal (cH H) τ r0.lhs (cfg (.ctor symC [v])) := hX ▸ hst.hmatch
    obtain ⟨h3, h2⟩ := lookups hm
    obtain ⟨a, h0, ha⟩ := hst.hσ 0 sA (by rw [r0_vars]; rfl)
    obtain ⟨b, h1, hb⟩ := hst.hσ 1 sA (by rw [r0_vars]; rfl)
    have hd := fnDet H
    have hp := Holds.functional_of_fnDet hd hst.hpre (pre_at H τ)
    rw [h3, h0, h1] at hp
    have hab : allSome [some a, some b] = some [a, b] := rfl
    rw [hab, Option.bind_some] at hp
    have hv : (cH H).paramVal andS [a, b] = some v := by
      have : sameResult (some v) ((cH H).paramVal andS [a, b]) = true := by
        simpa using hp.symm
      exact (sameResult_some_iff v _).mp this
    have hτ : ∀ j ∈ varOccs r0.rhs, (σ a b v).lookup j = τ.lookup j := fun j hj => by
      have hj4 := rhs_vars j hj
      match j, hj4 with
      | 0, _ => exact h0.symm
      | 1, _ => exact h1.symm
      | 2, _ => exact h2.symm
      | 3, _ => exact h3.symm
    have he := EvalTerm.functional_of_fnDet hd hst.heval
      (Exec.EvalTerm.congr (evalD H a b v) hτ)
    exact ⟨a, b, ha, hb, hv, Option.some.inj he⟩
  · rintro ⟨a, b, ha, hb, hv, hY⟩
    exact step_iff_by.mpr ⟨r0, σ a b v, stepBy H ha hb hv X Y hX hY⟩

/-! ## At `HookParams.none`: `c(x & y)` steps to `d(x)` only -/

def xy : GroundTerm := .ctor andS [x, y]

def X0 : Config (cH HookParams.none) := ⟨cfg (.ctor symC [xy]), by decide +kernel⟩
def DX0 : Config (cH HookParams.none) := ⟨cfg (.ctor symD [x]), by decide +kernel⟩

/-- At `HookParams.none` the value of `and` at values a, b is its raw application. -/
theorem none_val {a b v : GroundTerm} (h : (cH HookParams.none).paramVal andS [a, b] = some v) :
    v = .ctor andS [a, b] :=
  ((paramVal_raw_sorted (and_ok HookParams.none).2.2.2 rfl rfl).mp h).1

theorem none_xy : (cH HookParams.none).paramVal andS [x, y] = some xy := by decide +kernel

theorem none_iff (Y : Config (cH HookParams.none)) : Step (cH HookParams.none) X0 Y ↔ Y = DX0 := by
  rw [step_iff HookParams.none X0 Y xy rfl]
  constructor
  · rintro ⟨a, b, -, -, hv, hY⟩
    have := none_val hv
    injection this with _ hab
    injection hab with ha _
    subst ha
    exact Subtype.ext hY
  · rintro rfl
    exact ⟨x, y, by decide +kernel, by decide +kernel, none_xy, rfl⟩

/-! ## At `Hswap`: `c(x & y)` steps to `d(x)` and to `d(y)` -/

/-- The interpretation answering `and(x, y)` at `and [y, x]`, and nothing elsewhere. -/
def Hswap : HookParams :=
  ⟨fun f vs => if f == andS && decide (vs = [y, x]) then some xy else none⟩

def XS : Config (cH Hswap) := ⟨cfg (.ctor symC [xy]), by decide +kernel⟩
def DXS : Config (cH Hswap) := ⟨cfg (.ctor symD [x]), by decide +kernel⟩
def DYS : Config (cH Hswap) := ⟨cfg (.ctor symD [y]), by decide +kernel⟩

theorem swap_xy : (cH Hswap).paramVal andS [x, y] = some xy := by decide +kernel
theorem swap_yx : (cH Hswap).paramVal andS [y, x] = some xy := by decide +kernel

theorem swap_x : Step (cH Hswap) XS DXS :=
  (step_iff Hswap XS DXS xy rfl).mpr ⟨x, y, by decide +kernel, by decide +kernel, swap_xy, rfl⟩
theorem swap_y : Step (cH Hswap) XS DYS :=
  (step_iff Hswap XS DYS xy rfl).mpr ⟨y, x, by decide +kernel, by decide +kernel, swap_yx, rfl⟩

theorem DXS_ne : DXS ≠ DYS := fun h => absurd (congrArg Subtype.val h) (by decide +kernel)

end OpenCutStep

#check @OpenCutStep.step_iff
#check @OpenCutStep.none_iff
#check @OpenCutStep.swap_x
#check @OpenCutStep.swap_y
#print axioms OpenCutStep.step_iff
#print axioms OpenCutStep.none_iff
#print axioms OpenCutStep.swap_x
#print axioms OpenCutStep.swap_y
