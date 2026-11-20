/-
  The steps of a rule read through the cut of an open generator whose argument holds an alias, on
  K 7.1.337 kompile's text of fixture e2-open-mixed-as (`f2-examples/e2-open-mixed-as.kompile.kore`:
  `syntax A ::= "x" | "y"`, `syntax B ::= A "&" A [comm]`, `syntax KItem ::= c(B) | d(A)`,
  `rule <k> c((X #as Z) & Y) => d(Z) </k>`). Run from the package root:
  `lake env lean -j1 test/OpenCutStepAs.lean`.

  `&` is the open generator `and : A A → B` (a raw parameter without a law). The reader reads the
  rule's left side through the cut with the alias a condition (`Parse.ovlCut`, `Parse.cutAsBinds`;
  test/OpenGenerator.lean prints the reading): the rule `r0` is `c(Open0) => d(Z)` with
  `pre := Open0 ∈ and(Z, Y) ∧ Z ∈ X` (`r0_shape`), the first membership's term evaluated through
  the interpretation's value of `and` (`EvalTerm.param`, `Semantics.paramVal`), not matched.

  - `step_iff`: **for every interpretation H of the parameters**, a configuration `<k> c(v) </k>`
    steps to y exactly when y is `<k> d(a) </k>` for values a, b of A with `paramVal and [a, b] =
    some v` (Z and X take the value a). Every H satisfies `OpenLaws` here (`and` has no law), so
    `FnHyp` holds at every H (`fnHyp`); `OpenTotal` is not used.
  - `none_iff`: at `HookParams.none`, where `and` keeps its raw application, `<k> c(x & y) </k>`
    steps to `<k> d(x) </k>` and to nothing else.
  - `swap_x`, `swap_y`: at `Hswap`, which answers `and(x, y)` at `and [y, x]`, it steps both to
    `<k> d(x) </k>` and to `<k> d(y) </k>`.
  - `step_y_undetermined`: so over all H the reading's theory with the step's closure entails
    neither that `<k> c(x & y) </k>` steps to `<k> d(y) </k>` nor that it does not.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

open KCore

namespace OpenCutStepAs

definition_of defn from "f2-examples/e2-open-mixed-as.kompile.kore"

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

theorem r0_vars : r0.vars = [sA, sA, sA, 19, sB] := by decide +kernel
theorem r0_lhs : r0.lhs = .app topLabel [.app kCell [.app kseq [.app symC [.var 4], .app dotk []]],
    .var 3] := rfl
theorem r0_rhs : r0.rhs = .app topLabel [.app kCell [.app kseq [.app symD [.var 1], .app dotk []]],
    .var 3] := rfl
/-- The cut's reading with the alias: variables X, Z, Y (of A), the counter cell's and Open0 (of B);
no `requires` or `ensures`, `pre` the membership of `Open0` (variable 4) in `and(Z, Y)` and that of
Z in X, `post` true, no existential variable. -/
theorem r0_shape : r0.req = none ∧ r0.ens = none ∧
    r0.pre = .and (.mem sB (.var 4) (.app andS [.var 1, .var 2])) (.mem sA (.var 1) (.var 0)) ∧
    r0.post = .top ∧ r0.exs = [] :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem facts : c.ruleSorted r0 = true ∧ r0.prio = 50 ∧ c.fns = [] ∧
    c.params.filter (·.raw) = [andP] := by
  decide +kernel

/-- The condition holds Open0, which the left side binds: the rule's condition is not closed, so
the rule needs no witness at any interpretation. -/
theorem r0_reqClosed : r0.reqClosed = false := by decide +kernel

theorem rhs_vars : ∀ j ∈ varOccs r0.rhs, j = 1 ∨ j = 3 := by decide +kernel

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

/-- The substitution of the rule's variables X and Z (both a), Y, the counter and Open0. -/
def σ (a b v : GroundTerm) : Subst := [(0, a), (1, a), (2, b), (3, ctr), (4, v)]

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
`paramVal` gives `and` at the values of Z and Y, and the value of Z is that of X. -/
theorem pre_at (H : HookParams) (τ : Subst) :
    Holds (cH H) r0.vars.length τ r0.pre (((τ.lookup 4).isSome &&
      sameResult (τ.lookup 4) ((allSome [τ.lookup 1, τ.lookup 2]).bind ((cH H).paramVal andS))) &&
      ((τ.lookup 1).isSome && sameResult (τ.lookup 1) (τ.lookup 0))) := by
  rw [r0_shape.2.2.1]
  have ha := and_ok H
  exact .and (.mem .var (.param ha.1 ha.2.1 ha.2.2.1 (.cons .var (.cons .var .nil)) rfl)) (.mem .var .var)

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
    | 1, hs => cases hs; exact ⟨_, rfl, ha⟩
    | 2, hs => cases hs; exact ⟨_, rfl, hb⟩
    | 3, hs => cases hs; exact ⟨_, rfl, ctr_sort H⟩
    | 4, hs => cases hs; exact ⟨_, rfl, val_sort H hv⟩
  hmatch := hX ▸ matchX H a b v
  hreq := fun t ht => by rw [r0_shape.1] at ht; cases ht
  hpre := by
    have hp := pre_at H (σ a b v)
    have h4 : (σ a b v).lookup 4 = some v := rfl
    have h1 : (σ a b v).lookup 1 = some a := rfl
    have h0 : (σ a b v).lookup 0 = some a := rfl
    have hab : (allSome [(σ a b v).lookup 1, (σ a b v).lookup 2]) = some [a, b] := rfl
    rw [hab, h4, h1, h0, Option.bind_some, hv] at hp
    have ht : (((some v).isSome && sameResult (some v) (some v)) &&
        ((some a).isSome && sameResult (some a) (some a))) = true := by
      simp [(sameResult_some_iff v (some v)).mpr rfl, (sameResult_some_iff a (some a)).mpr rfl]
    exact ht ▸ hp
  heval := hY ▸ evalD H a b v
  hens := fun t ht => by rw [r0_shape.2.1] at ht; cases ht
  hpost := by rw [r0_shape.2.2.2.1]; exact .top
  hprio := fun r' hr' hlt => (prio_none H hr' hlt).elim

/-- A substitution under which the left side denotes `<k> c(v) </k>` gives Open0 the value v and
the counter cell its value. -/
theorem lookups {H : HookParams} {τ : Subst} {v : GroundTerm}
    (hm : PatVal (cH H) τ r0.lhs (cfg (.ctor symC [v]))) :
    τ.lookup 4 = some v ∧ τ.lookup 3 = some ctr := by
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
    obtain ⟨h4, h3⟩ := lookups hm
    obtain ⟨a, h1, ha⟩ := hst.hσ 1 sA (by rw [r0_vars]; rfl)
    obtain ⟨b, h2, hb⟩ := hst.hσ 2 sA (by rw [r0_vars]; rfl)
    obtain ⟨x0, h0, -⟩ := hst.hσ 0 sA (by rw [r0_vars]; rfl)
    have hd := fnDet H
    have hp := Holds.functional_of_fnDet hd hst.hpre (pre_at H τ)
    rw [h4, h1, h2, h0] at hp
    have hab : allSome [some a, some b] = some [a, b] := rfl
    rw [hab, Option.bind_some] at hp
    have hv : (cH H).paramVal andS [a, b] = some v := by
      have hp' := hp.symm
      simp only [Option.isSome_some, Bool.true_and, Bool.and_eq_true] at hp'
      have : sameResult (some v) ((cH H).paramVal andS [a, b]) = true := hp'.1
      exact (sameResult_some_iff v _).mp this
    have hτ : ∀ j ∈ varOccs r0.rhs, (σ a b v).lookup j = τ.lookup j := fun j hj => by
      rcases rhs_vars j hj with rfl | rfl
      · exact h1.symm
      · exact h3.symm
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

/-! ## The text does not determine whether `c(x & y)` steps to `d(y)` -/

def dy : GroundTerm := cfg (.ctor symD [y])
def DY0 : Config (cH HookParams.none) := ⟨dy, by decide +kernel⟩

theorem DY0_ne : DY0 ≠ DX0 := fun h => absurd (congrArg Subtype.val h) (by decide +kernel)

open ML Faithful in
/-- **The text does not determine whether `<k> c(x & y) </k>` steps to `<k> d(y) </k>`**: over
all H, the reading's theory with the step's closure entails neither that `<k> d(y) </k>` is not a
successor of `<k> c(x & y) </k>` nor that it is one. The first is refuted at `Hswap`, where
`and(y, x)` is `x & y` and the step exists (`swap_y`, in a model exactness gives); the second at
`HookParams.none`, where `x & y` is `and`'s value at (x, y) only, so the configuration steps to
`<k> d(x) </k>` alone (`none_iff`), and the theory has a model. -/
theorem step_y_undetermined :
    ¬ (∀ H : HookParams, (Γc (cH H) ∪ Γstep (cH H)) ⊧
        (den (cH H) (cfg (.ctor symC [xy])) ⇒ ∼ KoreAML.sNext (den (cH H) dy))) ∧
    ¬ (∀ H : HookParams, (Γc (cH H) ∪ Γstep (cH H)) ⊧
        (den (cH H) (cfg (.ctor symC [xy])) ⇒ KoreAML.sNext (den (cH H) dy))) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨M, hM, I, hI, hn⟩ := (exact_hyp (cH Hswap) (coreOK_H Hswap) (fnHyp Hswap) XS DYS).mp swap_y
    exact hn (h Hswap hI)
  · have hns : ¬ Step (cH HookParams.none) X0 DY0 := fun hs => DY0_ne ((none_iff DY0).mp hs)
    obtain ⟨M, hM, I, hI⟩ := (sound_hyp (cH HookParams.none) (coreOK_H _) (fnHyp _)).1
    have hIΓ : I ⊧ᴵP Γ (cH HookParams.none) := fun φ hφ => hI φ (Or.inl (Or.inl hφ))
    have hno : I ⊧ᴵ (den (cH HookParams.none) X0.val ⇒ ∼ KoreAML.sNext (den (cH HookParams.none) DY0.val)) :=
      Classical.not_not.mp fun hn =>
        hns ((exact_hyp _ (coreOK_H _) (fnHyp _) X0 DY0).mpr ⟨M, hM, I, hI, hn⟩)
    have hx := ((elemOf_spec hIΓ X0.property KoreAML.val0).1 (elemOf (cH HookParams.none) I X0.val)).mpr rfl
    have h1 := hno KoreAML.val0 (elemOf (cH HookParams.none) I X0.val)
    have h2 := h HookParams.none hI KoreAML.val0 (elemOf (cH HookParams.none) I X0.val)
    rw [interpret_impl] at h1 h2
    have h3 := h1 hx
    rw [interpret_neg] at h3
    exact h3 (h2 hx)

end OpenCutStepAs

#check @OpenCutStepAs.step_iff
#check @OpenCutStepAs.none_iff
#check @OpenCutStepAs.swap_x
#check @OpenCutStepAs.swap_y
#print axioms OpenCutStepAs.step_iff
#print axioms OpenCutStepAs.none_iff
#print axioms OpenCutStepAs.swap_x
#print axioms OpenCutStepAs.swap_y
#check @OpenCutStepAs.step_y_undetermined
#print axioms OpenCutStepAs.step_y_undetermined
