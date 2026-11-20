/-
  The open generator of `f2-examples/e8-llvm-e2-open-mixed-clause.kompile.kore` (fixture
  e8-llvm-e2-open-mixed-clause: `A ::= x | y`, `B ::= A & A`, `&` declared `functional` and no
  constructor, `rule first(X & _) => X`) and the interpretations H of it at which the theory has a
  model. Run from the package root: `lake env lean -j1 test/OpenHandNonuniform.lean`.
  Kernel-checked (`decide +kernel`).

  `Γc (c.withHooks H)` with the step's closure has a model exactly where the values H gives `and`
  at values of A determine the first argument (`consistent_iff`). It has none at `Hswap`, which
  gives `and(x, y)` the value `and(y, x)` (`not_consistent_swap`), so consistency does not hold for
  every H (`not_consistent_all`); it has one at `lawHooks c H` for every H (`consistent_lawHooks`).
  The section after the preamble is the consistency section of the text's tie.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.OpenHandNonuniform

open KCore ML Faithful KoreAML

definition_of defn from "f2-examples/e8-llvm-e2-open-mixed-clause.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

/-- `and`, the text's one open generator (`raw`), and B, its sort. -/
def and : Sym := 389
def b : Srt := 32

theorem names : c.symName and = "Lbland" ∧ c.sortName b = "B" := by decide +kernel

/-- **The definition's one open generator is `and`**, of B, `assoc` false and `idem` false. -/
theorem params_raw : (c.params.filter (·.raw)).map (fun k => (k.sig.name, k.sig.args, k.sig.result, k.assoc, k.idem)) =
    [(and, [33, 33], b, false, false)] := by decide +kernel

set_option maxHeartbeats 1000000 in
theorem coreOK : c.coreOK = true := by decide_cheap
theorem coreOKH (H : HookParams) : (cH H).coreOK = true := (Semantics.coreOK_withHooks c H).trans coreOK

/-! ## Consistency: exactly at the interpretations where `and` determines its first argument -/

/- The text's sentences about `and` are its `functional` sentence, B's no junk (every element of B
is an `and(X0, X1)`) and the equation `first(X0) = X` under `X0 ∈ and(X, _Gen0)`; A's two
generators `x` and `y` are apart (the text's no-confusion sentence). The text states no law of
`and`. In a model of these, `and(a, g) = and(a', g')` gives `first` of that element both `a` and
`a'`, so `a = a'`: every model of the text keeps `and(x, y)` and `and(y, x)` apart. The text has
models (B the pairs of A, `first` the first projection).

`Γ (cH H)` holds the graph of `and` that H gives at values. So `Γc (cH H)` with the step's closure
has a model exactly where that graph determines the first argument (`FirstDet H`, `consistent_iff`):
- where it does not, at one pair of argument lists with one value and first arguments apart,
  `first` at that value evaluates to both first arguments (`eval_first`), each of which the
  application denotes in a model of `Γc` (`eval_den4_coreCl`), and two values of A denote apart
  (`no_model_of_clash`, `not_consistent_of_clash`). `Hswap`, which gives `and(x, y)` the value
  `and(y, x)` and leaves the other applications free, is such an H (`not_consistent_swap`), so no
  statement of consistency holds for every H (`not_consistent_all`);
- where it does, the clause of `first` is coherent with itself (`first_coherent`), which is the one
  fact the deciders leave (`first_match_named`), so `FnHyp` holds (`first_fnHyp`) and the theory has
  a model (`consistent`).
`lawHooks c H` gives `and` its free applications (`lawHooks_and`), which determine their arguments
(`firstDet_lawHooks`): the theory has a model there for every H (`consistent_lawHooks`). -/

def firstS : Sym := 388
def xS : Sym := 386
def yS : Sym := 387
def aSrt : Srt := 33

theorem first_names : c.symName firstS = "Lblfirst" ∧ c.symName xS = "Lblx" ∧ c.symName yS = "Lbly" ∧
    c.sortName aSrt = "A" := by decide +kernel

/-! ### The clause of `first` and the parameter `and` -/

/-- `first(V) => X` with the predicate `V ∈ and(X, G)`; X and G of A, V of B. -/
def clFirst : Clause :=
  { vars := [aSrt, aSrt, b], pats := [.var 2], req := none, rhs := .var 0, ens := none,
    pre := .mem b (.var 2) (.app and [.var 0, .var 1]) }
def fFirst : Fn := { label := firstS, args := [b], result := aSrt, clauses := [clFirst] }

theorem first_text : c.fns = [fFirst] := by rfl
theorem first_lookupH (H : HookParams) : (cH H).lookupFn firstS = some fFirst := by rfl

/-- `and` as the definition's parameter: open, with no law. -/
def andK : ParamSig := { sig := ⟨and, [aSrt, aSrt], b⟩, raw := true }

theorem andK_mem : andK ∈ c.params := by decide +kernel
theorem and_syms : c.isCtor and = false ∧ isHook and = false ∧ c.isParam and = true := by decide +kernel

theorem andK_shape (H : HookParams) : LawShape (cH H) andK :=
  Semantics.lawShape_core (coreOKH H) andK andK_mem rfl

/-- **The value of `and` at H**: what H gives, the application itself where H gives nothing, kept
where it is a value of B. -/
theorem and_paramVal (H : HookParams) {vs : List GroundTerm} {v : GroundTerm} :
    (cH H).paramVal and vs = some v ↔ v = (H.app and vs).getD (.ctor and vs) ∧ (cH H).sortOf v = some b :=
  paramVal_raw_sorted (c := cH H) (f := and) (k := andK) (andK_shape H).1 rfl (andK_shape H).2.2.1

/-- **An application of `and` is a value at H** where its arguments are values of A and H leaves it
as it is; it is then of B. -/
theorem and_value (H : HookParams) {ts : List GroundTerm} {s : Srt} :
    (cH H).sortOf (.ctor and ts) = some s ↔
      (cH H).sortsOf ts = some [aSrt, aSrt] ∧ (cH H).keepsRaw and ts = true ∧ s = b :=
  Semantics.sortOf_open_iff (c := cH H) (f := and) (k := andK) (andK_shape H).2.1 (andK_shape H).2.2.2.1
    (andK_shape H).2.2.2.2.1

theorem first_srt1 {C : Semantics} {v : GroundTerm} {s : Srt} (h : C.sortOf v = some s) :
    C.sortsOf [v] = some [s] :=
  sortsOf_cons.mpr ⟨s, [], h, sortsOf_nil, rfl⟩

theorem first_srt2 {C : Semantics} {v w : GroundTerm} {s t : Srt} (h1 : C.sortOf v = some s)
    (h2 : C.sortOf w = some t) : C.sortsOf [v, w] = some [s, t] :=
  sortsOf_cons.mpr ⟨s, [t], h1, first_srt1 h2, rfl⟩

/-- **The hypothesis on H**: the values H gives `and` at values of A determine the first argument. -/
def FirstDet (H : HookParams) : Prop :=
  ∀ a g a' g' v : GroundTerm, (cH H).sortOf a = some aSrt → (cH H).sortOf g = some aSrt →
    (cH H).sortOf a' = some aSrt → (cH H).sortOf g' = some aSrt →
    (cH H).paramVal and [a, g] = some v → (cH H).paramVal and [a', g'] = some v → a = a'

/-! ### `first` at a value of `and` -/

/-- `X ↦ a, G ↦ g, V ↦ v`. -/
def σFirst (a g v : GroundTerm) : Subst := [(0, a), (1, g), (2, v)]

theorem first_sorted (H : HookParams) {a g v : GroundTerm} (ha : (cH H).sortOf a = some aSrt)
    (hg : (cH H).sortOf g = some aSrt) (hp : (cH H).paramVal and [a, g] = some v) :
    (cH H).WellSorted clFirst.vars (σFirst a g v) := by
  have hv := ((and_paramVal H).mp hp).2
  intro i s hs
  match i, hs with
  | 0, hs =>
    obtain rfl : aSrt = s := by simpa [clFirst] using hs
    exact ⟨a, rfl, ha⟩
  | 1, hs =>
    obtain rfl : aSrt = s := by simpa [clFirst] using hs
    exact ⟨g, rfl, hg⟩
  | 2, hs =>
    obtain rfl : b = s := by simpa [clFirst] using hs
    exact ⟨v, rfl, hv⟩
  | n + 3, hs => simp [clFirst] at hs

/-- The predicate `V ∈ and(X, G)` at `σFirst a g v`, where `and(a, g)` is `v`: true. -/
theorem first_pre (H : HookParams) {a g v : GroundTerm} (hp : (cH H).paramVal and [a, g] = some v) :
    Holds (cH H) clFirst.vars.length (σFirst a g v) clFirst.pre true := by
  have h := Holds.mem (c := cH H) (n := clFirst.vars.length) (σ := σFirst a g v) (s := b)
    (EvalTerm.var (i := 2))
    (EvalTerm.param (f := and) (ts := [.var 0, .var 1]) and_syms.1 and_syms.2.1 and_syms.2.2
      (.cons (.var (i := 0)) (.cons (.var (i := 1)) .nil)) rfl)
  have e : (((σFirst a g v).lookup 2).isSome && sameResult ((σFirst a g v).lookup 2)
      ((allSome [(σFirst a g v).lookup 0, (σFirst a g v).lookup 1]).bind ((cH H).paramVal and))) = true := by
    show ((some v).isSome && sameResult (some v) ((cH H).paramVal and [a, g])) = true
    rw [hp]
    simp [sameResult, GroundTerm.cmp_refl]
  rw [e] at h
  exact h

/-- **Where `and(a, g)` is `v` at H, `first(v)` evaluates to `a`**, by the clause at `σFirst a g v`. -/
theorem eval_first (H : HookParams) {a g v : GroundTerm} (ha : (cH H).sortOf a = some aSrt)
    (hg : (cH H).sortOf g = some aSrt) (hp : (cH H).paramVal and [a, g] = some v) :
    Eval (cH H) firstS [v] (some a) :=
  .clause (cl := clFirst) (σ := σFirst a g v) (first_lookupH H) (List.mem_singleton_self _)
    (first_sorted H ha hg hp) (.cons (.var rfl) .nil) (fun _ ht => by cases ht) (first_pre H hp)
    (fun cl' hcl' _ hlt => by
      have hcl : cl' = clFirst := by simpa [fFirst] using hcl'
      subst hcl
      exact absurd hlt (Nat.lt_irrefl _))
    rfl .var (fun _ ht => by cases ht) .top

/-! ### No model where two applications with first arguments apart have one value -/

theorem first_owed_rules : c.owedRules = ([] : List Nat) := by decide +kernel
theorem first_owed_clauses : c.owedClauses = ([] : List (Nat × Nat)) := by decide +kernel

/-- No clause's condition is owed, under every H. -/
theorem first_noWit (H : HookParams) :
    ∀ fn ∈ (cH H).fns, ∀ cl ∈ fn.clauses, cl.needsWitness (cH H) = true → cl.CondDecided (cH H) :=
  openClauses_of_owed (by rw [Semantics.owedClauses_withHooks, first_owed_clauses]; intro p hp; cases hp)

theorem first_noExs : c.FnsNoExs := Semantics.fnsNoExs_of_all (by decide +kernel)
theorem first_noExsH (H : HookParams) : (cH H).FnsNoExs := (Semantics.fnsNoExs_withHooks _ _).mpr first_noExs

/-- **`Γc (cH H)` has no model where H gives `and(a, g)` and `and(a', g')` one value with `a` and
`a'` apart**: `first` of that value denotes the element of `a` and the element of `a'`. -/
theorem no_model_of_clash (H : HookParams) {a g a' g' v : GroundTerm}
    (ha : (cH H).sortOf a = some aSrt) (hg : (cH H).sortOf g = some aSrt)
    (ha' : (cH H).sortOf a' = some aSrt) (hg' : (cH H).sortOf g' = some aSrt)
    (hp : (cH H).paramVal and [a, g] = some v) (hp' : (cH H).paramVal and [a', g'] = some v) (hne : a ≠ a') :
    ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M), ¬ (I ⊧ᴵP Γc (cH H)) := by
  intro M _ I hIc
  obtain ⟨hok, hsr, hnn, hgw, hph, hcso, hcs, hph', hno⟩ := hypSound_of_core (coreOKH H)
  haveI : OvlOK (cH H) := hno
  have F := HoldsShape.nodeFacts_of_core (coreOKH H) hIc
  have hws : (cH H).sortsOf [v] = some fFirst.args := first_srt1 ((and_paramVal H).mp hp).2
  have hden := fun (r : Option GroundTerm) (hev : Eval (cH H) firstS [v] r) (e : Valuation M) (m : M) =>
    eval_den4_coreCl hIc (Semantics.sortedOKCl_of_sortedOK_noExs hok (first_noExsH H)) hsr
      (Semantics.coreOK_parts (coreOKH H)).2.1 hph (first_noWit H)
      (HoldsShape.preReadAll_of_core (coreOKH H) hIc) hev (first_lookupH H) hws e m
  let e : Valuation M := ⟨fun _ => default, fun _ _ => False⟩
  obtain ⟨m, hm, -⟩ := F.val ha [] e
  have h1 := (hden _ (eval_first H ha hg hp) e m).mpr ((hm m).mpr rfl)
  have h2 := (hden _ (eval_first H ha' hg' hp') e m).mp h1
  exact hne (F.apart ha ha' e m ((hm m).mpr rfl) h2)

/-- **Not `Consistent` there.** -/
theorem not_consistent_of_clash (H : HookParams) {a g a' g' v : GroundTerm}
    (ha : (cH H).sortOf a = some aSrt) (hg : (cH H).sortOf g = some aSrt)
    (ha' : (cH H).sortOf a' = some aSrt) (hg' : (cH H).sortOf g' = some aSrt)
    (hp : (cH H).paramVal and [a, g] = some v) (hp' : (cH H).paramVal and [a', g'] = some v) (hne : a ≠ a') :
    ¬ Consistent (cH H) := fun ⟨M, hM, I, hI⟩ =>
  no_model_of_clash H ha hg ha' hg' hp hp' hne M hM I (fun φ hφ => hI φ (Or.inl hφ))

/-- **A model at H makes `and` determine its first argument.** -/
theorem firstDet_of_consistent (H : HookParams) (hc : Consistent (cH H)) : FirstDet H :=
  fun _ _ _ _ _ ha hg ha' hg' hp hp' =>
    Classical.byContradiction fun hne => not_consistent_of_clash H ha hg ha' hg' hp hp' hne hc

/-! ### An interpretation without a model -/

def xT : GroundTerm := .ctor xS []
def yT : GroundTerm := .ctor yS []

theorem xy_data : c.rawFree xT = true ∧ c.rawFree yT = true ∧ c.sortOf xT = some aSrt ∧
    c.sortOf yT = some aSrt := by decide +kernel

/-- `x` and `y` are values of A under every H. -/
theorem xy_sorts (H : HookParams) : (cH H).sortOf xT = some aSrt ∧ (cH H).sortOf yT = some aSrt :=
  ⟨(Semantics.sortOf_withHooks_rawFree c H xy_data.1).trans xy_data.2.2.1,
   (Semantics.sortOf_withHooks_rawFree c H xy_data.2.1).trans xy_data.2.2.2⟩

/-- `and(x, y) ↦ and(y, x)`, and nothing elsewhere: `and(y, x)` stays the application, so the two
have one value. -/
def Hswap : HookParams :=
  ⟨fun f vs => if f = and then
      (match vs with
        | [.ctor p [], .ctor q []] => if p = xS ∧ q = yS then some (.ctor and [yT, xT]) else none
        | _ => none)
    else none⟩

theorem swap_app : Hswap.app and [xT, yT] = some (.ctor and [yT, xT]) ∧ Hswap.app and [yT, xT] = none :=
  ⟨rfl, rfl⟩

/-- `and(y, x)` is a value of B at `Hswap`. -/
theorem swap_sort : (cH Hswap).sortOf (.ctor and [yT, xT]) = some b :=
  (and_value Hswap).mpr ⟨first_srt2 (xy_sorts Hswap).2 (xy_sorts Hswap).1,
    (by simp [Semantics.keepsRaw, Semantics.withHooks, swap_app.2]), rfl⟩

theorem swap_val : (cH Hswap).paramVal and [xT, yT] = some (.ctor and [yT, xT]) ∧
    (cH Hswap).paramVal and [yT, xT] = some (.ctor and [yT, xT]) :=
  ⟨(and_paramVal Hswap).mpr ⟨by rw [swap_app.1]; rfl, swap_sort⟩,
   (and_paramVal Hswap).mpr ⟨by rw [swap_app.2]; rfl, swap_sort⟩⟩

/-- **`Γc` with the step's closure has no model at `Hswap`.** -/
theorem not_consistent_swap : ¬ Consistent (cH Hswap) :=
  not_consistent_of_clash Hswap (xy_sorts Hswap).1 (xy_sorts Hswap).2 (xy_sorts Hswap).2 (xy_sorts Hswap).1
    swap_val.1 swap_val.2 (fun h => by simp [xT, yT, xS, yS] at h)

/-- **Consistency does not hold for every H.** -/
theorem not_consistent_all : ¬ ∀ H : HookParams, Consistent (cH H) := fun h => not_consistent_swap (h Hswap)

/-! ### A model where `and` determines its first argument -/

theorem holds_mem_inv {C : Semantics} {n : Nat} {σ : Subst} {s : Srt} {t u : Term} {bb : Bool}
    (h : Holds C n σ (.mem s t u) bb) :
    ∃ r r', EvalTerm C σ t r ∧ EvalTerm C σ u r' ∧ bb = (r.isSome && sameResult r r') := by
  generalize hc : Cond.mem s t u = p at h
  cases h with
  | mem h h' => cases hc; exact ⟨_, _, h, h', rfl⟩
  | _ => cases hc

/-- Where the clause of `first` applies under σ at `vs`: `vs` is one value, the value of `and` at
σ's X and G, which are values of A. -/
theorem first_applies (H : HookParams) {σ : Subst} {vs : List GroundTerm} (h : clFirst.AppliesAt (cH H) σ vs) :
    ∃ a g v, σ.lookup 0 = some a ∧ (cH H).sortOf a = some aSrt ∧ (cH H).sortOf g = some aSrt ∧
      (cH H).paramVal and [a, g] = some v ∧ vs = [v] := by
  obtain ⟨hws, hpat, -, hpre⟩ := h
  have hw : (cH H).WellSorted clFirst.vars σ := (wellSortedAt_univ (cl := clFirst) rfl).mp hws
  obtain ⟨a, ea, hsa⟩ := hw 0 aSrt (by simp [clFirst])
  obtain ⟨g, eg, hsg⟩ := hw 1 aSrt (by simp [clFirst])
  obtain ⟨w, vs', rfl, hpv, hnil⟩ := PatVals.cons_inv hpat
  cases hnil
  have ew := PatVal.var_inv hpv
  obtain ⟨r, r', hr, hr', hb⟩ := holds_mem_inv hpre
  have er := EvalTerm.var_inv hr
  obtain ⟨rs, hrs, err⟩ := EvalTerm.param_inv (c := cH H) and_syms.1 and_syms.2.1 and_syms.2.2 hr'
  obtain ⟨r0, rs0, rfl, h0, hrs0⟩ := EvalTerms.cons_inv hrs
  obtain ⟨r1, rs1, rfl, h1, hrs1⟩ := EvalTerms.cons_inv hrs0
  cases EvalTerms.nil_inv hrs1
  have e0 := EvalTerm.var_inv h0
  have e1 := EvalTerm.var_inv h1
  subst er; subst e0; subst e1; subst err
  rw [ew, ea, eg] at hb
  refine ⟨a, g, w, ea, hsa, hsg, ?_, rfl⟩
  have hb' : sameResult (some w) ((cH H).paramVal and [a, g]) = true := by simpa [allSome] using hb.symm
  cases hq : (cH H).paramVal and [a, g] with
  | none => rw [hq] at hb'; simp [sameResult] at hb'
  | some w' =>
    rw [hq] at hb'
    simp only [sameResult, beq_iff_eq] at hb'
    rw [cmp_eq_iff.mp hb']

/-- **Under `FirstDet H` the clause of `first` is coherent with itself**: two matches at one value
give X one value. -/
theorem first_coherent (H : HookParams) (hH : FirstDet H) : Coherent (cH H) clFirst clFirst := by
  intro vs σ σ' h1 h2 _ _ _ _ _
  refine .inl ⟨rfl, rfl, rfl, rfl, fun i hi => ?_, fun t ht => by cases ht⟩
  have hi0 : i = 0 := by simpa [clFirst, varOccs] using hi
  subst hi0
  obtain ⟨a, g, v, e0, hsa, hsg, hpv, hvs⟩ := first_applies H h1
  obtain ⟨a', g', v', e0', hsa', hsg', hpv', hvs'⟩ := first_applies H h2
  subst hvs
  have hv : v' = v := by simpa using hvs'.symm
  subst hv
  rw [e0, e0', hH a g a' g' _ hsa hsg hsa' hsg' hpv hpv']

/-- `first`. -/
def firstOrder : List Sym := [firstS]

theorem first_term_named : c.preRankObligationsFP firstOrder = [] := by decide +kernel
theorem first_agree_named : c.agreeObligationsI = [] := by decide +kernel
theorem first_match_named : c.matchObligationsL = [(firstS, 0)] := by decide +kernel
theorem first_fnOvl : c.fnOvlSyms = [] := by decide +kernel
theorem first_rightHeld (H : HookParams) : (cH H).RightHeld :=
  Semantics.rightHeld_withHooks_of_valued (by decide +kernel) H

/-- The match independence the deciders leave, the clause of `first`'s, under `FirstDet H`. -/
theorem first_matchObl (H : HookParams) (hH : FirstDet H) : Det.MatchObligationsL (cH H) := by
  intro p hp fn hfn cl hcl
  rw [Det.Semantics.matchObligationsL_withHooks, first_match_named, List.mem_singleton] at hp
  subst hp
  rw [first_lookupH] at hfn
  cases hfn
  simp only [fFirst, List.getElem?_cons_zero, Option.some.injEq] at hcl
  subst hcl
  exact (matchIndependent_iff_noExs rfl).mpr (first_coherent H hH)

/-- `and` has no law: `OpenLaws` holds under every interpretation. -/
theorem first_openLaws (H : HookParams) : OpenLaws (cH H) := fun k hk hr => by
  have hk' : k ∈ c.params.filter (·.raw) := List.mem_filter.mpr ⟨hk, hr⟩
  have hm := List.mem_map_of_mem (f := fun k : ParamSig => (k.sig.name, k.sig.args, k.sig.result, k.assoc, k.idem)) hk'
  rw [params_raw, List.mem_singleton] at hm
  simp only [Prod.mk.injEq] at hm
  exact ⟨fun h => (by rw [hm.2.2.2.1] at h; cases h), fun h => (by rw [hm.2.2.2.2] at h; cases h)⟩

/-- **`FnHyp` under `FirstDet H`**: no function's termination, totality or agreement is named, no
condition is owed, and the one match independence named is `first_coherent`. -/
theorem first_fnHyp (H : HookParams) (hH : FirstDet H) : FnHyp (cH H) :=
  fnHyp_of_decidedPre (coreOKH H) (first_rightHeld H) (show (cH H).fnOvlSyms = [] from first_fnOvl) firstOrder
    (fun g hg => by rw [Semantics.preRankObligationsFP_withHooks, first_term_named] at hg; cases hg)
    (fun fn hfn ht => by
      have hfn' : fn ∈ [fFirst] := first_text ▸ hfn
      rw [List.mem_singleton] at hfn'
      subst hfn'
      exact absurd ht (by decide))
    (fun f hf => by rw [Det.Semantics.agreeObligationsI_withHooks, first_agree_named] at hf; cases hf)
    (first_matchObl H hH)
    ⟨openRules_of_owed (by rw [Semantics.owedRules_withHooks, first_owed_rules]; intro i hi; cases hi),
      first_noWit H⟩
    (first_openLaws H) (hnoEx := first_noExsH H)

/-- **`Γc` with the step's closure has a model at every H where `and` determines its first
argument.** -/
theorem consistent (H : HookParams) (hH : FirstDet H) : Consistent (cH H) :=
  consistent_of_fnHyp _ (coreOKH H) (first_fnHyp H hH)

/-- **`Γc` with the step's closure has a model at H exactly where `and`, as H gives it, determines
its first argument.** -/
theorem consistent_iff (H : HookParams) : Consistent (cH H) ↔ FirstDet H :=
  ⟨firstDet_of_consistent H, consistent H⟩

/-! ### At `lawHooks c H` -/

/-- `lawHooks c H` gives `and` its application. -/
theorem lawHooks_and (H : HookParams) (vs : List GroundTerm) :
    (lawHooks c H).app and vs = some (.ctor and vs) :=
  (lawHooks_app_self (c := c) (H := H) (k := andK) (Semantics.lawShape_core coreOK andK andK_mem rfl) vs).trans
    (congrArg some (lawApp_plain (k := andK) rfl rfl vs))

/-- **`lawHooks c H` makes `and` determine its arguments**, for every H. -/
theorem firstDet_lawHooks (H : HookParams) : FirstDet (lawHooks c H) := by
  intro a g a' g' v _ _ _ _ hp hp'
  have e1 := ((and_paramVal (lawHooks c H)).mp hp).1
  have e2 := ((and_paramVal (lawHooks c H)).mp hp').1
  rw [lawHooks_and, Option.getD_some] at e1 e2
  exact (List.cons.inj (GroundTerm.ctor.inj (e1.symm.trans e2)).2).1

/-- **`Γc` with the step's closure has a model at `lawHooks c H`, for every H.** -/
theorem consistent_lawHooks (H : HookParams) : Consistent (c.withHooks (lawHooks c H)) :=
  consistent (lawHooks c H) (firstDet_lawHooks H)

end KCore.OpenHandNonuniform

#check @KCore.OpenHandNonuniform.first_names
#check @KCore.OpenHandNonuniform.first_text
#check @KCore.OpenHandNonuniform.and_paramVal
#check @KCore.OpenHandNonuniform.and_value
#check @KCore.OpenHandNonuniform.eval_first
#check @KCore.OpenHandNonuniform.no_model_of_clash
#check @KCore.OpenHandNonuniform.not_consistent_of_clash
#check @KCore.OpenHandNonuniform.firstDet_of_consistent
#check @KCore.OpenHandNonuniform.swap_val
#check @KCore.OpenHandNonuniform.not_consistent_swap
#check @KCore.OpenHandNonuniform.not_consistent_all
#check @KCore.OpenHandNonuniform.first_applies
#check @KCore.OpenHandNonuniform.first_coherent
#check @KCore.OpenHandNonuniform.first_term_named
#check @KCore.OpenHandNonuniform.first_match_named
#check @KCore.OpenHandNonuniform.first_fnHyp
#check @KCore.OpenHandNonuniform.consistent
#check @KCore.OpenHandNonuniform.consistent_iff
#check @KCore.OpenHandNonuniform.lawHooks_and
#check @KCore.OpenHandNonuniform.firstDet_lawHooks
#check @KCore.OpenHandNonuniform.consistent_lawHooks
#print axioms KCore.OpenHandNonuniform.not_consistent_swap
#print axioms KCore.OpenHandNonuniform.not_consistent_all
#print axioms KCore.OpenHandNonuniform.consistent
#print axioms KCore.OpenHandNonuniform.consistent_iff
#print axioms KCore.OpenHandNonuniform.consistent_lawHooks
