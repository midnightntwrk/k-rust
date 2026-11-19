/-
  The fixture e2-clause-rhs-empty-owise: `syntax T ::= f(Int) [function]`,
  `rule f(0) => g(Y:Empty) [unboundVariables(Y)]` and `rule f(_) => a [owise]` (`syntax Empty`, no
  production; `T ::= "a" | g(Empty)`). The text is `f2-examples/rhsemptyowise.kompile.kore`; its
  sentence 210 is `f(X0) = g(Y)` where X0 is 0, Y free, so universal over Empty, and 209 is
  `f(X0) = a` where X0 is not 0 (the negated premise of 210 binds only its pattern: `\not(X0 ∈ 0)`).
  Run from the package root: `lake env lean -j1 test/TieClauseRhsEmptyOwise.lean`.

  - `f(1)` is `a` (C7 form (a), from sentences): for every H, in a model of the function sentences
    as written, Γ's rule items, the families and the closure of Bool (`Pre`), sentence 209 at
    X0 = 1, whose negated premise holds since 1 is not 0 (`f1_is_a`). `Pre` with the step's closure
    has a model for every H (`pre_model`): Γc with it has one (`consistent`, from `consistent_of`
    with `FnDet` and `FnSolves` shown here: `f(0) => g(Y)` applies under no substitution, Y being
    of Empty, so it decides nowhere). `FnHyp` is false here: `f(0)` has no result.
  - `f(0)` is not determined by the text (C7 form (c)): the reading's theory with the step's
    closure entails neither that `f(0)` has no element nor that it is a value of its sort
    (`f0_undetermined`). Both by the model of `KCore.EmptyInh` in which Empty holds an element `e`
    (`cP := EmptyInh.plus c 33`): it is a model of c's theory (`model`), and in it sentence 210 at
    `Y = e` makes `f(0)` the element of `g(e)` (`f0_is_ge`), which is no value of c (`a`, T's one
    value in c, is apart from it: `values_apart`). In the value model, where Empty is empty, the
    clause neither applies nor fails at 0 and `f(0)` has no result (`test/ClauseRhsEmpty.lean`,
    namespace `Owise`, `f0_none`). The hypotheses of `EmptyInh.premises_sub` and `FnHyp cP` are
    those of `test/ModelEmptyInhabited.lean` (namespace `EmptyInhFixtures.Owise`), restated here at
    `HookParams.none`, the H the negations are witnessed at.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.TieClauseRhsEmptyOwise

open KCore ML Faithful KoreAML EmptyInh

kore_term kore from "f2-examples/rhsemptyowise.kompile.kore"
definition_of defn from "f2-examples/rhsemptyowise.kompile.kore"
user_axioms U from "f2-examples/rhsemptyowise.kompile.kore" module "E2-CLAUSE-RHS-EMPTY-OWISE"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H
noncomputable abbrev cP : Semantics := plus c 33

/-- `tr s`: the item `Theory.ofDefinition kore` holds for the sentence. -/
noncomputable def trS (ad : AxiomDecl) : Item := trAxiom kore.symbolDecls kore.aliasNames ad

def fS : Sym := 388
def aS : Sym := 386
def gS : Sym := 387

theorem names : c.symName fS = "Lblf" ∧ c.symName aS = "Lbla" ∧ c.symName gS = "Lblg" ∧
    c.sortName 33 = "Empty" ∧ eSym c = 389 := by
  decide +kernel

/-- The parsed data's interpretation is `HookParams.none`. -/
theorem cH_none : cH HookParams.none = c := rfl

theorem coreOK : c.coreOK = true := by decide_cheap
theorem coreOKH (H : HookParams) : (cH H).coreOK = true := (Semantics.coreOK_withHooks c H).trans coreOK

/-! ## What the reader reads -/

theorem facts : c.ovls = [] ∧ c.params = [] ∧ c.ctorSigs.all (·.name != eSym c) = true ∧ c.gens 33 = [] ∧
    (c.readsConfined = true → cP.readsConfined = true) ∧ (c.litSort Srt.bool = true → cP.litSort Srt.bool = true) := by
  decide +kernel

theorem noRaw : ∀ k ∈ c.params, k.raw = false := fun k hk => by rw [facts.2.1] at hk; cases hk

theorem sortOfH (H : HookParams) : (cH H).sortOf = c.sortOf := Semantics.sortOf_withHooks c H noRaw
theorem sortsOfH (H : HookParams) : (cH H).sortsOf = c.sortsOf := Semantics.sortsOf_withHooks c H noRaw

theorem wh_patCtxAll (H : HookParams) : (cH H).patCtxAll = c.patCtxAll := rfl
theorem wh_patCtxNF (H : HookParams) : (cH H).patCtxNF = c.patCtxNF := rfl
theorem wh_isCtor (H : HookParams) : (cH H).isCtor = c.isCtor := rfl

noncomputable def fF : Fn := c.fns[0]'(by decide +kernel)
noncomputable def cl0 : Clause := fF.clauses[0]'(by decide +kernel)
noncomputable def clX : Clause := fF.clauses[1]'(by decide +kernel)

theorem fF_mem : fF ∈ c.fns := List.getElem_mem _

/-- `f(0) => g(Y:Empty)` at priority 50 and `f(X:Int) => a` at priority 200 (the `[owise]` one);
`g : Empty → T` and `a : T` are constructors. -/
theorem shape : c.fns.length = 1 ∧ fF.label = fS ∧ fF.args = [Srt.int] ∧ fF.clauses.length = 2 ∧
    cl0.vars = [33] ∧ cl0.leftVars = [] ∧ cl0.exs = [] ∧ clX.vars = [Srt.int] ∧ clX.leftVars = [0] ∧
    clX.exs = [] ∧ cl0.prio = 50 ∧ clX.prio = 200 ∧ cl0.aside = false ∧ clX.aside = false ∧
    c.isCtor gS = true ∧ c.isCtor aS = true ∧ lookupSig c.ctorSigs gS = some ⟨gS, [33], fF.result⟩ ∧
    lookupSig c.ctorSigs aS = some ⟨aS, [], fF.result⟩ := by
  decide +kernel

theorem cl0_pats : cl0.pats = [.dv Srt.int (.int 0)] := by rfl
theorem cl0_req : cl0.req = none := by rfl
theorem cl0_ens : cl0.ens = none := by rfl
theorem cl0_rhs : cl0.rhs = .app gS [.var 0] := by rfl
theorem cl0_pre : cl0.pre = .top := by rfl
theorem clX_pats : clX.pats = [.var 0] := by rfl
theorem clX_req : clX.req = none := by rfl
theorem clX_ens : clX.ens = none := by rfl
theorem clX_rhs : clX.rhs = .app aS [] := by rfl
theorem clX_pre : clX.pre = .top := by rfl
theorem clX_post : clX.post = .top := by rfl
theorem cl0_post : cl0.post = .top := by rfl

theorem fns_eq : c.fns = [fF] := by
  apply List.ext_getElem (by rw [shape.1]; rfl)
  intro i h1 _
  have : i < 1 := shape.1 ▸ h1
  match i, this with
  | 0, _ => rfl

theorem clauses_eq : fF.clauses = [cl0, clX] := by
  apply List.ext_getElem (by rw [shape.2.2.2.1]; rfl)
  intro i h1 _
  have : i < 2 := shape.2.2.2.1 ▸ h1
  match i, this with
  | 0, _ => rfl
  | 1, _ => rfl

theorem cl0_mem : cl0 ∈ fF.clauses := by rw [clauses_eq]; simp
theorem clX_mem : clX ∈ fF.clauses := by rw [clauses_eq]; simp

theorem lookupF : c.lookupFn fS = some fF := shape.2.1 ▸ lookupFn_of_core coreOK fF_mem
theorem lookupFH (H : HookParams) : (cH H).lookupFn fS = some fF := by
  rw [Semantics.lookupFn_withHooks]; exact lookupF

theorem lookupFH_eq {H : HookParams} {fn : Fn} (h : (cH H).lookupFn fS = some fn) : fn = fF :=
  Option.some.inj (h.symm.trans (lookupFH H))

def one : GroundTerm := .dv Srt.int (.int 1)
def zero : GroundTerm := .dv Srt.int (.int 0)
def aV : GroundTerm := .ctor aS []

theorem one_sort : c.sortOf one = some Srt.int := sortOf_dv.mpr ⟨by decide +kernel, rfl⟩
theorem zero_sort : c.sortOf zero = some Srt.int := sortOf_dv.mpr ⟨by decide +kernel, rfl⟩
theorem aV_sort : c.sortOf aV = some fF.result := sortOf_ctor_intro ⟨_, shape.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2, sortsOf_nil, rfl⟩

/-! ## The second model (the hypotheses of `EmptyInh.premises_sub` and `FnHyp cP`) -/

theorem hooksNone : ∀ f vs, c.hooks.app f vs = none := fun _ _ => rfl

theorem empty : c.ctorSigs.all (·.result != 33) = true ∧ c.subsorts.all (fun p => p.2 != 33) = true ∧
    c.collOf 33 = none ∧ c.lib.carriers.all (·.1 != 33) = true ∧
    ((33 : Srt) != Srt.int && (33 : Srt) != Srt.bool && (33 : Srt) != Srt.kconfigVar && (33 : Srt) != Srt.string &&
      (33 : Srt) != Srt.bytes && (33 : Srt) != Srt.float && !c.lib.tokenSorts.contains 33 &&
      !c.lib.byteSorts.contains 33) = true := by
  decide +kernel

theorem fresh : ∀ k ∈ c.ctorSigs, k.name ≠ eSym c := fun k hk => by
  simpa using List.all_eq_true.mp facts.2.2.1 k hk

theorem freshP : ∀ k ∈ c.params, k.sig.name ≠ eSym c := fun k hk => by
  rw [facts.2.1] at hk; cases hk

theorem sortOf_e : cP.sortOf (eVal c) = some 33 :=
  EmptyInh.sortOf_e facts.1 fresh freshP (keepsRaw_of_none hooksNone)

theorem value_eq {v : GroundTerm} (h : cP.sortOf v = some 33) : v = eVal c :=
  value_E_eq empty.1 facts.1 noRaw empty.2.1 empty.2.2.1 empty.2.2.2.1 empty.2.2.2.2 h

/-- `e` is no value of c. -/
theorem e_not_c : c.sortOf (eVal c) = none := by decide +kernel

/-- **No value of c has sort Empty**, under every H. -/
theorem no_E (H : HookParams) (v : GroundTerm) : (cH H).sortOf v ≠ some 33 := fun h => by
  rw [sortOfH] at h
  have e := value_eq (sortOf_plus h)
  subst e
  rw [e_not_c] at h; cases h

theorem openLawsP : OpenLaws cP := by
  intro k hk _
  have hk' : k ∈ c.params ++ [eParam c 33] := hk
  rw [facts.2.1, List.nil_append, List.mem_singleton] at hk'
  subst hk'
  exact ⟨fun h => by simp [eParam] at h, fun h => by simp [eParam] at h⟩

theorem noFail : ∀ fn ∈ c.fns, ∀ vs, c.sortsOf vs = some fn.args → ∃ cl ∈ fn.clauses, ¬ Fails c vs cl := by
  intro fn hfn vs hvs
  rw [fns_eq, List.mem_singleton] at hfn
  subst hfn
  rw [shape.2.2.1] at hvs
  obtain ⟨v, rfl, hv⟩ := sortsOf_single hvs
  exact ⟨clX, clX_mem, not_fails_var shape.2.2.2.2.2.2.2.1 clX_pats clX_req clX_pre hv⟩

theorem sub : ∀ φ, φ ∈ Γc c ∪ Γstep c → φ ∈ Γc cP ∪ Γstep cP :=
  premises_sub facts.1 fresh facts.2.2.2.1
    (fun k hk => by rw [facts.2.1] at hk; cases hk)
    (fun k _ vs _ _ _ => fallback_plus_of_none hooksNone k.name vs)
    (hfails_of_noFail noFail) facts.2.2.2.2.1 facts.2.2.2.2.2

theorem namedP : cP.coreOK = true ∧ cP.heldObligations = [fS] ∧
    cP.rankObligations [fS] ++ cP.decObligationsL = [] ∧ cP.totalObligationsRP [fS] [] = [] ∧
    cP.agreeObligationsI = [] ∧ cP.matchObligationsL = [(fS, 0)] ∧ cP.owedRules = [] ∧
    cP.owedClauses = [] := by
  decide_cheap

theorem coreP : cP.coreOK = true := namedP.1

theorem lookupFP : cP.lookupFn fS = some fF :=
  shape.2.1 ▸ lookupFn_of_core coreP (show fF ∈ cP.fns from fF_mem)

theorem lookupFP_eq {fn : Fn} (h : cP.lookupFn fS = some fn) : fn = fF :=
  Option.some.inj (h.symm.trans lookupFP)

theorem heldP : ∀ f ∈ cP.heldObligations, HeldOwed cP f := by
  intro f hf fn hfn
  rw [namedP.2.1, List.mem_singleton] at hf
  subst hf
  have e := lookupFP_eq hfn
  subst e
  refine .inl fun cl hcl i s hi => ?_
  rw [clauses_eq] at hcl
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hcl
  rcases hcl with rfl | rfl
  · rw [shape.2.2.2.2.1] at hi
    cases i with
    | zero => cases hi; exact .inr ⟨eVal c, sortOf_e⟩
    | succ i => simp at hi
  · rw [shape.2.2.2.2.2.2.2.1] at hi
    cases i with
    | zero => exact .inl (by rw [shape.2.2.2.2.2.2.2.2.1]; simp)
    | succ i => simp at hi

theorem match0P : MatchIndependent cP cl0 := by
  obtain ⟨-, -, -, -, hv, -, hx, -⟩ := shape
  refine (matchIndependent_iff_noExs hx).mpr fun vs σ σ' ha ha' _ _ _ _ _ => .inl
    ⟨hx, hx, rfl, rfl, fun i hi => ?_, fun t ht => by rw [cl0_ens] at ht; cases ht⟩
  rw [cl0_rhs] at hi
  simp [varOccs, varOccsList] at hi
  subst hi
  have h0 : (0 : Nat) ∈ cl0.univ := by simp [Clause.univ, hv, hx]
  obtain ⟨v, hv1, hv2⟩ := ha.1 0 h0 33 (by rw [hv]; rfl)
  obtain ⟨w, hw1, hw2⟩ := ha'.1 0 h0 33 (by rw [hv]; rfl)
  rw [hv1, hw1, value_eq hv2, value_eq hw2]

theorem oblP : FnObligations cP [fS] [] := by
  obtain ⟨-, -, hterm, htot, hagr, hmat, howR, howC⟩ := namedP
  refine ⟨fun f hf => (by rw [hterm] at hf; cases hf), fun f hf => (by rw [htot] at hf; cases hf),
    fun f hf => (by rw [hagr] at hf; cases hf), fun p hp fn hfn cl hcl => ?_,
    ⟨openRules_of_owed (by rw [howR]; intro i hi; cases hi),
     openClauses_of_owed (by rw [howC]; intro p hp; cases hp)⟩, openLawsP⟩
  rw [hmat, List.mem_singleton] at hp
  subst hp
  have e := lookupFP_eq hfn
  subst e
  rw [clauses_eq] at hcl
  simp only [List.getElem?_cons_zero, Option.some.injEq] at hcl
  subst hcl
  exact match0P

theorem fnHypP : FnHyp cP := fnHyp_of_fnObligationsN coreP heldP ParamsTotal.nil oblP

theorem model : ∃ (M : Type) (_ : Inhabited M) (I : ML.Interpretation KoreAML.Sym M),
    (I ⊧ᴵP (Γc cP ∪ Γstep cP)) ∧ (I ⊧ᴵP (Γc c ∪ Γstep c)) :=
  model_exists sub coreP fnHypP

/-! ## `f(0)` in the second model: the element of `g(e)` -/

noncomputable def ge : GroundTerm := .ctor gS [eVal c]

theorem ge_sort : cP.sortOf ge = some fF.result :=
  sortOf_ctor_intro ⟨_, shape.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, sortsOf_cons.mpr ⟨_, _, sortOf_e, sortsOf_nil, rfl⟩, rfl⟩

theorem ge_not_c : c.sortOf ge = none := by decide +kernel

noncomputable def σe : Subst := [(0, eVal c)]

theorem ws_e : cP.WellSorted cl0.vars σe := fun i s hs => by
  rw [shape.2.2.2.2.1] at hs
  cases i with
  | zero =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hs
    subst hs
    exact ⟨_, rfl, sortOf_e⟩
  | succ i => simp at hs

theorem patval0 : PatVal cP σe cl0.rhs ge := by
  rw [cl0_rhs]
  exact .ctor shape.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (.cons (.var rfl) .nil)

theorem low0 : lowerClauses fF cl0 = [] := List.isEmpty_iff.mp (by decide +kernel)

theorem rhsv0 : ∀ i ∈ varOccs cl0.rhs, i < cl0.vars.length := by
  rw [cl0_rhs, shape.2.2.2.2.1]; simp [varOccs, varOccsList]

theorem rhs_plainP : plainPat cP cl0.rhs = true := by decide +kernel
theorem rhs_sortP : sortOfTerm cP.patCtxAll cl0.vars cl0.rhs = some fF.result := by decide +kernel
theorem pats_sortsP : sortsOfTerms cP.patCtxAll cl0.vars cl0.pats = some fF.args := by decide +kernel
theorem pats_plainP : plainPats cP cl0.pats = true := by decide +kernel

theorem occ0 : ∀ i < cl0.vars.length, i ∈ varOccsList cl0.pats ++ cl0.condVars ++ varOccs cl0.rhs ++
    (cl0.ens.map varOccs).getD [] := by
  intro i hi
  rw [shape.2.2.2.2.1] at hi
  have : i = 0 := by simpa using hi
  subst this
  rw [cl0_rhs]
  simp [varOccs, varOccsList]

/-- **Sentence 210 at `Y = e`**: in a model of `cP`'s Γ, `f(0)` is what `g(e)` denotes. -/
theorem f0_is_ge {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hΓ : I ⊧ᴵP Γ cP)
    (e0 : Valuation M) (m : M) :
    (TiePair.app c fS [zero]).interpret I e0 m ↔ (den c ge).interpret I e0 m := by
  obtain ⟨hsok, hsr', hnn, -, -, -, -, -, hno⟩ := hypSound_of_core coreP
  haveI : OvlOK cP := hno
  have htr := (sortCtx_of_all hsok hsr' (OvlOK.ovlCase hno)).trans
  have hfnm := (lookupFn_spec lookupFP).1
  have ihrhs : ∀ (tbl : VarTable) (e : Valuation M), Agrees cP I tbl (canonVars cP cl0.vars) σe e →
      ∀ m, (KoreAML.tr ⟨tbl, []⟩ (clauseRight cP fF cl0)).interpret I e m ↔ Res cP I e (some ge) m :=
    fun tbl e hag => right_iff hΓ hnn hfnm (fun v hv => by cases hv; exact ge_sort)
      (fun m => (patVal_den hΓ hnn.1 htr ws_e (canonVars_length _ _) hag patval0 rhs_plainP rhs_sortP).2 m)
      (fun t h => by rw [cl0_ens] at h; cases h)
  have hws : cP.sortsOf [zero] = some fF.args := by
    rw [shape.2.2.1]; exact sortsOf_cons.mpr ⟨_, _, sortOf_plus zero_sort, sortsOf_nil, rfl⟩
  have h := clause_eq_open hΓ hnn htr lookupFP cl0_mem low0 cl0_pre shape.2.2.2.2.2.2.1 hws ws_e
    (by rw [cl0_pats]; exact .cons .dv .nil) pats_plainP pats_sortsP occ0
    (fun t h => by rw [cl0_req] at h; cases h) rhsv0
    (fun t h => by rw [cl0_ens] at h; cases h) (r := some ge) (fun v hv => by cases hv; exact ge_sort)
    (fun _ _ _ t h => by rw [cl0_req] at h; cases h) ihrhs e0 m
  unfold TiePair.app
  rw [← symApp_plus (E := 33), ← koreList_plus_fun (E := 33), ← den_plus (E := 33)]
  exact h

/-! ## The expectation for `f(0)` (C7 form (c)) -/

/-- **The text determines no value of `f(0)`**: over all H, the reading's theory with the step's
closure entails neither that `f(0)` has no element nor that it is any value of its sort. At
`HookParams.none`, the model in which Empty holds `e` makes `f(0)` the element of `g(e)`, which is
no value of c. -/
theorem f0_undetermined :
    ¬ (∀ H : HookParams, (Γc (cH H) ∪ Γstep (cH H)) ⊧ (TiePair.app (cH H) fS [zero] ≡ ⊥)) ∧
    ∀ v, c.sortOf v = some fF.result →
      ¬ (∀ H : HookParams, (Γc (cH H) ∪ Γstep (cH H)) ⊧ (TiePair.app (cH H) fS [zero] ≡ den (cH H) v)) := by
  obtain ⟨M, hM, I, hP, hc⟩ := model
  have hΓP : I ⊧ᴵP Γ cP := fun φ hφ => hP φ (Or.inl (Or.inl hφ))
  have hD := defOK hΓP
  have hspec := elemOf_spec hΓP ge_sort KoreAML.val0
  have hfe : ∀ m, (TiePair.app c fS [zero]).interpret I KoreAML.val0 m ↔ m = elemOf cP I ge := fun m =>
    (f0_is_ge hΓP _ m).trans (by rw [← den_plus (E := 33)]; exact hspec.1 m)
  refine ⟨fun h => ?_, fun v hv h => ?_⟩
  · have h1 := h HookParams.none hc KoreAML.val0 (elemOf cP I ge)
    rw [cH_none, KoreAML.interp_equal hD] at h1
    have := ((h1 (elemOf cP I ge)).mp ((hfe _).mpr rfl))
    simp at this
  · have h1 := h HookParams.none hc KoreAML.val0 (elemOf cP I ge)
    rw [cH_none, KoreAML.interp_equal hD] at h1
    have hvP : cP.sortOf v = some fF.result := sortOf_plus hv
    have hspecv := elemOf_spec hΓP hvP KoreAML.val0
    have hm := (h1 (elemOf cP I ge)).mp ((hfe _).mpr rfl)
    rw [← den_plus (E := 33)] at hm
    have heq : elemOf cP I ge = elemOf cP I v := (hspecv.1 _).mp hm
    obtain ⟨hsok, hsr', -, hg, -, -, -, -, hno⟩ := hypSound_of_core coreP
    haveI : OvlOK cP := hno
    have htr := (sortCtx_of_all hsok hsr' (OvlOK.ovlCase hno)).trans
    have := values_apart hΓP hg htr (apartSort_of_sorted hg ge_sort) ge_sort hvP heq
    rw [← this, ge_not_c] at hv
    cases hv

/-! ## `f(1)`: the function sentences -/

/-- The text sentences of Γ's equations, in `fnItems`'s order: `f`'s two (210, `f(0) => g(Y)`, then
209, the `[owise]` one), then the sort predicates'. -/
noncomputable def fnText : List AxiomDecl := TiePair.fnTextOf c U.all

theorem fnText_index : (fnText.map (·.index)).take 2 = [210, 209] := by decide +kernel

noncomputable def textPats : List P := fnText.map (trS · |>.pat)

/-- **Each of Γ's equations is the translation of its text sentence** (`TiePair.sameB`; kernel). -/
theorem shapeT : TiePair.shapeB (TiePair.gammaPats c) textPats = true := by decide +kernel

theorem shapeH (H : HookParams) : TiePair.shapeB (TiePair.gammaPats (cH H)) textPats = true := by
  rw [TiePair.gammaPats_withHooks]; exact shapeT

/-- **E for the function equations**: Γ entails each, for every H. -/
theorem fns_entailed (H : HookParams) : ∀ ad ∈ fnText, Γ (cH H) ⊧ (trS ad).pat :=
  fun _ had => TiePair.entailed (shapeH H) _ (List.mem_map_of_mem had)

/-! ## `f(1)`: Γ with the step's closure has a model, for every H -/

/-- `f(0) => g(Y)` applies under no substitution, under every H: Y is of Empty. -/
theorem cl0_not_applies (H : HookParams) (σ : Subst) (vs : List GroundTerm) : ¬ cl0.AppliesAt (cH H) σ vs := by
  rintro ⟨h, -⟩
  have hu : cl0.univ = [0] := by
    unfold Clause.univ; rw [shape.2.2.2.2.1, shape.2.2.2.2.2.2.1]; rfl
  obtain ⟨v, -, hv⟩ := h 0 (by rw [hu]; exact List.mem_singleton_self _) 33 (by rw [shape.2.2.2.2.1]; rfl)
  exact no_E H v hv

theorem fnsH (H : HookParams) : (cH H).fns = [fF] := fns_eq

theorem agreeH (H : HookParams) : ∀ fn ∈ (cH H).fns, ClausesAgree (cH H) fn := by
  intro fn hfn
  rw [fnsH, List.mem_singleton] at hfn
  subst hfn
  intro cl cl' hp hcomp
  have hp' : (cl, cl') = (cl0, clX) := by rw [clauses_eq] at hp; simpa [pairs] using hp
  cases hp'
  obtain ⟨-, -, -, -, -, -, -, -, -, -, h0, hX, a0, aX, -⟩ := shape
  exact absurd hcomp (not_compete (by rw [h0, hX, a0, aX]; decide))

theorem matchH (H : HookParams) : ∀ fn ∈ (cH H).fns, ∀ cl ∈ fn.clauses, MatchIndependent (cH H) cl := by
  intro fn hfn cl hcl
  rw [fnsH, List.mem_singleton] at hfn
  subst hfn
  rw [clauses_eq] at hcl
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hcl
  rcases hcl with rfl | rfl
  · exact (matchIndependent_iff_noExs shape.2.2.2.2.2.2.1).mpr fun vs σ _ ha =>
      absurd ha (cl0_not_applies H σ vs)
  · have hx := shape.2.2.2.2.2.2.2.2.2.1
    refine (matchIndependent_iff_noExs hx).mpr fun vs σ σ' _ _ _ _ _ _ _ => .inl
      ⟨hx, hx, rfl, rfl, fun i hi => ?_, fun t ht => by rw [clX_ens] at ht; cases ht⟩
    rw [clX_rhs] at hi
    simp [varOccs, varOccsList] at hi

theorem fnDetH (H : HookParams) : FnDet (cH H) := Faithful.fnDet_of_agree (agreeH H) (matchH H)

theorem reqPreH : ∀ cl ∈ fF.clauses, cl.req = none ∧ cl.pre = .top := by
  intro cl hcl
  rw [clauses_eq] at hcl
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hcl
  rcases hcl with rfl | rfl
  · exact ⟨cl0_req, cl0_pre⟩
  · exact ⟨clX_req, clX_pre⟩

/-- A constant constructor evaluates to itself. -/
theorem evalConst {c : Semantics} {σ : Subst} {f : Sym} (h : c.isCtor f = true) :
    EvalTerm c σ (.app f []) (some (.ctor f [])) :=
  EvalTerm.ctor (rs := []) h .nil

theorem a_eval (H : HookParams) (σ : Subst) : EvalTerm (cH H) σ clX.rhs (some aV) := by
  rw [clX_rhs]
  exact evalConst (by rw [wh_isCtor]; exact shape.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)

/-- **Evaluation solves the equations**, for every H: `f(0) => g(Y)` decides nowhere, and the
`[owise]` clause's instance is `a`. -/
theorem fnSolvesH (H : HookParams) : FnSolves (cH H) := by
  refine fnSolves_of_parts_lookup (fun fn hfn => ?_) (fnDetH H) (fun fn hfn cl hcl => ?_) ?_ ?_
  · rw [fnsH, List.mem_singleton] at hfn; subst hfn; rw [shape.2.1]; exact lookupFH H
  · rw [fnsH, List.mem_singleton] at hfn; subst hfn
    rw [clauses_eq] at hcl
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hcl
    rcases hcl with rfl | rfl
    · exact ⟨shape.2.2.2.2.2.2.1, cl0_post⟩
    · exact ⟨shape.2.2.2.2.2.2.2.2.2.1, clX_post⟩
  · intro fn hfn _ _ _ _ _ cl' hcl' _ _ σ' _ _
    rw [fnsH, List.mem_singleton] at hfn; subst hfn
    obtain ⟨hr, hp⟩ := reqPreH cl' hcl'
    exact ⟨(fun t ht => by rw [hr] at ht; cases ht), true, Clause.holds_preTop hp σ'⟩
  · intro fn hfn vs cl σ cl' σ' _ hcl' _ hdec' _
    rw [fnsH, List.mem_singleton] at hfn; subst hfn
    rw [clauses_eq] at hcl'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hcl'
    rcases hcl' with rfl | rfl
    · exact absurd hdec'.1 (cl0_not_applies H σ' vs)
    · exact ⟨some aV, Or.inl ⟨(fun t ht => by rw [clX_ens] at ht; cases ht), a_eval H σ'⟩⟩

theorem preTop_all : (c.fns.all fun f => f.clauses.all fun cl => cl.pre.isTop) = true := by decide +kernel

/-- **Γc with the step's closure has a model, for every H** (`consistent_of`: `coreOK`, `FnDet`,
`FnSolves`, the clauses' predicates `\top`, no open generator). -/
theorem consistent (H : HookParams) : Consistent (cH H) :=
  consistent_of (cH H) (coreOKH H) (fnDetH H) (fnSolvesH H) (clausePreDecided_of_isTop preTop_all)
    (clausePostDecided_of_isTop (c := cH H)
      (by decide +kernel : (c.fns.all fun f => f.clauses.all fun cl => cl.post.isTop) = true))
    (openLaws_of_plain noRaw)

/-! ## The expectation for `f(1)` (C7 form (a)) -/

/-- The premises of the derivation: the function sentences as written (both of `f`'s), Γ's rule
items, the families, and the closure of Bool (`Γcl`). -/
noncomputable def Pre (H : HookParams) : Premises KoreAML.Sym := TiePair.Pre (cH H) textPats ∪ Γcl (cH H)

/-- **`Pre` with the step's closure has a model, for every H.** -/
theorem pre_model (H : HookParams) :
    ∃ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M), I ⊧ᴵP (Pre H ∪ Γstep (cH H)) := by
  obtain ⟨M, hM, I, hI⟩ := consistent H
  have hΓ : I ⊧ᴵP Γ (cH H) := fun φ hφ => hI φ (Or.inl (Or.inl hφ))
  refine ⟨M, hM, I, fun φ hφ => ?_⟩
  rcases hφ with (hφ | hφ) | hφ
  · rcases hφ with ((h1 | h1) | h1)
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
  · exact hI φ (Or.inl (Or.inr hφ))
  · exact hI φ (Or.inr hφ)

kernel_rfl cso_withHooks : ∀ (H : HookParams) (L : List CtorSig),
  (cH H).clauseSortedOpen fF L cl0 = c.clauseSortedOpen fF L cl0
kernel_rfl cpo_withHooks : ∀ (H : HookParams), (cH H).clausePlainOpen cl0 = c.clausePlainOpen cl0
kernel_rfl nw_withHooks : ∀ (H : HookParams), cl0.needsWitness (cH H) = cl0.needsWitness c
kernel_rfl cok_withHooks : ∀ (H : HookParams), (cH H).condOK cl0.vars cl0.pre = c.condOK cl0.vars cl0.pre
kernel_rfl condOKX_withHooks : ∀ (H : HookParams), (cH H).condOK clX.vars clX.pre = c.condOK clX.vars clX.pre

theorem cl0_open : c.clauseSortedOpen fF (c.allFns.map (·.sig)) cl0 = true ∧ c.clausePlainOpen cl0 = true ∧
    cl0.needsWitness c = false ∧ c.condOK cl0.vars cl0.pre = true ∧ c.condOK clX.vars clX.pre = true ∧
    (cl0.openCondVars.any fun i => (cl0.vars[i]?.map c.confined).getD false) = false := by
  decide +kernel

kernel_rfl ocv_withHooks : ∀ (H : HookParams),
  (cl0.openCondVars.any fun i => (cl0.vars[i]?.map (cH H).confined).getD false) =
    (cl0.openCondVars.any fun i => (cl0.vars[i]?.map c.confined).getD false)

kernel_rfl allFns_withHooks : ∀ (H : HookParams), (cH H).allFns = c.allFns

theorem low_X : lowerClauses fF clX = [cl0] := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, h0, hX, a0, aX, -⟩ := shape
  simp [lowerClauses, clauses_eq, h0, hX, a0, aX]

theorem pats_sorts0 : sortsOfTerms c.patCtxAll cl0.vars cl0.pats = some fF.args := by decide +kernel
theorem pats_sortsXN : sortsOfTerms c.patCtxNF clX.vars clX.pats = some fF.args := by decide +kernel

theorem occX : ∀ i < clX.vars.length, i ∈ varOccsList clX.pats ++ clX.condVars ++
    varOccs clX.rhs ++ (clX.ens.map varOccs).getD [] ++ varOccsCond clX.vars.length clX.post := by
  intro i hi
  rw [shape.2.2.2.2.2.2.2.1] at hi
  have : i = 0 := by simpa using hi
  subst this
  rw [clX_pats]
  simp [varOccsList, varOccs]

-- The `[owise]` clause's right side `a`, as the translation writes it, is the value `a`'s pattern.
kernel_rfl rhs_koreX : ∀ (H : HookParams) (vs : List KoreAML.Var),
  Term.kore (cH H) vs clX.rhs = GroundTerm.kore (cH H) aV

/-- **`f(1)` is `a`, derived from `Pre`**, for every H: sentence 209 (`f(X0) = a` where X0 is not
0) at X0 = 1, in a model of `Pre`; the negated premise holds since `f(0) => g(Y)`'s exclusion,
`X0 ∈ 0`, is empty at 1 in a model of Γc. -/
theorem f1_is_a (H : HookParams) : Pre H ⊧ (TiePair.app (cH H) fS [one] ≡ den (cH H) aV) := by
  intro M _ I hI
  have hΓ : I ⊧ᴵP Γ (cH H) := fun φ hφ =>
    TiePair.gamma_from (shapeH H) φ hφ (fun ψ hψ => hI ψ (Or.inl hψ))
  have hΓc : I ⊧ᴵP Γc (cH H) := fun φ hφ => hφ.elim (hΓ φ) (fun h => hI φ (Or.inr h))
  obtain ⟨hsok, hsr', hnn, -, hph, -, -, -, hno⟩ := hypSound_of_core (coreOKH H)
  haveI : OvlOK (cH H) := hno
  have htr := (sortCtx_of_all hsok hsr' (OvlOK.ovlCase hno)).trans
  have hD := defOK hΓ
  have hfnm := (lookupFn_spec (lookupFH H)).1
  obtain ⟨hso, hpo, hnw, hok0, hokX, hocv⟩ := cl0_open
  have hexcl : ExclEmptyCl (cH H) I fF cl0 :=
    exclEmptyCl_of (coreOKH H) hΓc (L := (cH H).allFns.map (·.sig)) (fun k hk => by
        obtain ⟨fn, hfn, rfl⟩ := List.mem_map.mp hk; exact ⟨fn, hfn, rfl⟩)
      (by rw [cso_withHooks, allFns_withHooks]; exact hso) (by rw [cpo_withHooks]; exact hpo) cl0_pre
      (fun h => by rw [ocv_withHooks, hocv] at h; cases h)
      (fun h => by rw [nw_withHooks, hnw] at h; cases h)
  have hfails : Fails (cH H) [one] cl0 := .intro fun σ _ hm => by
    rw [cl0_pats] at hm
    cases hm with
    | cons h _ => cases h
  have hmfails : ModelFailsCl (cH H) I cl0 [one] := fun _ _ _ σ _ hm => by
    rw [cl0_pats] at hm
    cases hm with
    | cons h _ => cases h
  have hothers : ∀ cl' ∈ lowerClauses fF clX, (cH H).condOK cl'.vars cl'.pre = true ∧
      sortsOfTerms (cH H).patCtxAll cl'.vars cl'.pats = some fF.args ∧
      (∀ t, cl'.req = some t → ∀ i ∈ varOccs t, i < cl'.vars.length) ∧
      ExclEmptyCl (cH H) I fF cl' ∧ Fails (cH H) [one] cl' ∧ ModelFailsCl (cH H) I cl' [one] := by
    intro cl' hcl'
    rw [low_X, List.mem_singleton] at hcl'
    subst hcl'
    exact ⟨(by rw [cok_withHooks]; exact hok0), (by rw [wh_patCtxAll]; exact pats_sorts0),
      (fun t h => by rw [cl0_req] at h; cases h), hexcl, hfails, hmfails⟩
  have hσ : (cH H).WellSorted clX.vars [(0, one)] := fun i s hs => by
    rw [shape.2.2.2.2.2.2.2.1] at hs
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hs
      subst hs
      exact ⟨_, rfl, by rw [sortOfH]; exact one_sort⟩
    | succ i => simp at hs
  have hws : (cH H).sortsOf [one] = some fF.args := by
    rw [sortsOfH, shape.2.2.1]; exact sortsOf_cons.mpr ⟨_, _, one_sort, sortsOf_nil, rfl⟩
  have haV : (cH H).sortOf aV = some fF.result := by rw [sortOfH]; exact aV_sort
  have key := compete_eq4Cl hΓ hnn hph htr (lookupFH H)
    (competingEquation_mem clX_mem (by rw [low_X]; simp)) hws hothers hσ
    (by rw [clX_pats]; exact .cons (.var rfl) .nil) (by rw [wh_patCtxNF]; exact pats_sortsXN)
    (by rw [condOKX_withHooks]; exact hokX) clX_post shape.2.2.2.2.2.2.2.2.2.1 occX
    (fun t h => by rw [clX_req] at h; cases h) (fun i hi => by rw [clX_rhs] at hi; simp [varOccs, varOccsList] at hi)
    (fun t h => by rw [clX_ens] at h; cases h) (r := some aV) (fun v hv => by cases hv; exact haV)
    (fun _ _ _ t h => by rw [clX_req] at h; cases h)
    (fun h => by rw [clX_pre] at h; cases h)
    (fun tbl e hag => right_iff hΓ hnn hfnm (fun v hv => by cases hv; exact haV)
      (fun m => by rw [rhs_koreX]; rfl)
      (fun t h => by rw [clX_ens] at h; cases h))
  intro e m
  rw [KoreAML.interp_equal hD]
  intro x
  exact key e x

end KCore.TieClauseRhsEmptyOwise

/-- info: 'KCore.TieClauseRhsEmptyOwise.f0_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.TieClauseRhsEmptyOwise.f0_undetermined
/-- info: 'KCore.TieClauseRhsEmptyOwise.f1_is_a' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.TieClauseRhsEmptyOwise.f1_is_a
/-- info: 'KCore.TieClauseRhsEmptyOwise.pre_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.TieClauseRhsEmptyOwise.pre_model
