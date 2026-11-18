/-
  kore.k's functions are coherent at the interpretation `HookParams.none`
  (`KK.coherent : CoherentAll (defn.sem.withHooks HookParams.none)`), on the package `RefKk` read
  from kompile's own KORE of kore.k.

  The deciders confirm every function but `cmpI`, `join` and `matchCol` (`agree_named`). Of
  those, every pair of equations the deciders leave is one that no argument list satisfies both
  of: `cmpI`'s three `requires` (`X <Int Y`, `X ==Int Y`, `X >Int Y`) hold of no two Ints together;
  `join`'s and `matchCol`'s pairs differ in what `isElem` gives at one argument (`true` against
  `false`, or `true` at a collection value `co(K, C, Es)`, which `isElem`'s two equations of
  priority 50 do not match), or in the kind (`list` against `K =/=K list`). The argument about
  `isElem` reads its rest: at `HookParams.none` a function no equation decides has none, so
  `isElem` is `true` exactly where an equation for `kv` or `el` matches.
-/
import RefKk
import KcoreSpec.Kore.KernelRfl

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KK

open KCore KCore.Det RefKk

/-- kore.k's semantics at the interpretation that gives no parameter and no rest a value. -/
noncomputable abbrev c₀ : Semantics := defn.sem.withHooks HookParams.none

/-! ## The equations the argument reads -/

/-- The clause of `cmpI` from kore.k's rule `cmpi-lt`. -/
def cmpiLt : Clause :=
  { vars := [3, 3],
    pats := [.var 0, .var 1],
    req := some (.app 19 [.var 0, .var 1]),
    rhs := .dv 3 (.int (-1)),
    ens := none,
    prio := 50,
    aside := false,
    exs := [],
    pre := .top,
    post := .top }

/-- The clause of `cmpI` from kore.k's rule `cmpi-eq`. -/
def cmpiEq : Clause :=
  { vars := [3, 3],
    pats := [.var 0, .var 1],
    req := some (.app 23 [.var 0, .var 1]),
    rhs := .dv 3 (.int 0),
    ens := none,
    prio := 50,
    aside := false,
    exs := [],
    pre := .top,
    post := .top }

/-- The clause of `cmpI` from kore.k's rule `cmpi-gt`. -/
def cmpiGt : Clause :=
  { vars := [3, 3],
    pats := [.var 0, .var 1],
    req := some (.app 21 [.var 0, .var 1]),
    rhs := .dv 3 (.int 1),
    ens := none,
    prio := 50,
    aside := false,
    exs := [],
    pre := .top,
    post := .top }

/-- `cmpI` (symbol 457) as the definition's semantics holds it. -/
def fnCmpI : Fn :=
  { label := 457, args := [3, 3], result := 3,
    clauses := [cmpiLt, cmpiEq, cmpiGt], total := false }

/-- The clause of `isElem` from kore.k's rule `elem-el`. -/
def elemEl : Clause :=
  { vars := [33],
    pats := [.app 419 [.var 0]],
    req := none,
    rhs := .dv 2 (.bool true),
    ens := none,
    prio := 50,
    aside := false,
    exs := [],
    pre := .top,
    post := .top }

/-- The clause of `isElem` from kore.k's rule `elem-kv`. -/
def elemKv : Clause :=
  { vars := [33, 33],
    pats := [.app 426 [.var 0, .var 1]],
    req := none,
    rhs := .dv 2 (.bool true),
    ens := none,
    prio := 50,
    aside := false,
    exs := [],
    pre := .top,
    post := .top }

/-- The clause of `isElem` from kore.k's rule `elem-not`. -/
def elemNot : Clause :=
  { vars := [33],
    pats := [.var 0],
    req := none,
    rhs := .dv 2 (.bool false),
    ens := none,
    prio := 200,
    aside := false,
    exs := [],
    pre := .top,
    post := .top }

/-- `isElem` (symbol 478) as the definition's semantics holds it. -/
def fnIsElem : Fn :=
  { label := 478, args := [33], result := 2,
    clauses := [elemEl, elemKv, elemNot], total := false }

/-- The clause of `join` from kore.k's rule `join-bot`. -/
def joinBot : Clause :=
  { vars := [33, 33, 43],
    pats := [.as (.app 412 []) 0, .app 407 [.var 1, .var 2]],
    req := none,
    rhs := .var 0,
    ens := none,
    prio := 50,
    aside := false,
    exs := [],
    pre := .top,
    post := .top }

/-- The clause of `join` from kore.k's rule `join-col`. -/
def joinCol : Clause :=
  { vars := [34, 3, 43, 33, 34, 3, 43, 43],
    pats := [.as (.app 416 [.var 0, .var 1, .var 2]) 3, .app 407 [.app 416 [.var 4, .var 5, .var 6], .var 7]],
    req := none,
    rhs := .app 479 [.var 3, .app 447 [.var 6, .var 7]],
    ens := none,
    prio := 50,
    aside := false,
    exs := [],
    pre := .top,
    post := .top }

/-- The clause of `join` from kore.k's rule `join-nil`. -/
def joinNil : Clause :=
  { vars := [33],
    pats := [.var 0, .app 406 []],
    req := none,
    rhs := .var 0,
    ens := none,
    prio := 50,
    aside := false,
    exs := [],
    pre := .top,
    post := .top }

/-- The clause of `join` from kore.k's rule `join-list`. -/
def joinList : Clause :=
  { vars := [34, 3, 43, 33, 43],
    pats := [.app 416 [.as (.app 427 []) 0, .var 1, .var 2], .app 407 [.var 3, .var 4]],
    req := some (.app 478 [.var 3]),
    rhs := .app 479 [.app 416 [.var 0, .var 1, .app 447 [.var 2, .app 407 [.var 3, .app 406 []]]], .var 4],
    ens := none,
    prio := 50,
    aside := false,
    exs := [],
    pre := .top,
    post := .top }

/-- The clause of `join` from kore.k's rule `join-elem`. -/
def joinElem : Clause :=
  { vars := [34, 3, 43, 33, 43],
    pats := [.app 416 [.var 0, .var 1, .var 2], .app 407 [.var 3, .var 4]],
    req := some (.app 4 [.app 478 [.var 3], .app 30 [.app 0 [.inj 34 1 (.var 0), .app 1 []], .app 0 [.inj 34 1 (.app 427 []), .app 1 []]]]),
    rhs := .app 479 [.app 491 [.var 0, .var 1, .app 474 [.var 0, .var 3, .var 2]], .var 4],
    ens := none,
    prio := 50,
    aside := false,
    exs := [],
    pre := .top,
    post := .top }

/-- `join` (symbol 479) as the definition's semantics holds it. -/
def fnJoin : Fn :=
  { label := 479, args := [33, 43], result := 33,
    clauses := [joinBot, joinCol, joinNil, joinList, joinElem], total := false }

/-- The clause of `matchCol` from kore.k's rule `mc-head`. -/
def mcHead : Clause :=
  { vars := [46, 32, 33, 43, 33, 43, 3, 34],
    pats := [.as (.app 427 []) 7, .var 6, .app 407 [.var 2, .var 3], .app 407 [.var 4, .var 5], .var 0, .var 1],
    req := some (.app 478 [.var 2]),
    rhs := .app 501 [.var 7, .var 6, .var 3, .var 5, .app 486 [.var 2, .var 4, .var 0, .var 1], .var 1],
    ens := none,
    prio := 50,
    aside := false,
    exs := [],
    pre := .top,
    post := .top }

/-- The clause of `matchCol` from kore.k's rule `mc-frame`. -/
def mcFrame : Clause :=
  { vars := [3, 33, 43, 46, 34, 32],
    pats := [.var 4, .var 0, .app 407 [.var 1, .app 406 []], .var 2, .var 3, .var 5],
    req := some (.app 3 [.app 478 [.var 1]]),
    rhs := .app 486 [.var 1, .app 416 [.var 4, .var 0, .var 2], .var 3, .var 5],
    ens := none,
    prio := 50,
    aside := false,
    exs := [],
    pre := .top,
    post := .top }

/-- The clause of `matchCol` from kore.k's rule `mc-choose`. -/
def mcChoose : Clause :=
  { vars := [43, 43, 46, 32, 34, 3, 33],
    pats := [.var 4, .var 5, .app 407 [.var 6, .var 0], .var 1, .var 2, .var 3],
    req := some (.app 4 [.app 478 [.var 6], .app 30 [.app 0 [.inj 34 1 (.var 4), .app 1 []], .app 0 [.inj 34 1 (.app 427 []), .app 1 []]]]),
    rhs := .app 454 [.var 4, .var 5, .var 6, .var 0, .app 406 [], .var 1, .var 2, .var 3],
    ens := none,
    prio := 50,
    aside := false,
    exs := [],
    pre := .top,
    post := .top }

/-- The clause of `matchCol` from kore.k's rule `mc-done`. -/
def mcDone : Clause :=
  { vars := [34, 3, 32, 46],
    pats := [.var 0, .var 1, .app 406 [], .app 406 [], .var 3, .var 2],
    req := none,
    rhs := .app 428 [.var 3, .app 403 []],
    ens := none,
    prio := 50,
    aside := false,
    exs := [],
    pre := .top,
    post := .top }

/-- The clause of `matchCol` from kore.k's rule `mc-split`. -/
def mcSplit : Clause :=
  { vars := [3, 33, 33, 46, 32, 43, 43, 43],
    pats := [.app 427 [], .var 0, .app 407 [.var 1, .as (.app 407 [.var 2, .var 5]) 6], .var 7, .var 3, .var 4],
    req := some (.app 3 [.app 478 [.var 1]]),
    rhs := .app 504 [.var 0, .var 1, .var 6, .app 406 [], .var 7, .var 3, .var 4],
    ens := none,
    prio := 50,
    aside := false,
    exs := [],
    pre := .top,
    post := .top }

/-- The clause of `matchCol` from kore.k's rule `mc-fail`. -/
def mcFail : Clause :=
  { vars := [34, 3, 43, 43, 46, 32],
    pats := [.var 0, .var 1, .var 2, .var 3, .var 4, .var 5],
    req := none,
    rhs := .app 403 [],
    ens := none,
    prio := 200,
    aside := false,
    exs := [],
    pre := .top,
    post := .top }

/-- `matchCol` (symbol 487) as the definition's semantics holds it. -/
def fnMatchCol : Fn :=
  { label := 487, args := [34, 3, 43, 43, 46, 32], result := 37,
    clauses := [mcHead, mcFrame, mcChoose, mcDone, mcSplit, mcFail], total := false }

theorem lookup_cmpI : c₀.lookupFn 457 = some fnCmpI := by kernel_rfl
theorem lookup_isElem : c₀.lookupFn 478 = some fnIsElem := by kernel_rfl
theorem lookup_join : c₀.lookupFn 479 = some fnJoin := by kernel_rfl
theorem lookup_matchCol : c₀.lookupFn 487 = some fnMatchCol := by kernel_rfl

theorem get_cmpI : c₀.fns[11]? = some fnCmpI := by kernel_rfl
theorem mem_cmpI : fnCmpI ∈ c₀.fns := List.mem_of_getElem? get_cmpI
theorem get_join : c₀.fns[33]? = some fnJoin := by kernel_rfl
theorem mem_join : fnJoin ∈ c₀.fns := List.mem_of_getElem? get_join
theorem get_matchCol : c₀.fns[41]? = some fnMatchCol := by kernel_rfl
theorem mem_matchCol : fnMatchCol ∈ c₀.fns := List.mem_of_getElem? get_matchCol

/-! ## What `coreOK` gives -/

theorem hcore : c₀.coreOK = true := coreOK_withHooks_defn HookParams.none

theorem hsorted : c₀.sortedOK = true := (Semantics.coreOK_parts hcore).1

theorem hsr : c₀.srReady = true := by
  obtain ⟨hok, -, -, hp, hids⟩ := Semantics.coreOK_parts hcore
  exact NamesApart.srReady_of hp hids hok
    (NamesApart.rangeKeys_genWf_of_faithCore (Semantics.coreOK_parts hcore).2.1) (Semantics.coreOK_ovls hcore)

theorem hmc : Exec.MatchCtxO c₀ := by
  obtain ⟨hok, -, hha, -, hids⟩ := Semantics.coreOK_parts hcore
  exact ⟨NamesApart.subsorts_trans_of hids hok, NamesApart.subsorts_irrefl_of hids hok,
    NamesApart.patHooks_of hha hids, Semantics.coreOK_ovls hcore⟩

theorem hovls : c₀.ovls = [] := by kernel_rfl

/-- Each clause of a function of the semantics is sorted (`clauseSorted`). -/
theorem hcls {fn : Fn} (hfn : fn ∈ c₀.fns) : ∀ cl ∈ fn.clauses, c₀.clauseSorted fn (c₀.fns.map Fn.sig) cl = true := by
  have hf := Semantics.sortedOK_sorted hsorted
  simp only [Bool.and_eq_true, List.all_eq_true] at hf
  exact hf.1.2 fn hfn

/-! ## Agreement from pairs no argument list satisfies both of -/

/-- No argument list satisfies both clauses: wherever both apply at one argument list, `False`. -/
def Apart (c : Semantics) (cl cl' : Clause) : Prop :=
  ∀ vs σ σ', cl.AppliesAt c σ vs → cl'.AppliesAt c σ' vs → False

theorem Apart.coherent {c : Semantics} {cl cl' : Clause} (h : Apart c cl cl') :
    Coherent c cl cl' ∧ Coherent c cl' cl :=
  ⟨fun vs σ σ' ha ha' _ _ _ _ => (h vs σ σ' ha ha').elim,
   fun vs σ σ' ha ha' _ _ _ _ => (h vs σ' σ ha' ha).elim⟩

/-- A function's equations without existential variables agree where each pair is one
`fnExclusiveI` accepts or one no argument list satisfies both of. -/
theorem clausesAgree_of_apart {c : Semantics} (hmc : Exec.MatchCtxO c) {heads : List CtorSig} {f : Fn}
    (hx : ∀ cl ∈ f.clauses, cl.exs = [])
    (hfr : ∀ cl ∈ f.clauses, c.ovlFreeList cl.pats = true)
    (hcls : ∀ cl ∈ f.clauses, c.clauseSorted f heads cl = true)
    (h : ∀ p ∈ pairs f.clauses, (c.pairAgreeL heads p.1 p.2 ||
      (p.1.prio == p.2.prio && (c.instAgree heads p.1 p.2 || c.instAgree heads p.2 p.1))) = true ∨
      Apart c p.1 p.2) :
    ClausesAgree c f := by
  intro cl cl' hp hprio
  obtain ⟨h1, h2⟩ := mem_pairs hp
  have hc1 := hcls cl h1
  have hc2 := hcls cl' h2
  rcases h _ hp with hpair | ha
  · simp only [Bool.or_eq_true, Bool.and_eq_true] at hpair
    have hc1' := hc1; have hc2' := hc2
    simp only [Semantics.clauseSorted, Bool.and_eq_true, beq_iff_eq] at hc1' hc2'
    rcases hpair with hl | ⟨-, hi | hi⟩
    · have := pairAgreeL_sound hmc (hfr cl h1) (hfr cl' h2) hc1 hc2 hl hprio
      exact ⟨Coherent.of_plain (hx cl h1) (hx cl' h2) this.1, Coherent.of_plain (hx cl' h2) (hx cl h1) this.2⟩
    · have := instAgree_sound hmc hc1'.1.1.1.1.1 hc2'.1.1.1.1.1 hi
      exact ⟨Coherent.of_plain (hx cl h1) (hx cl' h2) this.1, Coherent.of_plain (hx cl' h2) (hx cl h1) this.2⟩
    · have := instAgree_sound hmc hc2'.1.1.1.1.1 hc1'.1.1.1.1.1 hi
      exact ⟨Coherent.of_plain (hx cl h1) (hx cl' h2) this.2, Coherent.of_plain (hx cl' h2) (hx cl h1) this.1⟩
  · exact ha.coherent

/-! ## `isElem` -/

theorem isElem_flags : c₀.isCtor 478 = false ∧ isHook 478 = false ∧ c₀.isParam 478 = false ∧
    c₀.isOvl 478 = false := by decide +kernel

/-- At `HookParams.none` a function no equation decides has no rest. -/
theorem fnRest_none (fn : Fn) (vs : List GroundTerm) : c₀.fnRest fn vs = none := rfl

/-- `isElem(V)` with a result: `isElem` at V's value. -/
theorem isElem_call {σ : Subst} {i : Nat} {v : GroundTerm} {r : Option GroundTerm}
    (hi : σ.lookup i = some v) (h : EvalTerm c₀ σ (.app 478 [.var i]) r) : Eval c₀ 478 [v] r := by
  obtain ⟨hc, hh, hp, ho⟩ := isElem_flags
  obtain ⟨rs, hts, hcase⟩ := EvalTerm.call_inv hc hh hp ho h
  obtain ⟨r₁, rfl, h1⟩ := evalTerms_one hts
  rw [EvalTerm.var_inv h1, hi] at hcase
  rcases hcase with ⟨vs, hvs, hE⟩ | ⟨hn, -⟩
  · simp only [allSome, Option.bind_some, Option.map_some, Option.some.injEq] at hvs
    exact hvs ▸ hE
  · simp [allSome] at hn

/-- Where `isElem` is `true`, one of its equations of priority 50 (`el`, `kv`) applies. -/
theorem isElem_true {v : GroundTerm} (h : Eval c₀ 478 [v] (some (bool true))) :
    ∃ σ, elemEl.AppliesAt c₀ σ [v] ∨ elemKv.AppliesAt c₀ σ [v] := by
  generalize hr : some (bool true) = r at h
  cases h with
  | clause hfn hmem hσ hmatch hreq hpre _ _ hrhs _ _ =>
    rw [lookup_isElem, Option.some.injEq] at hfn
    subst hfn
    simp only [fnIsElem, List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl | rfl
    · exact ⟨_, .inl ⟨hσ, hmatch, hreq, hpre⟩⟩
    · exact ⟨_, .inr ⟨hσ, hmatch, hreq, hpre⟩⟩
    · rw [EvalTerm.dv_inv hrhs] at hr
      cases hr
  | rest _ _ => rw [fnRest_none] at hr; cases hr
  | ensFails => cases hr
  | clauseEx hfn hmem _ _ _ _ _ hne =>
    exact absurd ((Semantics.fnsNoExs_of_sortedOK hsorted).lookup hfn hmem) hne
  | exNone => cases hr

/-- Where `isElem` is `false`, its equations of priority 50 fail. -/
theorem isElem_false {v : GroundTerm} (h : Eval c₀ 478 [v] (some (bool false))) :
    Fails c₀ [v] elemEl ∧ Fails c₀ [v] elemKv := by
  generalize hr : some (bool false) = r at h
  cases h with
  | clause hfn hmem _ _ _ _ hprio _ hrhs _ _ =>
    rw [lookup_isElem, Option.some.injEq] at hfn
    subst hfn
    simp only [fnIsElem, List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl | rfl
    · rw [EvalTerm.dv_inv hrhs] at hr; cases hr
    · rw [EvalTerm.dv_inv hrhs] at hr; cases hr
    · exact ⟨hprio _ (by simp [fnIsElem]) rfl (by decide), hprio _ (by simp [fnIsElem]) rfl (by decide)⟩
  | rest _ _ => rw [fnRest_none] at hr; cases hr
  | ensFails => cases hr
  | clauseEx hfn hmem _ _ _ _ _ hne =>
    exact absurd ((Semantics.fnsNoExs_of_sortedOK hsorted).lookup hfn hmem) hne
  | exNone => cases hr

/-- A clause without a `requires` and with the predicate `\top` that applies does not fail. -/
theorem not_fails {c : Semantics} {vs : List GroundTerm} {cl : Clause} {σ : Subst}
    (hq : cl.req = none) (hp : cl.pre = .top) (ha : cl.AppliesAt c σ vs) (hf : Fails c vs cl) : False := by
  cases hf with
  | intro h =>
    cases h σ (ha.1.at _) ha.2.1 with
    | intro ht _ _ => rw [hq] at ht; cases ht
    | pre hf => rw [hp] at hf; cases hf

/-- `isElem` has one result: not `true` and `false` at one argument. -/
theorem isElem_det {v : GroundTerm} (h : Eval c₀ 478 [v] (some (bool true)))
    (h' : Eval c₀ 478 [v] (some (bool false))) : False := by
  obtain ⟨σ, ha | ha⟩ := isElem_true h
  · exact not_fails rfl rfl ha (isElem_false h').1
  · exact not_fails rfl rfl ha (isElem_false h').2

/-- `isElem` is not `true` at a collection value `co(K, C, Es)`. -/
theorem isElem_co {us : List GroundTerm} (h : Eval c₀ 478 [.ctor 416 us] (some (bool true))) : False := by
  obtain ⟨σ, ha | ha⟩ := isElem_true h
  · obtain ⟨p, ps, he, hp, -⟩ := PatVals.cons_inv ha.2.1
    simp only [List.cons.injEq] at he
    obtain ⟨rfl, -⟩ := he
    have := (PatVal.app_ctor_iff (f := 419) (by decide +kernel) (by decide +kernel)).mp hp
    exact absurd this.1 (by decide)
  · obtain ⟨p, ps, he, hp, -⟩ := PatVals.cons_inv ha.2.1
    simp only [List.cons.injEq] at he
    obtain ⟨rfl, -⟩ := he
    have := (PatVal.app_ctor_iff (f := 426) (by decide +kernel) (by decide +kernel)).mp hp
    exact absurd this.1 (by decide)

/-! ## Patterns, `=/=K` and the Int comparisons -/

/-- A constructor pattern denotes a constructor term of its arguments' values. -/
theorem pv_ctor {σ : Subst} {f : Sym} {ps : List Term} {v : GroundTerm} (h : PatVal c₀ σ (.app f ps) v)
    (hc : c₀.isCtor f = true := by decide +kernel) (hp : patternHooks.contains f = false := by decide +kernel) :
    ∃ vs, v = .ctor f vs ∧ PatVals c₀ σ ps vs :=
  (PatVal.ctor_iff_of_not_hook hc hp).mp h

/-- `kseq(inj{Kind,KItem}(t), dotk)`, the K sequence of one Kind term, as `=/=K` compares it. -/
abbrev kItemOf (t : Term) : Term := .app 0 [.inj 34 1 t, .app 1 []]

theorem kItem_eval {σ : Subst} {t : Term} {x : GroundTerm} (ht : ∀ r, EvalTerm c₀ σ t r → r = some x)
    {r : Option GroundTerm} (h : EvalTerm c₀ σ (kItemOf t) r) :
    r = some (.ctor 0 [injNormal 34 1 x, .ctor 1 []]) := by
  obtain ⟨rs, hts, rfl⟩ := EvalTerm.ctor_inv (by decide +kernel) h
  obtain ⟨r₁, r₂, rfl, h1, h2⟩ := evalTerms_two hts
  obtain ⟨r₀, h0, rfl⟩ := EvalTerm.inj_inv h1
  rw [ht _ h0]
  obtain ⟨rs', hts', rfl⟩ := EvalTerm.ctor_inv (by decide +kernel) h2
  cases hts'
  rfl

/-- `t =/=K u` is not `true` where t and u have the one value x. -/
theorem kne_self {σ : Subst} {t u : Term} {x : GroundTerm} (ht : ∀ r, EvalTerm c₀ σ t r → r = some x)
    (hu : ∀ r, EvalTerm c₀ σ u r → r = some x)
    (h : EvalTerm c₀ σ (.app 30 [kItemOf t, kItemOf u]) (some (bool true))) : False := by
  obtain ⟨v, w, h1, h2, hv⟩ := hook2_inv rfl h
  cases Option.some.inj (kItem_eval ht h1)
  cases Option.some.inj (kItem_eval hu h2)
  rw [hook_kNe, GroundTerm.cmp_refl] at hv
  exact absurd (bool_inj (Option.some.inj (Option.some.inj hv))) (by decide)

theorem var_eval {σ : Subst} {i : Nat} {x : GroundTerm} (hi : σ.lookup i = some x) :
    ∀ r, EvalTerm c₀ σ (.var i) r → r = some x := fun _ h => (EvalTerm.var_inv h).trans hi

/-- The kind `list` evaluates to itself. -/
theorem list_eval {σ : Subst} : ∀ r, EvalTerm c₀ σ (.app 427 []) r → r = some (.ctor 427 []) := by
  intro r h
  obtain ⟨rs, hts, rfl⟩ := EvalTerm.ctor_inv (by decide +kernel) h
  cases hts
  rfl

/-- A `requires` comparing two pattern variables as Ints: the arguments are Ints that compare so. -/
theorem int_req {σ : Subst} {vs : List GroundTerm} {f : Sym} {P : Int → Int → Prop} [∀ x y, Decidable (P x y)]
    (hhk : isHook f = true) (hf : ∀ vs, hook f vs = some (int2 vs fun x y => some (bool (decide (P x y)))))
    (hs : silentKey f = false)
    (hm : PatVals c₀ σ [.var 0, .var 1] vs) (h : EvalTerm c₀ σ (.app f [.var 0, .var 1]) (some (bool true))) :
    ∃ v w x y, vs = [v, w] ∧ asInt v = some x ∧ asInt w = some y ∧ P x y := by
  obtain ⟨v, w, x, y, h1, h2, hx, hy, hb⟩ := int2_inv hhk hf h hs
  rcases hm with _ | ⟨ha, _ | ⟨hb', _ | _⟩⟩
  cases Option.some.inj ((EvalTerm.var_inv h1).trans (PatVal.var_inv ha))
  cases Option.some.inj ((EvalTerm.var_inv h2).trans (PatVal.var_inv hb'))
  exact ⟨_, _, x, y, rfl, hx, hy, of_decide_eq_true hb.symm⟩

/-! ## The pairs the deciders leave -/

/-- `cmpI`: `X <Int Y` and `X ==Int Y` hold of no two Ints together. -/
theorem apart_lt_eq : Apart c₀ cmpiLt cmpiEq := fun _ _ _ ha ha' => by
  obtain ⟨v, w, x, y, rfl, hx, hy, hp⟩ := int_req (f := intLt) rfl hook_intLt (by decide) ha.2.1 (ha.2.2.1 _ rfl)
  obtain ⟨v', w', x', y', he, hx', hy', hq⟩ := int_req (f := intEq) rfl hook_intEq (by decide) ha'.2.1 (ha'.2.2.1 _ rfl)
  simp only [List.cons.injEq, and_true] at he
  obtain ⟨rfl, rfl⟩ := he
  rw [hx] at hx'; rw [hy] at hy'; cases hx'; cases hy'; omega

/-- `cmpI`: `X <Int Y` and `X >Int Y` hold of no two Ints together. -/
theorem apart_lt_gt : Apart c₀ cmpiLt cmpiGt := fun _ _ _ ha ha' => by
  obtain ⟨v, w, x, y, rfl, hx, hy, hp⟩ := int_req (f := intLt) rfl hook_intLt (by decide) ha.2.1 (ha.2.2.1 _ rfl)
  obtain ⟨v', w', x', y', he, hx', hy', hq⟩ := int_req (f := intGt) rfl hook_intGt (by decide) ha'.2.1 (ha'.2.2.1 _ rfl)
  simp only [List.cons.injEq, and_true] at he
  obtain ⟨rfl, rfl⟩ := he
  rw [hx] at hx'; rw [hy] at hy'; cases hx'; cases hy'; omega

/-- `cmpI`: `X ==Int Y` and `X >Int Y` hold of no two Ints together. -/
theorem apart_eq_gt : Apart c₀ cmpiEq cmpiGt := fun _ _ _ ha ha' => by
  obtain ⟨v, w, x, y, rfl, hx, hy, hp⟩ := int_req (f := intEq) rfl hook_intEq (by decide) ha.2.1 (ha.2.2.1 _ rfl)
  obtain ⟨v', w', x', y', he, hx', hy', hq⟩ := int_req (f := intGt) rfl hook_intGt (by decide) ha'.2.1 (ha'.2.2.1 _ rfl)
  simp only [List.cons.injEq, and_true] at he
  obtain ⟨rfl, rfl⟩ := he
  rw [hx] at hx'; rw [hy] at hy'; cases hx'; cases hy'; omega

/-- `join-col` against `join-list`: the element `join-list` reads is a collection value, at which
`isElem` is not `true`. -/
theorem apart_col_list : Apart c₀ joinCol joinList := fun _ _ _ ha ha' => by
  obtain ⟨-, hm, -, -⟩ := ha
  obtain ⟨-, hm', hq', -⟩ := ha'
  rcases hm with _ | ⟨-, _ | ⟨h2, _ | _⟩⟩
  obtain ⟨bs, rfl, hb⟩ := pv_ctor h2
  rcases hb with _ | ⟨h21, _ | ⟨-, _ | _⟩⟩
  obtain ⟨es, rfl, -⟩ := pv_ctor h21
  rcases hm' with _ | ⟨-, _ | ⟨h2', _ | _⟩⟩
  obtain ⟨bs', he, hb'⟩ := pv_ctor h2'
  cases he
  rcases hb' with _ | ⟨h3, -⟩
  exact isElem_co (isElem_call (PatVal.var_inv h3) (hq' _ rfl))

/-- `join-col` against `join-elem`: as against `join-list`. -/
theorem apart_col_elem : Apart c₀ joinCol joinElem := fun _ _ _ ha ha' => by
  obtain ⟨-, hm, -, -⟩ := ha
  obtain ⟨-, hm', hq', -⟩ := ha'
  rcases hm with _ | ⟨-, _ | ⟨h2, _ | _⟩⟩
  obtain ⟨bs, rfl, hb⟩ := pv_ctor h2
  rcases hb with _ | ⟨h21, _ | ⟨-, _ | _⟩⟩
  obtain ⟨es, rfl, -⟩ := pv_ctor h21
  rcases hm' with _ | ⟨-, _ | ⟨h2', _ | _⟩⟩
  obtain ⟨bs', he, hb'⟩ := pv_ctor h2'
  cases he
  rcases hb' with _ | ⟨h3, -⟩
  exact isElem_co (isElem_call (PatVal.var_inv h3) (and_inv (hq' _ rfl)).1)

/-- `join-list` against `join-elem`: the kind is `list`, and `join-elem` asks `K =/=K list`. -/
theorem apart_list_elem : Apart c₀ joinList joinElem := fun _ _ _ ha ha' => by
  obtain ⟨-, hm, -, -⟩ := ha
  obtain ⟨-, hm', hq', -⟩ := ha'
  rcases hm with _ | ⟨h1, _ | ⟨-, _ | _⟩⟩
  obtain ⟨as, rfl, ha1⟩ := pv_ctor h1
  rcases ha1 with _ | ⟨hk, -⟩
  obtain ⟨hk, -⟩ := PatVal.as_inv hk
  obtain ⟨ks, rfl, hks⟩ := pv_ctor hk
  cases hks
  rcases hm' with _ | ⟨h1', -⟩
  obtain ⟨as', he, ha1'⟩ := pv_ctor h1'
  cases he
  rcases ha1' with _ | ⟨hk', -⟩
  exact kne_self (var_eval (PatVal.var_inv hk')) list_eval (and_inv (hq' _ rfl)).2

/-- `mc-head` against a clause asking `notBool isElem(P)` of the element `mc-head` reads with
`isElem(P)`: `isElem` is not `true` and `false` there. -/
theorem apart_head_frame : Apart c₀ mcHead mcFrame := fun _ _ _ ha ha' => by
  obtain ⟨-, hm, hq, -⟩ := ha
  obtain ⟨-, hm', hq', -⟩ := ha'
  rcases hm with _ | ⟨-, _ | ⟨-, _ | ⟨h3, _ | ⟨-, _ | ⟨-, _ | ⟨-, _ | _⟩⟩⟩⟩⟩⟩
  obtain ⟨bs, rfl, hb⟩ := pv_ctor h3
  rcases hb with _ | ⟨hp, _ | ⟨-, _ | _⟩⟩
  rcases hm' with _ | ⟨-, _ | ⟨-, _ | ⟨h3', -⟩⟩⟩
  obtain ⟨bs', he, hb'⟩ := pv_ctor h3'
  cases he
  rcases hb' with _ | ⟨hp', -⟩
  exact isElem_det (isElem_call (PatVal.var_inv hp) (hq _ rfl))
    (isElem_call (PatVal.var_inv hp') (not_inv (hq' _ rfl)))

/-- `mc-head` against `mc-choose`: the kind is `list`, and `mc-choose` asks `K =/=K list`. -/
theorem apart_head_choose : Apart c₀ mcHead mcChoose := fun _ _ _ ha ha' => by
  obtain ⟨-, hm, -, -⟩ := ha
  obtain ⟨-, hm', hq', -⟩ := ha'
  rcases hm with _ | ⟨h1, -⟩
  obtain ⟨hk, -⟩ := PatVal.as_inv h1
  obtain ⟨ks, rfl, hks⟩ := pv_ctor hk
  cases hks
  rcases hm' with _ | ⟨h1', -⟩
  exact kne_self (var_eval (PatVal.var_inv h1')) list_eval (and_inv (hq' _ rfl)).2

/-- `mc-head` against `mc-split`: as against `mc-frame`. -/
theorem apart_head_split : Apart c₀ mcHead mcSplit := fun _ _ _ ha ha' => by
  obtain ⟨-, hm, hq, -⟩ := ha
  obtain ⟨-, hm', hq', -⟩ := ha'
  rcases hm with _ | ⟨-, _ | ⟨-, _ | ⟨h3, _ | ⟨-, _ | ⟨-, _ | ⟨-, _ | _⟩⟩⟩⟩⟩⟩
  obtain ⟨bs, rfl, hb⟩ := pv_ctor h3
  rcases hb with _ | ⟨hp, _ | ⟨-, _ | _⟩⟩
  rcases hm' with _ | ⟨-, _ | ⟨-, _ | ⟨h3', -⟩⟩⟩
  obtain ⟨bs', he, hb'⟩ := pv_ctor h3'
  cases he
  rcases hb' with _ | ⟨hp', -⟩
  exact isElem_det (isElem_call (PatVal.var_inv hp) (hq _ rfl))
    (isElem_call (PatVal.var_inv hp') (not_inv (hq' _ rfl)))

/-! ## The three functions agree, and every two competing clauses are coherent -/

theorem hfr (fn : Fn) : ∀ cl ∈ fn.clauses, c₀.ovlFreeList cl.pats = true :=
  fun _ _ => ovlFreeList_of_nil hovls _

theorem agree_cmpI : ClausesAgree c₀ fnCmpI := by
  refine clausesAgree_of_apart hmc (Semantics.fnsNoExs_of_sortedOK hsorted _ mem_cmpI) (hfr _) (hcls mem_cmpI) fun p hp => ?_
  simp only [fnCmpI, pairs, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl
  · exact .inr apart_lt_eq
  · exact .inr apart_lt_gt
  · exact .inr apart_eq_gt

theorem agree_join : ClausesAgree c₀ fnJoin := by
  refine clausesAgree_of_apart hmc (Semantics.fnsNoExs_of_sortedOK hsorted _ mem_join) (hfr _) (hcls mem_join) fun p hp => ?_
  simp only [fnJoin, pairs, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact .inl (by decide +kernel)
  · exact .inl (by decide +kernel)
  · exact .inl (by decide +kernel)
  · exact .inl (by decide +kernel)
  · exact .inl (by decide +kernel)
  · exact .inr apart_col_list
  · exact .inr apart_col_elem
  · exact .inl (by decide +kernel)
  · exact .inl (by decide +kernel)
  · exact .inr apart_list_elem

theorem agree_matchCol : ClausesAgree c₀ fnMatchCol := by
  refine clausesAgree_of_apart hmc (Semantics.fnsNoExs_of_sortedOK hsorted _ mem_matchCol) (hfr _) (hcls mem_matchCol) fun p hp => ?_
  simp only [fnMatchCol, pairs, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact .inr apart_head_frame
  · exact .inr apart_head_choose
  · exact .inl (by decide +kernel)
  · exact .inr apart_head_split
  all_goals exact .inl (by decide +kernel)

/-- The functions `agreeObligationsI` names (`cmpI`, `join`, `matchCol`) agree. -/
theorem agree_obligations : ∀ f ∈ c₀.agreeObligationsI, ∀ fn, c₀.lookupFn f = some fn → ClausesAgree c₀ fn := by
  intro f hf fn hfn
  rw [Semantics.agreeObligationsI_withHooks, agree_named] at hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl
  · rw [lookup_cmpI, Option.some.injEq] at hfn; exact hfn ▸ agree_cmpI
  · rw [lookup_join, Option.some.injEq] at hfn; exact hfn ▸ agree_join
  · rw [lookup_matchCol, Option.some.injEq] at hfn; exact hfn ▸ agree_matchCol

/-- **kore.k's functions are coherent at `HookParams.none`** (`CoherentAll`): every two
equations of one function that compete, each with itself among them, give one result wherever
both decide. The deciders show it for every function but `cmpI`, `join` and `matchCol`
(`agree_named`), and for every clause's match independence (`match_named`); for those three, the
pairs the deciders leave are pairs no argument list satisfies both of. -/
theorem coherent : CoherentAll (defn.sem.withHooks HookParams.none) := by
  have hag := clausesAgree_of_IO hsorted hsr hmc agree_obligations
  have hmi := matchIndependentAll_of_L hsorted hmc fun p hp => by
    rw [Semantics.matchObligationsL_withHooks, match_named] at hp
    exact absurd hp List.not_mem_nil
  exact coherentAll_of_parts hmi fun f fn hfn => by
    obtain ⟨hmem, -⟩ := lookupFn_spec hfn
    rcases List.mem_append.mp hmem with hu | hp
    · exact hag fn hu
    · exact sortPreds_agree hp

end KK
