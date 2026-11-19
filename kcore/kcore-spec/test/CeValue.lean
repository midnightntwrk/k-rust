/-
  A semantics whose function clause binds a variable by `\exists` and whose rule steps through it,
  kernel-checked: `cCeV` is test/SoundCE.lean's `cCeR` with `lp() => 0` in place of `lp() => lp()`
  and the one rule `r0`:

    f() => g(?Z:Int)  with post := Z ∈ lp()      lp() => 0      g(X:Int) => X
    <k> K </k> <counter> N </counter> => <k> K </k> <counter> f() </counter>

  - `coreOKEx` accepts it, and so does `coreOK`, which is `coreOKEx` (`cCeV_coreOKEx`,
    `cCeV_coreOK`). `Z` is of the sort Int, which is not confined: `post` fixes it.
  - `f()` is 0 (`fC_value`), by `Eval.clauseEx` at `Z = 0`: `post` is `Z = 0` at each instance, so
    the instance at 0 gives `g(0) = 0` and every other instance fails by its `post`; `f()` has no
    other result (`fC_inv`).
  - `FnHyp cCeV` (`cCeV_fnHyp`): every function has a result at every argument list of its sorts,
    none is `[total]`, each has one clause, and each clause is match independent (the clause of `f`
    has the one result 0 at each match, `res_eq`, and a result where it decides, `res_some`).
  - `Step cCeV x y` exactly where y is x with the counter 0 (`step_iff`), every configuration has the
    shape `r0` matches (`cfg_shape`), so has a successor (`step_exists`), and the evaluations a step
    reads have results at every term (`stepDecided`).
  - `step_of_successor_exCEx`, `sound_at_ce`, `famEx_closed_ce` and `complete_at_ce` at `cCeV`, at the
    step by `r0` from the counter 1 to the counter 0 (`successor_cfg`, `sound_x1`, `famEx_x1`,
    `complete_x1`) and at every step.
  - `HypModelCore`, `ClausePreDecided` and `ClausePostDecided` hold of `cCeV` (`cCeV_hypModelCore`,
    `cCeV_preDecided`, `cCeV_postDecided`), from `coreOKEx` and `FnHyp`; so its theory with the step's
    closure has a model (`cCeV_consistent`, by `consistent_ce`).
  - `has_model_choice_exCEx` at `T := Step cCeV` (`cCeV_model_step`): a model of `Γc` with the step's
    closure in which a configuration has exactly the configuration with the counter 0 as successor.
    So the models `successor_cfg` speaks of exist (`cCeV_has_model`), and in one of them the
    configuration with the counter 1 has the one with the counter 0 as successor and not itself
    (`cCeV_model_x1`).
  - `exact_ce` and `has_model_choice_ce` at `cCeV` (`cCeV_exact`, `cCeV_model_choice`), and
    `has_model_choice_ce` at `T := Step cCeV` (`cCeV_model_step_ce`).
  - `famEx_values_ce` and `famOpen_values_ce` at `cCeV` (`cCeV_famEx_values`,
    `cCeV_famOpen_values`): an element of `famEx r0 σX` at a configuration is y0's (`famEx_values_x1`).
-/
import KcoreSpec.SoundCE
import KcoreSpec.StepSuccessorExCEx
import KcoreSpec.ExChoiceCEx
import KcoreSpec.SubjectReduction
import KcoreSpec.EvalLemmas
import KcoreSpec.Invariant
import KcoreSpec.Obligations
import KcoreSpec.CoreDecide
import KcoreSpec.ExactHeldCEx
import KcoreSpec.FamValuesCE
import KcoreSpec.Sound

set_option autoImplicit false
set_option maxRecDepth 100000

namespace KCore.CeValueTest
open KCore GroundTerm

/-! ## The text -/

def cellSorts : List Srt := [Srt.top, Srt.topFrag, nRegSorts, nRegSorts + 1, Srt.counter, Srt.counterOpt]
def kcS : Sym := nRegSyms + 2
def cellCtors : List CtorSig :=
  [⟨topLabel, [nRegSorts, Srt.counter], Srt.top⟩, ⟨topFragLabel, [nRegSorts + 1, Srt.counterOpt], Srt.topFrag⟩,
   ⟨kcS, [Srt.k], nRegSorts⟩, ⟨nRegSyms + 3, [], nRegSorts + 1⟩,
   ⟨counterLabel, [Srt.int], Srt.counter⟩, ⟨noCounter, [], Srt.counterOpt⟩]
def cellSubsorts : List (Srt × Srt) := [(nRegSorts, nRegSorts + 1), (Srt.counter, Srt.counterOpt)]
def base : Semantics :=
  { lib := { sortsBelowKItem := [Srt.int] }
    sortNames := ["KCell", "KCellOpt"]
    symNames := ["LblisKCell", "LblisKCellOpt", "Lbl'-LT-'k'-GT-'", "LblnoKCell"]
    userSorts := cellSorts
    ctors := cellCtors
    fns := []
    userSubsorts := cellSubsorts
    pgmSort := Srt.k
    rules := [] }
def fC : Sym := nRegSyms + 4
def lpS : Sym := nRegSyms + 5
def gS : Sym := nRegSyms + 6
/-- `f() => g(?Z:Int)` with `post := Z ∈ lp()` -/
def clCf : Clause :=
  { vars := [Srt.int], pats := [], req := none, rhs := .app gS [.var 0], ens := none, exs := [0],
    post := .mem Srt.int (.var 0) (.app lpS []) }
def fnCf : Fn := { label := fC, args := [], result := Srt.int, clauses := [clCf] }
/-- `lp() => 0` -/
def clLp0 : Clause := { vars := [], pats := [], req := none, rhs := .dv Srt.int (.int 0), ens := none }
def fnLp0 : Fn := { label := lpS, args := [], result := Srt.int, clauses := [clLp0] }
/-- `g(X:Int) => X` -/
def clG : Clause := { vars := [Srt.int], pats := [.var 0], req := none, rhs := .var 0, ens := none }
def fnG : Fn := { label := gS, args := [Srt.int], result := Srt.int, clauses := [clG] }
/-- `<k> K </k> <counter> N </counter> => <k> K </k> <counter> f() </counter>` -/
def r0 : Rule :=
  { vars := [Srt.k, Srt.int], lhs := .app topLabel [.app kcS [.var 0], .app counterLabel [.var 1]],
    req := none, rhs := .app topLabel [.app kcS [.var 0], .app counterLabel [.app fC []]], ens := none, prio := 50 }
def cCeV : Semantics :=
  { base with symNames := base.symNames ++ ["Lblf", "Lbllp", "Lblg"], fns := [fnCf, fnLp0, fnG], rules := [r0] }

/-! ## What the deciders say -/

theorem cCeV_coreOKEx : cCeV.coreOKEx = true := by
  unfold Semantics.coreOKEx Semantics.sortedOKEx; decide_cheap

theorem cCeV_coreOK : cCeV.coreOK = true := Semantics.coreOK_iff_ex.mpr cCeV_coreOKEx

theorem cCeV_sortedOKEx : cCeV.sortedOKEx = true := by
  unfold Semantics.sortedOKEx; decide_cheap

theorem cCeV_sortedOKClEx : cCeV.sortedOKClEx = true :=
  Semantics.sortedOKClEx_of_sortedOKEx cCeV_sortedOKEx

theorem cCeV_readsConfined : cCeV.readsConfined = true := by decide +kernel

/-- `Z`'s sort Int is not confined. -/
theorem cCeV_int_open : cCeV.confined Srt.int = false := by decide +kernel

theorem cCeV_rules : ∀ r ∈ cCeV.rules, cCeV.ruleSorted r = true ∧ cCeV.rulePlainEx r = true := by
  decide +kernel

theorem noWitR : ∀ r ∈ cCeV.rules, r.needsWitness cCeV = false := by decide +kernel
theorem noWitCl : ∀ fn ∈ cCeV.fns, ∀ cl ∈ fn.clauses, cl.needsWitness cCeV = false := by decide +kernel
theorem noRaw : ∀ k ∈ cCeV.params, k.raw = false := by decide +kernel

theorem cCeV_openDecided : OpenDecided cCeV := openDecided_of_plain noWitR noWitCl
theorem cCeV_openLaws : OpenLaws cCeV := openLaws_of_plain noRaw

/-- No clause needs a witness: the clause hypothesis of the `_ce` statements. -/
theorem noWit : ∀ fn ∈ cCeV.fns, ∀ cl ∈ fn.clauses, cl.needsWitness cCeV = true → cl.CondDecided cCeV :=
  fun fn hfn cl hcl hw => absurd hw (by rw [noWitCl fn hfn cl hcl]; decide)

theorem r0_opens : r0.opens = [] := by decide
theorem r0_exs : r0.exs = [] := rfl

theorem mem_rules {r : Rule} (h : r ∈ cCeV.rules) : r = r0 := by simpa [cCeV] using h

theorem mem_fns {fn : Fn} (h : fn ∈ cCeV.fns) : fn = fnCf ∨ fn = fnLp0 ∨ fn = fnG := by
  simpa [cCeV] using h

/-! ## Small facts -/

abbrev i0 : GroundTerm := .dv Srt.int (.int 0)

theorem i0_int : cCeV.sortOf i0 = some Srt.int := sortOf_int 0

theorem lkSelf (i : Nat) (v : GroundTerm) (σ : Subst) : ((i, v) :: σ : Subst).lookup i = some v := by
  simp [List.lookup]

theorem lkNe {i j : Nat} (v : GroundTerm) (σ : Subst) (h : i ≠ j) :
    ((j, v) :: σ : Subst).lookup i = σ.lookup i := by
  have hb : (i == j) = false := by simp [h]
  simp [List.lookup, hb]

theorem sameResult_some {v w : GroundTerm} : sameResult (some v) (some w) = true ↔ v = w := by
  simp [sameResult, cmp_eq_iff]

theorem holds_cast {n : Nat} {σ : Subst} {p : Cond} {b b' : Bool}
    (h : Holds cCeV n σ p b) (e : b = b') : Holds cCeV n σ p b' := e ▸ h

theorem sortsOf_nilV {vs : List GroundTerm} (h : cCeV.sortsOf vs = some []) : vs = [] := by
  cases vs with
  | nil => rfl
  | cons v vs =>
    rw [Semantics.sortsOf] at h
    split at h <;> cases h

theorem sortsOf_consV {t : GroundTerm} {ts : List GroundTerm} {s : Srt} {ss : List Srt}
    (h : cCeV.sortsOf (t :: ts) = some (s :: ss)) : cCeV.sortOf t = some s ∧ cCeV.sortsOf ts = some ss := by
  obtain ⟨s', ss', h1, h2, he⟩ := sortsOf_cons.mp h
  simp only [List.cons.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  exact ⟨h1, h2⟩

theorem sortsOf_oneV {vs : List GroundTerm} {s : Srt} (h : cCeV.sortsOf vs = some [s]) :
    ∃ w, vs = [w] ∧ cCeV.sortOf w = some s := by
  cases vs with
  | nil => simp [Semantics.sortsOf] at h
  | cons w ws =>
    obtain ⟨h1, h2⟩ := sortsOf_consV h
    exact ⟨w, by rw [sortsOf_nilV h2], h1⟩

theorem match0 {σ : Subst} {vs : List GroundTerm} (h : PatVals cCeV σ [.var 0] vs) :
    ∃ v, vs = [v] ∧ σ.lookup 0 = some v := by
  obtain ⟨v, vs', rfl, hv, hs⟩ := PatVals.cons_inv h
  rw [PatVals.nil_inv hs]
  exact ⟨v, rfl, PatVal.var_inv hv⟩

theorem clCf_free : Clause.exsFree clCf = [0] := by decide

/-- The extension of σ that gives `Z` the value z: σ off `Z`, well sorted where z is an Int. -/
theorem ext_agree (z : GroundTerm) (σ : Subst) : AgreeOff clCf.exsFree σ ((0, z) :: σ) := by
  rw [clCf_free]
  intro i hi
  exact lkNe _ _ (fun h => hi (by simp [h]))

theorem ext_sorted {z : GroundTerm} (hz : cCeV.sortOf z = some Srt.int) (σ : Subst) :
    cCeV.WellSorted [Srt.int] ((0, z) :: σ) := by
  intro i s h
  match i, h with
  | 0, h => cases h; exact ⟨_, lkSelf _ _ _, hz⟩

theorem lookup_lp : cCeV.lookupFn lpS = some fnLp0 := by rw [Semantics.lookupFn_eq]; rfl
theorem lookup_fC : cCeV.lookupFn fC = some fnCf := by rw [Semantics.lookupFn_eq]; rfl
theorem lookup_g : cCeV.lookupFn gS = some fnG := by rw [Semantics.lookupFn_eq]; rfl

theorem flags : cCeV.isCtor lpS = false ∧ isHook lpS = false ∧ cCeV.isParam lpS = false ∧
    cCeV.isOvl lpS = false ∧ cCeV.isCtor gS = false ∧ isHook gS = false ∧ cCeV.isParam gS = false ∧
    cCeV.isOvl gS = false := by decide +kernel

theorem flagsF : cCeV.isCtor fC = false ∧ isHook fC = false ∧ cCeV.isParam fC = false ∧
    cCeV.isOvl fC = false := by decide +kernel

/-! ## `lp()` and `g` -/

/-- `lp()` is 0. -/
theorem evalLp : Eval cCeV lpS [] (some i0) :=
  .clause (fn := fnLp0) (cl := clLp0) (σ := []) lookup_lp (List.mem_singleton_self _)
    (fun i s h => by simp [clLp0] at h) .nil (fun t ht => nomatch ht) Holds.top
    (fun cl' hcl' _ hlt => by
      simp only [fnLp0, List.mem_singleton] at hcl'; subst hcl'; exact absurd hlt (Nat.lt_irrefl _))
    rfl .dv (fun t ht => nomatch ht) Holds.top

/-- `lp()` has no other result. -/
theorem evalLp_inv {r : Option GroundTerm} (h : Eval cCeV lpS [] r) : r = some i0 := by
  cases h with
  | clause hfn hmem _ _ _ _ _ _ hrhs _ _ =>
    rw [lookup_lp] at hfn; cases hfn
    simp only [fnLp0, List.mem_singleton] at hmem; subst hmem
    exact EvalTerm.dv_inv hrhs
  | rest hfn hnone =>
    rw [lookup_lp] at hfn; cases hfn
    cases hnone clLp0 (by simp [fnLp0]) with
    | intro h =>
      cases h [] (fun i hi => by simp [Clause.leftVars, Clause.condVars, clLp0, varOccsList, varOccsCond] at hi) .nil with
      | intro ht _ _ => cases ht
      | pre hp => exact absurd (Holds.top_eq hp) (by simp)
  | ensFails hfn hmem _ _ _ _ _ _ ht _ _ =>
    rw [lookup_lp] at hfn; cases hfn
    simp only [fnLp0, List.mem_singleton] at hmem; subst hmem
    cases ht
  | clauseEx hfn hmem _ _ _ _ _ hne _ _ _ _ =>
    rw [lookup_lp] at hfn; cases hfn
    simp only [fnLp0, List.mem_singleton] at hmem; subst hmem
    exact absurd rfl hne
  | exNone hfn hmem hne _ _ _ _ _ _ _ =>
    rw [lookup_lp] at hfn; cases hfn
    simp only [fnLp0, List.mem_singleton] at hmem; subst hmem
    exact absurd rfl hne

theorem termLp (σ : Subst) : EvalTerm cCeV σ (.app lpS []) (some i0) :=
  .call flags.1 flags.2.1 .nil rfl evalLp flags.2.2.1

theorem termLp_inv {σ : Subst} {r : Option GroundTerm} (h : EvalTerm cCeV σ (.app lpS []) r) : r = some i0 := by
  cases h with
  | ctor hc _ => exact absurd hc (by decide +kernel)
  | hook _ hhk _ _ _ => exact absurd hhk (by decide +kernel)
  | param _ _ hp _ _ => exact absurd hp (by decide +kernel)
  | call _ _ hts hvs hf _ =>
    cases hts
    simp only [allSome, Option.some.injEq] at hvs
    subst hvs
    exact evalLp_inv hf
  | callUndef _ _ hts hvs _ =>
    cases hts
    simp [allSome] at hvs
  | ovl _ ho _ _ => exact absurd ho (by decide +kernel)
  | ovlFn _ ho _ _ _ _ _ => exact absurd ho (by decide +kernel)

/-- `g(w)` is w at an Int w. -/
theorem evalG {w : GroundTerm} (hw : cCeV.sortOf w = some Srt.int) : Eval cCeV gS [w] (some w) := by
  have hr : EvalTerm cCeV [(0, w)] (.var 0) (some w) := by
    have := EvalTerm.var (c := cCeV) (σ := [(0, w)]) (i := 0); rwa [lkSelf] at this
  exact .clause (fn := fnG) (cl := clG) (σ := [(0, w)]) lookup_g (List.mem_singleton_self _)
    (ext_sorted hw []) (.cons (.var (lkSelf _ _ _)) .nil) (fun t ht => nomatch ht) Holds.top
    (fun cl' hcl' _ hlt => by
      simp only [fnG, List.mem_singleton] at hcl'; subst hcl'; exact absurd hlt (Nat.lt_irrefl _))
    rfl hr (fun t ht => nomatch ht) Holds.top

/-- `g(w)` has no other result at an Int w. -/
theorem evalG_inv {w : GroundTerm} (hw : cCeV.sortOf w = some Srt.int) {r : Option GroundTerm}
    (h : Eval cCeV gS [w] r) : r = some w := by
  cases h with
  | clause hfn hmem _ hm _ _ _ _ hrhs _ _ =>
    rw [lookup_g] at hfn; cases hfn
    simp only [fnG, List.mem_singleton] at hmem; subst hmem
    obtain ⟨v, hv, hl⟩ := match0 hm
    cases hv
    rw [EvalTerm.var_inv hrhs, hl]
  | rest hfn hnone =>
    rw [lookup_g] at hfn; cases hfn
    cases hnone clG (by simp [fnG]) with
    | intro h =>
      cases h [(0, w)] (fun i _ s hs => ext_sorted hw [] i s hs) (.cons (.var (lkSelf _ _ _)) .nil) with
      | intro ht _ _ => cases ht
      | pre hp => exact absurd (Holds.top_eq hp) (by simp)
  | ensFails hfn hmem _ _ _ _ _ _ ht _ _ =>
    rw [lookup_g] at hfn; cases hfn
    simp only [fnG, List.mem_singleton] at hmem; subst hmem
    cases ht
  | clauseEx hfn hmem _ _ _ _ _ hne _ _ _ _ =>
    rw [lookup_g] at hfn; cases hfn
    simp only [fnG, List.mem_singleton] at hmem; subst hmem
    exact absurd rfl hne
  | exNone hfn hmem hne _ _ _ _ _ _ _ =>
    rw [lookup_g] at hfn; cases hfn
    simp only [fnG, List.mem_singleton] at hmem; subst hmem
    exact absurd rfl hne

theorem termG {σ : Subst} {w : GroundTerm} (hl : σ.lookup 0 = some w) (hw : cCeV.sortOf w = some Srt.int) :
    EvalTerm cCeV σ (.app gS [.var 0]) (some w) := by
  have ht : EvalTerms cCeV σ [.var 0] [some w] := .cons (hl ▸ EvalTerm.var) .nil
  exact .call flags.2.2.2.2.1 flags.2.2.2.2.2.1 ht rfl (evalG hw) flags.2.2.2.2.2.2.1

theorem termG_inv {σ : Subst} {w : GroundTerm} (hl : σ.lookup 0 = some w) (hw : cCeV.sortOf w = some Srt.int)
    {r : Option GroundTerm} (h : EvalTerm cCeV σ (.app gS [.var 0]) r) : r = some w := by
  cases h with
  | ctor hc _ => exact absurd hc (by decide +kernel)
  | hook _ hhk _ _ _ => exact absurd hhk (by decide +kernel)
  | param _ _ hp _ _ => exact absurd hp (by decide +kernel)
  | call _ _ hts hvs hf _ =>
    cases hts with
    | cons h1 h2 =>
      cases h2; cases h1
      rw [hl] at hvs
      simp only [allSome, Option.bind_some, Option.map_some, Option.some.injEq] at hvs
      subst hvs
      exact evalG_inv hw hf
  | callUndef _ _ hts hvs _ =>
    cases hts with
    | cons h1 h2 =>
      cases h2; cases h1
      rw [hl] at hvs
      simp [allSome] at hvs
  | ovl _ ho _ _ => exact absurd ho (by decide +kernel)
  | ovlFn _ ho _ _ _ _ _ => exact absurd ho (by decide +kernel)

/-! ## The clause of `f`: its `post` is `Z = 0` -/

theorem post_holds (σ : Subst) :
    Holds cCeV 1 σ clCf.post ((σ.lookup 0).isSome && sameResult (σ.lookup 0) (some i0)) :=
  Holds.mem EvalTerm.var (termLp σ)

theorem post_inv {σ : Subst} {b : Bool} (h : Holds cCeV 1 σ clCf.post b) :
    b = ((σ.lookup 0).isSome && sameResult (σ.lookup 0) (some i0)) := by
  cases h with
  | mem h1 h2 =>
    have e1 := EvalTerm.var_inv h1
    have e2 := termLp_inv h2
    subst e1; subst e2; rfl

theorem post_true {σ : Subst} (h : Holds cCeV 1 σ clCf.post true) : σ.lookup 0 = some i0 := by
  have e := post_inv h
  cases hl : σ.lookup 0 with
  | none => rw [hl] at e; simp at e
  | some z =>
    rw [hl] at e
    simp only [Option.isSome_some, Bool.true_and] at e
    rw [sameResult_some.mp e.symm]

theorem sr_i0 : sameResult (some i0) (some i0) = true := sameResult_some.mpr rfl

theorem post_at0 (σ : Subst) : Holds cCeV 1 ((0, i0) :: σ) clCf.post true :=
  holds_cast (post_holds _) (by rw [lkSelf, sr_i0]; rfl)

/-- **Every instance of the clause of `f` is decided and gives 0 or nothing**: at `Z = 0` it gives
`g(0) = 0`, at any other Int its `post` is false. -/
theorem inst_all (σ' : Subst) (hw : cCeV.WellSorted clCf.vars σ') : InstIs cCeV σ' clCf (some i0) := by
  obtain ⟨z, hz, hzs⟩ := hw 0 Srt.int rfl
  cases hb : sameResult (some z) (some i0) with
  | true =>
    have hzi : z = i0 := sameResult_some.mp hb
    subst hzi
    exact .gives (termG hz i0_int) (fun t ht => nomatch ht) (holds_cast (post_holds σ') (by rw [hz, hb]; rfl))
  | false =>
    exact .fails (post_holds σ') (.post (holds_cast (post_holds σ') (by rw [hz, hb]; rfl)))

/-- The instance at `Z = 0` does not give nothing. -/
theorem inst_at0_not_none (σ : Subst) : ¬ InstIs cCeV ((0, i0) :: σ) clCf none := by
  have hl : ((0, i0) :: σ : Subst).lookup 0 = some i0 := lkSelf _ _ _
  intro hi
  cases hi with
  | fails _ hf =>
    cases hf with
    | ens ht _ _ => cases ht
    | post hp =>
      have e := post_inv hp
      rw [hl, sr_i0] at e
      simp at e
    | rhs h => cases termG_inv hl i0_int h

/-- **The clause of `f` has the one result 0 at each match.** -/
theorem res_eq (σ : Subst) (r : Option GroundTerm) (h : Clause.Res cCeV clCf σ r) : r = some i0 := by
  rcases h with ⟨hex, -⟩ | ⟨-, (⟨σ', v, -, -, ⟨hrhs, -, hpost⟩, -, rfl⟩ | ⟨rfl, -, hall⟩)⟩
  · exact absurd hex (by decide)
  · exact termG_inv (post_true hpost) i0_int hrhs
  · exact absurd (hall ((0, i0) :: σ) (ext_agree _ _) (ext_sorted i0_int _)) (inst_at0_not_none σ)

/-- **The clause of `f` has the result 0 at every match.** -/
theorem res_some (σ : Subst) : Clause.Res cCeV clCf σ (some i0) :=
  .inr ⟨by decide, .inl ⟨(0, i0) :: σ, i0, ext_agree _ _, ext_sorted i0_int _,
    ⟨termG (lkSelf _ _ _) i0_int, (fun t ht => nomatch ht), post_at0 σ⟩, fun σ'' _ hw => inst_all σ'' hw, rfl⟩⟩

/-! ## `f()` is 0 -/

/-- **`f()` is 0**, by `clauseEx` at `Z = 0`. -/
theorem fC_value : Eval cCeV fC [] (some i0) :=
  .clauseEx (fn := fnCf) (cl := clCf) (σ := [(0, i0)]) lookup_fC (List.mem_singleton_self _)
    (ext_sorted i0_int []) .nil (fun t ht => nomatch ht) Holds.top
    (fun cl' hcl' _ hlt => by
      simp only [fnCf, List.mem_singleton] at hcl'; subst hcl'; exact absurd hlt (Nat.lt_irrefl _))
    (by decide) (termG (lkSelf _ _ _) i0_int) (fun t ht => nomatch ht) (post_at0 [])
    (fun σ' _ hw => inst_all σ' hw)

/-- **`f()` has no other result.** -/
theorem fC_inv {r : Option GroundTerm} (h : Eval cCeV fC [] r) : r = some i0 := by
  cases h with
  | clause hfn hmem _ _ _ _ _ hex _ _ _ =>
    rw [lookup_fC] at hfn; cases hfn
    simp only [fnCf, List.mem_singleton] at hmem; subst hmem
    exact absurd hex (by decide)
  | rest hfn hnone =>
    rw [lookup_fC] at hfn; cases hfn
    cases hnone clCf (by simp [fnCf]) with
    | intro h =>
      cases h [] (fun i hi => by simp [Clause.leftVars, Clause.condVars, clCf, varOccsList, varOccsCond] at hi) .nil with
      | intro ht _ _ => cases ht
      | pre hp => exact absurd (Holds.top_eq hp) (by simp)
  | ensFails hfn hmem _ _ _ _ _ hex _ _ _ =>
    rw [lookup_fC] at hfn; cases hfn
    simp only [fnCf, List.mem_singleton] at hmem; subst hmem
    exact absurd hex (by decide)
  | clauseEx hfn hmem _ _ _ _ _ _ hrhs _ hpost _ =>
    rw [lookup_fC] at hfn; cases hfn
    simp only [fnCf, List.mem_singleton] at hmem; subst hmem
    exact termG_inv (post_true hpost) i0_int hrhs
  | @exNone _ _ _ _ σ hfn hmem _ _ _ _ _ _ _ hall =>
    rw [lookup_fC] at hfn; cases hfn
    simp only [fnCf, List.mem_singleton] at hmem; subst hmem
    exact absurd (hall ((0, i0) :: σ) (ext_agree _ _) (ext_sorted i0_int _)) (inst_at0_not_none σ)

theorem termF (σ : Subst) : EvalTerm cCeV σ (.app fC []) (some i0) :=
  .call flagsF.1 flagsF.2.1 .nil rfl fC_value flagsF.2.2.1

theorem termF_inv {σ : Subst} {r : Option GroundTerm} (h : EvalTerm cCeV σ (.app fC []) r) : r = some i0 := by
  cases h with
  | ctor hc _ => exact absurd hc (by decide +kernel)
  | hook _ hhk _ _ _ => exact absurd hhk (by decide +kernel)
  | param _ _ hp _ _ => exact absurd hp (by decide +kernel)
  | call _ _ hts hvs hf _ =>
    cases hts
    simp only [allSome, Option.some.injEq] at hvs
    subst hvs
    exact fC_inv hf
  | callUndef _ _ hts hvs _ =>
    cases hts
    simp [allSome] at hvs
  | ovl _ ho _ _ => exact absurd ho (by decide +kernel)
  | ovlFn _ ho _ _ _ _ _ => exact absurd ho (by decide +kernel)

/-! ## `FnHyp cCeV` -/

/-- **Every function of `cCeV` has a result at every argument list of its sorts.** -/
theorem cCeV_fnTerminates : FnTerminates cCeV := by
  intro fn hfn vs hvs
  rcases mem_fns hfn with rfl | rfl | rfl
  · obtain rfl := sortsOf_nilV hvs; exact ⟨_, fC_value⟩
  · obtain rfl := sortsOf_nilV hvs; exact ⟨_, evalLp⟩
  · obtain ⟨w, rfl, hw⟩ := sortsOf_oneV hvs; exact ⟨_, evalG hw⟩

theorem clG_coherent : Coherent cCeV clG clG := by
  intro vs σ σ' ha ha' _ _ _ _ _
  obtain ⟨v, rfl, hl⟩ := match0 ha.2.1
  obtain ⟨w, hw, hl'⟩ := match0 ha'.2.1
  cases hw
  refine .inl ⟨rfl, rfl, rfl, rfl, fun i hi => ?_, fun t ht => nomatch ht⟩
  have : i = 0 := by simpa [clG, varOccs] using hi
  rw [this, hl, hl']

theorem clLp0_coherent : Coherent cCeV clLp0 clLp0 := by
  intro _ _ _ _ _ _ _ _ _ _
  exact .inl ⟨rfl, rfl, rfl, rfl, fun i hi => by simp [clLp0, varOccs] at hi, fun t ht => nomatch ht⟩

theorem clCf_coherent : Coherent cCeV clCf clCf :=
  fun _ σ σ' _ _ _ _ _ _ _ => .inr fun r r' hr hr' => (res_eq σ r hr).trans (res_eq σ' r' hr').symm

theorem agree_one {fn : Fn} {cl : Clause} (h : fn.clauses = [cl]) : ClausesAgree cCeV fn := by
  intro a b hp _
  rw [h] at hp
  simp [pairs] at hp

/-- **`FnHyp cCeV`.** -/
theorem cCeV_fnHyp : FnHyp cCeV :=
  ⟨cCeV_fnTerminates,
   fun fn hfn ht => by rcases mem_fns hfn with rfl | rfl | rfl <;> exact absurd ht (by decide),
   fun fn hfn => by rcases mem_fns hfn with rfl | rfl | rfl <;> exact agree_one rfl,
   fun fn hfn cl hcl => by
     rcases mem_fns hfn with rfl | rfl | rfl <;> simp only [fnCf, fnLp0, fnG, List.mem_singleton] at hcl <;>
       subst hcl
     · exact ⟨clCf_coherent, fun _ _ _ _ σ _ _ _ => ⟨_, res_some σ⟩⟩
     · exact (matchIndependent_iff_noExs rfl).mpr clLp0_coherent
     · exact (matchIndependent_iff_noExs rfl).mpr clG_coherent,
   cCeV_openDecided, cCeV_openLaws⟩

/-! ## The steps -/

/-- `<k> K </k> <counter> N </counter>` -/
def cfgV (k n : GroundTerm) : GroundTerm := .ctor topLabel [.ctor kcS [k], .ctor counterLabel [n]]

theorem ctorsV : cCeV.isCtor topLabel = true ∧ cCeV.isCtor counterLabel = true ∧ cCeV.isCtor kcS = true := by
  decide +kernel

theorem phooksV : patternHooks.contains topLabel = false ∧ patternHooks.contains counterLabel = false ∧
    patternHooks.contains kcS = false := by
  decide +kernel

/-- A match of `r0`'s left side. -/
theorem lhs_inv {σ : Subst} {x : GroundTerm} (h : PatVal cCeV σ r0.lhs x) :
    ∃ k n, x = cfgV k n ∧ σ.lookup 0 = some k ∧ σ.lookup 1 = some n := by
  obtain ⟨-, vs, rfl, hs⟩ := PatVal.app_inv phooksV.1 h ctorsV.1
  obtain ⟨a, vs, rfl, ha, hs⟩ := PatVals.cons_inv hs
  obtain ⟨b, vs, rfl, hb, hs⟩ := PatVals.cons_inv hs
  rw [PatVals.nil_inv hs]
  obtain ⟨-, as, rfl, has⟩ := PatVal.app_inv phooksV.2.2 ha ctorsV.2.2
  obtain ⟨-, bs, rfl, hbs⟩ := PatVal.app_inv phooksV.2.1 hb ctorsV.2.1
  obtain ⟨k, as, rfl, hk, has⟩ := PatVals.cons_inv has
  obtain ⟨n, bs, rfl, hn, hbs⟩ := PatVals.cons_inv hbs
  rw [PatVals.nil_inv has, PatVals.nil_inv hbs]
  exact ⟨k, n, rfl, PatVal.var_inv hk, PatVal.var_inv hn⟩

/-- `r0`'s right side is the configuration with the counter 0. -/
theorem termRhs {σ : Subst} {k : GroundTerm} (h0 : σ.lookup 0 = some k) :
    EvalTerm cCeV σ r0.rhs (some (cfgV k i0)) := by
  have := EvalTerm.ctor (c := cCeV) (σ := σ) ctorsV.1
    (.cons (.ctor ctorsV.2.2 (.cons (EvalTerm.var (i := 0)) .nil)) (.cons (.ctor ctorsV.2.1 (.cons (termF σ) .nil)) .nil))
  rw [h0] at this
  exact this

theorem rhs_inv {σ : Subst} {k : GroundTerm} {r : Option GroundTerm} (h0 : σ.lookup 0 = some k)
    (h : EvalTerm cCeV σ r0.rhs r) : r = some (cfgV k i0) := by
  obtain ⟨rs, hrs, rfl⟩ := EvalTerm.ctor_inv ctorsV.1 h
  obtain ⟨r1, rs, rfl, h1, hrs⟩ := EvalTerms.cons_inv hrs
  obtain ⟨r2, rs, rfl, h2, hrs⟩ := EvalTerms.cons_inv hrs
  rw [EvalTerms.nil_inv hrs]
  obtain ⟨q1, hq1, rfl⟩ := EvalTerm.ctor_inv ctorsV.2.2 h1
  obtain ⟨q2, hq2, rfl⟩ := EvalTerm.ctor_inv ctorsV.2.1 h2
  obtain ⟨u, q1, rfl, hu, hq1⟩ := EvalTerms.cons_inv hq1
  obtain ⟨w, q2, rfl, hw, hq2⟩ := EvalTerms.cons_inv hq2
  rw [EvalTerms.nil_inv hq1, EvalTerms.nil_inv hq2, EvalTerm.var_inv hu, h0, termF_inv hw]
  rfl

theorem sig_top : lookupSig cCeV.ctorSigs topLabel = some ⟨topLabel, [nRegSorts, Srt.counter], Srt.top⟩ := by
  rw [lookupSig_eq]; rfl
theorem sig_kc : lookupSig cCeV.ctorSigs kcS = some ⟨kcS, [Srt.k], nRegSorts⟩ := by
  rw [lookupSig_eq]; rfl
theorem sig_counter : lookupSig cCeV.ctorSigs counterLabel = some ⟨counterLabel, [Srt.int], Srt.counter⟩ := by
  rw [lookupSig_eq]; rfl

theorem ctor_sorts {f : Sym} {ts : List GroundTerm} {k : CtorSig} {s : Srt} (hf : cCeV.isCtor f = true)
    (hk : lookupSig cCeV.ctorSigs f = some k) (h : cCeV.sortOf (.ctor f ts) = some s) :
    cCeV.sortsOf ts = some k.args := by
  obtain ⟨k', hk', hs, -⟩ := (sortOf_ctor_of_isCtor hf).mp h
  rw [hk] at hk'; cases hk'
  exact hs

/-- The parts of a configuration of the shape `r0` matches have their sorts. -/
theorem cfg_sorts {k n : GroundTerm} (h : cCeV.sortOf (cfgV k n) = some Srt.top) :
    cCeV.sortOf k = some Srt.k ∧ cCeV.sortOf n = some Srt.int := by
  have h1 := ctor_sorts ctorsV.1 sig_top h
  obtain ⟨ha, h2⟩ := sortsOf_consV h1
  obtain ⟨hb, -⟩ := sortsOf_consV h2
  obtain ⟨hk, -⟩ := sortsOf_consV (ctor_sorts ctorsV.2.2 sig_kc ha)
  obtain ⟨hn, -⟩ := sortsOf_consV (ctor_sorts ctorsV.2.1 sig_counter hb)
  exact ⟨hk, hn⟩

/-- `r0`'s premises from `<k> K </k> <counter> N </counter>` to `<k> K </k> <counter> 0 </counter>`. -/
theorem stepBy_r0 (x y : Config cCeV) (k n : GroundTerm) (hx : x.val = cfgV k n) (hy : y.val = cfgV k i0) :
    StepBy cCeV r0 [(0, k), (1, n)] x y := by
  have hp := x.property
  rw [hx] at hp
  obtain ⟨hk, hn⟩ := cfg_sorts hp
  exact
    { mem := by simp [cCeV]
      hσ := fun i s hs => by
        match i, hs with
        | 0, hs => cases (show some Srt.k = some s from hs); exact ⟨_, rfl, hk⟩
        | 1, hs => cases (show some Srt.int = some s from hs); exact ⟨_, rfl, hn⟩
        | _ + 2, hs => cases (show (none : Option Srt) = some s from hs)
      hmatch := by
        rw [hx]
        exact .ctor ctorsV.1 (.cons (.ctor ctorsV.2.2 (.cons (.var rfl) .nil))
          (.cons (.ctor ctorsV.2.1 (.cons (.var rfl) .nil)) .nil))
      hreq := fun t ht => nomatch ht
      hpre := .top
      heval := by rw [hy]; exact termRhs rfl
      hens := fun t ht => nomatch ht
      hpost := .top
      hprio := fun r' hr' hlt => by
        obtain rfl := mem_rules hr'
        exact absurd hlt (Nat.lt_irrefl _) }

/-- **`Step cCeV x y` exactly where y is x with the counter 0.** -/
theorem step_iff (x y : Config cCeV) : Step cCeV x y ↔ ∃ k n, x.val = cfgV k n ∧ y.val = cfgV k i0 := by
  rw [step_iff_by]
  constructor
  · rintro ⟨r, σ, hs⟩
    obtain rfl := mem_rules hs.mem
    obtain ⟨k, n, hx, h0, -⟩ := lhs_inv hs.hmatch
    exact ⟨k, n, hx, Option.some.inj (rhs_inv h0 hs.heval)⟩
  · rintro ⟨k, n, hx, hy⟩
    exact ⟨r0, _, stepBy_r0 x y k n hx hy⟩

/-- **The evaluations a step reads have results at every term**: `r0` has no `requires`, its
predicates are `\top`, and its right side has a result because `f()` has one. -/
theorem stepDecided (x : GroundTerm) : StepDecided cCeV x := by
  intro r hr _
  obtain rfl := mem_rules hr
  exact ⟨fun σ _ _ => ⟨(fun t ht => nomatch ht), true, Holds.top⟩,
    fun σ _ _ _ _ => ⟨⟨_, .ctor ctorsV.1 (.cons (.ctor ctorsV.2.2 (.cons .var .nil))
      (.cons (.ctor ctorsV.2.1 (.cons (termF σ) .nil)) .nil))⟩, (fun e he => nomatch he), true, Holds.top⟩⟩

/-! ## Every configuration has the shape `r0` matches -/

theorem noOvls : cCeV.ovls = [] := rfl

/-- A value of a sort that no subsort, collection or literal reaches is a constructor's term. -/
theorem ctor_of_sort {v : GroundTerm} {s : Srt} (h : cCeV.sortOf v = some s)
    (hsub : ∀ p ∈ cCeV.subsorts, p.2 ≠ s) (hcoll : cCeV.collOf s = none)
    (hdv : ∀ lit, dvOK cCeV.lib s lit = false) :
    ∃ f ts k, v = .ctor f ts ∧ lookupSig cCeV.ctorSigs f = some k ∧ cCeV.sortsOf ts = some k.args ∧
      s = k.result := by
  cases v with
  | ctor f ts =>
    obtain ⟨k, hk, hs, he⟩ := (cCeV.sortOf_ctor_of_none noOvls noRaw).mp h
    exact ⟨f, ts, k, rfl, hk, hs, he⟩
  | inj a b t =>
    simp only [Semantics.sortOf] at h
    split at h
    · rename_i hc
      cases h
      simp only [Bool.and_eq_true, List.contains_iff_mem] at hc
      exact absurd rfl (hsub _ hc.1.1)
    · cases h
  | dv s' lit =>
    simp only [Semantics.sortOf] at h
    split at h
    · rename_i hd; cases h; rw [hdv] at hd; cases hd
    · cases h
  | map s' es =>
    obtain ⟨k, -, hk, -, -, -, rfl⟩ := cCeV.sortOf_map_inv h
    rw [hcoll] at hk; cases hk
  | set s' es =>
    simp only [Semantics.sortOf] at h
    split at h
    · rename_i k ss hk _
      split at h
      · cases h; rw [hcoll] at hk; cases hk
      · cases h
    · cases h
  | list s' es =>
    simp only [Semantics.sortOf] at h
    split at h
    · rename_i k ss hk _
      split at h
      · cases h; rw [hcoll] at hk; cases hk
      · cases h
    · cases h

/-- A sort whose carrier is no literal sort has no literal. -/
theorem dv_none {s : Srt} (hi : (cCeV.lib.carrier s == Srt.int) = false)
    (hb : (cCeV.lib.carrier s == Srt.bool) = false) (hk : (cCeV.lib.carrier s == Srt.kconfigVar) = false)
    (hs : (cCeV.lib.carrier s == Srt.string) = false) (ht : cCeV.lib.tokenSorts.contains (cCeV.lib.carrier s) = false)
    (hy : (cCeV.lib.carrier s == Srt.bytes) = false) (hys : cCeV.lib.byteSorts.contains (cCeV.lib.carrier s) = false)
    (hf : (cCeV.lib.carrier s == Srt.float) = false) (lit : Lit) : dvOK cCeV.lib s lit = false := by
  cases lit <;> simp only [dvOK, hi, hb, hk, hs, ht, hy, hys, hf, Bool.or_false, Bool.false_and]

theorem dv_top : ∀ lit, dvOK cCeV.lib Srt.top lit = false :=
  dv_none (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem dv_kc : ∀ lit, dvOK cCeV.lib nRegSorts lit = false :=
  dv_none (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem dv_counter : ∀ lit, dvOK cCeV.lib Srt.counter lit = false :=
  dv_none (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem only_top : ∀ k ∈ cCeV.ctorSigs, k.result = Srt.top → k.name = topLabel := by decide +kernel
theorem only_kc : ∀ k ∈ cCeV.ctorSigs, k.result = nRegSorts → k.name = kcS := by decide +kernel
theorem only_counter : ∀ k ∈ cCeV.ctorSigs, k.result = Srt.counter → k.name = counterLabel := by
  decide +kernel

theorem shape_facts :
    (∀ p ∈ cCeV.subsorts, p.2 ≠ Srt.top) ∧ (∀ p ∈ cCeV.subsorts, p.2 ≠ nRegSorts) ∧
    (∀ p ∈ cCeV.subsorts, p.2 ≠ Srt.counter) ∧
    cCeV.collOf Srt.top = none ∧ cCeV.collOf nRegSorts = none ∧ cCeV.collOf Srt.counter = none := by
  decide +kernel

/-- The constructor of a value whose sort only one constructor has. -/
theorem ctor_unique {v : GroundTerm} {s : Srt} {g : Sym} (h : cCeV.sortOf v = some s)
    (hsub : ∀ p ∈ cCeV.subsorts, p.2 ≠ s) (hcoll : cCeV.collOf s = none)
    (hdv : ∀ lit, dvOK cCeV.lib s lit = false) (hone : ∀ k ∈ cCeV.ctorSigs, k.result = s → k.name = g) :
    ∃ ts, v = .ctor g ts ∧ ∃ k, lookupSig cCeV.ctorSigs g = some k ∧ cCeV.sortsOf ts = some k.args := by
  obtain ⟨f, ts, k, rfl, hk, hs, he⟩ := ctor_of_sort h hsub hcoll hdv
  have hfk : k ∈ cCeV.ctorSigs ∧ k.name = f := by
    rw [lookupSig_eq] at hk
    exact ⟨List.mem_of_find?_eq_some hk, by simpa using List.find?_some hk⟩
  have hg := hone k hfk.1 he.symm
  rw [hfk.2] at hg
  subst hg
  exact ⟨ts, rfl, k, hk, hs⟩

/-- **Every configuration of `cCeV` is `<k> K </k> <counter> N </counter>`**: `r0` matches it. -/
theorem cfg_shape (x : Config cCeV) : ∃ k n, x.val = cfgV k n := by
  obtain ⟨hst, hsk, hsc, hct, hck, hcc⟩ := shape_facts
  obtain ⟨ts, hx, k, hk, hs⟩ := ctor_unique x.property hst hct dv_top only_top
  rw [sig_top] at hk; cases hk
  obtain ⟨a, ts, rfl⟩ : ∃ a ts', ts = a :: ts' := by
    cases ts with | nil => simp [Semantics.sortsOf] at hs | cons a ts' => exact ⟨a, ts', rfl⟩
  obtain ⟨ha, hs⟩ := sortsOf_consV hs
  obtain ⟨b, hb', hb⟩ := sortsOf_oneV hs
  subst hb'
  obtain ⟨as, rfl, ka, hka, has⟩ := ctor_unique ha hsk hck dv_kc only_kc
  obtain ⟨bs, rfl, kb, hkb, hbs⟩ := ctor_unique hb hsc hcc dv_counter only_counter
  rw [sig_kc] at hka; cases hka
  rw [sig_counter] at hkb; cases hkb
  obtain ⟨k', rfl, -⟩ := sortsOf_oneV has
  obtain ⟨n', rfl, -⟩ := sortsOf_oneV hbs
  exact ⟨k', n', hx⟩

/-- **Every configuration has a successor**: itself with the counter 0. -/
theorem step_exists (x : Config cCeV) : ∃ y : Config cCeV, Step cCeV x y := by
  obtain ⟨k, n, hx⟩ := cfg_shape x
  have hp := x.property
  rw [hx] at hp
  obtain ⟨hk, -⟩ := cfg_sorts hp
  have hkc : cCeV.sortOf (.ctor kcS [k]) = some nRegSorts :=
    sortOf_ctor_intro ⟨_, sig_kc, sortsOf_cons.mpr ⟨_, _, hk, sortsOf_nil, rfl⟩, rfl⟩
  have hc0 : cCeV.sortOf (.ctor counterLabel [i0]) = some Srt.counter :=
    sortOf_ctor_intro ⟨_, sig_counter, sortsOf_cons.mpr ⟨_, _, i0_int, sortsOf_nil, rfl⟩, rfl⟩
  have hy : cCeV.sortOf (cfgV k i0) = some Srt.top :=
    sortOf_ctor_intro ⟨_, sig_top, sortsOf_cons.mpr ⟨_, _, hkc, sortsOf_cons.mpr ⟨_, _, hc0, sortsOf_nil, rfl⟩, rfl⟩, rfl⟩
  exact ⟨⟨_, hy⟩, (step_iff x ⟨_, hy⟩).mpr ⟨k, n, hx, rfl⟩⟩

/-! ## The statements at `cCeV` -/

/-- `<k> . </k> <counter> 1 </counter>` -/
def x1 : Config cCeV := ⟨cfgV (.ctor dotk []) (.dv Srt.int (.int 1)), by decide +kernel⟩
/-- `<k> . </k> <counter> 0 </counter>` -/
def y0 : Config cCeV := ⟨cfgV (.ctor dotk []) i0, by decide +kernel⟩

def σX : Subst := [(0, .ctor dotk []), (1, .dv Srt.int (.int 1))]

theorem stepX : StepBy cCeV r0 σX x1 y0 := stepBy_r0 x1 y0 _ _ rfl rfl

theorem x1_ne_y0 : x1 ≠ y0 := fun h => absurd (congrArg Subtype.val h) (by decide +kernel)

/-- **`step_of_successor_exCEx` at `cCeV`**: in every model of `Γc` with the step's closure, a
successor of a configuration is the configuration with the counter 0. -/
theorem successor_cfg {M : Type} [Inhabited M] {I : ML.Interpretation KoreAML.Sym M}
    (hI : I ⊧ᴵP (Faithful.Γc cCeV ∪ Faithful.Γstep cCeV)) (x y : Config cCeV) (e : ML.Valuation M)
    (hs : (KoreAML.sNext (den cCeV y.val)).interpret I e (Faithful.elemOf cCeV I x.val)) :
    ∃ k n, x.val = cfgV k n ∧ y.val = cfgV k i0 :=
  (step_iff x y).mp (step_of_successor_exCEx cCeV cCeV_coreOKEx cCeV_fnHyp cCeV_rules hI x y e hs)

/-- **`sound_at_ce` at every step of `cCeV`.** -/
theorem sound_step (x y : Config cCeV) (r : Rule) (σ : Subst) (hs : StepBy cCeV r σ x y) :
    (Faithful.Γc cCeV ⊧ (den cCeV x.val ⇒ KoreAML.sNext (Faithful.famEx cCeV r σ))) ∧
      (Faithful.Γc cCeV ⊧ (den cCeV y.val ⇒ Faithful.famEx cCeV r σ)) :=
  sound_at_ce cCeV cCeV_coreOKEx x y r σ hs
    (fun r' hr' hlt => by
      obtain rfl := mem_rules hr'; obtain rfl := mem_rules hs.mem; exact absurd hlt (Nat.lt_irrefl _))
    noWit

/-- **`sound_at_ce` at `r0`'s step from the counter 1 to the counter 0.** -/
theorem sound_x1 :
    (Faithful.Γc cCeV ⊧ (den cCeV x1.val ⇒ KoreAML.sNext (Faithful.famEx cCeV r0 σX))) ∧
      (Faithful.Γc cCeV ⊧ (den cCeV y0.val ⇒ Faithful.famEx cCeV r0 σX)) :=
  sound_step x1 y0 r0 σX stepX

/-- **`famEx_closed_ce` at every step of `cCeV`.** -/
theorem famEx_step {x y : Config cCeV} {r : Rule} {σ : Subst} (hs : StepBy cCeV r σ x y) :
    Faithful.Γc cCeV ⊧ (Faithful.famEx cCeV r σ ≡ den cCeV y.val) :=
  famEx_closed_ce cCeV cCeV_coreOKEx hs (by obtain rfl := mem_rules hs.mem; rfl) noWit

theorem famEx_x1 : Faithful.Γc cCeV ⊧ (Faithful.famEx cCeV r0 σX ≡ den cCeV y0.val) := famEx_step stepX

/-- **`complete_at_ce` at every configuration of `cCeV`**: with the step's closure, every successor
of `<k> K </k> <counter> N </counter>` is `<k> K </k> <counter> 0 </counter>`. -/
theorem complete_cfg (x : Config cCeV) (k n : GroundTerm) (hx : x.val = cfgV k n) :
    (Faithful.Γc cCeV ∪ Faithful.Γstep cCeV) ⊧
      (den cCeV x.val ⇒ KoreAML.allNext (KoreAML.disjList ([Outcome.val (cfgV k i0)].map (Outcome.pat cCeV)))) :=
  complete_at_ce cCeV cCeV_coreOKEx x (stepDecided _) [Outcome.val (cfgV k i0)]
    (fun y r σ _ hs => by
      obtain ⟨k', n', hx', hy⟩ := (step_iff x y).mp (step_iff_by.mpr ⟨r, σ, hs⟩)
      rw [hx] at hx'
      simp only [cfgV, GroundTerm.ctor.injEq, List.cons.injEq, and_true, true_and] at hx'
      rw [hy, ← hx'.1]
      exact List.mem_singleton.mpr rfl)
    (fun r hr hne => absurd (by obtain rfl := mem_rules hr; exact r0_opens) hne)
    noWit

theorem complete_x1 :
    (Faithful.Γc cCeV ∪ Faithful.Γstep cCeV) ⊧
      (den cCeV x1.val ⇒ KoreAML.allNext (KoreAML.disjList ([Outcome.val y0.val].map (Outcome.pat cCeV)))) :=
  complete_cfg x1 _ _ rfl

/-! ## The model -/

theorem cCeV_hypModelCore : Faithful.Model.HypModelCore cCeV :=
  Faithful.Model.hypModelCore_of_coreEx cCeV_coreOKEx (fnModel_of_fnHypCEx cCeV_coreOKEx cCeV_fnHyp).1
    (fnModel_of_fnHypCEx cCeV_coreOKEx cCeV_fnHyp).2

theorem cCeV_preDecided : ClausePreDecided cCeV := clausePreDecided_of_fnHypCEx cCeV_coreOKEx cCeV_fnHyp

theorem cCeV_postDecided : ClausePostDecided cCeV := clausePostDecided_of_fnHypCEx cCeV_coreOKEx cCeV_fnHyp

/-- **`consistent_ce` at `cCeV`**: the theory of the text with the rule `r0` has a model. -/
theorem cCeV_consistent : Consistent cCeV :=
  Faithful.Model.consistent_ce cCeV cCeV_hypModelCore cCeV_preDecided cCeV_postDecided cCeV_openLaws

/-- The pinned `consistent_of` and `sound_hyp` at `cCeV`, which `coreOK` accepts. -/
example : Consistent cCeV :=
  consistent_of cCeV cCeV_coreOK (fnModel_of_fnHypCEx cCeV_coreOKEx cCeV_fnHyp).1
    (fnModel_of_fnHypCEx cCeV_coreOKEx cCeV_fnHyp).2 cCeV_preDecided cCeV_postDecided cCeV_openLaws
example : SoundC cCeV := sound_hyp cCeV cCeV_coreOK cCeV_fnHyp

/-- **`has_model_choice_exCEx` at `cCeV`, at `T := Step cCeV`**: a model of `Γc` with the step's
closure in which x has y as a successor exactly where y is x with the counter 0. -/
theorem cCeV_model_step :
    ∃ (M : Type) (_ : Inhabited M) (I : ML.Interpretation KoreAML.Sym M),
      (I ⊧ᴵP (Faithful.Γc cCeV ∪ Faithful.Γstep cCeV)) ∧
      ∀ x y : Config cCeV, (∃ k n, x.val = cfgV k n ∧ y.val = cfgV k i0) ↔
        ¬ (I ⊧ᴵ (den cCeV x.val ⇒ ∼ KoreAML.sNext (den cCeV y.val))) := by
  obtain ⟨M, hM, I, hI, hT⟩ := has_model_choice_exCEx cCeV cCeV_coreOKEx cCeV_fnHyp cCeV_rules (Step cCeV)
    (fun _ _ h => h) (fun _ _ r σ hb _ => step_iff_by.mpr ⟨r, σ, hb⟩)
    (fun _ y r σ hb => ⟨y, σ, fun _ _ => rfl, hb, step_iff_by.mpr ⟨r, σ, hb⟩⟩)
  exact ⟨M, hM, I, hI, fun x y => (step_iff x y).symm.trans (hT x y)⟩

/-- The models `successor_cfg` speaks of exist. -/
theorem cCeV_has_model :
    ∃ (M : Type) (_ : Inhabited M) (I : ML.Interpretation KoreAML.Sym M),
      I ⊧ᴵP (Faithful.Γc cCeV ∪ Faithful.Γstep cCeV) := by
  obtain ⟨M, hM, I, hI, -⟩ := cCeV_model_step
  exact ⟨M, hM, I, hI⟩

/-- In a model of `Γc` with the step's closure, the configuration with the counter 1 has the one with
the counter 0 as a successor, and not itself. -/
theorem cCeV_model_x1 :
    ∃ (M : Type) (_ : Inhabited M) (I : ML.Interpretation KoreAML.Sym M),
      (I ⊧ᴵP (Faithful.Γc cCeV ∪ Faithful.Γstep cCeV)) ∧
      ¬ (I ⊧ᴵ (den cCeV x1.val ⇒ ∼ KoreAML.sNext (den cCeV y0.val))) ∧
      (I ⊧ᴵ (den cCeV x1.val ⇒ ∼ KoreAML.sNext (den cCeV x1.val))) := by
  obtain ⟨M, hM, I, hI, hT⟩ := cCeV_model_step
  refine ⟨M, hM, I, hI, (hT x1 y0).mp ⟨_, _, rfl, rfl⟩, Classical.byContradiction fun hn => ?_⟩
  obtain ⟨k, n, -, hy⟩ := (hT x1 x1).mpr hn
  have hc : cfgV (.ctor dotk []) (.dv Srt.int (.int 1)) = cfgV k i0 := hy
  simp [cfgV, i0] at hc

/-! ## `exact_ce`, `has_model_choice_ce`, `famEx_values_ce` and `famOpen_values_ce` at `cCeV` -/

/-- **`exact_ce` at `cCeV`**. -/
theorem cCeV_exact : ExactC cCeV := exact_ce cCeV cCeV_coreOKEx cCeV_fnHyp

/-- **`has_model_choice_ce` at `cCeV`**. -/
theorem cCeV_model_choice (T : Config cCeV → Config cCeV → Prop)
    (hsub : ∀ x y, T x y → Step cCeV x y)
    (hall : ∀ x y r σ, StepBy cCeV r σ x y → r.exs = [] → T x y)
    (hsome : ∀ x y r σ, StepBy cCeV r σ x y → ∃ y' σ',
       (∀ i, ¬ i ∈ r.exs → σ'.lookup i = σ.lookup i) ∧ StepBy cCeV r σ' x y' ∧ T x y') :
    ∃ (M : Type) (_ : Inhabited M) (I : ML.Interpretation KoreAML.Sym M),
      (I ⊧ᴵP (Faithful.Γc cCeV ∪ Faithful.Γstep cCeV)) ∧
      ∀ x y : Config cCeV, T x y ↔ ¬ (I ⊧ᴵ (den cCeV x.val ⇒ ∼ KoreAML.sNext (den cCeV y.val))) :=
  has_model_choice_ce cCeV cCeV_coreOKEx cCeV_fnHyp T hsub hall hsome

/-- **`has_model_choice_ce` at `cCeV`, at `T := Step cCeV`**: `cCeV_model_step`'s statement. -/
theorem cCeV_model_step_ce :
    ∃ (M : Type) (_ : Inhabited M) (I : ML.Interpretation KoreAML.Sym M),
      (I ⊧ᴵP (Faithful.Γc cCeV ∪ Faithful.Γstep cCeV)) ∧
      ∀ x y : Config cCeV, (∃ k n, x.val = cfgV k n ∧ y.val = cfgV k i0) ↔
        ¬ (I ⊧ᴵ (den cCeV x.val ⇒ ∼ KoreAML.sNext (den cCeV y.val))) := by
  obtain ⟨M, hM, I, hI, hT⟩ := cCeV_model_choice (Step cCeV)
    (fun _ _ h => h) (fun _ _ r σ hb _ => step_iff_by.mpr ⟨r, σ, hb⟩)
    (fun _ y r σ hb => ⟨y, σ, fun _ _ => rfl, hb, step_iff_by.mpr ⟨r, σ, hb⟩⟩)
  exact ⟨M, hM, I, hI, fun x y => (step_iff x y).symm.trans (hT x y)⟩

/-- **`famEx_values_ce` at `cCeV`**. -/
theorem cCeV_famEx_values (x y : Config cCeV) (r : Rule) (σ : Subst) (hs : ∃ y₀, StepBy cCeV r σ x y₀)
    (hy : Faithful.Γc cCeV ⊧ (den cCeV y.val ⇒ Faithful.famEx cCeV r σ)) :
    ∃ σ', (∀ i, ¬ i ∈ r.exs → σ'.lookup i = σ.lookup i) ∧ StepBy cCeV r σ' x y :=
  famEx_values_ce cCeV cCeV_coreOKEx cCeV_fnHyp x y r σ hs hy

/-- A configuration whose element is, in every model of `Γc`, in `famEx r0 σX` is y0. -/
theorem famEx_values_x1 (y : Config cCeV)
    (hy : Faithful.Γc cCeV ⊧ (den cCeV y.val ⇒ Faithful.famEx cCeV r0 σX)) : y = y0 := by
  obtain ⟨σ', -, hb⟩ := cCeV_famEx_values x1 y r0 σX ⟨y0, stepX⟩ hy
  obtain ⟨k, n, hx, hy'⟩ := (step_iff x1 y).mp (step_iff_by.mpr ⟨r0, σ', hb⟩)
  have hk : cfgV (.ctor dotk []) (.dv Srt.int (.int 1)) = cfgV k n := hx
  simp only [cfgV, GroundTerm.ctor.injEq, List.cons.injEq, and_true, true_and] at hk
  apply Subtype.ext
  show y.val = cfgV (.ctor dotk []) i0
  rw [hy', ← hk.1]

/-- **`famOpen_values_ce` at `cCeV`**, at its one rule. -/
theorem cCeV_famOpen_values (x : Config cCeV) (σ : Subst) (hu : Unblocked cCeV r0 σ x.val)
    (ys : List GroundTerm)
    (hys : ∀ y : Config cCeV, (∃ σ', (∀ i ∈ varOccs r0.lhs, σ'.lookup i = σ.lookup i) ∧ StepBy cCeV r0 σ' x y) →
      y.val ∈ ys) :
    Faithful.Γc cCeV ⊧ (Faithful.famOpen cCeV r0 σ ⇒ KoreAML.disjList (ys.map (den cCeV))) :=
  famOpen_values_ce cCeV cCeV_coreOKEx cCeV_fnHyp x r0 (by simp [cCeV]) σ hu (by simp [r0_opens]) ys hys

end KCore.CeValueTest

#check @KCore.CeValueTest.cCeV
#check @KCore.CeValueTest.fC_value
#check @KCore.CeValueTest.cCeV_fnHyp
#check @KCore.CeValueTest.successor_cfg
#print axioms KCore.CeValueTest.cCeV_coreOKEx
#print axioms KCore.CeValueTest.cCeV_coreOK
#print axioms KCore.CeValueTest.cCeV_sortedOKClEx
#print axioms KCore.CeValueTest.fC_value
#print axioms KCore.CeValueTest.fC_inv
#print axioms KCore.CeValueTest.cCeV_fnHyp
#print axioms KCore.CeValueTest.step_iff
#print axioms KCore.CeValueTest.step_exists
#print axioms KCore.CeValueTest.stepDecided
#print axioms KCore.CeValueTest.successor_cfg
#print axioms KCore.CeValueTest.sound_step
#print axioms KCore.CeValueTest.sound_x1
#print axioms KCore.CeValueTest.famEx_x1
#print axioms KCore.CeValueTest.complete_cfg
#print axioms KCore.CeValueTest.complete_x1
#check @KCore.has_model_choice_exCEx
#check @KCore.stdI_T_modelCEx
#print axioms KCore.has_model_choice_exCEx
#print axioms KCore.CeValueTest.cCeV_hypModelCore
#print axioms KCore.CeValueTest.cCeV_postDecided
#print axioms KCore.CeValueTest.cCeV_consistent
#print axioms KCore.CeValueTest.cCeV_model_step
#print axioms KCore.CeValueTest.cCeV_has_model
#print axioms KCore.CeValueTest.cCeV_model_x1
#print axioms KCore.CeValueTest.cCeV_exact
#print axioms KCore.CeValueTest.cCeV_model_choice
#print axioms KCore.CeValueTest.cCeV_model_step_ce
#print axioms KCore.CeValueTest.cCeV_famEx_values
#print axioms KCore.CeValueTest.famEx_values_x1
#print axioms KCore.CeValueTest.cCeV_famOpen_values
