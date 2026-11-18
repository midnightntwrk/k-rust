/-
  `consistent_ofCl` at two definitions with a clause whose variable only the right side holds.
  Run from the package root: `lake env lean -j1 test/OpenClauseConsistent.lean`. Kernel-checked
  (`decide +kernel`).

  Both are the reader's semantics for `f2-examples/opencl.kompile.kore` (`opencl.k`: Int, Bool, a
  sort S with the generators `a` and `c(Empty)`, Empty without a generator, the total predicate
  `isC`, `f()` without an equation (a parameter of the semantics), the function `g(Int)` with
  `g(_) => 0 [owise]`, the rule `<k> go => g(f()) </k>`), with `f` made a function whose clause is
  written by hand:
  - `cE`: `[total] f() => c(Y:Empty)`, f of sort S, its one clause (the rule, which reads `f` at Int,
    is left out). Y is of Empty, which no constructor has as its result: the clause applies nowhere
    and `f` has no result, so `FnHyp cE` is false (`not_fnHypE`: f is `[total]`); `FnDet` and
    `FnSolves` hold, nothing being asked where no clause decides. The theory has a model
    (`consistentE`): in the value model Empty is empty and the clause's equation holds vacuously.
  - `cI`: `f() => g(Y:Int)`, f of sort Int: Y has a value, and every instance gives `0`
    (`g(_) => 0`). Its functions terminate, agree and are match independent (shown by hand), and the
    theory has a model (`consistentI`).
  Both are `coreOK` (`clauseSorted` asks of Y only that it occur in the clause), and `sortedOKCl`.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

open KCore

namespace OpenClauseConsistentTest

definition_of defn from "f2-examples/opencl.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem

/-- The symbols and sorts the clauses name. -/
example : c.symName 391 = "Lblf" ∧ c.symName 387 = "Lblc" ∧ c.symName 389 = "Lblg" ∧
    c.sortName 32 = "S" ∧ c.sortName 33 = "Empty" := by
  decide +kernel

/-- In the text `f` is a parameter. -/
example : c.params.map (·.sig.name) = [391] ∧ c.fns.map (·.label) = [389, 390] := by decide +kernel

/-- The text's functions (`g`, `isC`): each clause's patterns bind its variables, it has no
`requires` and no `ensures`, and its right side is a literal. -/
theorem textFns : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, binds cl.vars.length (varOccsList cl.pats) = true ∧
    cl.req = none ∧ cl.ens = none ∧ (match cl.rhs with | .dv _ _ => true | _ => false) = true := by
  decide +kernel

/-- Each clause of the text's functions has the precondition `.top`. -/
theorem textPre : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, cl.pre = .top :=
  fun fn hfn cl hcl =>
    Cond.eq_top_of_isTop ((by decide +kernel : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, cl.pre.isTop = true) fn hfn cl hcl)

/-- Two clauses of one of the text's functions are of different priorities, neither `aside`. -/
theorem textPairs : ∀ fn ∈ c.fns,
    (pairs fn.clauses).all (fun p => p.1.prio != p.2.prio && !p.1.aside && !p.2.aside) = true := by
  decide +kernel

/-! ## `[total] f() => c(Y:Empty)` -/

/-- `f() => c(Y:Empty)` -/
def clE : Clause := { vars := [33], pats := [], req := none, rhs := .app 387 [.var 0], ens := none }

/-- `f`, `[total]`, of sort S, with the one clause `clE`. -/
def fE : Fn := { label := 391, args := [], result := 32, clauses := [clE], total := true }

/-- `c` with `f` a function of the clause `clE`, without the rule. -/
noncomputable def cE : Semantics :=
  { c with fns := c.fns ++ [fE], params := c.params.filter (·.sig.name != 391), rules := [] }

/-- Empty is the result of no constructor and not `valued`; `clE`'s variable is outside its patterns
and conditions, so `rightValued` fails; `sortedOK` and `coreOK` hold at `cE`. -/
theorem shapeE : cE.ctorSigs.all (·.result != 33) = true ∧ cE.valued 33 = false ∧ clE.leftVars = [] ∧
    cE.rightValued = false ∧ cE.sortedOK = true ∧ cE.coreOK = true := by
  decide_cheap

/-- What `consistent_ofCl` asks of `cE` beside the functions' facts, decided. -/
theorem decidedE : cE.sortedOKCl = true ∧ cE.srReady = true ∧ cE.faithCoreOK = true ∧
    Faithful.patHooksApart cE = true ∧ cE.idsOK = true ∧ cE.ovls = [] ∧ cE.subsorts.all (fun p => p.1 != p.2) = true := by
  decide_cheap

/-- `coreOK`'s other conjuncts hold at `cE`. -/
example : cE.hooksApart = true ∧ cE.predsApart = true ∧ cE.overloadsOK = true := by decide +kernel

instance ovlE : OvlOK cE := OvlOK.of_nil decidedE.2.2.2.2.2.1 decidedE.2.2.2.2.2.2

theorem lookupE {fn : Fn} (hfn : fn ∈ cE.fns) : cE.lookupFn fn.label = some fn := by
  rw [Semantics.lookupFn_eq]
  exact find?_label (sortCtx_of_allCl decidedE.1 decidedE.2.1 (OvlOK.ovlCase ovlE)).nodupFns
    (List.mem_append_left _ hfn)

theorem subs_E : cE.subsorts.all (fun p => p.2 != 33) = true := by decide +kernel
theorem coll_E : cE.collOf 33 = none := by decide +kernel
theorem lib_E : cE.lib.carriers.all (·.1 != 33) = true := by decide +kernel

/-- **No value has sort Empty**: no constructor and no subsort pair ends there, no literal is of
it, and it is no collection sort. -/
theorem no_E (v : GroundTerm) : cE.sortOf v ≠ some 33 := by
  intro h
  cases v with
  | ctor f ts =>
    rw [Semantics.sortOf] at h
    cases hk : lookupSig cE.ctorSigs f with
    | none =>
      have : cE.lookupOvl f = none := by simp [Semantics.lookupOvl, decidedE.2.2.2.2.2.1]
      rw [hk, this, cE.lookupOpen_of_noRaw (by decide +kernel) f] at h; cases h
    | some k =>
      rw [hk] at h
      simp only at h
      split at h
      · have hm := List.mem_of_find?_eq_some (by rw [← lookupSig_eq]; exact hk)
        have := List.all_eq_true.mp shapeE.1 k hm
        rw [Option.some.inj h] at this
        simp at this
      · cases h
  | inj a b t =>
    rw [Semantics.sortOf] at h
    split at h
    · rename_i h'
      cases h
      simp only [Bool.and_eq_true, List.contains_iff_mem] at h'
      have := List.all_eq_true.mp subs_E _ h'.1.1
      simp at this
    · cases h
  | dv s' lit =>
    obtain ⟨hd, rfl⟩ := sortOf_dv.mp h
    have hcs := Lib.carrier_of_not _ lib_E
    cases lit with
    | int _ => simp only [dvOK, hcs, beq_iff_eq] at hd; exact absurd hd (by decide)
    | bool _ => simp only [dvOK, hcs, beq_iff_eq] at hd; exact absurd hd (by decide)
    | float _ _ _ => simp only [dvOK, hcs, Bool.and_eq_true, beq_iff_eq] at hd; exact absurd hd.1 (by decide)
    | tok t =>
      simp only [dvOK, hcs, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hd
      rcases hd with ((hd | hd) | hd) | ⟨hd | hd, -⟩
      · exact absurd hd (by decide)
      · exact absurd hd (by decide)
      · exact absurd hd (by decide +kernel)
      · exact absurd hd (by decide)
      · exact absurd hd (by decide +kernel)
  | map s' es =>
    obtain ⟨k, -, hco, -, -, -, -, rfl⟩ := sortOf_mapS_fwd h
    rw [coll_E] at hco; cases hco
  | set s' es =>
    obtain ⟨k, hco, -, -, -, rfl⟩ := sortOf_setS.mp h
    rw [coll_E] at hco; cases hco
  | list s' es =>
    obtain ⟨k, hco, -, -, rfl⟩ := sortOf_listS.mp h
    rw [coll_E] at hco; cases hco

/-- `clE` applies under no substitution: Y is of Empty. -/
theorem clE_not_applies (σ : Subst) (vs : List GroundTerm) : ¬ clE.AppliesAt cE σ vs := by
  rintro ⟨h, -⟩
  obtain ⟨v, -, hv⟩ := h 0 33 rfl
  exact no_E v hv

/-- A clause without `ensures` or existential variables whose right side is a literal is coherent
with itself. -/
theorem coherent_dvE {cl : Clause} (hn : cl.ens = none) {s : Srt} {l : Lit} (hr : cl.rhs = .dv s l)
    (hx : cl.exs = []) : Coherent cE cl cl :=
  Coherent.of_rhs hn hn (fun _ _ _ _ _ _ _ _ => .inr fun r r' h h' => by
    rw [hr] at h h'; cases h; cases h'; rfl) hx hx

/-- The equations of `cE`'s functions agree: the text's clauses of one function are of different
priorities; `f` has one clause. -/
theorem agreeE : ∀ fn ∈ cE.fns, ClausesAgree cE fn := by
  intro fn hfn
  rcases List.mem_append.mp (show fn ∈ c.fns ++ [fE] from hfn) with hu | hf
  · intro cl cl' hp hcomp
    exact absurd hcomp (not_compete (List.all_eq_true.mp (textPairs fn hu) _ hp))
  · rw [List.mem_singleton] at hf
    subst hf
    intro cl cl' hp _
    simp [fE, pairs] at hp

/-- The clauses of `cE`'s functions are match independent: the text's have literal right sides
and no `ensures`; `clE` applies nowhere. -/
theorem matchIndE : ∀ fn ∈ cE.fns, ∀ cl ∈ fn.clauses, MatchIndependent cE cl := by
  intro fn hfn cl hcl
  rcases List.mem_append.mp (show fn ∈ c.fns ++ [fE] from hfn) with hu | hf
  · have h4 := (textFns fn hu cl hcl).2.2.2
    cases hr : cl.rhs with
    | dv s l =>
      have hx : cl.exs = [] :=
        (Semantics.sortedOK_plainCl shapeE.2.2.2.2.1 fn (List.mem_append_left _ hfn) cl hcl).1
      exact (matchIndependent_iff_noExs hx).mpr (coherent_dvE (textFns fn hu cl hcl).2.2.1 hr hx)
    | _ => rw [hr] at h4; cases h4
  · rw [List.mem_singleton] at hf
    subst hf
    simp only [fE, List.mem_cons, List.not_mem_nil, or_false] at hcl
    subst hcl
    exact (matchIndependent_iff_noExs rfl).mpr fun vs σ _ ha => absurd ha (clE_not_applies σ vs)

/-- No clause of `cE` has a `requires`. -/
theorem reqNoneE : ∀ fn ∈ cE.fns, ∀ cl ∈ fn.clauses, cl.req = none := by decide +kernel

/-- Each clause of `cE` has the precondition `.top`. -/
theorem preTopE : ∀ fn ∈ cE.fns, ∀ cl ∈ fn.clauses, cl.pre = .top :=
  fun fn hfn cl hcl =>
    Cond.eq_top_of_isTop ((by decide +kernel : ∀ fn ∈ cE.fns, ∀ cl ∈ fn.clauses, cl.pre.isTop = true) fn hfn cl hcl)

theorem fnDetE : FnDet cE := Faithful.fnDet_of_agree agreeE matchIndE

/-- **Evaluation solves `cE`'s equations**: a clause that decides is one of the text's, whose right
side is a literal; `clE` decides nowhere. -/
theorem fnSolvesE : FnSolves cE := by
  refine fnSolves_of_parts_lookup (fun _ hfn => lookupE hfn) fnDetE
    (fun fn hfn => Semantics.sortedOK_plainCl shapeE.2.2.2.2.1 fn (List.mem_append_left _ hfn)) ?_ ?_
  · intro fn hfn _ _ _ _ _ cl' hcl' _ _ σ' _ _
    exact ⟨(fun t ht => by rw [reqNoneE fn hfn cl' hcl'] at ht; cases ht), true,
      Clause.holds_preTop (preTopE fn hfn cl' hcl') σ'⟩
  · intro fn hfn vs cl σ cl' σ' hcl hcl' hdec _ _
    rcases List.mem_append.mp (show fn ∈ c.fns ++ [fE] from hfn) with hu | hf
    · have h4 := (textFns fn hu cl' hcl').2.2.2
      cases hr : cl'.rhs with
      | dv s l =>
        refine ⟨some (.dv s l), Or.inl ⟨fun t ht => ?_, ?_⟩⟩
        · rw [(textFns fn hu cl' hcl').2.2.1] at ht; cases ht
        · rw [hr]; exact .dv
      | _ => rw [hr] at h4; cases h4
    · rw [List.mem_singleton] at hf
      subst hf
      simp only [fE, List.mem_cons, List.not_mem_nil, or_false] at hcl
      subst hcl
      exact absurd hdec.1 (clE_not_applies σ vs)

/-- **`f` has no result**: its one clause applies nowhere and does not fail (it has no
`requires`). -/
theorem no_evalE (r : Option GroundTerm) : ¬ Eval cE 391 [] r := by
  have hfn : cE.lookupFn 391 = some fE := lookupE (List.mem_append_right _ (List.mem_singleton_self _))
  intro h
  cases h with
  | clause hfn' hmem hσ hmatch hreq hpre _ _ _ =>
    rw [hfn] at hfn'; cases hfn'
    simp only [fE, List.mem_cons, List.not_mem_nil, or_false] at hmem
    subst hmem
    exact clE_not_applies _ _ ⟨hσ, hmatch, hreq, hpre⟩
  | rest hfn' hnone =>
    rw [hfn] at hfn'; cases hfn'
    cases hnone clE (List.mem_singleton_self _) with
    | intro h =>
      cases h [] (fun i hi => by simp [shapeE.2.2.1] at hi) .nil with
      | intro hq _ _ => cases hq
      | pre h => exact absurd (Holds.top_eq h) (by simp)
  | clauseEx hfn' hmem hσ hmatch hreq hpre =>
    rw [hfn] at hfn'; cases hfn'
    simp only [fE, List.mem_cons, List.not_mem_nil, or_false] at hmem
    subst hmem
    exact clE_not_applies _ _ ⟨hσ, hmatch, hreq, hpre⟩
  | exNone hfn' hmem hne =>
    rw [hfn] at hfn'; cases hfn'
    simp only [fE, List.mem_cons, List.not_mem_nil, or_false] at hmem
    subst hmem
    exact absurd rfl hne
  | ensFails hfn' hmem hσ hmatch hreq hpre _ _ _ _ =>
    rw [hfn] at hfn'; cases hfn'
    simp only [fE, List.mem_cons, List.not_mem_nil, or_false] at hmem
    subst hmem
    exact clE_not_applies _ _ ⟨hσ, hmatch, hreq, hpre⟩

/-- **`FnHyp cE` is false**: `f` is `[total]` and has no result at `[]`. So `consistent_of`
(through `sound_hyp`'s `FnHyp`) says nothing of `cE`, though `coreOK` holds there. -/
theorem not_fnHypE : ¬ FnHyp cE := fun hf => by
  obtain ⟨v, hv⟩ := hf.2.1 fE (List.mem_append_right _ (List.mem_singleton_self _)) rfl [] rfl
  exact no_evalE _ hv

/-- **What is owed of `f` at `cE` is false** (`HeldOwed`): `f` is `cE`'s one held-named function
(`Semantics.heldObligations`); its clause's variable is of Empty, which has no value, so the
variables are not held; and `f` has no result at `[]` (`no_evalE`), so it does not terminate. The
held-named forms (`fnHyp_of_fnObligationsN`) then say nothing of `cE`, as they must: `FnHyp cE` is
false (`not_fnHypE`). -/
theorem not_heldOwedE : cE.heldObligations = [391] ∧ ¬ HeldOwed cE 391 := by
  refine ⟨by decide +kernel, fun h => ?_⟩
  rcases h fE (lookupE (List.mem_append_right _ (List.mem_singleton_self _))) with h | ⟨h, -⟩
  · rcases h clE (List.mem_singleton_self _) 0 33 rfl with h | ⟨v, hv⟩
    · rw [shapeE.2.2.1] at h; cases h
    · exact no_E v hv
  · obtain ⟨r, hr⟩ := h fE (lookupE (List.mem_append_right _ (List.mem_singleton_self _))) [] rfl
    exact no_evalE r hr

/-- **`consistent_ofCl` at `cE`**: the theory of `cE` with the step's closure has a model. -/
theorem consistentE : Consistent cE :=
  consistent_ofCl cE decidedE.1 (Semantics.rulesTop_of_isTop (by decide +kernel)) decidedE.2.1 decidedE.2.2.1 decidedE.2.2.2.1 decidedE.2.2.2.2.1 fnDetE fnSolvesE
    (clausePreDecided_of_isTop (by decide +kernel)) (openLaws_of_plain (by decide +kernel))

/-! ## `f() => g(Y:Int)`, `g(_) => 0` -/

/-- `f() => g(Y:Int)` -/
def clI : Clause := { vars := [Srt.int], pats := [], req := none, rhs := .app 389 [.var 0], ens := none }

/-- `f` of sort Int with the one clause `clI`. -/
def fI : Fn := { label := 391, args := [], result := Srt.int, clauses := [clI] }

/-- `c` with `f` a function of the clause `clI`. -/
noncomputable def cI : Semantics := { c with fns := c.fns ++ [fI], params := c.params.filter (·.sig.name != 391) }

/-- `clI`'s variable is outside its patterns and conditions, of Int: `rightValued` holds and
`sortedOK` and `coreOK` hold at `cI`. -/
theorem shapeI : clI.leftVars = [] ∧ cI.rightValued = true ∧ cI.sortedOK = true ∧ cI.coreOK = true ∧ cI.rules.length = 1 := by
  decide_cheap

/-- What `consistent_ofCl` asks of `cI` beside the functions' facts, decided. -/
theorem decidedI : cI.sortedOKCl = true ∧ cI.srReady = true ∧ cI.faithCoreOK = true ∧
    Faithful.patHooksApart cI = true ∧ cI.idsOK = true ∧ cI.ovls = [] ∧ cI.subsorts.all (fun p => p.1 != p.2) = true := by
  decide_cheap

/-- `coreOK`'s other conjuncts hold at `cI`. -/
example : cI.hooksApart = true ∧ cI.predsApart = true ∧ cI.overloadsOK = true := by decide +kernel

instance ovlI : OvlOK cI := OvlOK.of_nil decidedI.2.2.2.2.2.1 decidedI.2.2.2.2.2.2

theorem lookupI {fn : Fn} (hfn : fn ∈ cI.fns) : cI.lookupFn fn.label = some fn := by
  rw [Semantics.lookupFn_eq]
  exact find?_label (sortCtx_of_allCl decidedI.1 decidedI.2.1 (OvlOK.ovlCase ovlI)).nodupFns
    (List.mem_append_left _ hfn)

/-- `g`, the text's function, with its one clause `g(_) => 0`. -/
noncomputable def gF : Fn := c.fns[0]'(by decide +kernel)
noncomputable def clG : Clause := gF.clauses[0]'(by decide +kernel)

theorem gF_mem : gF ∈ cI.fns := List.mem_append_left _ (List.getElem_mem _)
theorem gF_shape : gF.label = 389 ∧ gF.clauses.length = 1 ∧ clG.vars = [Srt.int] := by decide +kernel
theorem clG_pats : clG.pats = [.var 0] := by rfl
theorem clG_req : clG.req = none := by rfl
theorem clG_rhs : clG.rhs = .dv Srt.int (.int 0) := by rfl
theorem clG_ens : clG.ens = none := by rfl
theorem clG_mem : clG ∈ gF.clauses := List.getElem_mem _
theorem fI_mem : fI ∈ cI.fns := List.mem_append_right _ (List.mem_singleton_self _)

theorem isG : cI.isCtor 389 = false ∧ isHook 389 = false ∧ cI.isParam 389 = false ∧ cI.isOvl 389 = false := by
  decide +kernel

theorem lookupG : cI.lookupFn 389 = some gF := gF_shape.1 ▸ lookupI gF_mem

/-- A clause of `g` is `clG`. -/
theorem gF_clause {cl : Clause} (h : cl ∈ gF.clauses) : cl = clG := by
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem h
  have hj0 : j = 0 := by have := gF_shape.2.1; omega
  subst hj0
  rfl

/-- `g(v)` is `0` at an Int `v`: its one clause applies. -/
theorem evalG {v : GroundTerm} (hv : cI.sortOf v = some Srt.int) : Eval cI 389 [v] (some (.dv Srt.int (.int 0))) := by
  refine Eval.clause (σ := [(0, v)]) lookupG clG_mem (fun i s hs => ?_) ?_
    (fun t ht => by rw [clG_req] at ht; cases ht) (Clause.holds_preTop (by rfl) _) (fun cl' hcl' _ hlt => ?_)
    (by rfl) ?_ (fun t ht => by rw [clG_ens] at ht; cases ht) (Clause.holds_postTop (by rfl) _)
  · rw [gF_shape.2.2] at hs
    cases i with
    | zero => cases hs; exact ⟨_, rfl, hv⟩
    | succ i => simp at hs
  · rw [clG_pats]; exact .cons (.var rfl) .nil
  · rw [gF_clause hcl'] at hlt; exact absurd hlt (Nat.lt_irrefl _)
  · rw [clG_rhs]; exact .dv

/-- **`g(v)` has no result but `0`** at an Int `v`: its clause's right side is `0`, and the clause,
with no `requires` and a variable as pattern, does not fail. -/
theorem g_val {v : GroundTerm} (hv : cI.sortOf v = some Srt.int) {r : Option GroundTerm} (h : Eval cI 389 [v] r) :
    r = some (.dv Srt.int (.int 0)) := by
  cases h with
  | clause hfn' hmem _ _ _ _ _ _ hrhs _ _ =>
    rw [lookupG] at hfn'; cases hfn'
    rw [gF_clause hmem, clG_rhs] at hrhs
    cases hrhs; rfl
  | clauseEx hfn' hmem _ _ _ _ _ hne =>
    rw [lookupG] at hfn'; cases hfn'
    rw [gF_clause hmem] at hne; exact absurd rfl hne
  | exNone hfn' hmem hne =>
    rw [lookupG] at hfn'; cases hfn'
    rw [gF_clause hmem] at hne; exact absurd rfl hne
  | rest hfn' hnone =>
    rw [lookupG] at hfn'; cases hfn'
    cases hnone clG clG_mem with
    | intro h =>
      have hσ : cI.WellSortedAt clG.vars clG.leftVars [(0, v)] := by
        intro i _ s hs
        rw [gF_shape.2.2] at hs
        cases i with
        | zero => cases hs; exact ⟨v, rfl, hv⟩
        | succ i => simp at hs
      cases h [(0, v)] hσ (by rw [clG_pats]; exact .cons (.var rfl) .nil) with
      | intro hq _ _ => rw [clG_req] at hq; cases hq
      | pre h => rw [show clG.pre = .top by rfl] at h; exact absurd (Holds.top_eq h) (by simp)
  | ensFails hfn' hmem _ _ _ _ _ _ ht _ _ =>
    rw [lookupG] at hfn'; cases hfn'
    rw [gF_clause hmem, clG_ens] at ht; cases ht

/-- `g(Y)` under a σ giving Y an Int has the result `0` and no other. -/
theorem evalTerm_gY {σ : Subst} (hσ : cI.WellSorted clI.vars σ) {r : Option GroundTerm}
    (h : EvalTerm cI σ clI.rhs r) : r = some (.dv Srt.int (.int 0)) := by
  obtain ⟨v, hv, hsv⟩ := hσ 0 Srt.int rfl
  obtain ⟨h1, h2, h3, h4⟩ := isG
  cases h with
  | ctor hc _ => rw [h1] at hc; cases hc
  | hook _ hhk _ _ _ => rw [h2] at hhk; cases hhk
  | param _ _ hp _ _ => rw [h3] at hp; cases hp
  | call _ _ hts hvs hf _ =>
    cases hts with
    | cons ht hts' =>
      cases ht
      cases hts'
      rw [hv] at hvs
      simp only [allSome, Option.bind_some, Option.map_some, Option.some.injEq] at hvs
      subst hvs
      exact g_val hsv hf
  | callUndef _ _ hts hvs _ =>
    cases hts with
    | cons ht hts' =>
      cases ht
      cases hts'
      rw [hv] at hvs
      simp [allSome] at hvs
  | ovl _ ho _ => rw [h4] at ho; cases ho
  | ovlFn _ ho => rw [h4] at ho; cases ho

/-- `f()` is `0`: `clI` applies under Y := 0. -/
theorem evalF : Eval cI 391 [] (some (.dv Srt.int (.int 0))) := by
  refine Eval.clause (cl := clI) (σ := [(0, .dv Srt.int (.int 0))]) (lookupI fI_mem) (List.mem_singleton_self _)
    (fun i s hs => ?_) .nil (fun t h => by cases h) .top (fun cl' h _ hlt => ?_) rfl ?_ (fun t h => by cases h) .top
  · cases i with
    | zero => cases hs; exact ⟨_, rfl, by decide +kernel⟩
    | succ i => simp [clI] at hs
  · simp only [fI, List.mem_singleton] at h; subst h; exact absurd hlt (Nat.lt_irrefl _)
  · obtain ⟨h1, h2, h3, -⟩ := isG
    exact .call h1 h2 (.cons .var .nil) rfl (evalG (by decide +kernel)) h3

theorem sortsOf_nilI {vs : List GroundTerm} (h : cI.sortsOf vs = some []) : vs = [] := by
  cases vs with
  | nil => rfl
  | cons v vs => simp only [Semantics.sortsOf] at h; split at h <;> cases h

/-- **The functions of `cI` terminate**: `g` and `isC` by `eval_result`; `f()` is `0`. -/
theorem fnTerminatesI : FnTerminates cI := by
  intro fn hfn vs hvs
  rcases List.mem_append.mp (show fn ∈ c.fns ++ [fI] from hfn) with hfn' | hfn'
  · refine eval_result (lookupI hfn)
      (fun cl hcl =>
        let p := Semantics.clausePlainOpen_parts ((Semantics.sortedOKCl_parts decidedI.1).2.1 fn hfn cl hcl).2
        ⟨p.1, p.2.2.1⟩)
      (fun cl hcl => (textFns fn hfn' cl hcl).1)
      (fun cl hcl σ _ _ => ⟨(fun t ht => by rw [(textFns fn hfn' cl hcl).2.1] at ht; cases ht), true,
        Clause.holds_preTop (textPre fn hfn' cl hcl) σ⟩) (fun cl hcl _ _ => ?_)
      (fun cl hcl _ _ t ht => by rw [(textFns fn hfn' cl hcl).2.2.1] at ht; cases ht)
    have h4 := (textFns fn hfn' cl hcl).2.2.2
    cases hr : cl.rhs with
    | dv s l => exact ⟨_, .dv⟩
    | _ => rw [hr] at h4; cases h4
  · rw [List.mem_singleton] at hfn'
    subst hfn'
    rw [sortsOf_nilI hvs]
    exact ⟨_, evalF⟩

/-- A clause without `ensures` or existential variables whose right side is a literal is coherent
with itself. -/
theorem coherent_dvI {cl : Clause} (hn : cl.ens = none) {s : Srt} {l : Lit} (hr : cl.rhs = .dv s l)
    (hx : cl.exs = []) : Coherent cI cl cl :=
  Coherent.of_rhs hn hn (fun _ _ _ _ _ _ _ _ => .inr fun r r' h h' => by
    rw [hr] at h h'; cases h; cases h'; rfl) hx hx

theorem agreeI : ∀ fn ∈ cI.fns, ClausesAgree cI fn := by
  intro fn hfn
  rcases List.mem_append.mp (show fn ∈ c.fns ++ [fI] from hfn) with hu | hf
  · intro cl cl' hp hcomp
    exact absurd hcomp (not_compete (List.all_eq_true.mp (textPairs fn hu) _ hp))
  · rw [List.mem_singleton] at hf
    subst hf
    intro cl cl' hp _
    simp [fI, pairs] at hp

/-- **The clauses of `cI`'s functions are match independent**: the text's have literal right sides;
`clI`'s right side is `0` under every substitution that gives Y an Int. -/
theorem matchIndI : ∀ fn ∈ cI.fns, ∀ cl ∈ fn.clauses, MatchIndependent cI cl := by
  intro fn hfn cl hcl
  rcases List.mem_append.mp (show fn ∈ c.fns ++ [fI] from hfn) with hu | hf
  · have h4 := (textFns fn hu cl hcl).2.2.2
    cases hr : cl.rhs with
    | dv s l =>
      have hx : cl.exs = [] :=
        (Semantics.clausePlainOpen_parts ((Semantics.sortedOKCl_parts decidedI.1).2.1 fn hfn cl hcl).2).1
      exact (matchIndependent_iff_noExs hx).mpr (coherent_dvI (textFns fn hu cl hcl).2.2.1 hr hx)
    | _ => rw [hr] at h4; cases h4
  · rw [List.mem_singleton] at hf
    subst hf
    simp only [fI, List.mem_cons, List.not_mem_nil, or_false] at hcl
    subst hcl
    exact (matchIndependent_iff_noExs rfl).mpr <|
      Coherent.of_rhs rfl rfl fun _ _ _ ha ha' _ _ _ => .inr fun r r' h h' =>
        (evalTerm_gY ha.1 h).trans (evalTerm_gY ha'.1 h').symm

theorem fnModelI : FnDet cI ∧ FnSolves cI :=
  Faithful.fnModel_ofCl decidedI.1 decidedI.2.1 ovlI fnTerminatesI agreeI matchIndI

/-- **`consistent_ofCl` at `cI`**: the theory of `cI` with the step's closure has a model. -/
theorem consistentI : Consistent cI :=
  consistent_ofCl cI decidedI.1 (Semantics.rulesTop_of_isTop (by decide +kernel)) decidedI.2.1 decidedI.2.2.1 decidedI.2.2.2.1 decidedI.2.2.2.2.1 fnModelI.1 fnModelI.2
    (clausePreDecided_of_isTop (by decide +kernel)) (openLaws_of_plain (by decide +kernel))

/-- info: 'KCore.consistent_ofCl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.consistent_ofCl

/-- info: 'OpenClauseConsistentTest.consistentE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms consistentE

/-- info: 'OpenClauseConsistentTest.consistentI' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms consistentI

end OpenClauseConsistentTest
