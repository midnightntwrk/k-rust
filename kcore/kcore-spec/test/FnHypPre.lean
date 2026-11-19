/-
  `FnHyp` and `Consistent` for every H on a text one of whose clauses has a predicate other than
  `\top` in its premise (KcoreSpec/FnHypPre.lean): the fixture e3-witnessed-pre,
  `f2-examples/e3-witnessed-pre.kompile.kore`.
  Run from the package root: `lake env lean -j1 test/FnHypPre.lean`.

  `syntax S ::= "a" | c(Empty) | "d"` (`syntax Empty`, no production), `isC(S)` total with
  `isC(c(_)) => true`, `isC(d) => true`, `isC(a) => false`, and `f(Int)` with
  `rule f(_) => 1 requires isC(H:S #And d) [unboundVariables(H)]`. The clause of `f` has the
  `requires` `isC(H)` and the premise predicate `H ∈ d` (`clG`), so `Semantics.clausesPreTop` is
  false (`clausesPreTop_false`) and no statement that reads it applies.

  - `fnHypH`: `FnHyp (cH H)` for every H, by `fnHyp_of_decidedPre_withHooks`. Termination: the order
    `callOrder` places `isC` before `f`, whose `requires` applies it and whose predicate applies no
    function (`term_named`: none named), so the predicate `H ∈ d` has a truth value at each match.
    Totality: `isC`, whose own clauses have the predicate `\top`, by `total_of_totalOKFP`. The
    agreement names no function (`agree_named`); the match independence names `f`'s clause
    (`match_named`), whose right side has no variable (`matchG`); `OpenDecided` is `openDecidedH`
    (the clause of `f` is `Witnessed` at H := d under every H); `OpenLaws` holds, the text having
    no open generator (`noRaw`).
  - `consistent`: `Consistent (cH H)` for every H, from it.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.FnHypPreTest

open KCore ML Faithful KoreAML

definition_of defn from "f2-examples/e3-witnessed-pre.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

def fS : Sym := 390
def isCS : Sym := 391
def dS : Sym := 388
def cS : Sym := 387
def aS : Sym := 386
def sS : Srt := 32

theorem names : c.symName fS = "Lblf" ∧ c.symName isCS = "LblisC" ∧ c.symName dS = "Lbld" ∧
    c.symName cS = "Lblc" ∧ c.symName aS = "Lbla" ∧ c.sortName sS = "S" ∧ c.sortName 33 = "Empty" := by
  decide +kernel

/-! ## The clauses -/

/-- `f(X) => 1 requires isC(H) ∧ H ∈ d`, X:Int, H:S -/
def clG : Clause :=
  { vars := [Srt.int, sS], pats := [.var 0], req := some (.app isCS [.var 1]), rhs := .dv Srt.int (.int 1),
    ens := none, pre := .mem sS (.var 1) (.app dS []) }
def fG : Fn := { label := fS, args := [Srt.int], result := Srt.int, clauses := [clG] }
/-- `isC(c(_)) => true` -/
def ic1 : Clause := { vars := [33], pats := [.app cS [.var 0]], req := none, rhs := .dv Srt.bool (.bool true), ens := none }
/-- `isC(a) => false` -/
def ica : Clause := { vars := [], pats := [.app aS []], req := none, rhs := .dv Srt.bool (.bool false), ens := none }
/-- `isC(d) => true` -/
def icd : Clause := { vars := [], pats := [.app dS []], req := none, rhs := .dv Srt.bool (.bool true), ens := none }
def fIsC : Fn := { label := isCS, args := [sS], result := Srt.bool, clauses := [ica, ic1, icd], total := true }

theorem text : c.fns = [fG, fIsC] := by rfl
theorem fG_mem : fG ∈ c.fns := by rw [text]; exact List.mem_cons_self ..
theorem fIsC_mem : fIsC ∈ c.fns := by rw [text]; exact List.mem_cons_of_mem _ (List.mem_singleton_self _)

theorem coreOK : c.coreOK = true := by decide_cheap
theorem coreOKH (H : HookParams) : (cH H).coreOK = true := (Semantics.coreOK_withHooks c H).trans coreOK

/-- A clause's predicate is not `\top`. -/
theorem clausesPreTop_false : c.clausesPreTop = false := by decide +kernel

theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel
theorem rightHeld : c.RightHeld := Semantics.rightHeld_of_valued (by decide +kernel)
theorem fnOvl_none : c.fnOvlSyms = [] := by decide +kernel
theorem noExs : c.FnsNoExs := Semantics.fnsNoExs_of_all (by decide +kernel)

theorem lookupFH (H : HookParams) : (cH H).lookupFn fS = some fG := by rfl
theorem lookupIsCH (H : HookParams) : (cH H).lookupFn isCS = some fIsC := by rfl

def dv : GroundTerm := .ctor dS []

theorem sorts : c.sortOf dv = some sS := by decide +kernel
theorem sortsH (H : HookParams) : (cH H).sortOf dv = some sS := by
  show (c.withHooks H).sortOf dv = some sS
  rw [Semantics.sortOf_withHooks c H noRaw]; exact sorts

theorem syms : c.isCtor dS = true ∧ c.isCtor isCS = false ∧ isHook isCS = false ∧ c.isParam isCS = false := by
  decide +kernel

/-! ## The facts the deciders name -/

/-- `isC`, then `f`. -/
def callOrder : List Sym := [isCS, fS]

/-- No function's termination is named: each applies, in its clauses' terms and predicates, only
functions placed before it. -/
theorem term_named : c.preRankObligationsFP callOrder = [] := by decide +kernel
theorem agree_named : c.agreeObligationsI = [] := by decide +kernel
theorem match_named : c.matchObligationsL = [(fS, 0)] := by decide +kernel
theorem owed_rules : c.owedRules = ([] : List Nat) := by decide +kernel
theorem owed_clauses : c.owedClauses = [(0, 0)] := by decide +kernel
/-- The totality check accepts `isC`. -/
theorem total_isC : c.totalOK fIsC = true ∧ c.totalBefore fIsC = [] := by decide +kernel

/-! ## Match independence and coherence, for every H -/

/-- The clause of `f` is match independent: its right side has no variable. -/
theorem matchG (H : HookParams) : MatchIndependent (cH H) clG := by
  have hx : clG.exs = [] := rfl
  refine (matchIndependent_iff_noExs hx).mpr fun vs σ σ' _ _ _ _ _ _ _ => .inl
    ⟨hx, hx, rfl, rfl, fun i hi => ?_, fun t ht => by cases ht⟩
  cases hi

/-- The match independences the deciders leave, for every H: the clause of `f`. -/
theorem matchOblH (H : HookParams) : Det.MatchObligationsL (cH H) := by
  intro p hp fn hfn cl hcl
  rw [Det.Semantics.matchObligationsL_withHooks, match_named, List.mem_singleton] at hp
  subst hp
  rw [lookupFH] at hfn
  cases hfn
  simp only [fG, List.getElem?_cons_zero, Option.some.injEq] at hcl
  subst hcl
  exact matchG H

open Det in
/-- **The clauses that compete are coherent, for every H.** No termination fact and no fact on the
clauses' predicates is read. -/
theorem coherentH (H : HookParams) : CoherentAll (cH H) := by
  obtain ⟨hok, -, hha, hp, hids⟩ := Semantics.coreOK_parts (coreOKH H)
  have hsr := NamesApart.srReady_of hp hids hok
    (NamesApart.rangeKeys_genWf_of_faithCore (Semantics.coreOK_parts (coreOKH H)).2.1) (Semantics.coreOK_ovls (coreOKH H))
  have hmc : Exec.MatchCtxO (cH H) := ⟨NamesApart.subsorts_trans_of hids hok,
    NamesApart.subsorts_irrefl_of hids hok, NamesApart.patHooks_of hha hids, Semantics.coreOK_ovls (coreOKH H)⟩
  have hnoEx : (cH H).FnsNoExs := (Semantics.fnsNoExs_withHooks _ _).mpr noExs
  have hag := clausesAgree_of_IO hok hnoEx hsr hmc (fun f hf => by
    rw [Det.Semantics.agreeObligationsI_withHooks, agree_named] at hf; exact absurd hf List.not_mem_nil)
  have hmi := matchIndependentAll_of_L hok hnoEx hmc (matchOblH H)
  exact coherentAll_of_parts hmi fun f fn hfn => by
    obtain ⟨hmem, -⟩ := lookupFn_spec hfn
    rcases List.mem_append.mp hmem with hu | hp
    · exact hag fn hu
    · exact sortPreds_agree hp

/-! ## The clause of `f` is `Witnessed` at H := d, for every H -/

/-- **`isC(d)` is `true`**, by `isC(d) => true`: no clause of a smaller priority. -/
theorem isC_d (H : HookParams) : Eval (cH H) isCS [dv] (some (bool true)) :=
  .clause (cl := icd) (σ := []) (lookupIsCH H) (by simp [fIsC]) (fun i s hs => by simp [icd] at hs)
    (.cons (.ctor syms.1 .nil) .nil) (fun _ ht => by cases ht) .top
    (fun cl' hcl' _ hlt => by
      simp only [fIsC, List.mem_cons, List.not_mem_nil, or_false] at hcl'
      rcases hcl' with rfl | rfl | rfl <;> exact absurd hlt (by decide))
    rfl .dv (fun _ ht => by cases ht) .top

/-- `H ↦ d`. -/
def σd : Subst := [(1, dv)]

/-- The `requires` `isC(H)` at H := d: `true`. -/
theorem req_d (H : HookParams) : EvalTerm (cH H) σd (.app isCS [.var 1]) (some (bool true)) :=
  .call (vs := [dv]) syms.2.1 syms.2.2.1 (.cons .var .nil) rfl (isC_d H) syms.2.2.2

/-- The predicate `H ∈ d` at H := d: true. -/
theorem pre_d (H : HookParams) : Holds (cH H) clG.vars.length σd clG.pre true := by
  have h := Holds.mem (c := cH H) (n := clG.vars.length) (σ := σd) (s := sS) (EvalTerm.var (i := 1))
    (EvalTerm.ctor (ts := []) syms.1 .nil)
  have e : ((σd.lookup 1).isSome &&
      sameResult (σd.lookup 1) ((allSome ([] : List (Option GroundTerm))).map (GroundTerm.ctor dS))) = true := by
    decide +kernel
  rw [e] at h
  exact h

/-- **The clause of `f` is `Witnessed`** at H := d, under every interpretation: its `requires`
`isC(d)` is `true` and its predicate `d ∈ d` true, and under `coherentH` neither has another
result. -/
theorem witnessedH (H : HookParams) : clG.Witnessed (cH H) := by
  refine Clause.witnessed_of_coherent (coherentH H) (σ := σd) (fun j hj s hs => ?_) (fun t ht => ?_) (pre_d H)
  · have hj1 : j = 1 := by
      have : clG.condVars = [1, 1] := by decide +kernel
      rw [this] at hj; simpa using hj
    subst hj1
    cases (show some sS = some s from hs)
    exact ⟨dv, rfl, sortsH H⟩
  · cases ht
    exact ⟨req_d H, fun r hr => EvalTerm.functional (coherentH H) hr (req_d H)⟩

/-- **`OpenDecided` for every H**: no rule's condition is owed, and the one clause owed, `f`'s, is
`Witnessed`. -/
theorem openDecidedH (H : HookParams) : OpenDecided (cH H) :=
  ⟨openRules_of_owed (by rw [Semantics.owedRules_withHooks, owed_rules]; intro i hi; cases hi),
   openClauses_of_owed (by
    intro p hp fn hfn cl hcl
    rw [Semantics.owedClauses_withHooks, owed_clauses, List.mem_singleton] at hp
    subst hp
    have hfn' : c.fns[0]? = some fn := hfn
    rw [text] at hfn'
    cases hfn'
    cases hcl
    exact .inl (witnessedH H))⟩

/-! ## Totality of `isC`, for every H -/

/-- **`isC` is total under every H**, given that every function terminates: its own clauses have
the predicate `\top`, and the totality check accepts it (`total_isC`). -/
theorem total_isCH (H : HookParams) (hterm : ∀ g, Terminates (cH H) g) : Total (cH H) isCS :=
  total_of_totalOKFP (c := cH H) (fn := fIsC) (coreOKH H) ((Semantics.fnsNoExs_withHooks _ _).mpr noExs) hterm
    fIsC_mem
    ((Semantics.rightHeld_withHooks rightHeld H noRaw).heldFn fIsC_mem)
    (show c.totalOK fIsC = true from total_isC.1)
    (fun cl hcl => by
      simp only [fIsC, List.mem_cons, List.not_mem_nil, or_false] at hcl
      rcases hcl with rfl | rfl | rfl <;> rfl)
    (fun g hg => by
      have : g ∈ c.totalBefore fIsC := hg
      rw [total_isC.2] at this
      cases this)

/-! ## `FnHyp` and consistency, for every H -/

/-- **Every function terminates under every H**: by the order `callOrder`, which names none. The
predicate of `f`'s clause is decided at each match, its terms applying no function. -/
theorem terminatesH (H : HookParams) : ∀ g, Terminates (cH H) g := by
  obtain ⟨hok, -, -, hp, hids⟩ := Semantics.coreOK_parts (coreOKH H)
  have hsr := NamesApart.srReady_of hp hids hok
    (NamesApart.rangeKeys_genWf_of_faithCore (Semantics.coreOK_parts (coreOKH H)).2.1) (Semantics.coreOK_ovls (coreOKH H))
  exact terminates_of_preRankFP (sortCtx_of_all hok hsr (Semantics.ovlCase_of_core (coreOKH H))) hok
    ((Semantics.fnsNoExs_withHooks _ _).mpr noExs) (Semantics.rightHeld_withHooks rightHeld H noRaw)
    fnOvl_none callOrder (fun g hg => by
      rw [Semantics.preRankObligationsFP_withHooks, term_named] at hg; cases hg)

/-- **`FnHyp` for every H**, by `fnHyp_of_decidedPre_withHooks`. -/
theorem fnHypH (H : HookParams) : FnHyp (cH H) :=
  fnHyp_of_decidedPre_withHooks coreOK rightHeld fnOvl_none H callOrder
    (fun g hg => by rw [term_named] at hg; cases hg)
    (fun fn hfn ht => by
      rw [text] at hfn
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hfn
      rcases hfn with rfl | rfl
      · cases ht
      · exact total_isCH H (terminatesH H))
    (fun f hf => by rw [agree_named] at hf; cases hf)
    (matchOblH H) (openDecidedH H) (openLaws_of_plain noRaw) noRaw noExs

/-- **Γ with the step's closure has a model, for every H.** -/
theorem consistent (H : HookParams) : Consistent (cH H) := consistent_of_fnHyp _ (coreOKH H) (fnHypH H)

/-- **The predicate of `f`'s clause has a truth value at every well-sorted σ, for every H**
(`holds_of_callsFP`): its terms apply no function. -/
theorem pre_decidedH (H : HookParams) {σ : Subst} (hσ : (cH H).WellSorted clG.vars σ) :
    ∃ b, Holds (cH H) clG.vars.length σ clG.pre b := by
  obtain ⟨hok, -, -, hp, hids⟩ := Semantics.coreOK_parts (coreOKH H)
  have hsr := NamesApart.srReady_of hp hids hok
    (NamesApart.rangeKeys_genWf_of_faithCore (Semantics.coreOK_parts (coreOKH H)).2.1) (Semantics.coreOK_ovls (coreOKH H))
  refine holds_of_callsFP (sortCtx_of_all hok hsr (Semantics.ovlCase_of_core (coreOKH H))) clG.pre
    (Semantics.sortedOK_preOK hok fG fG_mem clG (by simp [fG])) hσ
    (fun g hg => ?_)
  have hd : g = dS := by
    have : clG.pre.callHeadsFP = [dS] := by decide +kernel
    rw [this] at hg; simpa using hg
  subst hd
  refine ⟨fun gfn hgfn => ?_, ovlTerminates_of_not_fnOvl (by
    rw [Semantics.fnOvlSyms_withHooksFP, fnOvl_none]; exact List.not_mem_nil)⟩
  exact absurd hgfn (by
    have : (cH H).lookupFn dS = none := by rfl
    rw [this]; exact fun h => nomatch h)

end KCore.FnHypPreTest

#check @KCore.FnHypPreTest.fnHypH
#check @KCore.FnHypPreTest.consistent
#check @KCore.FnHypPreTest.openDecidedH
#check @KCore.FnHypPreTest.terminatesH
#check @KCore.FnHypPreTest.total_isCH
#check @KCore.FnHypPreTest.pre_decidedH

/-- info: 'KCore.FnHypPreTest.clausesPreTop_false' depends on axioms: [propext] -/
#guard_msgs in #print axioms KCore.FnHypPreTest.clausesPreTop_false
/-- info: 'KCore.FnHypPreTest.fnHypH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.FnHypPreTest.fnHypH
/-- info: 'KCore.FnHypPreTest.consistent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.FnHypPreTest.consistent
/-- info: 'KCore.FnHypPreTest.pre_decidedH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.FnHypPreTest.pre_decidedH
