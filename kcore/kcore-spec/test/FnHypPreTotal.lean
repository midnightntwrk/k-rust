/-
  Totality of a `[total]` function whose own clauses have a predicate other than `\top` in the
  premise (KcoreSpec/FnHypPre.lean, `total_of_totalOKPreFP`), on the three texts that have one.
  Run from the package root: `lake env lean -j1 test/FnHypPreTotal.lean`.

  A function has a value at an argument list where some clause applies there (its patterns match,
  its `requires` is `true`, its predicate is true), each clause applies or fails there, and the
  right-hand side of the clause of least priority that applies has a value. A predicate that is
  false takes its clause out, so the clauses that are sure to apply where their patterns match are
  those without `requires` whose predicate is `\top`.

  - `ReqNot`, `f2-examples/mleqreqnot.kompile.kore` (fixture e3-ml-eq-req-not):
    `f(X) => 1 requires #Not(X >Int 0)`, `f(_) => 0 [owise]`, `f` total. The first clause has the
    predicate `X >Int 0 = false`; the `[owise]` clause has none and its pattern is a variable, so
    it covers Int (`total_checked`: `totalOKFP`). `fnHypH`, `consistent`: for every H.
  - `ReqAndApp`, `f2-examples/mleqreqandapp.kompile.kore` (fixture e3-ml-eq-req-and-under-app):
    `f(X) => X -Int 1`, `g(X, Y) => 1 requires f(X #And Y) ==Int 0`, `g(_, _) => 0 [owise]`, both
    total. The first clause of `g` has the predicate `X ∈ Y`; the `[owise]` clause covers
    (`total_checked`). `fnHypH`, `consistent`: for every H.
  - `OrTotal`, `f2-examples/mleqort.kompile.kore` (fixture e3-ml-eq-rhs-or-total): `f(X) => X`,
    `g(X) => 0 -Int X`, `h(X) => f(X) #Or g(X)`, all total. Each of `h`'s three clauses has a
    predicate (`⌈f(X)⌉`, `⌈g(X)⌉`, and the conjunction of their negations with the `ensures`
    false), so no clause covers by its patterns and `totalOKFP` does not confirm `h`
    (`total_h_unchecked`). `h` has a value at every Int all the same (`total_hH`, for every H):
    `f` is total, so `⌈f(X)⌉` is true at every X and the clause `h(X) = f(X)` applies, no clause
    having a smaller priority. `FnHyp` is false on this text for another reason: the clauses for
    `f(X)` and `g(X)` both apply at 1 with the results 1 and -1, and Γ has no model
    (test/TieE3MlEqRhsOrTotalNoModel.lean: `inconsistent`, `not_fnHypH`).
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.FnHypPreTotal.ReqNot

open KCore ML Faithful KoreAML

definition_of defn from "f2-examples/mleqreqnot.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

def fS : Sym := 387

theorem names : c.symName fS = "Lblf" := by decide +kernel

theorem coreOK : c.coreOK = true := by decide_cheap
theorem coreOKH (H : HookParams) : (cH H).coreOK = true := (Semantics.coreOK_withHooks c H).trans coreOK

/-- A clause's predicate is not `\top`. -/
theorem clausesPreTop_false : c.clausesPreTop = false := by decide +kernel

theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel
theorem rightHeld : c.RightHeld := Semantics.rightHeld_of_valued (by decide +kernel)
theorem fnOvl_none : c.fnOvlSyms = [] := by decide +kernel
theorem noExs : c.FnsNoExs := Semantics.fnsNoExs_of_all (by decide +kernel)

/-! ### The facts the deciders name -/

def callOrder : List Sym := [fS]

/-- The functions, their `[total]` flags, the symbols their clauses' terms and predicates apply
(`_>Int_`, a hook, in the predicate of `f`'s first clause), and their clauses' priorities. -/
theorem fns_shape : (c.fns.map fun f => (f.label, f.total, f.callees, f.preHeadsFP, f.clauses.map (·.prio))) =
    [(fS, true, [], [21], [50, 200])] := by decide +kernel

theorem term_named : c.preRankObligationsFP callOrder = [] := by decide +kernel
theorem agree_named : c.agreeObligationsI = [] := by decide +kernel
theorem match_named : c.matchObligationsL = [] := by decide +kernel
theorem owed_rules : c.owedRules = ([] : List Nat) := by decide +kernel
theorem owed_clauses : c.owedClauses = [] := by decide +kernel

/-- The check of each `[total]` function, its covering rows those of clauses whose predicate is
`\top`: of `f`'s two clauses, the `[owise]` one. -/
theorem total_checked : c.fns.all (fun fn => !fn.total || c.totalOKFP fn) = true := by decide +kernel
theorem cover_rows : (c.fns.map fun fn => ((Semantics.coverRows fn).length, (Semantics.coverRowsFP fn).length)) =
    [(2, 1)] := by decide +kernel

/-! ### `FnHyp` and consistency, for every H -/

theorem matchOblH (H : HookParams) : Det.MatchObligationsL (cH H) := by
  intro p hp
  rw [Det.Semantics.matchObligationsL_withHooks, match_named] at hp
  cases hp

theorem openDecidedH (H : HookParams) : OpenDecided (cH H) :=
  ⟨openRules_of_owed (by rw [Semantics.owedRules_withHooks, owed_rules]; intro i hi; cases hi),
   openClauses_of_owed (by
    intro p hp
    rw [Semantics.owedClauses_withHooks, owed_clauses] at hp
    cases hp)⟩

/-- **Every function terminates under every H**: the order names none; the predicate of `f`'s
first clause applies a hook only, so it has a truth value at each match. -/
theorem terminatesH (H : HookParams) : ∀ g, Terminates (cH H) g := by
  obtain ⟨hok, -, -, hp, hids⟩ := Semantics.coreOK_parts (coreOKH H)
  have hsr := NamesApart.srReady_of hp hids hok
    (NamesApart.rangeKeys_genWf_of_faithCore (Semantics.coreOK_parts (coreOKH H)).2.1) (Semantics.coreOK_ovls (coreOKH H))
  exact terminates_of_preRankFP (sortCtx_of_all hok hsr (Semantics.ovlCase_of_core (coreOKH H))) hok
    ((Semantics.fnsNoExs_withHooks _ _).mpr noExs) (Semantics.rightHeld_withHooks rightHeld H noRaw)
    fnOvl_none callOrder (fun g hg => by
      rw [Semantics.preRankObligationsFP_withHooks, term_named] at hg; cases hg)

/-- **`f` is total under every H**: its `[owise]` clause, without `requires` and with the
predicate `\top`, applies at every Int; where the first clause's predicate is true and its
`requires` is `true`, that clause, of the smaller priority, gives the value. -/
theorem totalsH (H : HookParams) : ∀ fn ∈ c.fns, fn.total = true → Total (cH H) fn.label :=
  totals_of_totalOKPreFP_withHooks coreOK rightHeld fnOvl_none H (terminatesH H)
    (fun fn hfn ht => by simpa [ht] using List.all_eq_true.mp total_checked fn hfn) noRaw noExs

/-- **`FnHyp` for every H**, by `fnHyp_of_decidedPre_withHooks`. -/
theorem fnHypH (H : HookParams) : FnHyp (cH H) :=
  fnHyp_of_decidedPre_withHooks coreOK rightHeld fnOvl_none H callOrder
    (fun g hg => by rw [term_named] at hg; cases hg)
    (totalsH H)
    (fun f hf => by rw [agree_named] at hf; cases hf)
    (matchOblH H) (openDecidedH H) (openLaws_of_plain noRaw) noRaw noExs

/-- **Γ with the step's closure has a model, for every H.** -/
theorem consistent (H : HookParams) : Consistent (cH H) := consistent_of_fnHyp _ (coreOKH H) (fnHypH H)

end KCore.FnHypPreTotal.ReqNot

namespace KCore.FnHypPreTotal.ReqAndApp

open KCore ML Faithful KoreAML

definition_of defn from "f2-examples/mleqreqandapp.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

def fS : Sym := 387
def gS : Sym := 388

theorem names : c.symName fS = "Lblf" ∧ c.symName gS = "Lblg" := by decide +kernel

theorem coreOK : c.coreOK = true := by decide_cheap
theorem coreOKH (H : HookParams) : (cH H).coreOK = true := (Semantics.coreOK_withHooks c H).trans coreOK

/-- A clause's predicate is not `\top`. -/
theorem clausesPreTop_false : c.clausesPreTop = false := by decide +kernel

theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel
theorem rightHeld : c.RightHeld := Semantics.rightHeld_of_valued (by decide +kernel)
theorem fnOvl_none : c.fnOvlSyms = [] := by decide +kernel
theorem noExs : c.FnsNoExs := Semantics.fnsNoExs_of_all (by decide +kernel)

/-! ### The facts the deciders name -/

/-- `f`, then `g`, whose `requires` applies it. -/
def callOrder : List Sym := [fS, gS]

/-- The functions, their `[total]` flags, the symbols their clauses' terms and predicates apply
(the predicate `X ∈ Y` of `g`'s first clause applies none), and their clauses' priorities. -/
theorem fns_shape : (c.fns.map fun f => (f.label, f.total, f.callees, f.preHeadsFP, f.clauses.map (·.prio))) =
    [(fS, true, [13], [], [50]), (gS, true, [23, fS], [], [50, 200])] := by decide +kernel

theorem term_named : c.preRankObligationsFP callOrder = [] := by decide +kernel
theorem agree_named : c.agreeObligationsI = [] := by decide +kernel
theorem match_named : c.matchObligationsL = [] := by decide +kernel
theorem owed_rules : c.owedRules = ([] : List Nat) := by decide +kernel
theorem owed_clauses : c.owedClauses = [] := by decide +kernel

/-- The check of each `[total]` function, its covering rows those of clauses whose predicate is
`\top`: `f`'s clause, and of `g`'s two the `[owise]` one. -/
theorem total_checked : c.fns.all (fun fn => !fn.total || c.totalOKFP fn) = true := by decide +kernel
theorem cover_rows : (c.fns.map fun fn => ((Semantics.coverRows fn).length, (Semantics.coverRowsFP fn).length)) =
    [(1, 1), (1, 1)] := by decide +kernel

/-! ### `FnHyp` and consistency, for every H -/

theorem matchOblH (H : HookParams) : Det.MatchObligationsL (cH H) := by
  intro p hp
  rw [Det.Semantics.matchObligationsL_withHooks, match_named] at hp
  cases hp

theorem openDecidedH (H : HookParams) : OpenDecided (cH H) :=
  ⟨openRules_of_owed (by rw [Semantics.owedRules_withHooks, owed_rules]; intro i hi; cases hi),
   openClauses_of_owed (by
    intro p hp
    rw [Semantics.owedClauses_withHooks, owed_clauses] at hp
    cases hp)⟩

/-- **Every function terminates under every H**: the order names none. -/
theorem terminatesH (H : HookParams) : ∀ g, Terminates (cH H) g := by
  obtain ⟨hok, -, -, hp, hids⟩ := Semantics.coreOK_parts (coreOKH H)
  have hsr := NamesApart.srReady_of hp hids hok
    (NamesApart.rangeKeys_genWf_of_faithCore (Semantics.coreOK_parts (coreOKH H)).2.1) (Semantics.coreOK_ovls (coreOKH H))
  exact terminates_of_preRankFP (sortCtx_of_all hok hsr (Semantics.ovlCase_of_core (coreOKH H))) hok
    ((Semantics.fnsNoExs_withHooks _ _).mpr noExs) (Semantics.rightHeld_withHooks rightHeld H noRaw)
    fnOvl_none callOrder (fun g hg => by
      rw [Semantics.preRankObligationsFP_withHooks, term_named] at hg; cases hg)

/-- **`f` and `g` are total under every H**: `g`'s `[owise]` clause, without `requires` and with
the predicate `\top`, applies at every pair of Ints; where the first clause's predicate `X ∈ Y` is
true and its `requires` is `true`, that clause, of the smaller priority, gives the value. -/
theorem totalsH (H : HookParams) : ∀ fn ∈ c.fns, fn.total = true → Total (cH H) fn.label :=
  totals_of_totalOKPreFP_withHooks coreOK rightHeld fnOvl_none H (terminatesH H)
    (fun fn hfn ht => by simpa [ht] using List.all_eq_true.mp total_checked fn hfn) noRaw noExs

/-- **`FnHyp` for every H**, by `fnHyp_of_decidedPre_withHooks`. -/
theorem fnHypH (H : HookParams) : FnHyp (cH H) :=
  fnHyp_of_decidedPre_withHooks coreOK rightHeld fnOvl_none H callOrder
    (fun g hg => by rw [term_named] at hg; cases hg)
    (totalsH H)
    (fun f hf => by rw [agree_named] at hf; cases hf)
    (matchOblH H) (openDecidedH H) (openLaws_of_plain noRaw) noRaw noExs

/-- **Γ with the step's closure has a model, for every H.** -/
theorem consistent (H : HookParams) : Consistent (cH H) := consistent_of_fnHyp _ (coreOKH H) (fnHypH H)

end KCore.FnHypPreTotal.ReqAndApp

namespace KCore.FnHypPreTotal.OrTotal

open KCore ML Faithful KoreAML

definition_of defn from "f2-examples/mleqort.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

def fS : Sym := 384
def gS : Sym := 385
def hS : Sym := 386

theorem names : c.symName fS = "Lblf" ∧ c.symName gS = "Lblg" ∧ c.symName hS = "Lblh" := by decide +kernel

/-! ### The clauses -/

/-- `f(X) => X` -/
def clF : Clause := { vars := [Srt.int], pats := [.var 0], req := none, rhs := .var 0, ens := none }
def fF : Fn := { label := fS, args := [Srt.int], result := Srt.int, clauses := [clF], total := true }
/-- `g(X) => 0 -Int X` -/
def clGm : Clause :=
  { vars := [Srt.int], pats := [.var 0], req := none, rhs := .app 13 [.dv Srt.int (.int 0), .var 0], ens := none }
def gF : Fn := { label := gS, args := [Srt.int], result := Srt.int, clauses := [clGm], total := true }
/-- `h(X) = f(X)` where `f(X)` is defined -/
def clB : Clause :=
  { vars := [Srt.int], pats := [.var 0], req := none, rhs := .app fS [.var 0], ens := none,
    pre := .ceil Srt.int (.app fS [.var 0]) }
/-- `h(X) = g(X)` where `g(X)` is defined -/
def clC : Clause :=
  { vars := [Srt.int], pats := [.var 0], req := none, rhs := .app gS [.var 0], ens := none,
    pre := .ceil Srt.int (.app gS [.var 0]) }
/-- no value where neither is defined -/
def clA : Clause :=
  { vars := [Srt.int], pats := [.var 0], req := none, rhs := .app fS [.var 0],
    ens := some (.dv Srt.bool (.bool false)),
    pre := .and (.not (.ceil Srt.int (.app fS [.var 0]))) (.not (.ceil Srt.int (.app gS [.var 0]))) }
def hF : Fn := { label := hS, args := [Srt.int], result := Srt.int, clauses := [clB, clC, clA], total := true }

theorem text : c.fns = [fF, gF, hF] := by rfl
theorem fF_mem : fF ∈ c.fns := by rw [text]; exact List.mem_cons_self ..

theorem coreOK : c.coreOK = true := by decide_cheap
theorem coreOKH (H : HookParams) : (cH H).coreOK = true := (Semantics.coreOK_withHooks c H).trans coreOK

theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel
theorem rightHeld : c.RightHeld := Semantics.rightHeld_of_valued (by decide +kernel)
theorem fnOvl_none : c.fnOvlSyms = [] := by decide +kernel
theorem noExs : c.FnsNoExs := Semantics.fnsNoExs_of_all (by decide +kernel)

theorem lookupFH (H : HookParams) : (cH H).lookupFn fS = some fF := by rfl
theorem lookupHH (H : HookParams) : (cH H).lookupFn hS = some hF := by rfl
theorem syms : c.isCtor fS = false ∧ isHook fS = false ∧ c.isParam fS = false := by decide +kernel

/-- `f`, `g`, then `h`, whose clauses' right-hand sides and predicates apply them. -/
def callOrder : List Sym := [fS, gS, hS]

theorem term_named : c.preRankObligationsFP callOrder = [] := by decide +kernel

/-- The check accepts `f`, whose clause has the predicate `\top`; it does not accept `h`, none of
whose clauses has (and one has an `ensures`). -/
theorem total_f : c.totalOKFP fF = true ∧ c.totalBefore fF = [] := by decide +kernel
theorem total_h_unchecked : c.totalOKFP hF = false ∧ Semantics.coverRowsFP hF = [] := by decide +kernel

/-- **Every function terminates under every H**: the order names none, and the predicates of `h`'s
clauses apply `f` and `g`, placed before it. -/
theorem terminatesH (H : HookParams) : ∀ g, Terminates (cH H) g := by
  obtain ⟨hok, -, -, hp, hids⟩ := Semantics.coreOK_parts (coreOKH H)
  have hsr := NamesApart.srReady_of hp hids hok
    (NamesApart.rangeKeys_genWf_of_faithCore (Semantics.coreOK_parts (coreOKH H)).2.1) (Semantics.coreOK_ovls (coreOKH H))
  exact terminates_of_preRankFP (sortCtx_of_all hok hsr (Semantics.ovlCase_of_core (coreOKH H))) hok
    ((Semantics.fnsNoExs_withHooks _ _).mpr noExs) (Semantics.rightHeld_withHooks rightHeld H noRaw)
    fnOvl_none callOrder (fun g hg => by
      rw [Semantics.preRankObligationsFP_withHooks, term_named] at hg; cases hg)

/-- **`f` is total under every H** (`totalOKFP`). -/
theorem total_fH (H : HookParams) : Total (cH H) fS :=
  total_of_totalOKPreFP (c := cH H) (fn := fF) (coreOKH H) ((Semantics.fnsNoExs_withHooks _ _).mpr noExs)
    fnOvl_none (terminatesH H) fF_mem
    ((Semantics.rightHeld_withHooks rightHeld H noRaw).heldFn fF_mem)
    (show c.totalOKFP fF = true from total_f.1)
    (fun g hg => by
      have : g ∈ c.totalBefore fF := hg
      rw [total_f.2] at this
      cases this)

/-- An argument list of `h`'s sorts is one Int. -/
theorem args_one (H : HookParams) {vs : List GroundTerm} (h : (cH H).sortsOf vs = some [Srt.int]) :
    ∃ v, vs = [v] ∧ (cH H).sortOf v = some Srt.int := by
  cases vs with
  | nil => simp [Semantics.sortsOf] at h
  | cons v t =>
    obtain ⟨hv, ht⟩ := sortsOf_eq_cons.mp h
    cases t with
    | nil => exact ⟨v, rfl, hv⟩
    | cons u t' =>
      obtain ⟨_, _, _, _, he⟩ := sortsOf_cons.mp ht
      cases he

/-- **`h` has a value at every Int, under every H**, its three clauses having a predicate: `f(v)`
has a value `w`, so the predicate `⌈f(X)⌉` of `h(X) = f(X)` is true at `X := v`; no clause has a
smaller priority; the result is `w`. The predicates cover by evaluation, not by the patterns. -/
theorem total_hH (H : HookParams) : Total (cH H) hS := by
  intro fn hfn vs hvs
  rw [lookupHH H] at hfn
  cases hfn
  obtain ⟨v, rfl, hv⟩ := args_one H hvs
  obtain ⟨w, hw⟩ := total_fH H fF (lookupFH H) [v] hvs
  have hcall : EvalTerm (cH H) [(0, v)] (.app fS [.var 0]) (some w) :=
    .call (vs := [v]) syms.1 syms.2.1 (.cons .var .nil) rfl hw syms.2.2
  refine ⟨w, .clause (cl := clB) (σ := [(0, v)]) (lookupHH H) (by simp [hF]) (fun i s hs => ?_)
    (.cons (.var (lookup_cons_self _ _ _)) .nil) (fun _ ht => by cases ht) (Holds.ceil hcall)
    (fun cl' hcl' _ hlt => ?_) rfl hcall (fun _ ht => by cases ht) .top⟩
  · match i, hs with
    | 0, hs =>
      cases (show some Srt.int = some s from hs)
      exact ⟨v, rfl, hv⟩
    | i + 1, hs => simp [clB] at hs
  · simp only [hF, List.mem_cons, List.not_mem_nil, or_false] at hcl'
    rcases hcl' with rfl | rfl | rfl <;> exact absurd hlt (by decide)

end KCore.FnHypPreTotal.OrTotal

#check @KCore.FnHypPreTotal.ReqNot.fnHypH
#check @KCore.FnHypPreTotal.ReqNot.consistent
#check @KCore.FnHypPreTotal.ReqNot.totalsH
#check @KCore.FnHypPreTotal.ReqAndApp.fnHypH
#check @KCore.FnHypPreTotal.ReqAndApp.consistent
#check @KCore.FnHypPreTotal.ReqAndApp.totalsH
#check @KCore.FnHypPreTotal.OrTotal.total_hH

/-- info: 'KCore.FnHypPreTotal.ReqNot.fnHypH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.FnHypPreTotal.ReqNot.fnHypH
/-- info: 'KCore.FnHypPreTotal.ReqNot.consistent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.FnHypPreTotal.ReqNot.consistent
/-- info: 'KCore.FnHypPreTotal.ReqAndApp.fnHypH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.FnHypPreTotal.ReqAndApp.fnHypH
/-- info: 'KCore.FnHypPreTotal.ReqAndApp.consistent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.FnHypPreTotal.ReqAndApp.consistent
/-- info: 'KCore.FnHypPreTotal.OrTotal.total_hH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.FnHypPreTotal.OrTotal.total_hH
