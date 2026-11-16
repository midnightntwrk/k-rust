/-
  Totality through parameter symbols (ParamsTotal.lean) on a small core. Checked by
      lean test/ParamsTotal.lean   (LEAN_PATH from `lake env`)

  `Fp(X) = P(X)` declared `[total]`, P a parameter symbol `Int → Int` no registry hook implements,
  and `Fq(X) = Q(X)` declared `[total]`, Q such a parameter too.
  - `totalOKR` names both (`pt_R`); `totalOKP` with P taken total names only Fq (`pt_P`), and with
    no parameter taken total names both.
  - Under every interpretation total on P, Fp is total, nothing assumed of Q (`pt_Fp_total`; every
    function terminating and evaluation functional, as `totals_of_rankP` reads).
  - **Why the hypothesis**: under `HookParams.none` (the parsed data's interpretation) Fp has no
    value at 0 (`pt_Fp_not_total`), so the statement for that interpretation alone would be false.
-/
import KcoreSpec.FnObligations

set_option autoImplicit false

namespace KCore.ParamsTotalTest

open KCore

def cellSorts : List Srt := [Srt.top, Srt.topFrag, nRegSorts, nRegSorts + 1, Srt.counter, Srt.counterOpt]
def cellCtors : List CtorSig :=
  [⟨topLabel, [nRegSorts, Srt.counter], Srt.top⟩, ⟨topFragLabel, [nRegSorts + 1, Srt.counterOpt], Srt.topFrag⟩,
   ⟨nRegSyms + 50, [Srt.k], nRegSorts⟩, ⟨nRegSyms + 51, [], nRegSorts + 1⟩,
   ⟨counterLabel, [Srt.int], Srt.counter⟩, ⟨noCounter, [], Srt.counterOpt⟩]
def cellSubsorts : List (Srt × Srt) := [(nRegSorts, nRegSorts + 1), (Srt.counter, Srt.counterOpt)]

def Fp : Sym := nRegSyms + 130
def Fq : Sym := nRegSyms + 131
def P : Sym := nRegSyms + 132
def Q : Sym := nRegSyms + 133

def fnFp : Fn := ⟨Fp, [Srt.int], Srt.int, [⟨[Srt.int], [.var 0], none, .app P [.var 0], none, 50, false, [], .top, .top⟩], true⟩
def fnFq : Fn := ⟨Fq, [Srt.int], Srt.int, [⟨[Srt.int], [.var 0], none, .app Q [.var 0], none, 50, false, [], .top, .top⟩], true⟩

def pt : Semantics where
  lib := { sortsBelowKItem := [Srt.map, Srt.list, Srt.int, Srt.bool] }
  sortNames := []
  symNames := []
  userSorts := cellSorts
  ctors := cellCtors
  fns := [fnFp, fnFq]
  userSubsorts := cellSubsorts
  pgmSort := Srt.k
  rules := []
  params := [{ sig := ⟨P, [Srt.int], Srt.int⟩ }, { sig := ⟨Q, [Srt.int], Srt.int⟩ }]

theorem pt_sorted : pt.sortedOK = true ∧ pt.srReady = true := by decide +kernel

theorem pt_R : pt.totalObligationsR [Fp, Fq] = [Fp, Fq] := by decide +kernel

theorem pt_P : pt.totalObligationsRP [Fp, Fq] [P] = [Fq] ∧ pt.totalObligationsRP [Fp, Fq] [] = [Fp, Fq] := by
  decide +kernel

theorem pt_lookup : pt.lookupFn Fp = some fnFp := by rfl

/-- Under every interpretation total on P, Fp is total; Fq's totality is the named fact. -/
theorem pt_Fp_total (H : HookParams) (hH : ParamsTotal pt [P] H)
    (hterm : ∀ g, Terminates (pt.withHooks H) g) (hco : CoherentAll (pt.withHooks H))
    (hq : Total (pt.withHooks H) Fq) : Total (pt.withHooks H) Fp :=
  totals_of_rankP (c := pt.withHooks H) pt_sorted.1 pt_sorted.2
    (Semantics.ovlCase_withHooks (Semantics.ovlCase_of (by decide +kernel)) H)
    (Semantics.rightHeld_withHooks (c := pt) (Semantics.rightHeld_of_valued (by decide +kernel)) H (by decide +kernel)) hterm hco [Fp, Fq] [P]
    (hH.withHooks (by decide +kernel))
    (fun g hg => by
      rw [Semantics.totalObligationsRP_withHooks, pt_P.1] at hg
      simp only [List.mem_singleton] at hg; subst hg; exact hq) Fp fnFp pt_lookup rfl

theorem pt_isCtor : pt.isCtor P = false ∧ isHook P = false ∧ pt.isParam P = true := by decide +kernel

/-- **Under `HookParams.none`, Fp has no value at 0.** -/
theorem pt_Fp_not_total : ¬ Total pt Fp := by
  intro h
  have hl := pt_lookup
  obtain ⟨v, hv⟩ := h fnFp hl [.dv Srt.int (.int 0)] (by decide +kernel)
  cases hv with
  | clause hfn hmem hσ hm hreq hprio hrhs =>
    rw [hl] at hfn; cases hfn
    simp only [fnFp, List.mem_singleton] at hmem
    subst hmem
    obtain ⟨rs, hts, hr⟩ := EvalTerm.param_inv pt_isCtor.1 pt_isCtor.2.1 pt_isCtor.2.2 hrhs
    cases rs with
    | nil => cases hts
    | cons r rs =>
      cases rs with
      | cons _ _ => cases hts with | cons _ h => cases h
      | nil =>
        cases r with
        | none => simp [allSome] at hr
        | some w =>
          have : pt.paramVal P [w] = none := by
            unfold Semantics.paramVal
            rw [show pt.lookupParam P = some { sig := ⟨P, [Srt.int], Srt.int⟩ } by decide +kernel]
            rfl
          simp [allSome, this] at hr

/-- Neither parameter is an open generator: the open generators' totality holds at every
interpretation (`openTotal_of_plain`). -/
theorem pt_openTotal (H : HookParams) : OpenTotal (pt.withHooks H) :=
  openTotal_of_plain (c := pt.withHooks H) (show ∀ k ∈ pt.params, k.raw = false by decide +kernel)

/-! `paramVal` at an open generator (`raw`): the interpretation's answer where it gives one, the raw
application `P(1)` where it gives none, each kept only where it has P's result sort. `sortOf` gives
the raw application no sort (it has no open-generator arm), so under `HookParams.none` the value is
none; an answer of sort Int is kept and an ill-sorted one is not. -/
def ptRaw : Semantics := { pt with params := [{ sig := ⟨P, [Srt.int], Srt.int⟩, raw := true }] }
def H5 : HookParams := ⟨fun f _ => if f == P then some (int 5) else none⟩
def Hb : HookParams := ⟨fun f _ => if f == P then some (bool true) else none⟩

/-- `genWf` refuses `ptRaw`: its raw parameter's result sort Int is no constructor sort (`pt`, the
same without the parameter, passes); with result KItem, a constructor sort, it passes. -/
example : Faithful.genWf pt = true ∧ Faithful.genWf ptRaw = false ∧
    Faithful.genWf { pt with params := [{ sig := ⟨P, [Srt.int], Srt.kitem⟩, raw := true }] } = true := by
  decide +kernel

example : ((ptRaw.withHooks H5).paramVal P [int 1]).map (Exec.same (int 5)) = some true ∧
    ((ptRaw.withHooks Hb).paramVal P [int 1]).isNone = true ∧
    (ptRaw.withHooks HookParams.none).sortOf (.ctor P [int 1]) = none ∧
    ((ptRaw.withHooks HookParams.none).paramVal P [int 1]).isNone = true := by
  decide +kernel

/-- `rawFree` at `ptRaw`: the raw application `P(1)` applies the open generator, `1` and `5` do not;
`P(1)` inside a list is found. At the values that apply none, the sort is the same under every
interpretation (`sortOf_withHooks_rawFree`), though `ptRaw` has an open generator. -/
example : ptRaw.rawFree (.ctor P [int 1]) = false ∧ ptRaw.rawFree (int 5) = true ∧
    ptRaw.rawFree (.list Srt.list [int 1, .ctor P [int 1]]) = false ∧ pt.rawFree (.ctor P [int 1]) = true := by
  decide +kernel

example (H : HookParams) : (ptRaw.withHooks H).sortOf (int 5) = ptRaw.sortOf (int 5) :=
  Semantics.sortOf_withHooks_rawFree ptRaw H (by decide +kernel)

/-- At `pt`, no parameter is an open generator: the sorts are the same under every interpretation. -/
example (H : HookParams) : (pt.withHooks H).sortOf = pt.sortOf ∧ (pt.withHooks H).sortsOf = pt.sortsOf :=
  ⟨Semantics.sortOf_withHooks pt H (by decide +kernel), Semantics.sortsOf_withHooks pt H (by decide +kernel)⟩

/-! The conditions that list every way a sort gets values refuse a raw parameter of one of their
sorts, and those that need every value of a sort fixed by the data refuse every raw parameter;
`pt`, with none, passes each. -/

def rId : Rule := ⟨[Srt.int], .var 0, none, .var 0, none, 50, [], .top, .top⟩

example : pt.shapesOK = true ∧ ptRaw.shapesOK = false ∧
    pt.floatShapeOK = true ∧ ptRaw.floatShapeOK = true ∧
    { pt with params := [{ sig := ⟨P, [Srt.int], Srt.float⟩, raw := true }] }.floatShapeOK = false ∧
    pt.enumShapesOK = true ∧
    { pt with params := [{ sig := ⟨P, [], Srt.endianness⟩, raw := true }] }.enumShapesOK = false ∧
    pt.enumerable nRegSorts = true ∧ ptRaw.enumerable nRegSorts = false ∧
    NI.appOK pt [] rId = true ∧ NI.appOK ptRaw [] rId = false := by
  decide +kernel

/-- `sortOf_ctor`'s second hypothesis, decided at a closed semantics with no raw parameter. -/
example {ts : List GroundTerm} (h : pt.sortOf (.ctor counterLabel ts) = some Srt.counter) :
    pt.sortsOf ts = some [Srt.int] := by
  obtain ⟨k, hk, hks, -⟩ := (sortOf_ctor (by decide +kernel)).mp h
  rw [show lookupSig pt.ctorSigs counterLabel = some ⟨counterLabel, [Srt.int], Srt.counter⟩ by
    decide +kernel] at hk
  cases hk; exact hks

/-- `sortOf_of_T`'s `rawFree` argument, decided at a closed value; at `ptRaw` the tables give `1`
its sort. -/
example : ptRaw.sortOf (int 1) = some Srt.int := sortOf_of_T rfl (by decide +kernel)

end KCore.ParamsTotalTest

#print axioms KCore.ParamsTotalTest.pt_Fp_total
#print axioms KCore.ParamsTotalTest.pt_Fp_not_total
