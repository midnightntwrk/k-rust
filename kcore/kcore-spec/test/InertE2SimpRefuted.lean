/-
  Two simplification sentences of fixture e2-simplification that are not inert: with `f(X) => X` and
  `sl(X) => X` the equations of `f` and `sl`,
  - axiom 170, `rule f(X) -Int 1 => X [simplification, non-executable]`: at X = -1 its left side is
    -2 and its right side -1;
  - axiom 178, `rule sl(X) >=Int 0 => true [simplification, smt-lemma]`: at X = -1 its left side is
    `false` and its right side `true`.
  Each fails, in every model of Γ and for every H, at the valuation that sends X to the element of
  -1, so Γ with it has no model (`s170_refuted`, `s178_refuted`), from `eqn1_fails`: a one-variable
  equation without `requires` whose two sides have distinct values at a value of the variable fails
  there.
  The text is `f2-examples/e2-simplification.kompile.kore`: the kompiled text that
  `test/constructs/fixtures/e2-simplification/kompile.txt` records, with its paths restored.
  Run from the package root: `lake env lean -j1 test/InertE2SimpRefuted.lean`. Every statement is on
  the literal `defn`, for every interpretation H; nothing reads `Parse.parse` or `emit`.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.InertE2SimpRefuted

open KCore ML Faithful KoreAML

/-- **A one-variable equation without `requires` whose sides have distinct values at a value `v`
of the variable fails there**, in every model of `Γ c'`: at the valuation sending the variable to
`v`'s element and `R` to the sort of Bool. -/
theorem eqn1_fails {c' : Semantics} (h : c'.coreOK = true) (hok : c'.ok = true) {F : InertEvUser.ValTable}
    (hF : InertEvUser.TableOK c' F) (E : LibEv.Eqn) (hreq : E.req = none) (S : Srt) (hv1 : E.vars.length = 1)
    (hvS : E.vars[0]? = some ((E.vars.getD 0 ("", 0)).1, S)) (hSn : S < nRegSorts) (hEn : E.s < nRegSorts)
    (hdist : (distinctSorts c').contains E.s = true) (v vL vR : GroundTerm) (hsv : c'.sortOf v = some S)
    (htl : InertEvUser.srtU? c' F E.vars E.lhs = some E.s) (htr : InertEvUser.srtU? c' F E.vars E.rhs = some E.s)
    (hL : InertEvUser.valU c' F [(0, v)] E.lhs = some vL) (hR : InertEvUser.valU c' F [(0, v)] E.rhs = some vR)
    (hne : vL ≠ vR) (hvL : c'.sortOf vL = some E.s) (hvR : c'.sortOf vR = some E.s) (ad : AxiomDecl) (hp : ad.ax.pattern = E.pattern c') (hsvs : ad.ax.sortVars = [Rv])
    (hfree : (ad.ax.sortVars.map KoreAML.sortVarKey ++ KoreAML.freeOf [] ad.ax.pattern).eraseDups =
      [.sortVar "R", LibEv.vkey c' E.vars 0])
    (hne' : (KoreAML.tableOf ad.ax.sortVars ad.ax.pattern).ev (.sortVar "R") ≠
      (KoreAML.tableOf ad.ax.sortVars ad.ax.pattern).ev (LibEv.vkey c' E.vars 0))
    {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hI : I ⊧ᴵP Γ c') :
    ∃ e : Valuation M, AtValues c' I e ad.ax ∧ ¬ (trAxiom [] [] ad).pat.interpret I e default := by
  haveI : OvlOK c' := ovlOK_of_core h
  have hD := defOK hI
  have hc := sat_sigItem hI (sig_ceilDef (c := c'))
  have hnum : ∀ {s : Srt}, s < nRegSorts → s < nRegSorts + c'.sortNames.length :=
    fun hs => Nat.lt_of_lt_of_le hs (Nat.le_add_right _ _)
  obtain ⟨τ, hτsort, hτ⟩ := srt_den hI (hnum hEn)
  obtain ⟨τS, hτSsort, hτS⟩ := srt_den hI (hnum hSn)
  have hσ : ∀ i p, E.vars[i]? = some p → ∃ w, ([(0, v)] : Subst).lookup i = some w ∧ c'.sortOf w = some p.2 := by
    intro i p hp'
    have hi : i < 1 := hv1 ▸ (List.getElem?_eq_some_iff.mp hp').1
    match i, hi with
    | 0, _ => rw [hvS] at hp'; cases hp'; exact ⟨v, rfl, hsv⟩
  let T := KoreAML.tableOf ad.ax.sortVars ad.ax.pattern
  let mv : M := elemOf c' I v
  let mL : M := elemOf c' I vL
  let e : Valuation M := ⟨fun x => if x = T.ev (LibEv.vkey c' E.vars 0) then mv else τ, fun _ _ => False⟩
  have heX : e.evalEvar (T.ev (LibEv.vkey c' E.vars 0)) = mv := by simp [e]
  have heR : e.evalEvar (T.ev (.sortVar "R")) = τ := by
    show (if T.ev (.sortVar "R") = T.ev (LibEv.vkey c' E.vars 0) then mv else τ) = τ
    rw [if_neg hne']
  obtain ⟨hva, hvb⟩ := elemOf_spec hI hsv e
  obtain ⟨hLa, hLb⟩ := elemOf_spec hI hvL e
  have hinhL : KoreAML.Inh I τ mL := by
    refine (KoreAML.interp_inhOf_of (fun a' => ?_)).mp hLb
    have := hτ T e a'
    rwa [trSort_srtOf_twoT] at this
  have hinhv : KoreAML.Inh I τS mv := by
    refine (KoreAML.interp_inhOf_of (fun a' => ?_)).mp hvb
    have := hτS T e a'
    rwa [trSort_srtOf_twoT] at this
  have hkey : LibEv.vkey c' E.vars 0 = .evar (E.vars.getD 0 ("", 0)).1 (srtOf c' S) := by
    unfold LibEv.vkey; rw [List.getD_eq_getElem?_getD, hvS]; rfl
  refine ⟨e, ?_, fun hax => ?_⟩
  · intro n s hk
    have hk' : KoreAML.VarKey.evar n s ∈ [KoreAML.VarKey.sortVar "R", LibEv.vkey c' E.vars 0] := by
      rw [← hfree]; exact List.mem_eraseDups.mpr (List.mem_append_right _ (List.mem_eraseDups.mp hk))
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk'
    rcases hk' with hk' | hk'
    · cases hk'
    · rw [hkey] at hk'
      injection hk' with hn hs
      subst hn hs
      refine ⟨v, S, rfl, hsv, (hva _).mpr ?_⟩
      rw [← hkey]; exact heX
  · obtain ⟨hRa, -⟩ := elemOf_spec hI hvR e
    have hinhLR : KoreAML.Inh I (e.evalEvar (T.ev (.sortVar "R"))) mL := by rw [heR]; exact hinhL
    unfold KoreAML.trAxiom at hax
    dsimp only at hax
    rw [hfree] at hax
    have heX' : e.evalEvar ((KoreAML.tableOf ad.ax.sortVars ad.ax.pattern).ev (LibEv.vkey c' E.vars 0)) = mv := heX
    have heR' : e.evalEvar ((KoreAML.tableOf ad.ax.sortVars ad.ax.pattern).ev (.sortVar "R")) = τ := heR
    have hinhR' : KoreAML.Inh I (e.evalEvar ((KoreAML.tableOf ad.ax.sortVars ad.ax.pattern).ev (.sortVar "R"))) mL :=
      hinhLR
    clear_value e
    generalize htb : KoreAML.tableOf ad.ax.sortVars ad.ax.pattern = t at hax heX' heR' hinhR'
    have hRv : ∀ b, (KoreAML.trSort t KoreAML.R).interpret I e b ↔ b = e.evalEvar (t.ev (.sortVar "R")) :=
      fun b => by rw [trSort_R, KoreAML.interp_evar]
    have hRs : KoreAML.IsSort I (e.evalEvar (t.ev (.sortVar "R"))) := by rw [heR']; exact hτsort
    rw [interpret_impl] at hax
    have hg := hax (KoreAML.interp_conjList fun w hw => by
      obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl
      · exact (KoreAML.interp_guard_sortVar hD).mpr hRs
      · rw [hkey]
        unfold KoreAML.guardOf
        rw [KoreAML.interp_member hD]
        have hX : e.evalEvar (t.ev (.evar (E.vars.getD 0 ("", 0)).1 (srtOf c' S))) = mv := by rw [← hkey]; exact heX'
        rw [hX]
        exact (KoreAML.interp_inhOf_of (hτS t e)).mpr hinhv)
    rw [hp] at hg
    unfold LibEv.Eqn.pattern LibEv.Eqn.premise at hg
    rw [hreq] at hg
    simp only [KoreAML.sortOf] at hg
    rw [KoreAML.interp_equal hD] at hg
    have hA := (hg mL).mpr ((KoreAML.interp_inhOf_of hRv).mpr hinhR')
    rw [KoreAML.tr] at hA
    dsimp only at hA
    rw [KoreAML.interp_sImp] at hA
    have hEQ := hA.2 (by
      rw [KoreAML.tr]
      dsimp only
      rw [KoreAML.interp_sTop hD (InertEv.trSort_topFresh t _)]
      exact (KoreAML.interp_inhOf_of hRv).mpr hinhR')
    rw [KoreAML.tr] at hEQ
    dsimp only at hEQ
    rw [KoreAML.interp_sEquals hD hc (hτ t e) hRv hτsort hRs] at hEQ
    have hag : ∀ i w, i < E.vars.length → ([(0, v)] : Subst).lookup i = some w →
        ∀ m, m = e.evalEvar (t.ev (LibEv.vkey c' E.vars i)) ↔ (den c' w).interpret I e m := by
      intro i w hi hw m
      have hi1 : i < 1 := hv1 ▸ hi
      match i, hi1 with
      | 0, _ =>
        cases hw
        rw [heX']
        exact (hva m).symm
    have hDL := (InertEvUser.den_valU (tbl := t) (e := e) h hok hF hI hσ hag (Semantics.preTop_of_okAll (Semantics.okAll_of_ok hok)) E.lhs htl).1 mL
    have hDR := (InertEvUser.den_valU (tbl := t) (e := e) h hok hF hI hσ hag (Semantics.preTop_of_okAll (Semantics.okAll_of_ok hok)) E.rhs htr).1 mL
    rw [hL] at hDL
    rw [hR] at hDR
    have hRHS := (hEQ.2 mL hinhL).mp (hDL.mpr ((hLa _).mpr rfl))
    have hAnd : (KoreAML.sAnd (KoreAML.tr ⟨t, []⟩ (LibEv.kore c' E.vars E.rhs))
        (KoreAML.tr ⟨t, []⟩ (.top (srtOf c' E.s)))).interpret I e mL := hRHS
    have hr := hDR.mp (KoreAML.interp_sAnd.mp hAnd).1
    exact dom_apart hI hdist hvL hvR hne e mL ⟨(hLa _).mpr rfl, hr⟩

kore_term kore from "f2-examples/e2-simplification.kompile.kore"
definition_of defn from "f2-examples/e2-simplification.kompile.kore"
user_axioms U from "f2-examples/e2-simplification.kompile.kore" module "E2-SIMPLIFICATION"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

/-- `tr s`: the item `Theory.ofDefinition kore` holds for the sentence. -/
noncomputable def trS (ad : AxiomDecl) : Item := trAxiom kore.symbolDecls kore.aliasNames ad

theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel
theorem coreOK : c.coreOK = true := by decide_cheap
theorem coreOKH (H : HookParams) : (cH H).coreOK = true := (Semantics.coreOK_withHooks c H).trans coreOK
theorem hok : c.ok = true := by decide +kernel
theorem hokH (H : HookParams) : (cH H).ok = true := (Semantics.ok_withHooks c H).trans hok
theorem shapesOK_c : c.shapesOK = true := by decide +kernel

def f : Sym := 384

theorem names : c.symName f = "Lblf" := by decide +kernel

noncomputable abbrev fn : Fn := c.fns[0]'(by decide +kernel)

theorem hfn : c.lookupFn f = some fn := rfl
theorem hfnH (H : HookParams) : (cH H).lookupFn f = some fn := by rw [Semantics.lookupFn_withHooks]; exact hfn
theorem fn_args : fn.args = [Srt.int] := by decide +kernel
theorem hkf : lookupSig hookSigs f = none := by decide +kernel

/-! ## `f`'s value at every integer -/

/-- `f`'s one clause: `f(X) => X`. -/
noncomputable abbrev cl0 : Clause := fn.clauses[0]'(by decide +kernel)

theorem cl0_vars : cl0.vars = [Srt.int] := by decide +kernel
theorem cl0_pats : cl0.pats = [.var 0] := rfl
theorem cl0_req : cl0.req = none := rfl
theorem cl0_rhs : cl0.rhs = .var 0 := rfl
theorem cl0_pre : cl0.pre = .top := rfl
theorem cl0_ens : cl0.ens = none := rfl
theorem cl0_least : fn.clauses.all (fun cl' => !decide (cl'.prio < cl0.prio)) = true := by decide +kernel

/-- **`f(n) = n` at every integer n, for every H**: the clause matches and has no condition. -/
theorem eval_all (H : HookParams) (n : Int) : Eval (cH H) f [int n] (some (int n)) := by
  have hσ : (cH H).WellSorted cl0.vars [(0, int n)] := by
    intro i s hi
    rw [cl0_vars] at hi
    match i, hi with
    | 0, hi => cases hi; exact ⟨int n, rfl, rfl⟩
    | k + 1, hi => simp at hi
  have hm : PatVals (cH H) [(0, int n)] cl0.pats [int n] := by
    rw [cl0_pats]; exact .cons (.var rfl) .nil
  have hr : EvalTerm (cH H) [(0, int n)] cl0.rhs (some (int n)) := by
    rw [cl0_rhs]; exact .var
  exact .clause (cl := cl0) (σ := [(0, int n)]) (hfnH H) (List.getElem_mem _) hσ hm
    (fun t ht => by rw [cl0_req] at ht; cases ht) (by rw [cl0_pre]; exact .top)
    (fun cl' hcl' _ hlt => absurd hlt (by simpa using List.all_eq_true.mp cl0_least cl' hcl')) (by rfl) hr
    (fun t ht => by rw [cl0_ens] at ht; cases ht) (Clause.holds_postTop (by rfl) _)

/-- The value table of `f`: `f(n) = n`. -/
def fTable : InertEvUser.ValTable := fun s =>
  if s = f then some fun ws => match ws with
    | [.dv _ (.int n)] => some (int n)
    | _ => none
  else none

/-- **The table is `Eval`'s**, for every H. -/
theorem table_ok (H : HookParams) : InertEvUser.TableOK (cH H) fTable := by
  intro s g fn' ws hg _ hfn' hws
  by_cases hs : s = f
  · subst hs
    simp only [fTable, ite_true, Option.some.injEq] at hg
    subst hg
    have he : fn' = fn := Option.some.inj (hfn'.symm.trans (hfnH H))
    subst he
    rw [fn_args, Semantics.sortsOf_withHooks _ _ noRaw] at hws
    obtain ⟨w, ws', rfl, hw, hws'⟩ := sortsOf_inv_cons hws
    cases sortsOf_inv_nil hws'
    obtain ⟨n, rfl⟩ := shape_int shapesOK_c hw
    exact eval_all H n
  · simp [fTable, hs] at hg



def sl : Sym := 386

theorem namesS : c.symName sl = "Lblsl" := by decide +kernel

noncomputable abbrev fnS : Fn := c.fns[2]'(by decide +kernel)

theorem hfnS : c.lookupFn sl = some fnS := rfl
theorem hfnHS (H : HookParams) : (cH H).lookupFn sl = some fnS := by rw [Semantics.lookupFn_withHooks]; exact hfnS
theorem fn_argsS : fnS.args = [Srt.int] := by decide +kernel
theorem hkfS : lookupSig hookSigs sl = none := by decide +kernel

/-! ## `sl`'s value at every integer -/

/-- `sl`'s one clause: `sl(X) => X`. -/
noncomputable abbrev clS : Clause := fnS.clauses[0]'(by decide +kernel)

theorem clS_vars : clS.vars = [Srt.int] := by decide +kernel
theorem clS_pats : clS.pats = [.var 0] := rfl
theorem clS_req : clS.req = none := rfl
theorem clS_rhs : clS.rhs = .var 0 := rfl
theorem clS_pre : clS.pre = .top := rfl
theorem clS_ens : clS.ens = none := rfl
theorem clS_least : fnS.clauses.all (fun cl' => !decide (cl'.prio < clS.prio)) = true := by decide +kernel

/-- **`sl(n) = n` at every integer n, for every H**: the clause matches and has no condition. -/
theorem eval_allS (H : HookParams) (n : Int) : Eval (cH H) sl [int n] (some (int n)) := by
  have hσ : (cH H).WellSorted clS.vars [(0, int n)] := by
    intro i s hi
    rw [clS_vars] at hi
    match i, hi with
    | 0, hi => cases hi; exact ⟨int n, rfl, rfl⟩
    | k + 1, hi => simp at hi
  have hm : PatVals (cH H) [(0, int n)] clS.pats [int n] := by
    rw [clS_pats]; exact .cons (.var rfl) .nil
  have hr : EvalTerm (cH H) [(0, int n)] clS.rhs (some (int n)) := by
    rw [clS_rhs]; exact .var
  exact .clause (cl := clS) (σ := [(0, int n)]) (hfnHS H) (List.getElem_mem _) hσ hm
    (fun t ht => by rw [clS_req] at ht; cases ht) (by rw [clS_pre]; exact .top)
    (fun cl' hcl' _ hlt => absurd hlt (by simpa using List.all_eq_true.mp clS_least cl' hcl')) (by rfl) hr
    (fun t ht => by rw [clS_ens] at ht; cases ht) (Clause.holds_postTop (by rfl) _)

/-- The value table of `sl`: `sl(n) = n`. -/
def slTable : InertEvUser.ValTable := fun s =>
  if s = sl then some fun ws => match ws with
    | [.dv _ (.int n)] => some (int n)
    | _ => none
  else none

/-- **The table is `Eval`'s**, for every H. -/
theorem table_okS (H : HookParams) : InertEvUser.TableOK (cH H) slTable := by
  intro s g fnS' ws hg _ hfnS' hws
  by_cases hs : s = sl
  · subst hs
    simp only [slTable, ite_true, Option.some.injEq] at hg
    subst hg
    have he : fnS' = fnS := Option.some.inj (hfnS'.symm.trans (hfnHS H))
    subst he
    rw [fn_argsS, Semantics.sortsOf_withHooks _ _ noRaw] at hws
    obtain ⟨w, ws', rfl, hw, hws'⟩ := sortsOf_inv_cons hws
    cases sortsOf_inv_nil hws'
    obtain ⟨n, rfl⟩ := shape_int shapesOK_c hw
    exact eval_allS H n
  · simp [slTable, hs] at hg



/-! ## The two sentences -/

/-- `f(X) -Int 1 => X`. -/
def E170 : LibEv.Eqn := ⟨[("VarX", Srt.int)], Srt.int, none, .app intSub [.app f [.var 0], .dv Srt.int (.int 1)], .var 0⟩
/-- `sl(X) >=Int 0 => true`. -/
def E178 : LibEv.Eqn :=
  ⟨[("VarX", Srt.int)], Srt.bool, none, .app intGe [.app sl [.var 0], .dv Srt.int (.int 0)], .dv Srt.bool (.bool true)⟩

/-- The reader's class of the two sentences. -/
theorem simp_class : [U.ax170, U.ax178].map (fun ad => Parse.classify (.axiom ad.ax)) =
    [.inert .simplification, .inert .simplification] := by decide +kernel

theorem text170 : U.ax170.ax.pattern = E170.pattern c ∧ U.ax170.ax.sortVars = [Rv] ∧
    (trS U.ax170).pat = (trAxiom [] [] U.ax170).pat ∧
    (U.ax170.ax.sortVars.map KoreAML.sortVarKey ++ KoreAML.freeOf [] U.ax170.ax.pattern).eraseDups =
      [.sortVar "R", LibEv.vkey c E170.vars 0] ∧
    (KoreAML.tableOf U.ax170.ax.sortVars U.ax170.ax.pattern).ev (.sortVar "R") ≠
      (KoreAML.tableOf U.ax170.ax.sortVars U.ax170.ax.pattern).ev (LibEv.vkey c E170.vars 0) := by
  decide +kernel
theorem text178 : U.ax178.ax.pattern = E178.pattern c ∧ U.ax178.ax.sortVars = [Rv] ∧
    (trS U.ax178).pat = (trAxiom [] [] U.ax178).pat ∧
    (U.ax178.ax.sortVars.map KoreAML.sortVarKey ++ KoreAML.freeOf [] U.ax178.ax.pattern).eraseDups =
      [.sortVar "R", LibEv.vkey c E178.vars 0] ∧
    (KoreAML.tableOf U.ax178.ax.sortVars U.ax178.ax.pattern).ev (.sortVar "R") ≠
      (KoreAML.tableOf U.ax178.ax.sortVars U.ax178.ax.pattern).ev (LibEv.vkey c E178.vars 0) := by
  decide +kernel

kernel_rfl pattern170_wh : ∀ H : HookParams, E170.pattern (cH H) = E170.pattern c
kernel_rfl pattern178_wh : ∀ H : HookParams, E178.pattern (cH H) = E178.pattern c
kernel_rfl vkey170_wh : ∀ H : HookParams, LibEv.vkey (cH H) E170.vars 0 = LibEv.vkey c E170.vars 0
kernel_rfl vkey178_wh : ∀ H : HookParams, LibEv.vkey (cH H) E178.vars 0 = LibEv.vkey c E178.vars 0

theorem typed170 : InertEvUser.srtU? c fTable E170.vars E170.lhs = some Srt.int ∧
    InertEvUser.srtU? c fTable E170.vars E170.rhs = some Srt.int := by decide +kernel
theorem typed178 : InertEvUser.srtU? c slTable E178.vars E178.lhs = some Srt.bool ∧
    InertEvUser.srtU? c slTable E178.vars E178.rhs = some Srt.bool := by decide +kernel
kernel_rfl t170l_wh : ∀ H : HookParams, InertEvUser.srtU? (cH H) fTable E170.vars E170.lhs = InertEvUser.srtU? c fTable E170.vars E170.lhs
kernel_rfl t170r_wh : ∀ H : HookParams, InertEvUser.srtU? (cH H) fTable E170.vars E170.rhs = InertEvUser.srtU? c fTable E170.vars E170.rhs
kernel_rfl t178l_wh : ∀ H : HookParams, InertEvUser.srtU? (cH H) slTable E178.vars E178.lhs = InertEvUser.srtU? c slTable E178.vars E178.lhs
kernel_rfl t178r_wh : ∀ H : HookParams, InertEvUser.srtU? (cH H) slTable E178.vars E178.rhs = InertEvUser.srtU? c slTable E178.vars E178.rhs

theorem distInt (H : HookParams) : (distinctSorts (cH H)).contains Srt.int = true := by
  rw [show distinctSorts (cH H) = distinctSorts c from rfl]; decide +kernel
theorem distBool (H : HookParams) : (distinctSorts (cH H)).contains Srt.bool = true := by
  rw [show distinctSorts (cH H) = distinctSorts c from rfl]; decide +kernel

theorem hkSub : lookupSig hookSigs intSub = some ⟨intSub, [Srt.int, Srt.int], Srt.int⟩ := by decide +kernel
theorem hkGe : lookupSig hookSigs intGe = some ⟨intGe, [Srt.int, Srt.int], Srt.bool⟩ := by decide +kernel
theorem appU_f (H : HookParams) : InertEvUser.appU (cH H) fTable f = fun ws => match ws with
    | [.dv _ (.int n)] => some (int n)
    | _ => none := InertEvUser.appU_fn hkf (by simp [fTable])
theorem appU_sl (H : HookParams) : InertEvUser.appU (cH H) slTable sl = fun ws => match ws with
    | [.dv _ (.int n)] => some (int n)
    | _ => none := InertEvUser.appU_fn hkfS (by simp [slTable])

theorem val170 (H : HookParams) : InertEvUser.valU (cH H) fTable [(0, int (-1))] E170.lhs = some (int (-2)) ∧
    InertEvUser.valU (cH H) fTable [(0, int (-1))] E170.rhs = some (int (-1)) := by
  constructor
  · simp only [E170, InertEvUser.valU, InertEvUser.valUList, allSome, appU_f, InertEvUser.appU_hook hkSub]
    exact hv_of_value rfl
  · rfl
theorem val178 (H : HookParams) : InertEvUser.valU (cH H) slTable [(0, int (-1))] E178.lhs = some (bool false) ∧
    InertEvUser.valU (cH H) slTable [(0, int (-1))] E178.rhs = some (bool true) := by
  constructor
  · simp only [E178, InertEvUser.valU, InertEvUser.valUList, allSome, appU_sl, InertEvUser.appU_hook hkGe]
    exact hv_of_value rfl
  · rfl

/-- **Sentence 170 fails at X = -1 in every model of Γ, for every H**, and Γ with it has no model. -/
theorem s170_refuted (H : HookParams) : ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M),
    I ⊧ᴵP Γ (cH H) → ¬ (I ⊧ᴵ (trS U.ax170).pat) := by
  intro M _ I hI hax
  obtain ⟨hp, hsv, htr, hfr, hne⟩ := text170
  obtain ⟨hl, hr⟩ := typed170
  obtain ⟨e, -, hn⟩ := eqn1_fails (coreOKH H) (hokH H) (table_ok H) E170 rfl Srt.int rfl rfl (by decide) (by decide)
    (distInt H) (int (-1)) (int (-2)) (int (-1)) rfl ((t170l_wh H).trans hl) ((t170r_wh H).trans hr)
    (val170 H).1 (val170 H).2 (by decide) rfl rfl U.ax170 (hp.trans (pattern170_wh H).symm) hsv
    (by rw [hfr, vkey170_wh]) (by rw [vkey170_wh]; exact hne) hI
  exact hn (htr ▸ hax e default)

/-- **Sentence 178 fails at X = -1 in every model of Γ, for every H**, and Γ with it has no model. -/
theorem s178_refuted (H : HookParams) : ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M),
    I ⊧ᴵP Γ (cH H) → ¬ (I ⊧ᴵ (trS U.ax178).pat) := by
  intro M _ I hI hax
  obtain ⟨hp, hsv, htr, hfr, hne⟩ := text178
  obtain ⟨hl, hr⟩ := typed178
  obtain ⟨e, -, hn⟩ := eqn1_fails (coreOKH H) (hokH H) (table_okS H) E178 rfl Srt.int rfl rfl (by decide) (by decide)
    (distBool H) (int (-1)) (bool false) (bool true) rfl ((t178l_wh H).trans hl) ((t178r_wh H).trans hr)
    (val178 H).1 (val178 H).2 (by decide) (rmS_sortOf_bool _ false) (rmS_sortOf_bool _ true) U.ax178
    (hp.trans (pattern178_wh H).symm) hsv (by rw [hfr, vkey178_wh]) (by rw [vkey178_wh]; exact hne) hI
  exact hn (htr ▸ hax e default)

end KCore.InertE2SimpRefuted

#check @KCore.InertE2SimpRefuted.eqn1_fails
#check @KCore.InertE2SimpRefuted.s170_refuted
#check @KCore.InertE2SimpRefuted.s178_refuted
#print axioms KCore.InertE2SimpRefuted.simp_class
#print axioms KCore.InertE2SimpRefuted.s170_refuted
#print axioms KCore.InertE2SimpRefuted.s178_refuted
