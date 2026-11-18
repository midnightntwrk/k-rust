/-
  C3 'simplification x ensures' on the fixture c3-simp-ens: `rule f(X) => X [priority(40)]` beside
  `rule f(f(X)) => f(X) ensures X >=Int 0 [simplification]`. The simplification is not inert: its
  sentence (axiom 201)
  `\implies{R}(\top{R}(), \equals{SortInt{}, R}(f(f(X)), \and{SortInt{}}(f(X), \equals{SortBool{}, SortInt{}}(X >=Int 0, true))))`
  fails, in every model of Γ and for every H, at the valuation that sends X to the element of -1:
  there `f(f(X))` denotes the element of -1 (`eval_all`: `f(n) = n`), and `X >=Int 0` denotes the
  element of `false`, so the right side's conjunct `X >=Int 0 = true` holds nowhere and the right side
  is empty. Γ with the sentence has no model (`ens_refuted`).
  The text is `f2-examples/c3-simp-ens.kompile.kore`: the kompiled text that
  `test/constructs/fixtures/c3-simp-ens/kompile.txt` records, with its paths restored.
  Run from the package root: `lake env lean -j1 test/C3SimpEnsRefuted.lean`. Every statement is on
  the literal `defn`, for every interpretation H; nothing reads `Parse.parse` or `emit`.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.C3SimpEnsRefuted

open KCore ML Faithful KoreAML

kore_term kore from "f2-examples/c3-simp-ens.kompile.kore"
definition_of defn from "f2-examples/c3-simp-ens.kompile.kore"
user_axioms U from "f2-examples/c3-simp-ens.kompile.kore" module "C3-SIMP-ENS"

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

/-- `f`'s one clause: `f(X) => X [priority(40)]`. -/
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

/-! ## The sentence and its failure at X = -1 -/

/-- The sentence. -/
noncomputable abbrev ensAx : AxiomDecl := U.ax201

/-- The reader's class of the sentence. -/
theorem ens_class : Parse.classify (.axiom ensAx.ax) = .inert .simplification := by decide +kernel

def vars : LibEv.Vars := [("VarX", Srt.int)]
def tL : Term := .app f [.app f [.var 0]]
def tR : Term := .app f [.var 0]
def tG : Term := .app intGe [.var 0, .dv Srt.int (.int 0)]

/-- The sentence's pattern. -/
def ensPat (c : Semantics) : Kore.Pattern :=
  .implies KoreAML.R (.top KoreAML.R) (.equals (srtOf c Srt.int) KoreAML.R (LibEv.kore c vars tL)
    (.and (srtOf c Srt.int) [LibEv.kore c vars tR,
      .equals (srtOf c Srt.bool) (srtOf c Srt.int) (LibEv.kore c vars tG) (.dv (srtOf c Srt.bool) "true")]))

theorem ens_text : ensAx.ax.pattern = ensPat c ∧ ensAx.ax.sortVars = [Rv] ∧
    (trS ensAx).pat = (trAxiom [] [] ensAx).pat := by
  decide +kernel

theorem ens_free : (ensAx.ax.sortVars.map KoreAML.sortVarKey ++ KoreAML.freeOf [] ensAx.ax.pattern).eraseDups =
    [.sortVar "R", LibEv.vkey c vars 0] := by decide +kernel

kernel_rfl ensPat_wh : ∀ H : HookParams, ensPat (cH H) = ensPat c
kernel_rfl vkey_wh : ∀ H : HookParams, LibEv.vkey (cH H) vars 0 = LibEv.vkey c vars 0

/-- The table of the sentence's variables: R and X at distinct places. -/
noncomputable abbrev tb : KoreAML.VarTable := KoreAML.tableOf ensAx.ax.sortVars ensAx.ax.pattern
theorem tb_ne : tb.ev (.sortVar "R") ≠ tb.ev (LibEv.vkey c vars 0) := by decide +kernel

theorem typedL : InertEvUser.srtU? c fTable vars tL = some Srt.int := by decide +kernel
theorem typedR : InertEvUser.srtU? c fTable vars tR = some Srt.int := by decide +kernel
theorem typedG : InertEvUser.srtU? c fTable vars tG = some Srt.bool := by decide +kernel
kernel_rfl typedL_wh : ∀ H : HookParams, InertEvUser.srtU? (cH H) fTable vars tL = InertEvUser.srtU? c fTable vars tL
kernel_rfl typedR_wh : ∀ H : HookParams, InertEvUser.srtU? (cH H) fTable vars tR = InertEvUser.srtU? c fTable vars tR
kernel_rfl typedG_wh : ∀ H : HookParams, InertEvUser.srtU? (cH H) fTable vars tG = InertEvUser.srtU? c fTable vars tG

/-- The substitution X := -1. -/
def σ1 : Subst := [(0, int (-1))]

theorem appU_f (H : HookParams) : InertEvUser.appU (cH H) fTable f = fun ws => match ws with
    | [.dv _ (.int n)] => some (int n)
    | _ => none := InertEvUser.appU_fn hkf (by simp [fTable])
theorem hkGe : lookupSig hookSigs intGe = some ⟨intGe, [Srt.int, Srt.int], Srt.bool⟩ := by decide +kernel

theorem valL (H : HookParams) : InertEvUser.valU (cH H) fTable σ1 tL = some (int (-1)) := by
  simp only [tL, σ1, InertEvUser.valU, InertEvUser.valUList, allSome, appU_f]
  rfl
theorem valG (H : HookParams) : InertEvUser.valU (cH H) fTable σ1 tG = some (bool false) := by
  simp only [tG, σ1, InertEvUser.valU, InertEvUser.valUList, allSome, InertEvUser.appU_hook hkGe, Option.bind_some]
  exact hv_of_value rfl

/-- **The sentence fails at X = -1 in every model of Γ, for every H.** -/
theorem ens_fails (H : HookParams) (M : Type) [Inhabited M] (I : Interpretation KoreAML.Sym M)
    (hI : I ⊧ᴵP Γ (cH H)) : ∃ e : Valuation M, AtValues (cH H) I e ensAx.ax ∧
      ¬ (trS ensAx).pat.interpret I e default := by
  haveI : OvlOK (cH H) := ovlOK_of_core (coreOKH H)
  have hD := defOK hI
  have hc := sat_sigItem hI (sig_ceilDef (c := cH H))
  obtain ⟨hp, hsv, htr⟩ := ens_text
  have hnum : ∀ {s : Srt}, s < nRegSorts → s < nRegSorts + (cH H).sortNames.length :=
    fun hs => Nat.lt_of_lt_of_le hs (Nat.le_add_right _ _)
  obtain ⟨τ, hτsort, hτ⟩ := srt_den hI (hnum (show Srt.int < nRegSorts by decide))
  obtain ⟨τb, hτbsort, hτb⟩ := srt_den hI (hnum (show Srt.bool < nRegSorts by decide))
  have hS1 : (cH H).sortOf (int (-1)) = some Srt.int := rfl
  have hT : (cH H).sortOf (bool true) = some Srt.bool := rmS_sortOf_bool _ true
  have hF : (cH H).sortOf (bool false) = some Srt.bool := rmS_sortOf_bool _ false
  let m1 : M := elemOf (cH H) I (int (-1))
  let e : Valuation M := ⟨fun x => if x = tb.ev (LibEv.vkey c vars 0) then m1 else τb, fun _ _ => False⟩
  have heX : e.evalEvar (tb.ev (LibEv.vkey c vars 0)) = m1 := by simp [e]
  have heR : e.evalEvar (tb.ev (.sortVar "R")) = τb := by simp [e, tb_ne]
  obtain ⟨h1a, h1b⟩ := elemOf_spec hI hS1 e
  obtain ⟨hTa, hTb⟩ := elemOf_spec hI hT e
  have hinh1 : KoreAML.Inh I τ m1 := by
    refine (KoreAML.interp_inhOf_of (fun a' => ?_)).mp h1b
    have := hτ tb e a'
    rwa [trSort_srtOf_twoT] at this
  have hinhT : KoreAML.Inh I τb (elemOf (cH H) I (bool true)) := by
    refine (KoreAML.interp_inhOf_of (fun a' => ?_)).mp hTb
    have := hτb tb e a'
    rwa [trSort_srtOf_twoT] at this
  have h2 : LibEv.vkey c vars 0 = .evar "VarX" (srtOf c Srt.int) := rfl
  refine ⟨e, ?_, fun hax => ?_⟩
  · intro n s hk
    have hfr : (KoreAML.freeOf [] ensAx.ax.pattern).eraseDups = [LibEv.vkey c vars 0] := by decide +kernel
    rw [hfr, List.mem_singleton, h2] at hk
    injection hk with hn hs
    subst hn hs
    exact ⟨int (-1), Srt.int, rfl, hS1, (h1a _).mpr heX⟩
  · rw [htr] at hax
    unfold KoreAML.trAxiom at hax
    dsimp only at hax
    have hdist : (distinctSorts (cH H)).contains Srt.bool = true := by
      refine List.elem_eq_true_of_mem ?_
      unfold distinctSorts
      exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
        (List.mem_cons_of_mem _ (List.mem_cons_self ..)))))
    rw [ens_free] at hax
    have heX' : e.evalEvar ((KoreAML.tableOf ensAx.ax.sortVars ensAx.ax.pattern).ev (LibEv.vkey c vars 0)) = m1 := heX
    have heR' : e.evalEvar ((KoreAML.tableOf ensAx.ax.sortVars ensAx.ax.pattern).ev (.sortVar "R")) = τb := heR
    clear heX heR
    generalize htb : KoreAML.tableOf ensAx.ax.sortVars ensAx.ax.pattern = t at hax heX' heR'
    have hinhR : KoreAML.Inh I (e.evalEvar (t.ev (.sortVar "R"))) (elemOf (cH H) I (bool true)) := by
      rw [heR']; exact hinhT
    have hRv : ∀ b, (KoreAML.trSort t KoreAML.R).interpret I e b ↔ b = e.evalEvar (t.ev (.sortVar "R")) :=
      fun b => by rw [trSort_R, KoreAML.interp_evar]
    have hR : KoreAML.IsSort I (e.evalEvar (t.ev (.sortVar "R"))) := by rw [heR']; exact hτbsort
    rw [interpret_impl] at hax
    have hg := hax (KoreAML.interp_conjList fun w hw => by
      obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl
      · exact (KoreAML.interp_guard_sortVar hD).mpr hR
      · rw [h2]
        unfold KoreAML.guardOf
        rw [KoreAML.interp_member hD]
        have hX : e.evalEvar (t.ev (.evar "VarX" (srtOf c Srt.int))) = m1 := heX'
        rw [hX]
        exact (KoreAML.interp_inhOf_of (hτ t e)).mpr hinh1)
    rw [hp, ← ensPat_wh H] at hg
    unfold ensPat at hg
    simp only [KoreAML.sortOf] at hg
    rw [KoreAML.interp_equal hD] at hg
    have hA := (hg (elemOf (cH H) I (bool true))).mpr ((KoreAML.interp_inhOf_of hRv).mpr hinhR)
    rw [KoreAML.tr] at hA
    dsimp only at hA
    rw [KoreAML.interp_sImp] at hA
    have hEQ := hA.2 (by
      rw [KoreAML.tr]
      dsimp only
      rw [KoreAML.interp_sTop hD (InertEv.trSort_topFresh t _)]
      exact (KoreAML.interp_inhOf_of hRv).mpr hinhR)
    rw [KoreAML.tr] at hEQ
    dsimp only at hEQ
    rw [KoreAML.interp_sEquals hD hc (hτ t e) hRv hτsort hR] at hEQ
    have hσ : ∀ i p, vars[i]? = some p → ∃ v, σ1.lookup i = some v ∧ (cH H).sortOf v = some p.2 := by
      intro i p hp'
      match i, hp' with
      | 0, hp' => cases hp'; exact ⟨int (-1), rfl, hS1⟩
    have hag : ∀ i v, i < vars.length → σ1.lookup i = some v →
        ∀ m, m = e.evalEvar (t.ev (LibEv.vkey (cH H) vars i)) ↔ (den (cH H) v).interpret I e m := by
      intro i v hi hv m
      match i, hi with
      | 0, _ =>
        cases hv
        rw [vkey_wh H, heX']
        exact (h1a m).symm
    have hL := (InertEvUser.den_valU (tbl := t) (e := e) (coreOKH H) (hokH H) (table_ok H) hI hσ hag tL
      ((typedL_wh H).trans typedL)).1 (elemOf (cH H) I (int (-1)))
    have hG := (InertEvUser.den_valU (tbl := t) (e := e) (coreOKH H) (hokH H) (table_ok H) hI hσ hag tG
      ((typedG_wh H).trans typedG)).1 (elemOf (cH H) I (bool true))
    rw [valL] at hL
    rw [valG] at hG
    have hRHS := (hEQ.2 m1 hinh1).mp (hL.mpr ((h1a _).mpr rfl))
    have hIn : (KoreAML.tr ⟨t, []⟩ (.equals (srtOf (cH H) Srt.bool) (srtOf (cH H) Srt.int)
        (LibEv.kore (cH H) vars tG) (.dv (srtOf (cH H) Srt.bool) "true"))).interpret I e m1 := by
      have : (KoreAML.sAnd (KoreAML.tr ⟨t, []⟩ (LibEv.kore (cH H) vars tR))
          (KoreAML.tr ⟨t, []⟩ (.equals (srtOf (cH H) Srt.bool) (srtOf (cH H) Srt.int)
            (LibEv.kore (cH H) vars tG) (.dv (srtOf (cH H) Srt.bool) "true")))).interpret I e m1 := hRHS
      exact (KoreAML.interp_sAnd.mp this).2
    rw [KoreAML.tr] at hIn
    dsimp only at hIn
    rw [KoreAML.interp_sEquals hD hc (hτb t e) (hτ t e) hτbsort hτsort] at hIn
    have hTrue : (KoreAML.tr ⟨t, []⟩ (.dv (srtOf (cH H) Srt.bool) "true")).interpret I e
        (elemOf (cH H) I (bool true)) := by
      have : (den (cH H) (bool true)).interpret I e (elemOf (cH H) I (bool true)) := (hTa _).mpr rfl
      unfold den KoreAML.den bool at this
      rw [GroundTerm.kore] at this
      unfold srtOf
      rw [KoreAML.tr_dv] at this ⊢
      exact this
    have hGv : (den (cH H) (bool false)).interpret I e (elemOf (cH H) I (bool true)) := hG.mp ((hIn.2 _ hinhT).mpr hTrue)
    exact dom_apart hI hdist hF hT (by decide) e _ ⟨hGv, (hTa _).mpr rfl⟩

/-- **Γ with the sentence has no model, for every H**: the sentence is not inert. -/
theorem ens_refuted (H : HookParams) : ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M),
    I ⊧ᴵP Γ (cH H) → ¬ (I ⊧ᴵ (trS ensAx).pat) := by
  intro M _ I hI hax
  obtain ⟨e, -, hn⟩ := ens_fails H M I hI
  exact hn (hax e default)

end KCore.C3SimpEnsRefuted

#check @KCore.C3SimpEnsRefuted.ens_fails
#check @KCore.C3SimpEnsRefuted.ens_refuted
#print axioms KCore.C3SimpEnsRefuted.ens_class
#print axioms KCore.C3SimpEnsRefuted.ens_fails
#print axioms KCore.C3SimpEnsRefuted.ens_refuted
