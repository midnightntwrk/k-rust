/-
  The step cases of the induction on an evaluation of kore.k (User.SpecMotive) at the functions
  of the walk of a function's clauses: `apply`, `applyL`, `result`, `evalAt`, `evalIf`, `tryAt`,
  `orElse`, `tryCl`, `tryM`, each with no hypothesis beyond the step case's own (`execReady d`,
  `encDef d = some E`).

  Each inverts the call (User.WalkInv) and reads `Spec` at the calls the clause makes:

  - `result`: the term `some` holds, `bot` at `none`.
  - `orElse`: `some` stays, `none` is `tryAt` at the clauses after.
  - `tryAt`: at a clause of priority `P`, `tryCl` at it, whose result is one of `f` since every
    clause below `P` fails; at another priority, the clauses after.
  - `evalIf`: `some` stays; `none` means every clause at `P` fails, so `evalAt` at the next
    priority has every clause below it fail (`below_next_ksc`).
  - `evalAt`: `noP` means every clause fails; `at(P)` is `tryAt` at all clauses, then `evalIf`.
  - `applyL`: `nofn` where `f` is no function; `fnd(Cs)` where it is one, `evalAt` from the first
    priority (`below_first_ksc`) and `result`: a result of `f`, or none where every clause fails,
    which is `Eval.rest` (no rest at `d₀ d`).
  - `apply`: `bot` where an argument is undefined; else `lookup`, which at the encoded definition
    is `lookupFn` (`lookFn_encDef_ksc`), and `applyL`.
  - `tryM`: at a binding with an entry for every variable, the instances of the `requires` and of
    the right side have values (`reqInst_ksc`, `rhsInst_ksc`) and `eval` gives at them the
    encodings of what the object semantics gives (`reqEval_spec_ksc`, `rhsEval_spec_ksc`):
    `try-holds` gives a result of `f` by `Eval.clause` (or `Eval.ensFails`) at the binding's
    substitution, `try-refuted` a `requires` that fails under every substitution the binding agrees
    with, and the two do not both fail (one call of `eval`, one value).
  - `tryCl`: `matchTs` has a value at sorted patterns (`matchTsF_total`), each of its bindings has
    an entry for every variable and agrees with a well-sorted substitution under which the patterns
    denote the arguments (`matchTsF_col_sound`, `matchTsF_col_wellSorted`), and every such
    substitution agrees with one of its bindings (`matchTsF_col_complete`): `tryM`'s `none` is
    `Fails`. The collections' condition is C13's (`encodable_colls_c13`).
-/
import User.ClauseObj

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option Elab.async false

namespace KCore.KK

section Steps
open _root_.KK
variable {d : Semantics} {E : D}

theorem called_eval_ksc : ∀ g ws q, Called d E g ws q → Eval c₀ g ws q := fun _ _ _ h => h.1

/-- **A clause gives a result of `f`**, where every clause of a smaller priority fails, under a
well-sorted substitution under which its patterns denote the arguments and its `requires` is
true: the right side's result, or none where the ensures is not true. -/
theorem found_clause_ksc (hc : encodable d = true) {f : Sym} {fn : Fn} {ws : List GroundTerm}
    {cl : Clause} (hw : WalkAt_ksm d f fn ws) (hcl : cl ∈ fn.clauses)
    (hb : Below_ksm d fn ws (some (cl.prio : Int))) {σ : Subst} (hσ : (d₀ d).WellSorted cl.vars σ)
    (hp : PatVals (d₀ d) σ cl.pats ws)
    (hreq : ∀ t, cl.req = some t → EvalTerm (d₀ d) σ t (some (bool true)))
    {o : Option GroundTerm} (hrhs : EvalTerm (d₀ d) σ cl.rhs o) {u : T}
    (hu : (cl.ens = none ∧ u = encR o) ∨
      ∃ e w, cl.ens = some e ∧ EvalTerm (d₀ d) σ e w ∧ u = ensureF (encR w) (encR o)) :
    Found_ksm d f ws u := by
  have hfn : fn ∈ (d₀ d).allFns := (lookupFn_spec hw.1).1
  obtain ⟨hex, hpre, hpost, -, -⟩ := clauseShape_ksc hc hfn hcl
  have hpre' : Holds (d₀ d) cl.vars.length σ cl.pre true := by rw [hpre]; exact .top
  have hpost' : Holds (d₀ d) cl.vars.length σ cl.post true := by rw [hpost]; exact .top
  have hprio : ∀ cl' ∈ fn.clauses, cl'.aside = false → cl'.prio < cl.prio → Fails (d₀ d) ws cl' :=
    fun cl' hm _ hlt => hb cl' hm fun P e => by cases e; exact Int.ofNat_lt.mpr hlt
  rcases hu with ⟨hen, rfl⟩ | ⟨e, w, hen, hew, rfl⟩
  · exact ⟨o, rfl, .clause hw.1 hcl hσ hp hreq hpre' hprio hex hrhs
      (fun t ht => by rw [hen] at ht; cases ht) hpost'⟩
  · by_cases hwt : w = some (bool true)
    · subst hwt
      refine ⟨o, rfl, .clause hw.1 hcl hσ hp hreq hpre' hprio hex hrhs
        (fun t ht => by rw [hen] at ht; cases ht; exact hew) hpost'⟩
    · refine ⟨none, ?_, .ensFails hw.1 hcl hσ hp hreq hpre' hprio hex hen hew hwt⟩
      have : encR w ≠ .bv true := fun h => hwt (encR_eq_bv_ksc h)
      show ensureF (encR w) (encR o) = .bot
      unfold ensureF
      rw [if_neg this]

/-- **The step case at `result`.** -/
theorem stepCase_result_ksc : StepCase d E 502 := fun _ _ vs r hb =>
  (Spec_result d E vs r).mpr fun _ _ _ hvs => by
    subst hvs
    exact result_inv_ksc hb

/-- **The step case at `orElse`.** -/
theorem stepCase_orElse_ksc : StepCase d E 497 := fun _ _ vs r hb =>
  (Spec_orElse d E vs r).mpr fun f fn ws suf P x hvs hw hsuf hb' hx => by
    subst hvs
    rcases orElse_inv_ksc hb with ⟨t, rfl, hr'⟩ | ⟨rfl, hR⟩
    · exact ⟨some t, hr', hx, fun h => (nomatch h)⟩
    · obtain ⟨y, hy, hf, hn⟩ := (Spec_tryAt d E _ _).mp hR.2 f fn ws suf P rfl hw hsuf hb'
      exact ⟨y, hy, hf, fun h => ⟨rfl, hn h⟩⟩

/-- **The step case at `tryAt`.** -/
theorem stepCase_tryAt_ksc : StepCase d E 512 := fun _ _ vs r hb =>
  (Spec_tryAt d E vs r).mpr fun f fn ws suf P hvs hw hsuf hb' => by
    subst hvs
    rcases tryAt_inv_ksc called_eval_ksc hb with ⟨hnil, hr'⟩ | ⟨c, cs', hcs, hcase⟩
    · have : suf = [] := List.map_eq_nil_iff.mp hnil
      subst this
      exact ⟨none, hr', fun u h => (nomatch h), fun _ cl hcl => (nomatch hcl)⟩
    · obtain ⟨cl, suf', rfl, rfl, rfl⟩ := List.map_eq_cons_iff.mp hcs
      have hsuf' : ∀ c ∈ suf', c ∈ fn.clauses := fun c hc => hsuf c (List.mem_cons_of_mem _ hc)
      rcases hcase with ⟨hP, q, hq, hcase⟩ | ⟨hP, hR⟩
      · have hP' : (cl.prio : Int) = P := hP
        have hcl := hsuf cl (List.mem_cons_self ..)
        obtain ⟨x₁, hx₁, hf₁, hn₁⟩ := (Spec_tryCl d E _ _).mp hq.2 f fn ws cl rfl hw hcl
        rcases hcase with ⟨y, hy, hR⟩ | ⟨hn, -⟩
        · rw [hx₁] at hy
          cases hy
          obtain ⟨z, hz, hfz, hnz⟩ := (Spec_orElse d E _ _).mp hR.2 f fn ws suf' P x₁ rfl hw hsuf' hb'
            (hf₁ (by rw [hP']; exact hb'))
          refine ⟨z, hz, hfz, fun h c hc hcP => ?_⟩
          obtain ⟨hx1n, hrest⟩ := hnz h
          rcases List.mem_cons.mp hc with rfl | hc
          · exact hn₁ hx1n
          · exact hrest c hc hcP
        · rw [hx₁] at hn; cases hn
      · have hP' : (cl.prio : Int) ≠ P := hP
        obtain ⟨x, hx, hf, hn⟩ := (Spec_tryAt d E _ _).mp hR.2 f fn ws suf' P rfl hw hsuf' hb'
        refine ⟨x, hx, hf, fun h c hc hcP => ?_⟩
        rcases List.mem_cons.mp hc with rfl | hc
        · exact absurd hcP hP'
        · exact hn h c hc hcP

/-- **The step case at `evalIf`.** -/
theorem stepCase_evalIf_ksc : StepCase d E 466 := fun _ _ vs r hb =>
  (Spec_evalIf d E vs r).mpr fun f fn ws P x hvs hw hb' hf hn => by
    subst hvs
    rcases evalIf_inv_ksc called_eval_ksc hb with ⟨t, rfl, hr'⟩ | ⟨rfl, hR⟩
    · exact ⟨some t, hr', hf, fun h => (nomatch h)⟩
    · exact (Spec_evalAt d E _ _).mp hR.2 f fn ws _ rfl hw (below_next_ksc hb' (hn rfl))

/-- **The step case at `evalAt`.** -/
theorem stepCase_evalAt_ksc : StepCase d E 465 := fun _ _ vs r hb =>
  (Spec_evalAt d E vs r).mpr fun f fn ws p hvs hw hb' => by
    subst hvs
    rcases evalAt_inv_ksc hb with ⟨rfl, hr'⟩ | ⟨P, rfl, q, hq, hcase⟩
    · exact ⟨none, hr', fun u h => (nomatch h), fun _ cl hcl => hb' cl hcl fun P h => (nomatch h)⟩
    · obtain ⟨x, hx, hf, hn⟩ := (Spec_tryAt d E _ _).mp hq.2 f fn ws fn.clauses P rfl hw
        (fun c hc => hc) hb'
      rcases hcase with ⟨y, hy, hR⟩ | ⟨hn', -⟩
      · rw [hx] at hy
        cases hy
        exact (Spec_evalIf d E _ _).mp hR.2 f fn ws P x rfl hw hb' hf hn
      · rw [hx] at hn'; cases hn'

/-- **The step case at `applyL`.** -/
theorem stepCase_applyL_ksc : StepCase d E 449 := fun _ _ vs r hb =>
  (Spec_applyL d E vs r).mpr fun f ws l hvs hlv hl => by
    subst hvs
    rcases applyL_inv_ksc called_eval_ksc hb with ⟨rfl, hr'⟩ | ⟨cs, rfl, q, hq, hcase⟩
    · refine ⟨fun _ => hr', fun fn hfn _ => ?_⟩
      rw [hfn] at hl; cases hl
    · cases hfn : (d₀ d).lookupFn f with
      | none => rw [hfn] at hl; cases hl
      | some fn =>
        rw [hfn] at hl
        cases hl
        refine ⟨fun h => (by rw [hfn] at h; cases h), fun fn' hfn' hs => ?_⟩
        rw [hfn] at hfn'
        cases hfn'
        have hw : WalkAt_ksm d f fn ws := ⟨hfn, hs, hlv⟩
        obtain ⟨x, hx, hf, hn⟩ := (Spec_evalAt d E _ _).mp hq.2 f fn ws _ rfl hw
          (below_first_ksc d fn ws)
        rcases hcase with ⟨y, hy, hR⟩ | ⟨hn', -⟩
        · rw [hx] at hy
          cases hy
          have hres := (Spec_result d E _ _).mp hR.2 f (encTs ws) x rfl
          cases x with
          | some u =>
            obtain ⟨o, rfl, ho⟩ := hf u rfl
            exact ⟨o, hres, ho⟩
          | none => exact ⟨none, hres, Eval.rest hfn (hn rfl)⟩
        · rw [hx] at hn'; cases hn'

/-- **The step case at `apply`.** -/
theorem stepCase_apply_ksc : StepCase d E 448 := fun _ hE vs r hb =>
  (Spec_apply d E vs r).mpr fun f os hvs hlv => by
    subst hvs
    rcases apply_inv_ksc called_eval_ksc hb with ⟨hbot, hr'⟩ | ⟨hbot, hR⟩
    · refine ⟨fun _ => hr', fun ws hws => ?_⟩
      have hos := allSome_eq_map hws
      subst hos
      have he : (ws.map some).map encR = encTs ws := by rw [List.map_map, encTs_eq_map]; rfl
      rw [he, hasBotF_encTs_ksc fun v hv => hlv v (List.mem_map_of_mem hv)] at hbot
      cases hbot
    · refine ⟨fun hn => absurd (hasBotF_of_none_kst hn) (by rw [hbot]; decide), fun ws hws => ?_⟩
      have hos := allSome_eq_map hws
      subst hos
      have he : (ws.map some).map encR = encTs ws := by rw [List.map_map, encTs_eq_map]; rfl
      rw [he, lookFn_encDef_ksc hE] at hR
      exact (Spec_applyL d E _ _).mp hR.2 f ws _ rfl
        (litsVL_iff.mpr fun v hv => hlv v (List.mem_map_of_mem hv)) rfl

/-- **The step case at `tryM`.** -/
theorem stepCase_tryM_ksc : StepCase d E 514 := fun hr hE vs r hb =>
  (Spec_tryM d E vs r).mpr fun f fn ws cl ms hvs hw hcl hms => by
    subst hvs
    have hc := encodable_of_encDef_ksc hE
    have hfn : fn ∈ (d₀ d).allFns := (lookupFn_spec hw.1).1
    rcases tryM_inv_ksc called_eval_ksc hb with ⟨rfl, hr'⟩ | ⟨B, ms', rfl, hcase⟩
    · exact ⟨none, hr', fun _ u h => (nomatch h), fun _ B hB => (nomatch hB)⟩
    · obtain ⟨hcov, σ₀, hB₀, hσ₀, hp₀⟩ := hms B (List.mem_cons_self ..)
      obtain ⟨t, ht⟩ := reqInst_ksc hr hc hfn hcl hcov
      rcases hcase t ht with ⟨q, hq, hne, hR⟩ | ⟨q, hq, heq, hrhs⟩ | ⟨q, q', hq, hq', h1, h2⟩
      · obtain ⟨u, rfl, hnone, hall⟩ := clauseReqEval_ksc hr hc hfn hcl ht hB₀ hσ₀ hq
        have hu := hne u rfl
        obtain ⟨x, hx, hf, hn⟩ := (Spec_tryM d E _ _).mp hR.2 f fn ws cl ms' rfl hw hcl
          (fun B' hB' => hms B' (List.mem_cons_of_mem _ hB'))
        refine ⟨x, hx, hf, fun h B' hB' σ hBσ hσ hp => ?_⟩
        rcases List.mem_cons.mp hB' with rfl | hB'
        · cases hrq : cl.req with
          | none => exact absurd (hnone hrq) hu
          | some tq =>
            obtain ⟨o, rfl, ho⟩ := hall tq hrq σ hBσ hσ
            exact .intro hrq ho fun e => hu (by rw [e]; rfl)
        · exact hn h B' hB' σ hBσ hσ hp
      · obtain ⟨u, rfl, -, hall⟩ := clauseReqEval_ksc hr hc hfn hcl ht hB₀ hσ₀ hq
        have hu := heq u rfl
        rcases hrhs with ⟨hn, -⟩ | ⟨t', q', ht', hq', rfl⟩
        · obtain ⟨t', ht'⟩ := rhsInst_ksc hr hc hfn hcl hcov
          rw [ht'] at hn; cases hn
        · obtain ⟨u', rfl, hall'⟩ := clauseRhsEval_ksc hr hc hfn hcl ht' hB₀ hσ₀ hq'
          refine ⟨some u', rfl, fun hb' u'' hu'' => ?_, fun h => (nomatch h)⟩
          cases hu''
          obtain ⟨o, ho, hens⟩ := hall' σ₀ hB₀ hσ₀
          refine found_clause_ksc hc hw hcl hb' hσ₀ hp₀ (fun tq hrq => ?_) ho hens
          obtain ⟨o', ho', he'⟩ := hall tq hrq σ₀ hB₀ hσ₀
          rw [hu] at ho'
          rw [encR_eq_bv_ksc ho'.symm] at he'
          exact he'
      · obtain ⟨u, rfl, -, -⟩ := clauseReqEval_ksc hr hc hfn hcl ht hB₀ hσ₀ hq
        have e : q' = some (emb u) := (evalF_iff hq.1).mp hq'.1
        exact absurd (h1 u rfl) (h2 u e)

/-- **The step case at `tryCl`.** -/
theorem stepCase_tryCl_ksc : StepCase d E 513 := fun hr hE vs r hb =>
  (Spec_tryCl d E vs r).mpr fun f fn ws cl hvs hw hcl => by
    subst hvs
    have hc := encodable_of_encDef_ksc hE
    have hfn : fn ∈ (d₀ d).allFns := (lookupFn_spec hw.1).1
    obtain ⟨hmc, hov⟩ := matchCtx_d₀ hr hc
    have hcs : Faithful.collsOK (d₀ d) = true := (encodable_colls_c13 hc).1
    obtain ⟨hpe, hcp, -⟩ := clauseEnc_ksc hc hfn hcl
    have hq : encTermsWith (d₀ d) encLit cl.pats = some (encCl d cl).pats := by
      rw [encTermsWith_d₀]; exact hpe
    have hp := clausePats_d₀ hr hc hfn hcl
    have hbinds := (clauseShape_ksc hc hfn hcl).2.2.2.2
    have hsubs : E.subs = subsF (d₀ d) := (encDef_subs hE).trans (subsF_d₀ d).symm
    rcases tryCl_inv_ksc called_eval_ksc hb with ⟨M, hM, hR⟩ | ⟨hM, -⟩
    · rw [hsubs] at hM
      have hprem : ∀ B ∈ M, Covers_ksm B (List.range cl.vars.length) ∧
          ∃ σ, BindAgree B σ ∧ (d₀ d).WellSorted cl.vars σ ∧ PatVals (d₀ d) σ cl.pats ws :=
        fun B hB => by
          obtain ⟨-, hcov, -, -⟩ := matchTsF_col_sound hmc hov hcs hq hp hw.2.1 hw.2.2 hM hB
          obtain ⟨σ, hrep, hσ, hpv⟩ :=
            matchTsF_col_wellSorted hmc hov hcs hq hp hw.2.1 hw.2.2 hbinds hM hB
          exact ⟨fun i hi => hcov i (Exec.binds_all hbinds i (List.mem_range.mp hi)), σ,
            bindAgree_of_rep_ksc hrep, hσ, hpv⟩
      obtain ⟨x, hx, hf, hn⟩ := (Spec_tryM d E _ _).mp hR.2 f fn ws cl M rfl hw hcl hprem
      refine ⟨x, hx, hf, fun h => .intro fun σ hσa hpv => ?_⟩
      have hσ := wellSorted_of_at_kmf hσa hbinds (fun i hi => List.mem_append_left _ hi)
      obtain ⟨M', hM', B', hB', hagree, -⟩ :=
        matchTsF_col_complete hmc hov hcs hσ hq hcp hp hw.2.2 hpv (bindAgree_nil σ)
      rw [hM] at hM'
      cases hM'
      exact hn h B' hB' σ hagree hσ hpv
    · rw [hsubs] at hM
      have := matchTsF_total hov hq hp hw.2.1 (subsF (d₀ d)) []
      rw [hM] at this
      cases this

/-- **The step cases of the walk of the clauses**: `apply`, `applyL`, `result`, `evalAt`,
`evalIf`, `tryAt`, `orElse`, `tryCl`, `tryM`, with no hypothesis. -/
theorem stepCases_clauses_ksc (d : Semantics) (E : D) :
    ∀ f ∈ [448, 449, 502, 465, 466, 512, 497, 513, 514], StepCase d E f := by
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact stepCase_apply_ksc
  · exact stepCase_applyL_ksc
  · exact stepCase_result_ksc
  · exact stepCase_evalAt_ksc
  · exact stepCase_evalIf_ksc
  · exact stepCase_tryAt_ksc
  · exact stepCase_orElse_ksc
  · exact stepCase_tryCl_ksc
  · exact stepCase_tryM_ksc

end Steps

/-! ## Checks -/

#check @stepCase_apply_ksc
#check @stepCase_applyL_ksc
#check @stepCase_result_ksc
#check @stepCase_evalAt_ksc
#check @stepCase_evalIf_ksc
#check @stepCase_tryAt_ksc
#check @stepCase_orElse_ksc
#check @stepCase_tryCl_ksc
#check @stepCase_tryM_ksc
#check @stepCases_clauses_ksc

open Lean in
#eval show CoreM Unit from do
  for n in [``found_clause_ksc, ``stepCase_result_ksc, ``stepCase_orElse_ksc, ``stepCase_tryAt_ksc,
      ``stepCase_evalIf_ksc, ``stepCase_evalAt_ksc, ``stepCase_applyL_ksc, ``stepCase_apply_ksc,
      ``stepCase_tryM_ksc, ``stepCase_tryCl_ksc, ``stepCases_clauses_ksc] do
    let axs ← collectAxioms n
    unless axs.all ([``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "{n}: axioms {axs}"

end KCore.KK
