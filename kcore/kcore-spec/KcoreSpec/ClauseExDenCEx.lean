/-
  KCore. The clause facts and the reading of clauses with existential variables that the block of
  OpenClauseDenQ.lean asks, from `coreOKEx`.

  `eval_den_exReadCEx` and its corollaries (`eval_den_exCEx`, `eval_den_clauseExCEx`,
  `eval_den_exNoneCEx`) are `eval_den_exRead` and its corollaries for a semantics `coreOKEx`
  accepts, proved as they are (their proofs read the clauses' sorts, never `clausesPlain`). From
  `sortedOKEx`, every clause of every function has `ClauseOpenFactsQ`
  (`clauseOpenFactsQ_of_sortedOKEx`); from `coreOKEx`, in a model of `Γc` of a definition that reads
  confined sorts, every clause with existential variables has `ClauseExRead`
  (`clauseExRead_of_coreEx`): `eval_den_exReadCEx` with the clause's facts from `sortedOKEx`.
-/
import KcoreSpec.ClauseExDen
import KcoreSpec.CoreOKExFacts
import KcoreSpec.OpenClauseDenQ

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace KCore

namespace Faithful

open ML
open KoreAML (DefOK Inh IsSort Closed KGround VarKey VarTable)

section
variable {c : Semantics} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}

open HoldsShape in
/-- `eval_den_exRead` for a semantics `coreOKEx` accepts. -/
theorem eval_den_exReadCEx (h : c.coreOKEx = true) (hrc : c.readsConfined = true) (hIc : I ⊧ᴵP Γc c)
    {f : Sym} {fn : Fn} {cl : Clause} {ws : List GroundTerm} {σ₀ : Subst} {r : Option GroundTerm}
    (hfn : c.lookupFn f = some fn) (hcl : cl ∈ fn.clauses) (hws : c.sortsOf ws = some fn.args)
    (hpats : sortsOfTerms c.patCtxAll cl.vars cl.pats = some fn.args)
    (hpreOK : c.condOK cl.vars cl.pre = true)
    (hs : c.clauseExOK cl = true) (hb : Cond.bound c cl.vars.length cl.post = true)
    (hp : c.clausePlainEx cl = true) (hne : cl.exs ≠ [])
    (hocc : ∀ i < cl.vars.length, i ∈ cl.exs ∨ i ∈ varOccsList cl.pats ++ cl.condVars ++ varOccs cl.rhs ++
      (cl.ens.map varOccs).getD [] ++ varOccsCond cl.vars.length cl.post)
    (hreqs : ∀ t, cl.req = some t → sortOfTerm (c.rhsCtx (c.fns.map Fn.sig)) cl.vars t = some Srt.bool)
    (hrhss : sortOfTerm (c.rhsCtx (c.fns.map Fn.sig)) cl.vars cl.rhs = some fn.result)
    (henss : ∀ t, cl.ens = some t → sortOfTerm (c.rhsCtx (c.fns.map Fn.sig)) cl.vars t = some Srt.bool)
    (hσ₀ : c.WellSorted cl.vars σ₀) (hmatch0 : PatVals c σ₀ cl.pats ws)
    (ihreq : ∀ t, cl.req = some t → ∀ (tbl : VarTable) (e' : Valuation M), Agrees c I tbl (canonVars c cl.vars) σ₀ e' →
      ∀ m', (KoreAML.tr ⟨tbl, []⟩ (Term.kore c (canonVars c cl.vars) t)).interpret I e' m' ↔
        (den c (bool true)).interpret I e' m')
    (ihpre : cl.pre.isTop = false → ∀ (tbl : VarTable) (e : Valuation M) (σr m0 : M),
      Agrees c I tbl (canonVars c cl.vars) σ₀ e →
      (∀ k ∈ KoreAML.varsOf (Cond.kore c (canonVars c cl.vars) KoreAML.R cl.pre), k ∈ tbl) →
      VarKey.sortVar "R" ∈ tbl → (∀ a, (KoreAML.trSort tbl KoreAML.R).interpret I e a ↔ a = σr) → IsSort I σr →
      Inh I σr m0 → (KoreAML.tr ⟨tbl, []⟩ (Cond.kore c (canonVars c cl.vars) KoreAML.R cl.pre)).interpret I e m0)
    (hlow : ∀ cl' ∈ fn.clauses, cl'.aside = false → cl'.prio < cl.prio →
      c.condOK cl'.vars cl'.pre = true ∧ sortsOfTerms c.patCtxAll cl'.vars cl'.pats = some fn.args ∧
      (∀ t, cl'.req = some t → ∀ i ∈ varOccs t, i < cl'.vars.length) ∧
      ExclEmptyCl c I fn cl' ∧ Fails c ws cl' ∧ ModelFailsCl c I cl' ws)
    (hall0 : ∀ σ', AgreeOff cl.exs σ₀ σ' → c.WellSorted cl.vars σ' → InstIsRead c I σ' cl r)
    (hgive0 : ∀ v, r = some v → EvalTerm c σ₀ cl.rhs (some v) ∧ TermAt c I σ₀ cl.rhs (some v) ∧
      (∀ t, cl.ens = some t → TermAt c I σ₀ t (some (bool true))) ∧
      HoldsRead c I cl.vars.length σ₀ cl.post true)
    (e : Valuation M) (m : M) :
    (KoreAML.den (symApp c f (GroundTerm.koreList c ws))).interpret I e m ↔ Res c I e r m := by
  have hI : I ⊧ᴵP Γ c := fun φ hφ => hIc φ (Or.inl hφ)
  obtain ⟨hok, hsr, hnn, hg, hph, hcso, hcs, hph', hno⟩ := hypSoundEx_of_coreEx h
  haveI : OvlOK c := hno
  have hsc := sortCtx_of_allCEx hok hsr (OvlOK.ovlCase hno)
  have hD := defOK hI
  have N : NodeFacts c I := nodeFacts_of_coreEx h hIc
  have hfnm := (lookupFn_spec hfn).1
  have hS : fn.result < nRegSorts + c.sortNames.length := hnn.2.2 fn hfnm fn.result (List.mem_cons_self ..)
  -- the clause's facts
  have hs' := hs
  simp only [Semantics.clauseExOK, Bool.and_eq_true] at hs'
  obtain ⟨⟨⟨hltB, hndB⟩, hleft⟩, hokQ⟩ := hs'
  have hlt : ∀ i ∈ cl.exs, i < cl.vars.length := fun i hi => of_decide_eq_true (List.all_eq_true.mp hltB i hi)
  have hnd : cl.exs.Nodup := (NamesApart.nodupB_iff _).mp hndB
  have hreqv : ∀ t, cl.req = some t → ∀ i ∈ varOccs t, i < cl.vars.length := fun t ht => varOccs_lt t (hreqs t ht)
  have hrhsv := varOccs_lt _ hrhss
  have hensv : ∀ t, cl.ens = some t → ∀ i ∈ varOccs t, i < cl.vars.length := fun t ht => varOccs_lt t (henss t ht)
  have hfreeF : cl.exs.filter (!cl.leftVars.contains ·) = cl.exs :=
    List.filter_eq_self.mpr fun i hi => List.all_eq_true.mp hleft i hi
  have hsj : ∀ j, j < cl.vars.length → cl.vars[j]? = some (cl.vars.getD j 0) := fun j hj => by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]
  have hr : ∀ v, r = some v → c.sortOf v = some fn.result := fun v hv =>
    EvalTerm.sorted hsc (hgive0 v hv).1 fns_headsOK hσ₀ hrhss rfl
  -- a term's reading at a valuation that agrees with a well-sorted σ' and holds every key
  have allOf : ∀ {σ' : Subst} {t : Term} {r' : Option GroundTerm} {s : Srt} {tbl : VarTable} {e : Valuation M},
      TermAt c I σ' t r' → c.WellSorted cl.vars σ' → Agrees c I tbl (canonVars c cl.vars) σ' e →
      (∀ i < cl.vars.length, canonKey c cl.vars i ∈ tbl) →
      sortOfTerm (c.rhsCtx (c.fns.map Fn.sig)) cl.vars t = some s →
      ∀ m, (KoreAML.tr ⟨tbl, []⟩ (Term.kore c (canonVars c cl.vars) t)).interpret I e m ↔ Res c I e r' m :=
    fun {σ' t r' s tbl e} hTA hw hag hkeys ht m =>
      hTA (fun i hi => hi) (reads_of_agrees hw hag (P := fun i => i ∈ varOccs t)
        fun i hi => ⟨varOccs_lt t ht i hi, hkeys i (varOccs_lt t ht i hi)⟩) ht m
  -- the keys of the right side's predicate are keys of the body
  have hkQ : ∀ {tbl : VarTable}, (∀ k ∈ KoreAML.varsOf (clauseRhsBody c fn cl), k ∈ tbl) →
      ∀ k ∈ KoreAML.varsOf (Cond.kore c (canonVars c cl.vars) (srtOf c fn.result) cl.post), k ∈ tbl := by
    intro tbl hkB k hk
    cases hpt : cl.post.isTop with
    | false =>
      refine hkB k ?_
      unfold clauseRhsBody
      exact Model.varsOf_and_mem (by simp [Cond.conj, hpt]) hk
    | true =>
      rw [Cond.eq_top_of_isTop hpt] at hk
      simp [Cond.kore, KoreAML.varsOf, srtOf, KoreAML.srt, KoreAML.sortVarsOf, KoreAML.sortVarsOfList] at hk
  have hinSort : ∀ {tbl : VarTable} {e : Valuation M} {m : M}, InS I (c.sortName fn.result) m →
      (KoreAML.inhOf (KoreAML.trSort tbl (srtOf c fn.result))).interpret I e m := fun {tbl e m} hm => by
    unfold srtOf; rw [trSort_srt]; exact (inS_iff e).mpr hm
  -- the body's first two conjuncts are the right side `rhs ∧ ens`
  have hbody : ∀ {tbl : VarTable} {e : Valuation M} {m : M},
      (KoreAML.tr ⟨tbl, []⟩ (clauseRhsBody c fn cl)).interpret I e m ↔
        (KoreAML.tr ⟨tbl, []⟩ (clauseRight c fn cl)).interpret I e m ∧
          (cl.post.isTop = false →
            (KoreAML.tr ⟨tbl, []⟩ (Cond.kore c (canonVars c cl.vars) (srtOf c fn.result) cl.post)).interpret I e m) := by
    intro tbl e m
    unfold clauseRhsBody clauseRight
    rw [interp_and (by simp), tr_and2, KoreAML.interp_sAnd]
    constructor
    · intro hq
      refine ⟨⟨hq _ (by simp), hq _ (by simp)⟩, fun hpt => hq _ (by simp [Cond.conj, hpt])⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩ q hq
      rcases List.mem_append.mp hq with hq | hq
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl
        · exact h1
        · exact h2
      · have hq' := Model.mem_condConj hq
        subst hq'
        refine h3 ?_
        cases hpt : cl.post.isTop with
        | false => rfl
        | true => simp [Cond.conj, hpt] at hq
  refine clause_den_exCore hI hnn hsc hph hfn hcl hws hσ₀ hmatch0 hpats hpreOK hokQ hne hlt hnd hocc hreqv hrhsv hensv hr
    ihreq ihpre hlow ?_ ?_ e m
  · -- the instance at σ₀ gives what `r` denotes
    intro tbl e hag hkeys hkB m hm
    cases r with
    | none => exact hm.elim
    | some v =>
      obtain ⟨hrhs, hrhsT, hensT, hpost⟩ := hgive0 v rfl
      have hmS : InS I (c.sortName fn.result) m := by
        have hsp := elemOf_spec hI (hr v rfl) e
        rw [(hsp.1 m).mp hm]
        exact (inS_iff e).mp hsp.2
      refine hbody.mpr ⟨(right_iff hI hnn hfnm hr
        (fun m' => allOf hrhsT hσ₀ hag hkeys hrhss m')
        (fun t ht m' => allOf (hensT t ht) hσ₀ hag hkeys (henss t ht) m') m).mpr hm, fun _ => ?_⟩
      have hrd := reads_of_agrees hσ₀ hag (P := fun i => i ∈ varOccsCond cl.vars.length cl.post)
        fun i hi => ⟨varOccsCond_lt_twoT cl.post hokQ i hi, hkeys i (varOccsCond_lt_twoT cl.post hokQ i hi)⟩
      exact (CE.holdsReadT_holdsAt_bound (Semantics.coreOK_iff_ex.mpr h) hrc hIc N hpost rfl hokQ hb
        (fun i hi _ => hi) hrd (hkQ hkB) hS m (hinSort hmS)).mpr rfl
  · -- an instance at elements that holds `m` is one at values, which gives `r` or nothing
    intro tbl e hag hkeys hkB e'' m hoff hin hmS hb''
    obtain ⟨hR, hQ⟩ := hbody.mp hb''
    have hkey : ∀ i, i < cl.vars.length → i ∉ cl.exs →
        e''.evalEvar (tbl.ev (canonKey c cl.vars i)) = e.evalEvar (tbl.ev (canonKey c cl.vars i)) := fun i hi hx =>
      hoff _ fun j hj he => hx ((canonKey_inj hi (hlt j hj) (ev_inj (hkeys i hi) (hkeys j (hlt j hj)) he)) ▸ hj)
    -- `post` holds at the instance
    have hpostE : (KoreAML.tr ⟨tbl, []⟩ (Cond.kore c (canonVars c cl.vars) (srtOf c fn.result) cl.post)).interpret I e'' m := by
      cases hpt : cl.post.isTop with
      | false => exact hQ hpt
      | true =>
        have hrd : Reads c I cl.vars (fun i => i ∈ varOccsCond cl.vars.length cl.post) σ₀ tbl e'' := fun i hi => by
          rw [Cond.eq_top_of_isTop hpt] at hi; simp [varOccsCond] at hi
        have hpT : HoldsAtB (Cond.bound c) c I cl.vars.length σ₀ cl.post true := by
          rw [Cond.eq_top_of_isTop hpt]; exact holdsAt_top N
        exact (hpT rfl hokQ hb (fun i hi _ => hi) hrd (hkQ hkB) hS m (hinSort hmS)).mpr rfl
    have hwit := CE.exs_values_hrCEx h hrc hIc N hs hb hp (σ := σ₀) (hσ₀.at _) ⟨σ₀, AgreeOff.refl _ _, hσ₀⟩
      (fun σ' ha hw => (hall0 σ' (hfreeF ▸ ha) hw).post)
      (tbl := tbl) (e := e'') (S := fn.result)
      (fun i hi v hv m' => by
        have hiu := List.mem_filter.mp hi
        have hil : i < cl.vars.length := List.mem_range.mp hiu.1
        have hix : i ∉ cl.exs := by simpa using hiu.2
        show m' = e''.evalEvar (tbl.ev (canonKey c cl.vars i)) ↔ _
        rw [hkey i hil hix]
        exact (hag i v (by rw [canonVars_length]; exact hil) hv m').trans ((den_closed c v).interp e e'' m'))
      (fun i hi s hs'' => by
        have hil := hlt i hi
        rw [hsj i hil] at hs''
        cases hs''
        exact (inS_iff e'').mpr (hin i hi))
      (fun j hj => hkeys j hj) (hkQ hkB) hS ⟨m, hinSort hmS, hpostE⟩
    obtain ⟨σ', hao, hw', hag'⟩ := subst_of_witnessedEx hI hg hsc.trans hlt hσ₀ hkeys hag hoff hwit
    cases hall0 σ' hao hw' with
    | fails hp' hf =>
      exfalso
      cases hf with
      | ens ht he hTe hw =>
        exact (right_empty hI hnn hfnm ht hw (fun v hv => EvalTerm.sorted hsc he fns_headsOK hw' (henss _ ht) hv)
          (fun m' => allOf hTe hw' hag' hkeys (henss _ ht) m') m).mp hR
      | post hf' =>
        cases hpt : cl.post.isTop with
        | true =>
          have hf'' := hf'.holds
          rw [Cond.eq_top_of_isTop hpt] at hf''
          exact absurd hf''.top_eq (by simp)
        | false =>
          have hrd := reads_of_agrees hw' hag' (P := fun i => i ∈ varOccsCond cl.vars.length cl.post)
            fun i hi => ⟨varOccsCond_lt_twoT cl.post hokQ i hi, hkeys i (varOccsCond_lt_twoT cl.post hokQ i hi)⟩
          exact absurd ((CE.holdsReadT_holdsAt_bound (Semantics.coreOK_iff_ex.mpr h) hrc hIc N hf' rfl hokQ hb
            (fun i hi _ => hi) hrd (hkQ hkB) hS m (hinSort hmS)).mp (hQ hpt))
            (by simp)
      | rhs hn hTn =>
        unfold clauseRight at hR
        rw [tr_and2, KoreAML.interp_sAnd] at hR
        exact (allOf hTn hw' hag' hkeys hrhss m).mp hR.1
    | gives hrhs hrhsT _ _ =>
      unfold clauseRight at hR
      rw [tr_and2, KoreAML.interp_sAnd] at hR
      exact (Res_closed _ e'' e m).mp ((allOf hrhsT hw' hag' hkeys hrhss m).mp hR.1)

open HoldsShape in
/-- `eval_den_ex` for a semantics `coreOKEx` accepts. -/
theorem eval_den_exCEx (h : c.coreOKEx = true) (hrc : c.readsConfined = true) (hIc : I ⊧ᴵP Γc c)
    (hT : HoldsShape.TermSound c I)
    {f : Sym} {fn : Fn} {cl : Clause} {ws : List GroundTerm} {σ : Subst} {r : Option GroundTerm}
    (hfn : c.lookupFn f = some fn) (hcl : cl ∈ fn.clauses) (hws : c.sortsOf ws = some fn.args)
    (hpats : sortsOfTerms c.patCtxAll cl.vars cl.pats = some fn.args)
    (hpreOK : c.condOK cl.vars cl.pre = true)
    (hs : c.clauseExOK cl = true) (hb : Cond.bound c cl.vars.length cl.post = true)
    (hp : c.clausePlainEx cl = true) (hne : cl.exs ≠ [])
    (hocc : ∀ i < cl.vars.length, i ∈ cl.exs ∨ i ∈ varOccsList cl.pats ++ cl.condVars ++ varOccs cl.rhs ++
      (cl.ens.map varOccs).getD [] ++ varOccsCond cl.vars.length cl.post)
    (hreqs : ∀ t, cl.req = some t → sortOfTerm (c.rhsCtx (c.fns.map Fn.sig)) cl.vars t = some Srt.bool)
    (hrhss : sortOfTerm (c.rhsCtx (c.fns.map Fn.sig)) cl.vars cl.rhs = some fn.result)
    (henss : ∀ t, cl.ens = some t → sortOfTerm (c.rhsCtx (c.fns.map Fn.sig)) cl.vars t = some Srt.bool)
    (hpreR : cl.pre ≠ .top → PreRead c I cl)
    (hmatch : PatVals c σ cl.pats ws)
    (hreq : ∀ t, cl.req = some t → EvalTerm c σ t (some (bool true)))
    (hpre : Holds c cl.vars.length σ cl.pre true)
    (hlow : ∀ cl' ∈ fn.clauses, cl'.aside = false → cl'.prio < cl.prio →
      c.condOK cl'.vars cl'.pre = true ∧ sortsOfTerms c.patCtxAll cl'.vars cl'.pats = some fn.args ∧
      (∀ t, cl'.req = some t → ∀ i ∈ varOccs t, i < cl'.vars.length) ∧
      ExclEmptyCl c I fn cl' ∧ Fails c ws cl' ∧ ModelFailsCl c I cl' ws)
    (hsome : ∃ σ', AgreeOff cl.exsFree σ σ' ∧ c.WellSorted cl.vars σ')
    (hall : ∀ σ', AgreeOff cl.exsFree σ σ' → c.WellSorted cl.vars σ' → InstIs c σ' cl r)
    (hgv : ∀ v, r = some v → ∃ σ', AgreeOff cl.exsFree σ σ' ∧ c.WellSorted cl.vars σ' ∧ cl.Gives c σ' v)
    (e : Valuation M) (m : M) :
    (KoreAML.den (symApp c f (GroundTerm.koreList c ws))).interpret I e m ↔ Res c I e r m := by
  have F : AtomFacts c I := atomFacts_of_coreEx h hIc hT
  have hfree : cl.exsFree = cl.exs := by
    have hs' := hs
    simp only [Semantics.clauseExOK, Bool.and_eq_true] at hs'
    exact List.filter_eq_self.mpr fun i hi => List.all_eq_true.mp hs'.1.2 i hi
  -- an instance, the one that gives `v` where `r` is `some v`
  obtain ⟨σ₀, hag0, hσ₀, hgive0⟩ : ∃ σ₀, AgreeOff cl.exsFree σ σ₀ ∧ c.WellSorted cl.vars σ₀ ∧
      ∀ v, r = some v → cl.Gives c σ₀ v := by
    cases r with
    | none =>
      obtain ⟨σ₀, h1, h2⟩ := hsome
      exact ⟨σ₀, h1, h2, fun v hv => by cases hv⟩
    | some v =>
      obtain ⟨σ₀, h1, h2, h3⟩ := hgv v rfl
      exact ⟨σ₀, h1, h2, fun v' hv' => by cases hv'; exact h3⟩
  -- the left side reads σ₀ as it reads σ
  have hl : ∀ i ∈ cl.leftVars, σ₀.lookup i = σ.lookup i := fun i hi =>
    hag0 i (by simp [Clause.exsFree, hi])
  have hmatch0 : PatVals c σ₀ cl.pats ws :=
    PatVals.congr_lookup hmatch fun j hj => hl j (List.mem_append_left _ hj)
  have hreq0 : ∀ t, cl.req = some t → EvalTerm c σ₀ t (some (bool true)) := fun t ht =>
    Exec.EvalTerm.congr (hreq t ht) fun i hi => (hl i (Clause.req_leftVars ht i hi)).symm
  have hpre0 : Holds c cl.vars.length σ₀ cl.pre true :=
    Holds.congr_NI hpre fun j hj => (hl j (Clause.pre_leftVarsRH j hj)).symm
  have hall0 : ∀ σ', AgreeOff cl.exs σ₀ σ' → c.WellSorted cl.vars σ' → InstIs c σ' cl r := fun σ' ha hw =>
    hall σ' (hag0.trans (hfree ▸ ha)) hw
  have HD : ∀ p : Cond, HoldsDenB (Cond.bound c) c I p := fun p =>
    CE.holds_den_bound (Semantics.coreOK_iff_ex.mpr h) hIc F p fun _ => hrc
  exact eval_den_exReadCEx h hrc hIc hfn hcl hws hpats hpreOK hs hb hp hne hocc hreqs hrhss henss hσ₀ hmatch0
    (fun t ht tbl e' hag m' => hT (hreq0 t ht) hσ₀ (canonVars_length c cl.vars) hag (hreqs t ht) m')
    (fun hpt tbl e' σr m0 hag hkp hRk hRv hσr hm0 =>
      (preRead_agreesCl (hpreR (ne_top_of_isTop_false hpt)) hpreOK
        (HoldsAtB.mono (Cond.bound_of_boundConf c _) (holdsAt_of_den (HD _) hpre0)) hσ₀ hag hkp hRk hRv hσr hm0).mpr rfl)
    hlow (fun σ' ha hw => InstIsRead.of_instIs F (hall0 σ' ha hw))
    (fun v hv => by
      obtain ⟨hrhs, hens, hpost⟩ := hgive0 v hv
      exact ⟨hrhs, F.termAt hrhs, fun t ht => F.termAt (hens t ht), HoldsReadT.of_holds F.termAt _ hpost⟩) e m

/-- `eval_den_clauseEx` for a semantics `coreOKEx` accepts. -/
theorem eval_den_clauseExCEx (h : c.coreOKEx = true) (hrc : c.readsConfined = true) (hIc : I ⊧ᴵP Γc c)
    (hT : HoldsShape.TermSound c I)
    {f : Sym} {fn : Fn} {cl : Clause} {ws : List GroundTerm} {σ : Subst} {v : GroundTerm}
    (hfn : c.lookupFn f = some fn) (hcl : cl ∈ fn.clauses) (hws : c.sortsOf ws = some fn.args)
    (hpats : sortsOfTerms c.patCtxAll cl.vars cl.pats = some fn.args)
    (hpreOK : c.condOK cl.vars cl.pre = true)
    (hs : c.clauseExOK cl = true) (hb : Cond.bound c cl.vars.length cl.post = true)
    (hp : c.clausePlainEx cl = true)
    (hocc : ∀ i < cl.vars.length, i ∈ cl.exs ∨ i ∈ varOccsList cl.pats ++ cl.condVars ++ varOccs cl.rhs ++
      (cl.ens.map varOccs).getD [] ++ varOccsCond cl.vars.length cl.post)
    (hreqs : ∀ t, cl.req = some t → sortOfTerm (c.rhsCtx (c.fns.map Fn.sig)) cl.vars t = some Srt.bool)
    (hrhss : sortOfTerm (c.rhsCtx (c.fns.map Fn.sig)) cl.vars cl.rhs = some fn.result)
    (henss : ∀ t, cl.ens = some t → sortOfTerm (c.rhsCtx (c.fns.map Fn.sig)) cl.vars t = some Srt.bool)
    (hpreR : cl.pre ≠ .top → HoldsShape.PreRead c I cl)
    (hlow : ∀ cl' ∈ fn.clauses, cl'.aside = false → cl'.prio < cl.prio →
      c.condOK cl'.vars cl'.pre = true ∧ sortsOfTerms c.patCtxAll cl'.vars cl'.pats = some fn.args ∧
      (∀ t, cl'.req = some t → ∀ i ∈ varOccs t, i < cl'.vars.length) ∧
      ExclEmptyCl c I fn cl' ∧ Fails c ws cl' ∧ ModelFailsCl c I cl' ws)
    (hσ : c.WellSorted cl.vars σ) (hmatch : PatVals c σ cl.pats ws)
    (hreq : ∀ t, cl.req = some t → EvalTerm c σ t (some (bool true)))
    (hpre : Holds c cl.vars.length σ cl.pre true) (hne : cl.exs ≠ [])
    (hrhs : EvalTerm c σ cl.rhs (some v))
    (hens : ∀ t, cl.ens = some t → EvalTerm c σ t (some (bool true)))
    (hpost : Holds c cl.vars.length σ cl.post true)
    (hall : ∀ σ', AgreeOff cl.exsFree σ σ' → c.WellSorted cl.vars σ' → InstIs c σ' cl (some v))
    (e : Valuation M) (m : M) :
    (KoreAML.den (symApp c f (GroundTerm.koreList c ws))).interpret I e m ↔ (den c v).interpret I e m :=
  eval_den_exCEx h hrc hIc hT hfn hcl hws hpats hpreOK hs hb hp hne hocc hreqs hrhss henss hpreR hmatch hreq hpre hlow
    ⟨σ, AgreeOff.refl _ _, hσ⟩ hall
    (fun v' hv' => by cases hv'; exact ⟨σ, AgreeOff.refl _ _, hσ, hrhs, hens, hpost⟩) e m

/-- `eval_den_exNone` for a semantics `coreOKEx` accepts. -/
theorem eval_den_exNoneCEx (h : c.coreOKEx = true) (hrc : c.readsConfined = true) (hIc : I ⊧ᴵP Γc c)
    (hT : HoldsShape.TermSound c I)
    {f : Sym} {fn : Fn} {cl : Clause} {ws : List GroundTerm} {σ : Subst}
    (hfn : c.lookupFn f = some fn) (hcl : cl ∈ fn.clauses) (hws : c.sortsOf ws = some fn.args)
    (hpats : sortsOfTerms c.patCtxAll cl.vars cl.pats = some fn.args)
    (hpreOK : c.condOK cl.vars cl.pre = true)
    (hs : c.clauseExOK cl = true) (hb : Cond.bound c cl.vars.length cl.post = true)
    (hp : c.clausePlainEx cl = true)
    (hocc : ∀ i < cl.vars.length, i ∈ cl.exs ∨ i ∈ varOccsList cl.pats ++ cl.condVars ++ varOccs cl.rhs ++
      (cl.ens.map varOccs).getD [] ++ varOccsCond cl.vars.length cl.post)
    (hreqs : ∀ t, cl.req = some t → sortOfTerm (c.rhsCtx (c.fns.map Fn.sig)) cl.vars t = some Srt.bool)
    (hrhss : sortOfTerm (c.rhsCtx (c.fns.map Fn.sig)) cl.vars cl.rhs = some fn.result)
    (henss : ∀ t, cl.ens = some t → sortOfTerm (c.rhsCtx (c.fns.map Fn.sig)) cl.vars t = some Srt.bool)
    (hpreR : cl.pre ≠ .top → HoldsShape.PreRead c I cl)
    (hlow : ∀ cl' ∈ fn.clauses, cl'.aside = false → cl'.prio < cl.prio →
      c.condOK cl'.vars cl'.pre = true ∧ sortsOfTerms c.patCtxAll cl'.vars cl'.pats = some fn.args ∧
      (∀ t, cl'.req = some t → ∀ i ∈ varOccs t, i < cl'.vars.length) ∧
      ExclEmptyCl c I fn cl' ∧ Fails c ws cl' ∧ ModelFailsCl c I cl' ws)
    (hne : cl.exs ≠ []) (hmatch : PatVals c σ cl.pats ws)
    (hreq : ∀ t, cl.req = some t → EvalTerm c σ t (some (bool true)))
    (hpre : Holds c cl.vars.length σ cl.pre true)
    (hsome : ∃ σ', AgreeOff cl.exsFree σ σ' ∧ c.WellSorted cl.vars σ')
    (hall : ∀ σ', AgreeOff cl.exsFree σ σ' → c.WellSorted cl.vars σ' → InstIs c σ' cl none)
    (e : Valuation M) (m : M) :
    ¬ (KoreAML.den (symApp c f (GroundTerm.koreList c ws))).interpret I e m :=
  (eval_den_exCEx h hrc hIc hT hfn hcl hws hpats hpreOK hs hb hp hne hocc hreqs hrhss henss hpreR hmatch hreq hpre hlow
    hsome hall (fun v' hv' => by cases hv') e m).mp

end

section
variable {c : Semantics}

/-- `clause_ctxOccE` for a semantics `coreOKEx` accepts. -/
theorem clause_ctxOccECEx (hok : c.sortedOKEx = true) {fn : Fn} (hfn : fn ∈ c.allFns) {cl : Clause} (hcl : cl ∈ fn.clauses) :
    sortsOfTerms c.patCtxAll cl.vars cl.pats = some fn.args ∧
      (∀ i < cl.vars.length, i ∈ varOccsList cl.pats ++ cl.condVars ++ varOccs cl.rhs ++
        (cl.ens.map varOccs).getD [] ++ varOccsCond cl.vars.length cl.post) ∧
      ∃ L, HeadsOK c L ∧ (∀ t, cl.req = some t → sortOfTerm (c.rhsCtx L) cl.vars t = some Srt.bool) ∧
        sortOfTerm (c.rhsCtx L) cl.vars cl.rhs = some fn.result ∧
        (∀ t, cl.ens = some t → sortOfTerm (c.rhsCtx L) cl.vars t = some Srt.bool) := by
  rcases List.mem_append.mp hfn with hu | hp
  · replace hok := Semantics.sortedOKEx_sorted hok
    simp only [Bool.and_eq_true, List.all_eq_true] at hok
    have h2 := hok.1.2 fn hu cl hcl
    simp only [Semantics.clauseSorted, Bool.and_eq_true, beq_iff_eq] at h2
    replace h2 := h2.1
    obtain ⟨⟨⟨⟨⟨hpats, hb⟩, hreq⟩, hrhs⟩, hens⟩, -⟩ := h2
    refine ⟨sortsOfTerms_all_of_nf hpats, fun i hi => ?_, c.fns.map Fn.sig, fun k hk => ?_, fun t ht => ?_, hrhs, fun t ht => ?_⟩
    · simp only [binds, List.all_eq_true, List.mem_range, List.contains_iff_mem] at hb
      exact hb i hi
    · obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hk
      exact ⟨g, List.mem_append_left _ hg, rfl⟩
    · rw [ht] at hreq
      simpa [reqOK] using hreq
    · rw [ht] at hens
      simpa [reqOK] using hens
  · obtain ⟨hpats, -, hb, hreq, hrhs, hens⟩ := sortPreds_ctx hp cl hcl
    refine ⟨sortsOfTerms_heads c.patCtx (c.collPatSigs ++ c.ovlSigs) cl.vars cl.pats hpats, fun i hi => ?_, [],
      fun k hk => absurd hk List.not_mem_nil, fun t ht => ?_, hrhs, fun t ht => ?_⟩
    · simp only [binds, List.all_eq_true, List.mem_range, List.contains_iff_mem] at hb
      exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
        (List.mem_append_left _ (hb i hi))))
    · rw [ht] at hreq
      simpa [reqOK] using hreq
    · rw [ht] at hens
      simpa [reqOK] using hens

/-- **`sortedOKEx` gives `ClauseOpenFactsQ` of every clause of every function** (the user's and the
sort predicates'). -/
theorem clauseOpenFactsQ_of_sortedOKEx (hok : c.sortedOKEx = true) :
    ∀ fn ∈ c.allFns, ∀ cl ∈ fn.clauses, ∃ L, HeadsOK c L ∧ ClauseOpenFactsQ c fn L cl := by
  intro fn hfn cl hcl
  obtain ⟨hpats, hbinds, L, hL, hreqs, hrhss, henss⟩ := clause_ctxOccECEx hok hfn hcl
  have hpp : c.condOK cl.vars cl.pre = true ∧ (cl.exs = [] → cl.post = .top) := by
    rcases List.mem_append.mp hfn with hu | hp
    · exact ⟨(Semantics.sortedOKEx_clausePre hok hu hcl).1, Semantics.sortedOKEx_post_of_nil hok hu hcl⟩
    · obtain ⟨hpre, hpost⟩ := sortPreds_topCl hp cl hcl
      exact ⟨by rw [hpre, Semantics.condOK], fun _ => hpost⟩
  exact ⟨L, hL, hpats, hpp.1, hpp.2, hbinds, hreqs, hrhss, henss⟩

end

section
variable {c : Semantics} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}

/-- **Every clause with existential variables has `ClauseExRead`**, in a model of `Γc` of a
definition `coreOKEx` accepts that reads confined sorts: `eval_den_exReadCEx` with the clause's
facts from `sortedOKEx` (`clauseSorted`, `clausePlainEx`, `clauseExOK`); the existential variables
being outside the left side (`clauseExOK`), those an instance varies are all of them. The sort
predicates' clauses have none. -/
theorem clauseExRead_of_coreEx (h : c.coreOKEx = true) (hrc : c.readsConfined = true) (hIc : I ⊧ᴵP Γc c) :
    ∀ fn ∈ c.allFns, ∀ cl ∈ fn.clauses, cl.exs ≠ [] → ClauseExRead c I fn cl := by
  intro fn hfn cl hcl hne
  rcases List.mem_append.mp hfn with hu | hp
  rotate_left
  · exact absurd (Semantics.sortPreds_exs hp cl hcl) hne
  have hok := (Semantics.coreOKEx_parts h).1
  have hsrt := (Semantics.sortedOKEx_parts hok).2.1 fn hu cl hcl
  obtain ⟨hpats, hocc, hreqs, hrhss, henss⟩ :=
    Semantics.clauseSortedOpen_parts (Semantics.clauseSortedOpen_of_sorted hsrt)
  have hb : Cond.bound c cl.vars.length cl.post = true := by
    simp only [Semantics.clauseSorted, Bool.and_eq_true] at hsrt
    exact hsrt.1.2.2
  have hpreOK := (Semantics.sortedOKEx_clausePre hok hu hcl).1
  obtain ⟨hp, hs, -, -⟩ := Semantics.clausesPlainEx_spec (Semantics.sortedOKEx_parts hok).2.2.2.2.1 hu hcl
  have hfree : cl.exsFree = cl.exs := by
    have hs' := hs
    simp only [Semantics.clauseExOK, Bool.and_eq_true] at hs'
    exact List.filter_eq_self.mpr fun i hi => List.all_eq_true.mp hs'.1.2 i hi
  intro f ws σ₀ r hfn' hws hσ₀ hmatch ihreq ihpre hlow hall0 hgive0 e m
  exact eval_den_exReadCEx h hrc hIc hfn' hcl hws hpats hpreOK hs hb hp hne (fun i hi => Or.inr (hocc i hi))
    hreqs hrhss henss hσ₀ hmatch ihreq ihpre hlow (fun σ' ha hw => hall0 σ' (hfree ▸ ha) hw) hgive0 e m

end

end Faithful

end KCore
