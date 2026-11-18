/-
  KCore. Every model of `Γc` of a definition `coreOK` accepts has the facts the Holds lemma reads:
  the atoms' facts given the soundness of `EvalTerm` (`atomFacts_of_core`), which holds under the
  clause hypothesis of `sound_at` (`termSound_of_core`, ClausePreCore.lean), and the binders' fact where the definition
  reads confined sorts (`binderFacts_of_core`; the reading of a pattern, `patReading_of_core`, asks
  `coreOK` alone).
-/
import KcoreSpec.HoldsFacts
import KcoreSpec.OpenClauseFn

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace KCore

open ML Faithful

namespace HoldsShape

section Core
variable {c : Semantics} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}

/-- **A model of `Γc` of a definition `coreOK` accepts has the atoms' facts**, given the soundness of
`EvalTerm`. -/
theorem atomFacts_of_core (h : c.coreOK = true) (hIc : I ⊧ᴵP Γc c) (hT : TermSound c I) :
    AtomFacts c I := by
  have htn : ∀ {vars : List Srt} {t : Term} {s : Srt}, sortOfTerm (c.rhsCtx (c.fns.map Fn.sig)) vars t = some s →
      (∀ i ∈ varOccs t, ∀ s', vars[i]? = some s' → s' < nRegSorts + c.sortNames.length) →
      s < nRegSorts + c.sortNames.length := fun {vars t s} ht hv =>
    sortOfTerm_numbered (sortOf_numbered_of (hypSound_of_core h) (sortsNumbered_of_core h) (Semantics.coreOK_ovls h)) (sortsNumbered_of_core h) (Semantics.coreOK_ovls h)
      (fun k hk => Model.rhsHead_kernel fns_headsOK hk) (fun _ _ h' => h') rfl t ht hv
  have hvn : ∀ {v : GroundTerm} {s : Srt}, c.sortOf v = some s → s < nRegSorts + c.sortNames.length :=
    fun hv => sortOf_numbered_of (hypSound_of_core h) (sortsNumbered_of_core h) (Semantics.coreOK_ovls h) hv
  have hI : I ⊧ᴵP Γ c := fun φ hφ => hIc φ (Or.inl hφ)
  obtain ⟨hok, hsr, hnn, hg, hph, hcso, hcs, hph', hno⟩ := hypSound_of_core h
  haveI : OvlOK c := hno
  have hsc := sortCtx_of_all hok hsr (OvlOK.ovlCase hno)
  refine ⟨defOK hI, sat_sigItem hI (by simp [sigItems]), fun {s} hs => ?_, fun {v s} hv tbl e => ?_,
    fun {v w s} hv hw e a h1 h2 => ?_, termSoundAt_of hI hT, hsc, htn, hvn⟩
  · obtain ⟨τ, hτ, hτs⟩ := sortSing hI hs
    exact ⟨τ, hτs, fun tbl e a => by unfold srtOf; rw [trSort_srt]; exact hτ a⟩
  · refine ⟨elemOf c I v, (elemOf_spec hI hv e).1, ?_⟩
    have := (elemOf_spec hI hv e).2
    unfold srtOf; rw [trSort_srt]; exact this
  · exact values_apart hI hg hsc.trans (apartSort_of_sorted hg hv) hv hw
      (((elemOf_spec hI hv e).1 a).mp h1 ▸ ((elemOf_spec hI hw e).1 a).mp h2 ▸ rfl)

/-- **A model of `Γc` of a definition `coreOK` accepts reads a pattern at a value's element**: downwards
by `patVal_backC`, upwards by `patVal_den4`, each at the valuation that gives a variable the pattern
does not hold the sort Bool and `true`'s element. -/
theorem patReading_of_core (h : c.coreOK = true) (hIc : I ⊧ᴵP Γc c) : PatReading c I := by
  have hI : I ⊧ᴵP Γ c := fun φ hφ => hIc φ (Or.inl hφ)
  obtain ⟨hok, hsr, hnn, hg, hph, hcso, hcs, hph', hno⟩ := hypSound_of_core h
  haveI : OvlOK c := hno
  have hsc := sortCtx_of_all hok hsr (OvlOK.ovlCase hno)
  intro vars p s w tbl e hpSN hw hin m hm
  have hpS := sortOfTerm_all_of_nf hpSN
  classical
  have hmw : m = elemOf c I w := ((elemOf_spec hI hw e).1 m).mp hm
  subst hmw
  let v0 : GroundTerm := bool true
  let vars' : List Srt := (List.range vars.length).map fun i => if i ∈ varOccs p then vars.getD i 0 else Srt.bool
  let e1 := fillV c tbl vars (varOccs p) (elemOf c I v0) e
  have hlen : vars'.length = vars.length := by simp [vars']
  have hl : ∀ i ∈ varOccs p, i < vars.length := varOccs_lt p hpS
  have hkeys : ∀ i < vars.length, i ∈ varOccs p → canonKey c vars i ∈ tbl := fun i _ hi => (hin i hi).1
  have hget? : ∀ i < vars.length, vars'[i]? = some (if i ∈ varOccs p then vars.getD i 0 else Srt.bool) := by
    intro i hi; simp [vars', hi]
  have hpS' : sortOfTerm c.patCtxAll vars' p = some s := by
    rw [sortOfTerm_congr p fun i hi => ?_]; exact hpS
    rw [hget? i (hl i hi), if_pos hi, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (hl i hi)]; rfl
  have hpSN' : sortOfTerm c.patCtxNF vars' p = some s := by
    rw [sortOfTerm_congr p fun i hi => ?_]; exact hpSN
    rw [hget? i (hl i hi), if_pos hi, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (hl i hi)]; rfl
  have hvsl : (canonVars c vars).length = vars'.length := by rw [canonVars_length, hlen]
  have hoff : ∀ i ∈ varOccs p, e.evalEvar (tbl.ev (keyAt (canonVars c vars) i)) =
      e1.evalEvar (tbl.ev (keyAt (canonVars c vars) i)) := fun i hi =>
    (fillV_off (a := elemOf c I v0) (e := e) hkeys (hl i hi) hi).symm
  have hin' : ∀ i < vars'.length, InS I (c.sortName (vars'.getD i 0))
      (e1.evalEvar (tbl.ev (keyAt (canonVars c vars) i))) := by
    intro i hi
    rw [hlen] at hi
    rw [List.getD_eq_getElem?_getD, hget? i hi]
    by_cases hio : i ∈ varOccs p
    · rw [if_pos hio, Option.getD_some, ← hoff i hio]
      exact inhOf_srtOf_inS.mp (hin i hio).2
    · rw [if_neg hio, Option.getD_some]
      show InS I _ (e1.evalEvar (tbl.ev (canonKey c vars i)))
      rw [fillV_on hi hio]
      exact (inS_iff e1).mp (elemOf_spec hI (sortOf_bool true) e1).2
  have hpc := collPat_of_sorted hph' hpS'
  constructor
  · intro hpm
    have hpm1 := (tr_kore_congr p hoff _).mp hpm
    obtain ⟨hpv, hwit⟩ := patVal_backC hI hph hcs hcso hg hsc.trans hnn.1 hvsl hin' hpc hpSN' hw hpm1
    refine ⟨_, hpv, fun i hi => ?_⟩
    obtain ⟨v, hsv, hev⟩ := hwit i hi
    have hgi : vars'.getD i 0 = vars.getD i 0 := by
      rw [List.getD_eq_getElem?_getD, hget? i (hl i hi), if_pos hi]; rfl
    rw [hgi] at hsv
    refine ⟨v, substOf_var hI hg hsc.trans hnn.1 hvsl hin' (by rw [hget? i (hl i hi), if_pos hi]) hsv hev, hsv,
      fun m' => ?_⟩
    rw [(elemOf_spec hI hsv e).1 m', hev, ← hoff i hi]; rfl
  · rintro ⟨σ', hpv, hwit⟩
    let f : Nat → GroundTerm := fun i => if i ∈ varOccs p then (σ'.lookup i).getD v0 else v0
    let σ'' : Subst := (List.range vars.length).map fun j => (j, f j)
    have hσ''i : ∀ i < vars.length, σ''.lookup i = some (f i) := fun i hi => lookup_tab f _ i (List.mem_range.mpr hi)
    have hcong : ∀ i ∈ varOccs p, σ''.lookup i = σ'.lookup i := fun i hi => by
      obtain ⟨v, hv, -, -⟩ := hwit i hi
      rw [hσ''i i (hl i hi), hv]; simp [f, hi, hv]
    have hσ : c.WellSorted vars' σ'' := by
      intro i s' hs'
      have hli : i < vars.length := by rw [← hlen]; exact (List.getElem?_eq_some_iff.mp hs').1
      refine ⟨f i, hσ''i i hli, ?_⟩
      rw [hget? i hli] at hs'
      cases hs'
      by_cases hio : i ∈ varOccs p
      · obtain ⟨v, hv, hsv, -⟩ := hwit i hio
        simp [f, hio, hv, hsv]
      · simp [f, hio]; exact sortOf_bool true
    have hag : Agrees c I tbl (canonVars c vars) σ'' e1 := by
      intro i v hi hv m'
      rw [canonVars_length] at hi
      rw [hσ''i i hi] at hv
      cases hv
      show m' = e1.evalEvar (tbl.ev (canonKey c vars i)) ↔ _
      by_cases hio : i ∈ varOccs p
      · obtain ⟨u, hu, -, hdu⟩ := hwit i hio
        rw [fillV_off hkeys hi hio]
        simp only [f, hio, ite_true, hu, Option.getD_some]
        exact ((hdu m').trans Iff.rfl).symm.trans ((den_closed c u).interp e e1 m')
      · rw [fillV_on hi hio]
        simp only [f, hio, ite_false]
        exact ((elemOf_spec hI (sortOf_bool true) e1).1 m').symm
    have hpv'' : PatVal c σ'' p w := Faithful.PatVal.congr_lookup hpv hcong
    have := (patVal_den4 hI hnn.1 hph hsc.trans hσ hvsl hag hpv'' hpSN').2 (elemOf c I w)
      |>.mpr (((elemOf_spec hI hw e1).1 _).mpr rfl)
    exact (tr_kore_congr p hoff _).mpr this

/-- A model of `Γc` of a definition that reads a confined sort has the binders' facts. -/
theorem binderFacts_of_core (h : c.coreOK = true) (hrc : c.readsConfined = true) (hIc : I ⊧ᴵP Γc c) :
    BinderFacts c I :=
  ⟨fun {s} hs tbl e a ha => confined_value h hrc hIc hs e a (by
    unfold srtOf at ha; rw [trSort_srt] at ha; exact ha),
   fun hs => confinedAt_numbered_ids (Semantics.coreOK_parts h).2.2.2.2 _ hs, patReading_of_core h hIc⟩

/-- `ceil` in every model of `Γc`, from the proof for every interpretation with the facts. -/
theorem holds_ceil_core (h : c.coreOK = true) (hIc : I ⊧ᴵP Γc c) (hT : TermSound c I)
    (s : Srt) (t : Term) : HoldsDen' c I (.ceil s t) :=
  holds_ceil' (atomFacts_of_core h hIc hT) s t

end Core

end HoldsShape

end KCore
