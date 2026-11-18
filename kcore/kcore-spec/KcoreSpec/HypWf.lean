/-
  KCore. What `coreOK` and `CoreObligations` give of a semantics: what step soundness reads
  (`hypSound_of_core`, from `coreOK` alone; with it every Range value is a KItem,
  `rangeBelow_of_core`), what the statements assume of the functions
  (`fnHyp_of_core`), what they assume (`hyp_of_fnHyp`, `hyp_of_core`), and what the existence of a
  model reads (`hypModel_of_fnHyp`, `hypModel_of_core`); the same from `wf` and `Obligations` for a
  definition's semantics (`hypSound_of`, `hyp_of`, `hypModel_of`), also for every interpretation
  of the parameter symbols (`hypModel_of_withHooks`).

  From `coreOK` the bundles are those over `sortedOK` (`HypSoundCore`, `HypCore`, `HypModelCore`);
  from `wf`, which checks `okAll`, the bundles over `okAll` (`HypSound`, `Hyp`, `HypModel`).

  The agreement of a function's equations and the match independence of its clauses (`Hyp`) come
  from `CoreObligations` for the functions and clauses it names, and from their deciders
  (`fnExclusiveOK`, `clauseFixed`) for the others. The deciders are sound for every pattern well
  sorted in a left-hand side's context (`patCtxAll`), which is what `sortedOK`, and so `coreOK`,
  checks of a clause (`clausesAgree_of_sortedOK`, `matchIndependentAll_of_sortedOK`).
-/
import KcoreSpec.ModelFns
import KcoreSpec.ModelUndefRhsWitness
import KcoreSpec.ModelJunkWitness
import KcoreSpec.ModelNamesWitness
import KcoreSpec.ModelDupCtorWitness
import KcoreSpec.ModelFnCtorWitness
import KcoreSpec.Totals
import KcoreSpec.FnExclusive
import KcoreSpec.RangeMapKeys

set_option autoImplicit false

namespace KCore

open ML Faithful Faithful.Model

/-! ## The deciders in a core that `okAll` accepts -/

/-- **Every clause is match independent** in a core that `sortedOK` and `matchReady` accept, given
the named obligations: a clause `clauseFixed` confirms by `clauseFixed_sound`, the others by their
obligation. -/
theorem matchIndependentAll_of_sortedOK {c : Semantics} (hok : c.sortedOK = true) (hmr : c.matchReady = true)
    (hob : MatchObligations c) : MatchIndependentAll c := by
  intro f fn hfn cl hcl
  obtain ⟨hmem, hlab⟩ := lookupFn_spec hfn
  obtain ⟨hpt, -, L, -, -, hrt, hens⟩ := Faithful.clause_ctxOccE hok hmem hcl
  cases hfx : c.clauseFixed cl with
  | true =>
    refine clauseFixed_sound (Exec.matchCtx_of hmr) hpt hrt ?_ hfx (Semantics.sortedOK_plainCl hok fn hmem cl hcl).1
    cases he : cl.ens with
    | none => rfl
    | some t => simpa [reqOK, he] using hens t he
  | false =>
    rcases List.mem_append.mp hmem with hf | hp
    · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hcl
      refine hob (fn.label, i) ?_ fn (by rw [hlab]; exact hfn) _ (List.getElem?_eq_getElem hi)
      simp only [Semantics.matchObligations, List.mem_flatMap, List.mem_map, List.mem_filter,
        List.mem_range, Prod.mk.injEq]
      refine ⟨fn, hf, i, ⟨hi, ?_⟩, rfl, rfl⟩
      simp [List.getElem?_eq_getElem hi, hfx, (Exec.matchCtx_of hmr).noOvl]
    · exact absurd (sortPreds_fixed hp cl hcl) (by rw [hfx]; decide)

/-- In a core that `sortedOK`, `srReady` and `matchReady` accept, each two equations of one
priority of each function are coherent: by `fnExclusiveOK_sound` where `fnExclusiveOK` confirms it,
and by the named obligation for the functions it does not (`agreeObligations`). -/
theorem clausesAgree_of_sortedOK {c : Semantics} (hok : c.sortedOK = true) (hsr : c.srReady = true)
    (hmr : c.matchReady = true)
    (hob : ∀ f ∈ c.agreeObligations, ∀ fn, c.lookupFn f = some fn → ClausesAgree c fn) :
    ∀ fn ∈ c.fns, ClausesAgree c fn := by
  intro fn hfn
  have hsc := sortCtx_of_all hok hsr (Exec.ovlCase_of hmr)
  by_cases hx : c.fnExclusiveOK (c.fns.map Fn.sig) fn = true
  · have hf := hok
    replace hf := Semantics.sortedOK_sorted hf
    simp only [Bool.and_eq_true, List.all_eq_true] at hf
    exact (Det.fnExclusiveOK_sound (Exec.matchCtx_of hmr) (fun _ _ => Det.ovlFreeList_of_nil (Exec.matchCtx_of hmr).noOvl _)
      (hf.1.2 fn hfn) (Semantics.fnsNoExs_of_sortedOK hok fn hfn) hx).agree (Semantics.fnsNoExs_of_sortedOK hok fn hfn)
  · refine hob fn.label ?_ fn ?_
    · simp only [Semantics.agreeObligations, List.mem_map, List.mem_filter]
      exact ⟨fn, ⟨hfn, by simpa [(Exec.matchCtx_of hmr).noOvl] using hx⟩, rfl⟩
    · rw [Semantics.lookupFn_eq]
      exact find?_label hsc.nodupFns (List.mem_append_left _ hfn)

theorem faithOK_parts {c : Semantics} (h : c.faithOK = true) :
    namesNumbered c = true ∧ genWf c = true ∧ collSortsOK c = true ∧ collsOK c = true ∧
    patHeadsOK c = true ∧ namesApartK c = true ∧ LitsApart c = true ∧ sortsNumbered c = true ∧
    collsNotCtors c = true ∧ itesApart c = true ∧ kindsApart c = true ∧ ctorsOnce c = true ∧
    fnsApart c = true := by
  simp only [Semantics.faithOK, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩

theorem faithCoreOK_parts {c : Semantics} (h : c.faithCoreOK = true) :
    namesNumbered c = true ∧ genWf c = true ∧ collSortsOK c = true ∧ collsOK c = true ∧
    patHeadsOK c = true ∧ namesApartK c = true ∧ LitsApart c = true ∧ sortsNumbered c = true ∧
    itesApart c = true ∧ kindsApart c = true ∧ ctorsOnce c = true ∧ fnsApart c = true := by
  simp only [Semantics.faithCoreOK, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h10⟩, h11⟩, h12⟩, h13⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h10, h11, h12, h13⟩

/-! ## What `coreOK` and `CoreObligations` give -/

section Core

variable {c : Semantics} {t : Certificates}

/-- Two numbered sorts of one name are one sort (`namesApartK`). -/
theorem sort_eq_of_name (hn : namesApartK c = true) {A B : Srt} (hA : A < nRegSorts + c.sortNames.length)
    (hB : B < nRegSorts + c.sortNames.length) (he : c.sortName A = c.sortName B) : A = B := by
  simp only [namesApartK, Bool.and_eq_true, List.all_eq_true] at hn
  have := hn.2 A (List.mem_range.mpr hA) B (List.mem_range.mpr hB)
  simpa [he] using this

/-- The sorts of a symbol with a signature are numbered (`sortsNumbered`). -/
theorem kernel_sort_lt (hs : sortsNumbered c = true) {k : CtorSig} (hk : k ∈ kernelSyms c) {s : Srt}
    (hsk : s ∈ k.result :: k.args) : s < nRegSorts + c.sortNames.length := by
  simp only [sortsNumbered, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hs
  exact hs.1.1.1 k hk s hsk

/-- What the readings of `Γ` take of the overloading symbols (`OvlOK`), from `coreOK`: `overloadsOK`,
the subsorts irreflexive (`NamesApart.subsorts_irrefl_of`), and the sorts of an overload numbered
under distinct names (`sortsNumbered`, `namesApartK`). -/
theorem ovlOK_of_core (h : c.coreOK = true) : OvlOK c := by
  obtain ⟨hok, hfa, -, -, hids⟩ := Semantics.coreOK_parts h
  obtain ⟨-, -, -, -, -, hn, -, hs, -, -, -, hfns⟩ := faithCoreOK_parts hfa
  refine ⟨Semantics.coreOK_ovls h, NamesApart.subsorts_irrefl_of hids hok, ?_,
    fnOvlSyms_nil_of_apart (Semantics.coreOK_ovls h) hfns⟩
  intro o ho kg hkg A hA B hB he
  have hkgk : kg ∈ kernelSyms c := by
    obtain ⟨g, -, hg⟩ := List.mem_filterMap.mp hkg
    rcases List.mem_append.mp (lookupSig_spec hg).1 with h1 | h1
    · rcases List.mem_append.mp h1 with h2 | h2
      · exact ctor_kernel h2
      · exact List.mem_append_right _ h2
    · obtain ⟨fn, hfn, rfl⟩ := List.mem_map.mp h1
      exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _
        (List.mem_map.mpr ⟨fn, List.mem_append_left _ hfn, rfl⟩))))
  have hok' : o.sig ∈ kernelSyms c := List.mem_append_right _ (List.mem_map_of_mem ho)
  exact sort_eq_of_name hn (kernel_sort_lt hs hkgk hA) (kernel_sort_lt hs hok' hB) he

/-- **What step soundness reads, from `coreOK`**: `sortedOK`, `srReady` (`NamesApart.srReady_of`),
the map pattern symbols apart from the constructors (`NamesApart.patHooks_of`), and the conditions
`faithCoreOK` decides. -/
theorem hypSound_of_core (h : c.coreOK = true) : HypSoundCore c := by
  obtain ⟨hok, hfa, hha, hp, hids⟩ := Semantics.coreOK_parts h
  obtain ⟨hnn, hg, hcso, hcs, hph, -⟩ := faithCoreOK_parts hfa
  refine ⟨hok, NamesApart.srReady_of hp hids hok
    (NamesApart.rangeKeys_genWf_of_faithCore (Semantics.coreOK_parts h).2.1) (Semantics.coreOK_ovls h), namesNumbered_spec hnn, hg, ?_, hcso, hcs, hph,
    ovlOK_of_core h⟩
  exact List.all_eq_true.mpr fun f hf => by
    simp [NamesApart.patHooks_of hha hids f hf]

/-- `RangeBelow`, from `coreOK`: every Range value of a semantics `coreOK` accepts is a KItem. -/
theorem rangeBelow_of_core (h : c.coreOK = true) : RangeBelow c :=
  rangeBelow_of_sound (hypSound_of_core h)

/-- A user function is the one `lookupFn` finds under its label (the labels are apart). -/
theorem lookupFn_of_core (h : c.coreOK = true) {fn : Fn} (hfn : fn ∈ c.fns) :
    c.lookupFn fn.label = some fn := by
  obtain ⟨hok, -, -, hp, hids⟩ := Semantics.coreOK_parts h
  have hsc := sortCtx_of_all hok (NamesApart.srReady_of hp hids hok
    (NamesApart.rangeKeys_genWf_of_faithCore (Semantics.coreOK_parts h).2.1) (Semantics.coreOK_ovls h)) (Semantics.ovlCase_of_core h)
  rw [Semantics.lookupFn_eq]
  exact find?_label hsc.nodupFns (List.mem_append_left _ hfn)

/-- With an overloading symbol, `agreeObligations` names every function. -/
theorem agree_mem_of_ovl {fn : Fn} (hno : c.ovls ≠ []) (hfn : fn ∈ c.fns) : fn.label ∈ c.agreeObligations := by
  simp only [Semantics.agreeObligations, List.mem_map, List.mem_filter]
  exact ⟨fn, ⟨hfn, by simp [List.isEmpty_iff, hno]⟩, rfl⟩

/-- With an overloading symbol, `matchObligations` names every clause. -/
theorem match_mem_of_ovl {fn : Fn} (hno : c.ovls ≠ []) (hfn : fn ∈ c.fns) {i : Nat} (hi : i < fn.clauses.length) :
    (fn.label, i) ∈ c.matchObligations := by
  simp only [Semantics.matchObligations, List.mem_flatMap, List.mem_map, List.mem_filter, List.mem_range,
    Prod.mk.injEq]
  exact ⟨fn, hfn, i, ⟨hi, by simp [List.isEmpty_iff, hno]⟩, rfl, rfl⟩

/-- **What the statements assume of the functions, from `coreOK` and `CoreObligations`**:
termination and totality by `CoreObligations.terminates` and `CoreObligations.totals`; the
agreement of the equations and the match independence of the clauses by their deciders and the
named obligations (all of them named where there is an overloading symbol, which the deciders' matcher
does not read) (`CoreObligations`' third and fourth conjuncts). Its last conjunct, the lazy
occurrences, is not read; its two last, `OpenDecided` and `OpenLaws`, are `FnHyp`'s. Termination
and totality read `hrh`: each clause variable the patterns and conditions do not hold is of a sort
with a value; and `hpreTop`: every clause's predicate is `\top` (the certificates read no call of
a predicate). -/
theorem fnHyp_of_core (h : c.coreOK = true) (hrh : c.RightHeld) (hob : CoreObligations c t) (hpreTop : c.clausesPreTop = true := by first | decide +kernel | (simp only [Semantics.clausesPreTop_withHooks]; decide +kernel) | exact rfl) : FnHyp c := by
  obtain ⟨hok, -, hha, hp, hids⟩ := Semantics.coreOK_parts h
  have hsr := NamesApart.srReady_of hp hids hok
    (NamesApart.rangeKeys_genWf_of_faithCore (Semantics.coreOK_parts h).2.1) (Semantics.coreOK_ovls h)
  have hmo : MatchObligations c := hob.2.2.2.1
  refine ⟨fun fn hfn vs hvs => ?_, fun fn hfn ht vs hvs => ?_, fun fn hfn => ?_, fun fn hfn cl hcl => ?_,
    hob.2.2.2.2.2.1, hob.2.2.2.2.2.2⟩
  · exact CoreObligations.terminates (hpreTop := hpreTop) h hrh hob fn.label fn
      (lookupFn_of_core h hfn) vs hvs
  · exact CoreObligations.totals (hpreTop := hpreTop) h hrh hob fn.label fn (lookupFn_of_core h hfn) ht fn
      (lookupFn_of_core h hfn) vs hvs
  · by_cases hno : c.ovls = []
    · exact clausesAgree_of_sortedOK hok hsr (NamesApart.matchReady_of hha hids hok hno) hob.2.2.1 fn hfn
    · exact hob.2.2.1 fn.label (agree_mem_of_ovl hno hfn) fn (lookupFn_of_core h hfn)
  · by_cases hno : c.ovls = []
    · exact matchIndependentAll_of_sortedOK hok (NamesApart.matchReady_of hha hids hok hno) hmo fn.label fn
        (lookupFn_of_core h hfn) cl hcl
    · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hcl
      exact hmo (fn.label, i) (match_mem_of_ovl hno hfn hi) fn (lookupFn_of_core h hfn) _
        (List.getElem?_eq_getElem hi)

/-- **What the statements assume, from `coreOK` and `FnHyp`**: `sortedOK`, `srReady`
(`NamesApart.srReady_of`) and the names numbered (`faithCoreOK`) are decided; the facts about the
functions are `FnHyp`. -/
theorem hyp_of_fnHyp (h : c.coreOK = true) (hf : FnHyp c) : HypCore c := by
  obtain ⟨hok, hfa, -, hp, hids⟩ := Semantics.coreOK_parts h
  exact ⟨hok, NamesApart.srReady_of hp hids hok
    (NamesApart.rangeKeys_genWf_of_faithCore (Semantics.coreOK_parts h).2.1) (Semantics.coreOK_ovls h), hf.1, hf.2.1, hf.2.2.1, hf.2.2.2.1,
    namesNumbered_spec (faithCoreOK_parts hfa).1⟩

/-- **What the statements assume, from `coreOK` and `CoreObligations`**: `hyp_of_fnHyp` with
`fnHyp_of_core`. -/
theorem hyp_of_core (h : c.coreOK = true) (hrh : c.RightHeld) (hob : CoreObligations c t) (hpreTop : c.clausesPreTop = true := by first | decide +kernel | (simp only [Semantics.clausesPreTop_withHooks]; decide +kernel) | exact rfl) : HypCore c :=
  hyp_of_fnHyp h (fnHyp_of_core (hpreTop := hpreTop) h hrh hob)

/-- **What the existence of a model reads, from `coreOK`, `FnDet` and `FnSolves`**: `sortedOK`,
`srReady` and the names numbered with the two facts on the functions (`HypFnModel`),
`HypSoundCore` (`hypSound_of_core`), the semantics' own sorts and symbols numbered (`idsOK`), the
conditions `faithCoreOK` decides, and the collection symbols apart from the constructors, which
follows from two of them (`collsNotCtors_of`). -/
theorem hypModel_of_fn (h : c.coreOK = true) (hd : FnDet c) (hs : FnSolves c) : HypModelCore c := by
  obtain ⟨hok, hfa, -, hp, hids⟩ := Semantics.coreOK_parts h
  obtain ⟨hnn, -, -, hcs, -, hn, hl, hs', hi, hk, hc, hf'⟩ := faithCoreOK_parts hfa
  exact ⟨⟨Semantics.sortedOKCl_of_sortedOK hok, NamesApart.srReady_of hp hids hok
    (NamesApart.rangeKeys_genWf_of_faithCore (Semantics.coreOK_parts h).2.1) (Semantics.coreOK_ovls h), namesNumbered_spec hnn, hd, hs⟩,
    HypSoundCore.model (hypSound_of_core h), hn, hl,
    hids, hs', collsNotCtors_of hk hcs, hi, hk, hc, hf', Semantics.coreOK_ovls h, ovlsOnce_of_ids hids⟩

/-- **What the existence of a model reads, for a semantics whose clauses are asked CN-4's bodies**:
`hypModel_of_fn` with `sortedOKCl` for `sortedOK`, and `srReady`, `OvlOK` and the map pattern
symbols apart from the constructors (`patHooksApart`), which `coreOK` gives through `sortedOK`,
taken as hypotheses. -/
theorem hypModel_ofCl (hok : c.sortedOKCl = true) (hsr : c.srReady = true) (hov : OvlOK c)
    (hfa : c.faithCoreOK = true) (hph : patHooksApart c = true) (hids : c.idsOK = true)
    (hd : FnDet c) (hs : FnSolves c) : HypModelCore c := by
  obtain ⟨hnn, hg, hcso, hcs, hph', hn, hl, hs', hi, hk, hc, hf'⟩ := faithCoreOK_parts hfa
  exact ⟨⟨hok, hsr, namesNumbered_spec hnn, hd, hs⟩,
    ⟨hok, hsr, namesNumbered_spec hnn, hg, hph, hcso, hcs, hph', hov⟩, hn, hl,
    hids, hs', collsNotCtors_of hk hcs, hi, hk, hc, hf', hov.ok, ovlsOnce_of_ids hids⟩

/-- **`FnHyp` gives `FnDet` and `FnSolves`**: the agreement of the equations and the match
independence of the clauses give coherence, so one result (`fnDet_of_coherent`); with termination
every `requires` and right-hand side read has a result, and match independence holds a result of
each clause with existential variables where it decides, so where a clause decides the function's
values are its right side's (`fnSolves_of_total`). `FnHyp`'s totality conjunct is not read. -/
theorem fnModel_of_fnHyp (h : c.coreOK = true) (hf : FnHyp c) : FnDet c ∧ FnSolves c :=
  have hd := fnDet_of_coherent (CoherentAll_of (hyp_of_fnHyp h hf))
  ⟨hd, fnSolves_of_total (hypSound_of_core h) hd hf.1 fun fn hfn cl hcl hne vs σ hdec =>
    (hf.2.2.2.1 fn hfn cl hcl).2 hne fn.label fn vs σ (lookupFn_of_core h hfn) hcl hdec⟩

/-- **Under `FnHyp`, values that satisfy a clause's conditions witness it**: `FnHyp`'s agreement and
match-independence conjuncts give `FnDet` (`fnDet_of_agree`), with no other fact on the
semantics. -/
theorem Clause.witnessedDet_of_fnHyp {c : Semantics} (hf : FnHyp c) {cl : Clause}
    (hw : ∃ σ, c.WellSortedAt cl.vars cl.condVars σ ∧
      (∀ t, cl.req = some t → EvalTerm c σ t (some (bool true))) ∧ Holds c cl.vars.length σ cl.pre true) :
    cl.Witnessed c :=
  (Clause.witnessedDet_iff_of_fnDet (fnDet_of_agree hf.2.2.1 hf.2.2.2.1) cl).mpr hw

/-- **`FnDet`, `PrioDecided` and `CoDefined` give `FnSolves`** in a semantics that `coreOK`
accepts (`fnSolves_of_parts_lookup`, FnSolves.lean; the labels are apart, `lookupFn_of_core`). -/
theorem fnSolves_of_parts (h : c.coreOK = true) (hd : FnDet c) (hp : PrioDecided c) (ha : CoDefined c) :
    FnSolves c :=
  fnSolves_of_parts_lookup (fun _ hfn => lookupFn_of_core h hfn) hd
    (fun fn hfn => Semantics.sortedOK_plainCl (Semantics.coreOK_parts h).1 fn (List.mem_append_left _ hfn)) hp ha

/-- **What the existence of a model reads, from `coreOK` and `FnHyp`**: `hypModel_of_fn` with
`fnModel_of_fnHyp`. -/
theorem hypModel_of_fnHyp (h : c.coreOK = true) (hf : FnHyp c) : HypModelCore c :=
  hypModel_of_fn h (fnModel_of_fnHyp h hf).1 (fnModel_of_fnHyp h hf).2

/-- **What the existence of a model reads, from `coreOK` and `CoreObligations`**:
`hypModel_of_fnHyp` with `fnHyp_of_core`. -/
theorem hypModel_of_core (h : c.coreOK = true) (hrh : c.RightHeld) (hob : CoreObligations c t) (hpreTop : c.clausesPreTop = true := by first | decide +kernel | (simp only [Semantics.clausesPreTop_withHooks]; decide +kernel) | exact rfl) : HypModelCore c :=
  hypModel_of_fnHyp h (fnHyp_of_core (hpreTop := hpreTop) h hrh hob)

end Core

/-! ## What `wf` and `Obligations` give -/

variable {d : Definition}

/-- **What step soundness reads, from `wf`**: `hypSound_of_core`, `wf` giving `coreOK` and
`okAll`. -/
theorem hypSound_of (hwf : wf d = true) : HypSound d.sem :=
  ⟨(NamesApart.wf_parts hwf).2.2.2, (hypSound_of_core (Definition.coreOK_of_wf hwf)).2⟩

/-- A user function is the one `lookupFn` finds under its label (the labels are apart). -/
theorem lookupFn_of_wf (hwf : wf d = true) {fn : Fn} (hfn : fn ∈ d.sem.fns) :
    d.sem.lookupFn fn.label = some fn :=
  lookupFn_of_core (Definition.coreOK_of_wf hwf) hfn

/-- **What the statements assume, from `wf` and `Obligations`**: `hyp_of_core`, `wf` giving
`okAll`. -/
theorem hyp_of (hwf : wf d = true) (hrh : d.sem.RightHeld) (hob : Obligations d) : Hyp d.sem :=
  have hpreTop := Semantics.preTop_of_okAll (NamesApart.wf_parts hwf).2.2.2
  ⟨(NamesApart.wf_parts hwf).2.2.2, (hyp_of_core (hpreTop := hpreTop) (Definition.coreOK_of_wf hwf) hrh hob).2⟩

/-- **What the existence of a model reads, from `wf` and `Obligations`**: `hypModel_of_core`, `wf`
giving `coreOK`, and `hyp_of`, `hypSound_of`. -/
theorem hypModel_of (hwf : wf d = true) (hrh : d.sem.RightHeld) (hob : Obligations d) : HypModel d.sem :=
  have hpreTop := Semantics.preTop_of_okAll (NamesApart.wf_parts hwf).2.2.2
  have h := hypModel_of_core (hpreTop := hpreTop) (Definition.coreOK_of_wf hwf) hrh hob
  ⟨hyp_of hwf hrh hob, hypSound_of hwf, h.names, h.lits, h.ids, h.sorts, h.collCtors, h.ites, h.kinds,
    h.ctors, h.fns⟩

/-- `hypModel_of` for every interpretation of the parameters, under the obligations stated for
that interpretation, of a definition without an open generator (`hr`). -/
theorem hypModel_of_withHooks (hwf : wf d = true) (hrh : d.sem.RightHeld) (H : HookParams)
    (hob : Obligations { d with sem := d.sem.withHooks H })
    (hr : ∀ k ∈ d.sem.params, k.raw = false := by decide +kernel) : HypModel (d.sem.withHooks H) :=
  have hpreTop := Semantics.preTop_of_okAll (NamesApart.wf_parts hwf).2.2.2
  hypModel_of (d := { d with sem := d.sem.withHooks H }) ((Definition.wf_withHooks d H).trans hwf)
    (Semantics.rightHeld_withHooks hrh H hr) hob

kernel_rfl Semantics.lazyObligations_withHooks :
  ∀ (c : Semantics) (H : HookParams), (c.withHooks H).lazyObligations = c.lazyObligations

/-- With none named, the obligations hold for every interpretation of the parameters: the named
lists do not read the interpretation. -/
theorem Obligations.withHooks_of_nil (h1 : d.sem.orderObligations ++ d.cert.obligations d.sem = [])
    (h2 : d.sem.totalObligations = []) (h3 : d.sem.agreeObligations = [])
    (h4 : d.sem.matchObligations = []) (h5 : d.sem.lazyObligations = []) (H : HookParams)
    (h6 : d.sem.plain = true := by decide +kernel) :
    Obligations { d with sem := d.sem.withHooks H } :=
  Obligations.of_nil
    (by
      show (d.sem.withHooks H).orderObligations ++ d.cert.obligations (d.sem.withHooks H) = []
      rw [orderObligations_withHooks, certObligations_withHooks]; exact h1)
    ((Semantics.totalObligations_withHooks d.sem H).trans h2)
    ((Semantics.agreeObligations_withHooks d.sem H).trans h3)
    ((Semantics.matchObligations_withHooks d.sem H).trans h4)
    ((Semantics.lazyObligations_withHooks d.sem H).trans h5)
    ((Semantics.plain_withHooks d.sem H).trans h6)

end KCore
