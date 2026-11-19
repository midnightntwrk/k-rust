/-
  KCore. What the existence of a model reads (`HypModelCore`), for a semantics whose clauses may bind
  variables by `\exists` (`Semantics.coreOKEx`).

  - `Faithful.Model.hypModelCore_of_coreEx`: `HypModelCore` from `coreOKEx`, `FnDet` and `FnSolves`,
    as `hypModel_of_fn` gives it from `coreOK`; the value model's sortedness `sortedOKClEx` is
    `Semantics.sortedOKClEx_of_sortedOKEx`'s, from `sortedOKEx`.
  - `Faithful.Model.HypModel.fnsNoExs`: `HypModel` holds `okAll`, hence `sortedOK`, which asks every
    clause to bind no variable by `\exists`. So no semantics with such a clause meets `HypModel`;
    what the model reads of it is `HypModelCore`, which `hypModelCore_of_coreEx` gives.
  - `Faithful.Model.consistent_of_coreEx`: `consistent_of_modelEx` with `HypModelCore` from
    `hypModelCore_of_coreEx` and the clauses' facts from `sortedOKClEx`.
  - `Faithful.coherentAll_ofSelfCEx`: every two competing clauses are coherent where each user
    function's clauses agree and each user clause is coherent with itself; match independence, whose
    second conjunct asks a result of a clause with existential variables wherever it decides, is not
    read. So `FnDet` (`fnDet_of_coherent`) without it.
-/
import KcoreSpec.ModelHasEx
import KcoreSpec.CoreOKExFacts
import KcoreSpec.OpenClauseModel
import KcoreSpec.TermSoundCEx

set_option autoImplicit false

namespace KCore

namespace Faithful

/-- `HypSoundCoreEx` gives what the value model reads of the conditions step soundness reads. -/
theorem HypSoundCoreEx.model {c : Semantics} (h : HypSoundCoreEx c) : Model.HypSoundModel c :=
  ⟨Semantics.sortedOKClEx_of_sortedOKEx h.1, h.2⟩

variable {c : Semantics}

/-- **Every two clauses that compete are coherent**, where each user function's clauses agree
(`ClausesAgree`) and each user clause is coherent with itself; a generated sort predicate's clauses
agree (`sortPreds_agree`) and each is coherent with itself, its right-hand side being a domain value
and it having no `ensures`. -/
theorem coherentAll_ofSelfCEx (hag : ∀ fn ∈ c.fns, ClausesAgree c fn)
    (hco : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, Coherent c cl cl) : CoherentAll c := by
  intro f fn hfn cl hcl cl' hcl' hprio
  obtain ⟨hmem, -⟩ := lookupFn_spec hfn
  have hagf : ClausesAgree c fn := by
    rcases List.mem_append.mp hmem with hu | hp
    · exact hag fn hu
    · exact sortPreds_agree hp
  by_cases he : cl = cl'
  · subst he
    rcases List.mem_append.mp hmem with hu | hp
    · exact hco fn hu cl hcl
    · intro vs σ σ' _ _ _ _ _ _ _
      refine Or.inl ⟨Semantics.sortPreds_exs hp cl hcl, Semantics.sortPreds_exs hp cl hcl, rfl, rfl,
        fun i hi => absurd hi ?_, fun t ht => ?_⟩
      · obtain ⟨s', lit, hr⟩ := sortPreds_rhs hp cl hcl
        rw [hr, varOccs]
        exact List.not_mem_nil
      · rw [sortPreds_ens hp cl hcl] at ht; cases ht
  · rcases mem_pairs_of_ne hcl hcl' he with hp | hp
    · exact (hagf cl cl' hp hprio).1
    · refine (hagf cl' cl hp ?_).2
      rcases hprio with h | h | h
      · exact .inl h.symm
      · exact .inr (.inr h)
      · exact .inr (.inl h)

namespace Model

open ML

/-- **What the existence of a model reads, from `coreOKEx`, `FnDet` and `FnSolves`**:
`hypModel_of_fn` with `coreOKEx` for `coreOK`. The clauses' sortedness `sortedOKClEx` is
`sortedOKClEx_of_sortedOKEx`; `srReady`, the names numbered and the conditions of `HypSoundModel`
are `hypSoundEx_of_coreEx`'s; the conditions `faithCoreOK` decides are read as there. -/
theorem hypModelCore_of_coreEx (h : c.coreOKEx = true) (hd : FnDet c) (hs : FnSolves c) :
    HypModelCore c := by
  obtain ⟨-, hfa, -, -, hids⟩ := Semantics.coreOKEx_parts h
  obtain ⟨hnn, -, -, hcs, -, hn, hl, hs', hi, hk, hc, hf'⟩ := faithCoreOK_parts hfa
  have hsd := hypSoundEx_of_coreEx h
  exact ⟨⟨Semantics.sortedOKClEx_of_sortedOKEx hsd.1, hsd.2.1, namesNumbered_spec hnn, hd, hs⟩,
    hsd.model, hn, hl, hids, hs', collsNotCtors_of hk hcs, hi, hk, hc, hf', Semantics.coreOKEx_ovls h,
    ovlsOnce_of_ids hids⟩

/-- **`HypModel` asks every clause to bind no variable by `\exists`**: it holds `okAll`, whose
`clausesNoExsTop` asks it. -/
theorem HypModel.fnsNoExs (h : HypModel c) : c.FnsNoExs :=
  Semantics.fnsNoExs_of_okAll h.hyp.1

/-- No semantics with a clause that binds a variable by `\exists` meets `HypModel`. -/
theorem not_hypModel_of_exs {fn : Fn} (hfn : fn ∈ c.fns) {cl : Clause} (hcl : cl ∈ fn.clauses)
    (hex : cl.exs ≠ []) : ¬ HypModel c :=
  fun h => hex (h.fnsNoExs fn hfn cl hcl)

end Model

end Faithful

open ML Faithful Faithful.Model

variable {c : Semantics}

/-- **The theory of a semantics `coreOKEx` accepts is consistent**, where its functions have one
result (`FnDet`), evaluation solves the equations (`FnSolves`), the clauses' predicates have truth
values (`ClausePreDecided`, `ClausePostDecided`) and the open generators meet their laws
(`OpenLaws`): `consistent_of_modelEx` with `hypModelCore_of_coreEx` and the clauses' facts from
`sortedOKClEx` (`clauseSortedOpen`, and `clauseExOK` and a `\top` right-side predicate where there
is no existential variable, from `clausePlainOpenEx`). -/
theorem Faithful.Model.consistent_of_coreEx (h : c.coreOKEx = true) (hd : FnDet c) (hs : FnSolves c)
    (hp : ClausePreDecided c) (hq : ClausePostDecided c) (hl : OpenLaws c) : Consistent c :=
  consistent_of_modelEx c (hypModelCore_of_coreEx h hd hs)
    (fun fn hfn cl hcl =>
      have hcp := (Semantics.sortedOKClEx_parts (Semantics.sortedOKClEx_of_sortedOKEx
        (Semantics.coreOKEx_parts h).1)).2.1 fn hfn cl hcl
      ⟨hcp.1, (Semantics.clausePlainOpenEx_parts hcp.2).1, (Semantics.clausePlainOpenEx_parts hcp.2).2.1⟩)
    hp hq hl

end KCore
