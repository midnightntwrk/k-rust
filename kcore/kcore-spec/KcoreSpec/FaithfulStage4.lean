/-
  KCore. Step soundness for the fourth stage: left-hand sides and clause patterns may be
  collection patterns, the map pattern symbols (`PatVal.hook`: `.Map`, `|->`, `_Map_`) and the
  collection pattern symbols (`PatVal.coll`: a list's, a cell map's).

  Upwards (`patVal_den4`), a collection pattern is read through the graphs of its symbols on
  values (`ΓDomains`): each sub-pattern translates to what its value denotes, and the graph says
  what the symbol gives on those values. Nothing about elements that are not values is read, so
  this direction needs nothing beyond `Γ`.

  Downwards, a negated premise (a competitor's exclusion or `applies`) is read at elements that
  need not be values; `Γ` says nothing of the collection symbols there (FaithfulColl.lean). The
  steps here are therefore proved for every model in which the competitors' exclusions and
  `applies` are empty where they fail (`ExclEmpty`, `AppEmpty`, `step_at4`); the fourth stage's
  scope (`Stage4a`) asks that every clause and rule read negatively be plain, where the third
  stage's lemmas give that emptiness (`exclusion_empty`, `applies_empty`).
-/
import KcoreSpec.FaithfulStage3
import KcoreSpec.PatCtxNF

set_option autoImplicit false

namespace KCore

namespace Faithful

open ML
open KoreAML (DefOK Inh IsSort Closed KGround VarKey VarTable)

/-! ## The heads of a left-hand side's context -/

/-- The map pattern symbols are not constructors (the third part of `matchReady`). Decidable on the
data; `Hyp` does not give it (`okAll` does not read it; `wf` does, `NamesApart.matchReady_of_wf`). -/
def patHooksApart (c : Semantics) : Bool := patternHooks.all fun f => !c.isCtor f

theorem patHooksApart_spec {c : Semantics} (h : patHooksApart c = true) {f : Sym} (hf : patternHooks.contains f = true) :
    c.isCtor f = false := by
  have := List.all_eq_true.mp h f (List.contains_iff_mem.mp hf)
  simpa using this

theorem find?_filter_name (q : Sym → Bool) (f : Sym) : ∀ l : List CtorSig,
    (l.filter (fun k => q k.name)).find? (·.name == f) = if q f = true then l.find? (·.name == f) else none
  | [] => by simp
  | k :: l => by
    have ih := find?_filter_name q f l
    by_cases hk : k.name = f
    · subst hk
      cases hq : q k.name <;> simp [List.filter, hq, ih]
    · have hne : (k.name == f) = false := by simpa using hk
      cases hq : q k.name <;> simp [List.filter, hq, ih, hne]

theorem find?_filter_of {α : Type} {p q : α → Bool} : ∀ {l : List α} {x : α}, l.find? p = some x → q x = true →
    (l.filter q).find? p = some x
  | [], _, h, _ => by simp at h
  | a :: l, x, h, hq => by
    by_cases hp : p a = true
    · rw [List.find?_cons_of_pos hp] at h
      cases h
      rw [List.filter_cons_of_pos hq, List.find?_cons_of_pos hp]
    · have hp' : p a = false := by simpa using hp
      rw [List.find?_cons_of_neg (by simpa using hp')] at h
      by_cases hqa : q a = true
      · rw [List.filter_cons_of_pos hqa, List.find?_cons_of_neg (by simpa using hp')]
        exact find?_filter_of h hq
      · rw [List.filter_cons_of_neg hqa]
        exact find?_filter_of h hq

section
variable {c : Semantics}

/-- A map pattern symbol's signature in a left-hand side's context is its hook's. -/
theorem patAll_lookup_hook (hph : patHooksApart c = true) {f : Sym} (hf : patternHooks.contains f = true)
    {k : CtorSig} (hk : lookupSig c.patCtxAll.heads f = some k) : lookupSig hookSigs f = some k := by
  have hnc : lookupSig c.ctorSigs f = none :=
    Option.not_isSome_iff_eq_none.mp (by simpa [Semantics.isCtor] using patHooksApart_spec hph hf)
  have hfm : f ∈ patternHooks := List.contains_iff_mem.mp hf
  have hhook : ∃ k0, lookupSig hookSigs f = some k0 := by
    have : ∀ f ∈ patternHooks, (lookupSig hookSigs f).isSome = true := by decide
    exact Option.isSome_iff_exists.mp (this f hfm)
  obtain ⟨k0, hk0⟩ := hhook
  have hpc : lookupSig c.patCtx.heads f = some k0 := by
    simp only [Semantics.patCtx]
    rw [lookupSig_append_of_none hnc, Exec.patternHooks_lookup f hfm, hk0]
  simp only [Semantics.patCtxAll] at hk
  rw [lookupSig_append_of_some hpc] at hk
  rw [hk0, hk]

/-- A collection pattern symbol that is a hook: its signature in a left-hand side's context is its
hook's. -/
theorem patAll_lookup_collHook {f : Sym} (hc : c.isCtor f = false) (hp : c.isCollPat f = true) (hh : isHook f = true)
    {k : CtorSig} (hk : lookupSig c.patCtxAll.heads f = some k) : lookupSig hookSigs f = some k := by
  have hnc : lookupSig c.ctorSigs f = none :=
    Option.not_isSome_iff_eq_none.mp (by simpa [Semantics.isCtor] using hc)
  unfold Semantics.isCollPat at hp
  rw [hh, if_pos rfl] at hp
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hp
  obtain ⟨hnp, hcp⟩ := hp
  obtain ⟨k0, hk0⟩ := lookupSig_hookSigs_of_isHook hh
  have h1 : lookupSig (hookSigs.filter (patternHooks.contains ·.name)) f = none := by
    rw [lookupSig_eq, find?_filter_name (patternHooks.contains ·) f hookSigs, hnp]; rfl
  have h2 : lookupSig (hookSigs.filter (collPatternHooks.contains ·.name)) f = some k0 := by
    rw [lookupSig_eq, find?_filter_name (collPatternHooks.contains ·) f hookSigs, hcp, if_pos rfl, ← lookupSig_eq, hk0]
  simp only [Semantics.patCtxAll, Semantics.patCtx, Semantics.collPatSigs] at hk
  rw [lookupSig_append_of_none ((lookupSig_append_of_none hnc).trans h1),
    lookupSig_append_of_some (lookupSig_append_of_some h2)] at hk
  rw [hk0, hk]

/-- A collection pattern symbol that is a parameter: its signature in a left-hand side's context is
the parameter's. -/
theorem patAll_lookup_collParam {f : Sym} (hc : c.isCtor f = false) (hp : c.isCollPat f = true) (hh : isHook f = false)
    {k : CtorSig} (hk : lookupSig c.patCtxAll.heads f = some k) :
    ∃ kp, c.lookupParam f = some kp ∧ kp ∈ c.params ∧ kp.sig = k ∧ kp.sig.name = f := by
  have hnc : lookupSig c.ctorSigs f = none :=
    Option.not_isSome_iff_eq_none.mp (by simpa [Semantics.isCtor] using hc)
  have hnh := lookupSig_hookSigs_of_not_isHook hh
  have hnf : ∀ q : Sym → Bool, lookupSig (hookSigs.filter (fun k => q k.name)) f = none := fun q => by
    rw [lookupSig_eq, find?_filter_name q f hookSigs]
    split
    · rw [← lookupSig_eq, hnh]
    · rfl
  unfold Semantics.isCollPat at hp
  rw [hh, if_neg Bool.false_ne_true] at hp
  simp only [Bool.and_eq_true] at hp
  obtain ⟨-, hp⟩ := hp
  cases hkp : c.lookupParam f with
  | none => rw [hkp] at hp; cases hp
  | some kp =>
    rw [hkp] at hp
    simp only at hp
    have hfind := hkp
    rw [Semantics.lookupParam_eq] at hfind
    have key : ∀ (P : ParamSig → Bool), P kp = true →
        lookupSig ((c.params.filter P).map (·.sig) ++ c.ovlSigs) f = some k → kp.sig = k := fun P hP h => by
      rw [lookupSig_eq, List.find?_append, List.find?_map] at h
      have := find?_filter_of (p := fun x : ParamSig => x.sig.name == f) hfind hP
      simp only [Function.comp_def] at h
      rw [this] at h
      simpa using h
    simp only [Semantics.patCtxAll, Semantics.patCtx, Semantics.collPatSigs] at hk
    rw [lookupSig_append_of_none ((lookupSig_append_of_none hnc).trans (hnf _)), List.append_assoc,
      lookupSig_append_of_none (hnf _)] at hk
    refine ⟨kp, rfl, List.mem_of_find?_eq_some hfind, key _ ?_ hk, by simpa using List.find?_some hfind⟩
    cases hi : kp.impl with
    | none => rw [hi] at hp; simp at hp
    | some g =>
      rw [hi] at hp
      simp only [hi]
      exact hp

/-- An overloading symbol of a left-hand side has its declaration's signature there. -/
theorem patAll_lookup_ovl {f : Sym} (ho : c.isOvl f = true) {k : CtorSig} (hk : lookupSig c.patCtxAll.heads f = some k) :
    ∃ o, c.lookupOvl f = some o ∧ k = o.sig := by
  obtain ⟨hc, hh, hp, -, -⟩ := c.isOvl_parts ho
  have hnc : lookupSig c.ctorSigs f = none :=
    Option.not_isSome_iff_eq_none.mp (by simpa [Semantics.isCtor] using hc)
  have hnh := lookupSig_hookSigs_of_not_isHook hh
  have hnf : ∀ q : Sym → Bool, lookupSig (hookSigs.filter (fun k => q k.name)) f = none := fun q => by
    rw [lookupSig_eq, find?_filter_name q f hookSigs]
    split
    · rw [← lookupSig_eq, hnh]
    · rfl
  have hnp : ∀ P : ParamSig → Bool, lookupSig ((c.params.filter P).map (·.sig)) f = none := fun P => by
    rw [lookupSig_eq, List.find?_eq_none]
    intro k hk hkn
    obtain ⟨kp, hkp, rfl⟩ := List.mem_map.mp hk
    have hpn := c.lookupSig_params_of_not hp
    rw [lookupSig_eq, List.find?_eq_none] at hpn
    exact hpn _ (List.mem_map_of_mem (List.mem_filter.mp hkp).1) hkn
  simp only [Semantics.patCtxAll, Semantics.patCtx, Semantics.collPatSigs] at hk
  rw [lookupSig_append_of_none ((lookupSig_append_of_none hnc).trans (hnf _)), List.append_assoc,
    lookupSig_append_of_none (hnf _), lookupSig_append_of_none (hnp _), lookupSig_eq, OvlLaws.find_ovlSigs] at hk
  obtain ⟨o, ho', rfl⟩ := Option.map_eq_some_iff.mp hk
  exact ⟨o, ho', rfl⟩

end

/-! ## Collection patterns, upwards -/

section
variable {c : Semantics} {M : Type} {I : Interpretation KoreAML.Sym M}
variable [Inhabited M] (hI : I ⊧ᴵP Γ c) (hnm : NamesPlain c) (hph : patHooksApart c = true) [OvlOK c]
  (htr : ∀ a b d, (a, b) ∈ c.subsorts → (b, d) ∈ c.subsorts → (a, d) ∈ c.subsorts)
  {σ : Subst} {vars : List Srt} {vs : List KoreAML.Var} {t : KoreAML.VarTable} {e : Valuation M}
  (hσ : c.WellSorted vars σ) (hvs : vs.length = vars.length) (hag : Agrees c I t vs σ e)
include hI hnm hph htr hσ hvs hag

mutual
  /-- **Patterns, upwards, collection patterns included.** A well-sorted pattern that denotes `v`
  under a well-sorted σ translates, at a valuation that agrees with σ, to the element `v` denotes;
  and `v` has the pattern's sort. A map or collection pattern symbol is read through its graph on
  the values its arguments denote. -/
  theorem patVal_den4 : ∀ {p : Term} {v : GroundTerm} {s : Srt}, PatVal c σ p v →
      sortOfTerm c.patCtxNF vars p = some s →
      c.sortOf v = some s ∧ ∀ m, (KoreAML.tr ⟨t, []⟩ (Term.kore c vs p)).interpret I e m ↔ (den c v).interpret I e m
    | _, _, s, .var (i := i) (v := v) hl, ht => by
      have hi := sortOfTerm_var.mp ht
      have hlt : i < vs.length := by rw [hvs]; exact (List.getElem?_eq_some_iff.mp hi).1
      refine ⟨?_, fun m => ?_⟩
      · obtain ⟨w, hw, hsw⟩ := hσ i s hi
        rw [hl] at hw; cases hw; exact hsw
      · rw [tr_var]
        exact hag i v hlt hl m
    | _, _, s, .dv (s := s') (lit := lit), ht => by
      obtain ⟨hok, rfl⟩ := sortOfTerm_dv.mp ht
      refine ⟨sortOf_dv.mpr ⟨hok, rfl⟩, fun m => ?_⟩
      rw [Term.kore]; unfold den KoreAML.den; rw [GroundTerm.kore]; unfold srtOf
      rw [KoreAML.tr_dv, KoreAML.tr_dv]
    | _, _, s, .ctor (f := f) (ps := ps) (vs := ws) hk hs, ht => by
      obtain ⟨k, hk', hargs, rfl⟩ := sortOfTerm_app.mp ht
      have hnfo := (patCtxNF_lookup.mp hk').2
      replace hk' := (patCtxNF_lookup.mp hk').1
      obtain ⟨k0, hk0⟩ := Option.isSome_iff_exists.mp hk
      have hkk := lookup_patCtxAll hk0 hk'
      subst hkk
      have ih := patVals_den4 hs hargs
      refine ⟨sortOf_ctor_intro ⟨k, hk0, ih.1, rfl⟩, fun m => ?_⟩
      rw [Term.kore, iteSort_ctor hnm hk0]
      dsimp only
      rw [KoreAML.tr_app0, den_ctor]
      exact ih.2 _ _ (fun _ => Iff.rfl) m
    | _, _, s, .hook (f := f) (vs := ws) (v := v) hp hs hv, ht => by
      obtain ⟨k, hk', hargs, rfl⟩ := sortOfTerm_app.mp ht
      have hnfo := (patCtxNF_lookup.mp hk').2
      replace hk' := (patCtxNF_lookup.mp hk').1
      have hks := patAll_lookup_hook hph hp hk'
      obtain ⟨hkm, hkn⟩ := lookupSig_spec hks
      have ih := patVals_den4 hs hargs
      refine ⟨hook_sorted (fun he => patternHooks_ne_rmKeys _ hp he |>.elim) hks ih.1 hv, fun m => ?_⟩
      have hax := sat_dom hI (Or.inl ⟨k, ws, some v, hkm, ih.1, by rw [hkn]; exact hv, (by intro h; cases h), rfl⟩)
      have hgr := (KoreAML.interp_equal (defOK hI)).mp (hax e default) m
      rw [hkn] at hgr
      unfold KoreAML.den at hgr
      rw [tr_symApp] at hgr
      rw [kore_app, tr_symApp, ih.2 _ _ (fun _ => Iff.rfl) m]
      exact hgr
    | _, _, s, .coll (f := f) (vs := ws) (v := v) hc hp hs hv, ht => by
      obtain ⟨k, hk', hargs, rfl⟩ := sortOfTerm_app.mp ht
      have hnfo := (patCtxNF_lookup.mp hk').2
      replace hk' := (patCtxNF_lookup.mp hk').1
      have ih := patVals_den4 hs hargs
      unfold Semantics.collVal at hv
      cases hh : isHook f with
      | true =>
        rw [if_pos hh] at hv
        have hks := patAll_lookup_collHook hc hp hh hk'
        obtain ⟨hkm, hkn⟩ := lookupSig_spec hks
        have hv' : hook f ws = some (some v) := by
          cases h : hook f ws with
          | none => rw [h] at hv; cases hv
          | some r => rw [h] at hv; cases r with
            | none => cases hv
            | some w => cases hv; rfl
        refine ⟨hook_sorted (fun he => isCollPat_hook_ne_rmKeys hp hh he |>.elim) hks ih.1 hv', fun m => ?_⟩
        have hax := sat_dom hI (Or.inl ⟨k, ws, some v, hkm, ih.1, by rw [hkn]; exact hv', (by intro h; cases h), rfl⟩)
        have hgr := (KoreAML.interp_equal (defOK hI)).mp (hax e default) m
        rw [hkn] at hgr
        unfold KoreAML.den at hgr
        rw [tr_symApp] at hgr
        rw [kore_app, tr_symApp, ih.2 _ _ (fun _ => Iff.rfl) m]
        exact hgr
      | false =>
        rw [if_neg (by simp [hh])] at hv
        obtain ⟨kp, hkp, hkpm, rfl, hkn⟩ := patAll_lookup_collParam hc hp hh hk'
        obtain ⟨k', hk'', hsv⟩ := c.paramVal_sorted hv
        rw [hkp] at hk''; cases hk''
        refine ⟨hsv, fun m => ?_⟩
        have hax := sat_dom hI (Or.inr (Or.inl ⟨kp, ws, hkpm, ih.1, rfl⟩))
        have hgr := (KoreAML.interp_equal (defOK hI)).mp (hax e default) m
        rw [hkn] at hgr
        unfold KoreAML.den at hgr
        rw [tr_symApp, hv] at hgr
        rw [kore_app, tr_symApp, ih.2 _ _ (fun _ => Iff.rfl) m]
        exact hgr
    | _, _, s, .inj (a := a) (b := b) (p := p) (w := w) h, ht => by
      obtain ⟨hab, ht', hsb⟩ := sortOfTerm_inj.mp ht
      rw [hsb]
      have ih := patVal_den4 h ht'
      refine ⟨sortOf_injNormal htr hab ih.1, fun m => ?_⟩
      rw [Term.kore, KoreAML.tr_injP]
      rcases injNormal_cases a b w with ⟨a', a'', w', rfl, hn⟩ | hn
      · rw [hn]
        obtain ⟨h1, -, h3, rfl⟩ := sortOf_inj.mp ih.1
        obtain ⟨x, hx, hxs⟩ := den_single hI h3 e
        rw [injApp_congr ih.2 m, den_inj, den_inj]
        exact coh_at hI h1 hab hx hxs m
      · rw [hn, den_inj]
        exact injApp_congr ih.2 m
    | _, _, s, .as (p := p) (i := i) (v := v) h hi, ht => by
      obtain ⟨hvi, ht'⟩ := Exec.sortOfTerm_as ht
      have ih := patVal_den4 h ht'
      have hlt : i < vs.length := by rw [hvs]; exact (List.getElem?_eq_some_iff.mp hvi).1
      refine ⟨ih.1, fun m => ?_⟩
      rw [Term.kore, KoreAML.tr]
      simp only [KoreAML.trAndList]
      rw [KoreAML.interp_sAnd, ih.2 m]
      have hv := tr_var (c := c) (I := I) (vs := vs) (t := t) (e := e) i m
      rw [Term.kore] at hv
      rw [hv, hag i v hlt hi m, and_self]
    | _, _, s, .ovl (f := f) (ps := ps) (vs := ws) (v := v) hc ho hs hv, ht => by
      obtain ⟨k, hk', hargs, rfl⟩ := sortOfTerm_app.mp ht
      have hnfo := (patCtxNF_lookup.mp hk').2
      replace hk' := (patCtxNF_lookup.mp hk').1
      obtain ⟨o, hlo, rfl⟩ := patAll_lookup_ovl ho hk'
      have ih := patVals_den4 hs hargs
      subst hv
      have hnf := OvlLaws.fnCover_none_of_not_fnOvl hnfo ws
      refine ⟨OvlLaws.sortOf_norm_ovlF (OvlOK.hyp inferInstance htr) (OvlOK.hyp inferInstance htr).fnFacts hlo ih.1 hnf,
        fun m => ?_⟩
      rw [kore_app, tr_symApp, ih.2 _ _ (fun _ => Iff.rfl) m]
      have := (normDen_of hI htr).1 hlo ih.1 hnf e m
      unfold KoreAML.den at this
      rw [tr_symApp] at this
      exact this
  theorem patVals_den4 : ∀ {ps : List Term} {ws : List GroundTerm} {ss : List Srt}, PatVals c σ ps ws →
      sortsOfTerms c.patCtxNF vars ps = some ss →
      c.sortsOf ws = some ss ∧ ∀ (acc acc' : KoreAML.P), (∀ m, acc.interpret I e m ↔ acc'.interpret I e m) →
        ∀ m, (KoreAML.trArgs ⟨t, []⟩ acc (Term.koreList c vs ps)).interpret I e m ↔
          (KoreAML.trArgs ⟨[], []⟩ acc' (GroundTerm.koreList c ws)).interpret I e m
    | _, _, _, .nil, ht => by
      rw [sortsOfTerms_nil.mp ht]
      refine ⟨sortsOf_nil, fun acc acc' h m => ?_⟩
      rw [Term.koreList, GroundTerm.koreList, KoreAML.trArgs_nil, KoreAML.trArgs_nil]
      exact h m
    | _, _, _, .cons (p := p) (ps := ps) (v := w) (vs := ws) h hs, ht => by
      obtain ⟨s, ss', h1, h2, rfl⟩ := sortsOfTerms_cons.mp ht
      have ih1 := patVal_den4 h h1
      have ih2 := patVals_den4 hs h2
      refine ⟨sortsOf_cons.mpr ⟨s, ss', ih1.1, ih2.1, rfl⟩, fun acc acc' hacc m => ?_⟩
      rw [Term.koreList, GroundTerm.koreList, KoreAML.trArgs_cons, KoreAML.trArgs_cons]
      exact ih2.2 _ _ (KoreAML.interp_app_congr hacc ih1.2) m
end

end

/-! ## A clause's premise and equations, collection patterns included -/

section
variable {c : Semantics} {M : Type} {I : Interpretation KoreAML.Sym M}
variable [Inhabited M] (hI : I ⊧ᴵP Γ c) (hnm : NamesPlain c) (hph : patHooksApart c = true) [OvlOK c]
  (htr : ∀ a b d, (a, b) ∈ c.subsorts → (b, d) ∈ c.subsorts → (a, d) ∈ c.subsorts)
  {σ' : Subst} {vars : List Srt} {vs : List KoreAML.Var} {tbl : VarTable} {e' : Valuation M}
  (hσ' : c.WellSorted vars σ') (hvs : vs.length = vars.length) (hag : Agrees c I tbl vs σ' e')
  {σres m0 : M} (hR : ∀ a, (KoreAML.trSort tbl KoreAML.R).interpret I e' a ↔ a = σres)
  (hσres : IsSort I σres) (hm0 : Inh I σres m0)
include hI hnm hph htr hσ' hvs hag hR hσres hm0

/-- The argument part of a clause's premise, `⋀ⱼ Xⱼ ∈ pⱼ`, holds at a valuation that gives each
`Xⱼ` the element of the argument the pattern `pⱼ` denotes; the patterns may be collection
patterns (`patVal_den4`). -/
theorem argsConj_den4 : ∀ {ps : List Term} {ws : List GroundTerm}, PatVals c σ' ps ws → ∀ (ss : List Srt) (j : Nat),
    sortsOfTerms c.patCtxNF vars ps = some ss →
    (∀ s ∈ ss, s < nRegSorts + c.sortNames.length) →
    (∀ k s w, ss[k]? = some s → ws[k]? = some w → ∀ m,
      m = e'.evalEvar (tbl.ev (.evar ("X" ++ toString (j + k)) (KoreAML.srt (c.sortName s)))) ↔ (den c w).interpret I e' m) →
    (KoreAML.tr ⟨tbl, []⟩ (KoreAML.argsConj j ((ss.map c.sortName).zip (Term.koreList c vs ps)))).interpret I e' m0
  | _, _, .nil, ss, j, ht, _, _ => by
    rw [sortsOfTerms_nil.mp ht, Term.koreList]
    simp only [List.map_nil, List.zip_nil_left, KoreAML.argsConj]
    rw [KoreAML.tr, KoreAML.interp_sTop (defOK hI) isFree_R, KoreAML.interp_inhOf_of hR]
    exact hm0
  | _, _, .cons (p := p) (ps := ps) (v := w) (vs := ws) h hs, ss, j, ht, hnum, hX => by
    obtain ⟨s, ss', h1, h2, rfl⟩ := sortsOfTerms_cons.mp ht
    have hD := defOK hI
    have hc := sat_sigItem hI (sig_ceilDef (c := c))
    have hl2 := patVal_den4 hI hnm hph htr hσ' hvs hag h h1
    obtain ⟨σs, hσs1, hσs2⟩ := sortSing hI (hnum s (List.mem_cons_self ..))
    rw [Term.koreList]
    simp only [List.map_cons, List.zip_cons_cons, KoreAML.argsConj]
    rw [tr_and2, KoreAML.interp_sAnd]
    have hX0 := hX 0 s w rfl rfl
    simp only [Nat.add_zero] at hX0
    have hwx := (hX0 _).mp rfl
    obtain ⟨x, hx, hxs⟩ := den_single hI hl2.1 e'
    have hex : e'.evalEvar (tbl.ev (.evar ("X" ++ toString j) (KoreAML.srt (c.sortName s)))) = x := (hx _).mp hwx
    refine ⟨?_, argsConj_den4 hs ss' (j + 1) h2 (fun s' hs' => hnum s' (List.mem_cons_of_mem _ hs'))
      (fun k s' w' hk1 hk2 m => ?_)⟩
    · rw [KoreAML.tr]
      rw [KoreAML.interp_sIn hD hc (S := KoreAML.trSort tbl (KoreAML.srt (c.sortName s))) (by rw [trSort_srt]; exact hσs1)
        hR hσs2 hσres (fun a ha => ?_) m0]
      · refine ⟨⟨x, ?_, ?_⟩, hm0⟩
        · unfold KoreAML.ev; rw [KoreAML.tr]; exact hex.symm
        · exact (hl2.2 x).mpr ((hx x).mpr rfl)
      · unfold KoreAML.ev at ha; rw [KoreAML.tr] at ha
        have ha' : a = x := by rw [← hex]; exact ha
        rw [ha']
        exact (KoreAML.interp_inhOf_of (S := KoreAML.sym _) hσs1).mp hxs
    · have := hX (k + 1) s' w' (by simpa using hk1) (by simpa using hk2) m
      rwa [show j + (k + 1) = j + 1 + k by omega] at this

end

section
variable {c : Semantics} {M : Type} {I : Interpretation KoreAML.Sym M}

/-- **A clause's premise, read in a model**, its patterns possibly collection patterns. -/
theorem premise_holds4 [Inhabited M] [OvlOK c] (hI : I ⊧ᴵP Γ c) (hnn : NamesNumbered c) (hph : patHooksApart c = true)
    (htr : ∀ a b d, (a, b) ∈ c.subsorts → (b, d) ∈ c.subsorts → (a, d) ∈ c.subsorts)
    {fn : Fn} (hfnm : fn ∈ c.allFns) {cl : Clause} {ws : List GroundTerm} (hws : c.sortsOf ws = some fn.args)
    {σ' : Subst} (hσ' : c.WellSorted cl.vars σ') (hmatch : PatVals c σ' cl.pats ws)
    (hpats : sortsOfTerms c.patCtxNF cl.vars cl.pats = some fn.args)
    {tbl : VarTable} {e : Valuation M} {σr m0 : M} (hag : Agrees c I tbl (canonVars c cl.vars) σ' e)
    (hX : ∀ (j : Nat) w s, ws[j]? = some w → (fn.args.map c.sortName)[j]? = some s →
      e.evalEvar (tbl.ev (.evar ("X" ++ toString j) (KoreAML.srt s))) = elemOf c I w)
    (hRv : ∀ a, (KoreAML.trSort tbl KoreAML.R).interpret I e a ↔ a = σr) (hσr2 : IsSort I σr) (hm0 : Inh I σr m0)
    (ihreq : ∀ t, cl.req = some t → ∀ m, (KoreAML.tr ⟨tbl, []⟩ (Term.kore c (canonVars c cl.vars) t)).interpret I e m ↔
      (den c (bool true)).interpret I e m) :
    (KoreAML.tr ⟨tbl, []⟩ (premise (fn.args.map c.sortName) (cl.req.map (Term.kore c (canonVars c cl.vars)))
      (Term.koreList c (canonVars c cl.vars) cl.pats))).interpret I e m0 := by
  have hD := defOK hI
  have hc := sat_sigItem hI (sig_ceilDef (c := c))
  have hnum := hnn.2.2 fn hfnm
  obtain ⟨σB, hσB1, hσB2⟩ := sortSing hI (bool_numbered (c := c))
  rw [sortName_bool] at hσB1
  unfold premise
  rw [tr_and2, KoreAML.interp_sAnd]
  refine ⟨?_, argsConj_den4 hI hnn.1 hph htr hσ' (canonVars_length c cl.vars) hag hRv hσr2 hm0 hmatch fn.args 0
    hpats (fun s hs => hnum s (List.mem_cons_of_mem _ hs)) ?_⟩
  · cases hq : cl.req with
    | none =>
      simp only [Option.map_none, reqPat]
      rw [KoreAML.tr, KoreAML.interp_sTop hD isFree_R, KoreAML.interp_inhOf_of hRv]
      exact hm0
    | some t =>
      simp only [Option.map_some, reqPat]
      rw [KoreAML.tr, KoreAML.interp_sEquals hD hc (by rw [trSort_srt]; exact hσB1) hRv hσB2 hσr2]
      refine ⟨hm0, fun a _ => ?_⟩
      rw [ihreq t hq a, KoreAML.tr_dv]
      unfold den KoreAML.den bool
      rw [GroundTerm.kore, sortName_bool, KoreAML.tr_dv]
      exact Iff.rfl
  · intro k s w hk hw m'
    rw [Nat.zero_add]
    obtain ⟨w', hw', hsw⟩ := sortsOf_get hws hk
    rw [hw] at hw'; cases hw'
    rw [hX k w (c.sortName s) hw (by rw [List.getElem?_map, hk]; rfl)]
    exact ((elemOf_spec hI hsw e).1 m').symm

/-- **An ordinary clause's equation, read in a model**, its patterns possibly collection
patterns. -/
theorem plain_eq4 [Inhabited M] (hI : I ⊧ᴵP Γ c) [OvlOK c] (hnn : NamesNumbered c) (hph : patHooksApart c = true)
    (htr : ∀ a b d, (a, b) ∈ c.subsorts → (b, d) ∈ c.subsorts → (a, d) ∈ c.subsorts)
    {f : Sym} {fn : Fn} (hfn : c.lookupFn f = some fn) {cl : Clause}
    (hmem : clauseEquation c fn cl ∈ fnEquationsK c fn) (hpre : cl.pre = .top) (hexs : cl.exs = [])
    {ws : List GroundTerm} (hws : c.sortsOf ws = some fn.args)
    {σ' : Subst} (hσ' : c.WellSorted cl.vars σ') (hmatch : PatVals c σ' cl.pats ws)
    (hpats : sortsOfTerms c.patCtxNF cl.vars cl.pats = some fn.args)
    (hbinds : ∀ i < cl.vars.length, i ∈ varOccsList cl.pats)
    (hreqv : ∀ t, cl.req = some t → ∀ i ∈ varOccs t, i < cl.vars.length)
    (hrhsv : ∀ i ∈ varOccs cl.rhs, i < cl.vars.length)
    (hensv : ∀ t, cl.ens = some t → ∀ i ∈ varOccs t, i < cl.vars.length)
    {r : Option GroundTerm} (hr : ∀ v, r = some v → c.sortOf v = some fn.result)
    (ihreq : ∀ (tbl : VarTable) (e : Valuation M), Agrees c I tbl (canonVars c cl.vars) σ' e →
      ∀ t, cl.req = some t → ∀ m, (KoreAML.tr ⟨tbl, []⟩ (Term.kore c (canonVars c cl.vars) t)).interpret I e m ↔
        (den c (bool true)).interpret I e m)
    (ihrhs : ∀ (tbl : VarTable) (e : Valuation M), Agrees c I tbl (canonVars c cl.vars) σ' e →
      ∀ m, (KoreAML.tr ⟨tbl, []⟩ (clauseRight c fn cl)).interpret I e m ↔ Res c I e r m)
    (e0 : Valuation M) (m : M) :
    (KoreAML.den (symApp c f (GroundTerm.koreList c ws))).interpret I e0 m ↔ Res c I e0 r m := by
  have hfnm := (lookupFn_spec hfn).1
  have hv := premise_vars (c := c) (sortsOfTerms_of_nf _ hpats).1 hbinds hreqv
  rw [clauseEquation_top hpre hexs] at hmem
  exact eqn_at hI hnn hfn (prem := clausePrem c fn cl) (eqn_item_mem hfnm hmem) hws hσ' hv.1 hv.2.1 hv.2.2 hrhsv hensv hr
    (fun tbl e σr m0 _ hag hX hRv hσr2 hm0 =>
      premise_holds4 hI hnn hph htr hfnm hws hσ' hmatch hpats hag hX hRv hσr2 hm0 (ihreq tbl e hag))
    ihrhs e0 m

end

/-! ## Negated premises: what the steps read of them -/

/-- **A competing clause's exclusion is empty where it fails**, in the model `I`: at arguments of
`fn`'s sorts where the clause fails in the model (`ModelFails`), its exclusion
`∃ȳ. ⌈req = true⌉ ∧ X̄ ∈ p̄` is empty, at a valuation that gives each formal argument `Xⱼ` the
element of the argument and the sort variable `R` a sort. The conclusion of `exclusion_empty`,
which gives it for a clause whose patterns are plain. -/
def ExclEmpty {M : Type} [Inhabited M] (c : Semantics) (I : Interpretation KoreAML.Sym M) (fn : Fn) (cl : Clause) : Prop :=
  ∀ {ws : List GroundTerm}, c.sortsOf ws = some fn.args →
    ∀ {tbl : VarTable}, (∀ i < cl.vars.length, canonKey c cl.vars i ∈ tbl) →
    (∀ (j : Nat) s, fn.args[j]? = some s → VarKey.evar ("X" ++ toString j) (KoreAML.srt (c.sortName s)) ∈ tbl) →
    VarKey.sortVar "R" ∈ tbl →
    ∀ {e : Valuation M}, (∀ (j : Nat) w s, ws[j]? = some w → fn.args[j]? = some s →
      e.evalEvar (tbl.ev (.evar ("X" ++ toString j) (KoreAML.srt (c.sortName s)))) = elemOf c I w) →
    ∀ {σR : M}, e.evalEvar (tbl.ev (.sortVar "R")) = σR → IsSort I σR →
    ModelFails c I cl ws → ∀ m, ¬ (KoreAML.tr ⟨tbl, []⟩ (exclusion c fn cl (canonClausePres cl))).interpret I e m

/-- **A competing rule's `applies` is empty where it does not apply**, in the model `I`: the
conclusion of `applies_empty`, which gives it for a rule whose left-hand side is plain. -/
def AppEmpty {M : Type} [Inhabited M] (c : Semantics) (I : Interpretation KoreAML.Sym M) (r : Rule) : Prop :=
  ∀ {x : GroundTerm}, c.sortOf x = some topCellSort →
    ∀ {tbl : VarTable}, (∀ i < r.vars.length, canonKey c r.vars i ∈ tbl) → ∀ (e : Valuation M),
    ModelNotApplies c I r x → ¬ (KoreAML.tr ⟨tbl, []⟩ (applies c r (canonRulePres r))).interpret I e (elemOf c I x)

/-- The clause `cl` of `fn` is read negatively by an axiom a step may read: `cl` is a competitor of
a clause of `fn` of a larger priority, whose equation negates it. A clause of the largest priority
among its function's clauses is read positively only. -/
def ClauseNeg (c : Semantics) (fn : Fn) (cl : Clause) : Prop :=
  ∃ cl0 ∈ fn.clauses, cl.prio < cl0.prio

/-- The rule `r` is read negatively: it has a smaller priority than some rule, whose axiom negates
its `applies`. -/
def RuleNeg (c : Semantics) (r : Rule) : Prop := ∃ r0 ∈ c.rules, r.prio < r0.prio

section
variable {c : Semantics} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}

/-- A clause whose patterns are plain has an empty exclusion where it fails (`exclusion_empty`). -/
theorem exclEmpty_of_plain (hI : I ⊧ᴵP Γ c) (hg : genWf c = true) [OvlOK c]
    (htr : ∀ a b d, (a, b) ∈ c.subsorts → (b, d) ∈ c.subsorts → (a, d) ∈ c.subsorts) (hnm : NamesPlain c)
    {fn : Fn} {cl : Clause} (hpre : cl.pre = .top) (hpats : sortsOfTerms c.patCtxAll cl.vars cl.pats = some fn.args)
    (hbinds : ∀ i < cl.vars.length, i ∈ varOccsList cl.pats) (hplain : plainPats c cl.pats = true) :
    ExclEmpty c I fn cl :=
  fun hws _ hkeys hXkeys hRkey _ hX _ hR hσR hfail m =>
    exclusion_empty hI hg htr hnm hpre hpats hbinds hplain hws hkeys hXkeys hRkey hX hR hσR hfail m

/-- A rule whose left-hand side is plain has an empty `applies` where it does not apply
(`applies_empty`). -/
theorem appEmpty_of_plain (hI : I ⊧ᴵP Γ c) (hg : genWf c = true) [OvlOK c]
    (htr : ∀ a b d, (a, b) ∈ c.subsorts → (b, d) ∈ c.subsorts → (a, d) ∈ c.subsorts) (hnm : NamesPlain c)
    {r : Rule} (hlhs : sortOfTerm c.patCtxAll r.vars r.lhs = some topCellSort)
    (hbinds : ∀ i < r.vars.length, i ∈ varOccs r.lhs) (hplain : plainPat c r.lhs = true)
    (hpre : r.pre = .top) : AppEmpty c I r :=
  fun hx _ hkeys e hfail => applies_empty hI hg htr hnm hlhs hbinds hplain hpre hx hkeys e hfail

/-- **A clause's equation under negated competitors, read in a model**, the clause's own patterns
possibly collection patterns, each competitor's exclusion empty where it fails (`ExclEmpty`). -/
theorem compete_eq4 (hI : I ⊧ᴵP Γ c) [OvlOK c] (hnn : NamesNumbered c) (hph : patHooksApart c = true)
    (htr : ∀ a b d, (a, b) ∈ c.subsorts → (b, d) ∈ c.subsorts → (a, d) ∈ c.subsorts)
    {f : Sym} {fn : Fn} (hfn : c.lookupFn f = some fn) {others : List Clause} {cl : Clause}
    (hmem : competingEquation c fn others cl ∈ fnEquationsK c fn) (hpre : cl.pre = .top) (hexs : cl.exs = [])
    (hpres : ∀ cl' ∈ others, cl'.pre = .top) {ws : List GroundTerm} (hws : c.sortsOf ws = some fn.args)
    (hothers : ∀ cl' ∈ others, sortsOfTerms c.patCtxNF cl'.vars cl'.pats = some fn.args ∧
      (∀ i < cl'.vars.length, i ∈ varOccsList cl'.pats) ∧ (∀ t, cl'.req = some t → ∀ i ∈ varOccs t, i < cl'.vars.length) ∧
      ExclEmpty c I fn cl' ∧ ModelFails c I cl' ws)
    {σ' : Subst} (hσ' : c.WellSorted cl.vars σ') (hmatch : PatVals c σ' cl.pats ws)
    (hpats : sortsOfTerms c.patCtxNF cl.vars cl.pats = some fn.args)
    (hbinds : ∀ i < cl.vars.length, i ∈ varOccsList cl.pats)
    (hreqv : ∀ t, cl.req = some t → ∀ i ∈ varOccs t, i < cl.vars.length)
    (hrhsv : ∀ i ∈ varOccs cl.rhs, i < cl.vars.length)
    (hensv : ∀ t, cl.ens = some t → ∀ i ∈ varOccs t, i < cl.vars.length)
    {r : Option GroundTerm} (hr : ∀ v, r = some v → c.sortOf v = some fn.result)
    (ihreq : ∀ (tbl : VarTable) (e : Valuation M), Agrees c I tbl (canonVars c cl.vars) σ' e →
      ∀ t, cl.req = some t → ∀ m, (KoreAML.tr ⟨tbl, []⟩ (Term.kore c (canonVars c cl.vars) t)).interpret I e m ↔
        (den c (bool true)).interpret I e m)
    (ihrhs : ∀ (tbl : VarTable) (e : Valuation M), Agrees c I tbl (canonVars c cl.vars) σ' e →
      ∀ m, (KoreAML.tr ⟨tbl, []⟩ (clauseRight c fn cl)).interpret I e m ↔ Res c I e r m)
    (e0 : Valuation M) (m : M) :
    (KoreAML.den (symApp c f (GroundTerm.koreList c ws))).interpret I e0 m ↔ Res c I e0 r m := by
  rw [competingEquation_top hpre hexs] at hmem
  have hfnm := (lookupFn_spec hfn).1
  have hD := defOK hI
  have hv := premise_vars (c := c) (sortsOfTerms_of_nf _ hpats).1 hbinds hreqv
  let comps := others.map fun cl' => exclusion c fn cl' (canonClausePres cl')
  let P := premise (fn.args.map c.sortName) (cl.req.map (Term.kore c (canonVars c cl.vars)))
    (Term.koreList c (canonVars c cl.vars) cl.pats)
  have hP : ∀ k, k ∈ KoreAML.varsOf P →
      k ∈ KoreAML.varsOf (competingPremise (fn.args.map c.sortName) comps (cl.req.map (Term.kore c (canonVars c cl.vars)))
        (Term.koreList c (canonVars c cl.vars) cl.pats)) := fun k hk => by
    unfold competingPremise
    rw [KoreAML.varsOf, KoreAML.varsOfList, KoreAML.varsOfList, KoreAML.varsOfList]
    exact List.mem_append_right _ (List.mem_append_right _ (List.mem_append_left _ hk))
  have hN : ∀ k, k ∈ KoreAML.varsOf (anyOfC KoreAML.R comps) →
      k ∈ KoreAML.varsOf (competingPremise (fn.args.map c.sortName) comps (cl.req.map (Term.kore c (canonVars c cl.vars)))
        (Term.koreList c (canonVars c cl.vars) cl.pats)) := fun k hk => by
    unfold competingPremise
    rw [KoreAML.varsOf, KoreAML.varsOfList, KoreAML.varsOfList, KoreAML.varsOf, anyOf_eq]
    exact List.mem_append_right _ (List.mem_append_left _ (List.mem_append_right _ hk))
  refine eqn_at hI hnn hfn (eqn_item_mem hfnm hmem) hws hσ' (fun j s hj => hP _ (hv.1 j s hj))
    (fun i hi => hP _ (hv.2.1 i hi)) (fun k hk => ?_) hrhsv hensv hr (fun tbl e σr m0 hkeys hag hX hRv hσr2 hm0 => ?_) ihrhs e0 m
  · unfold competingPremise at hk
    rw [KoreAML.freeOf, KoreAML.freeOfList, KoreAML.freeOfList, KoreAML.freeOfList, KoreAML.freeOf] at hk
    simp only [List.append_nil, List.mem_append] at hk
    rcases hk with hk | hk
    · rw [anyOf_eq] at hk
      obtain ⟨φ, hφ, hk⟩ := mem_freeOf_anyOfC hk
      obtain ⟨cl', hcl', rfl⟩ := List.mem_map.mp hφ
      obtain ⟨hp', hb', hq', -, -⟩ := hothers cl' hcl'
      exact Or.inl (freeOf_exclusion (hpres cl' hcl') (sortsOfTerms_of_nf _ hp').1 hq' (binds_of_forall hb') hk)
    · exact hv.2.2 k hk
  · have hR' : e.evalEvar (tbl.ev (.sortVar "R")) = σr := (hRv _).mp (by rw [trSort_R, KoreAML.interp_evar])
    have hRkey : VarKey.sortVar "R" ∈ tbl := hkeys _ (by
      unfold competingPremise
      rw [KoreAML.varsOf]
      exact List.mem_append_left _ (List.mem_singleton_self _))
    unfold competingPremise
    rw [tr_and2, KoreAML.interp_sAnd]
    refine ⟨?_, premise_holds4 hI hnn hph htr hfnm hws hσ' hmatch hpats hag hX hRv hσr2 hm0 (ihreq tbl e hag)⟩
    rw [KoreAML.tr, KoreAML.interp_sNot]
    refine ⟨?_, (KoreAML.interp_inhOf_of hRv).mpr hm0⟩
    rw [anyOf_eq]
    refine anyOfC_empty hD isFree_R comps (fun φ hφ => ?_)
    obtain ⟨cl', hcl', rfl⟩ := List.mem_map.mp hφ
    obtain ⟨-, hb', -, hpl', hf'⟩ := hothers cl' hcl'
    exact hpl' hws
      (fun i hi => hkeys _ (hN _ (mem_varsOf_anyOfC hφ (varsOf_exclusion (hpres cl' hcl') (binds_of_forall hb') hi))))
      (fun j s hj => hkeys _ (hP _ (hv.1 j _ (by rw [List.getElem?_map, hj]; rfl))))
      hRkey (fun j w s hw hs => hX j w _ hw (by rw [List.getElem?_map, hs]; rfl)) hR' hσr2 hf' m0

end

/-! ## L3, fourth stage: functions and terms -/

section
variable {c : Semantics} {M : Type} {I : Interpretation KoreAML.Sym M}
variable [Inhabited M] (hI : I ⊧ᴵP Γ c) (hnn : NamesNumbered c) (hsc : SortCtx c) [OvlOK c]
  (hok : c.sortedOK = true) (hbc : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, binds cl.vars.length (varOccsList cl.pats) = true) (hph : patHooksApart c = true)
  (hneg : ∀ fn ∈ c.allFns, ∀ cl ∈ fn.clauses, ClauseNeg c fn cl → ExclEmpty c I fn cl)
include hI hnn hsc hok hbc hph hneg

/-- A clause that decides, read in a model: from its right side's reading `ihright` (for the
result `r`), `f` applied to the arguments' elements is what `r` denotes, through `plain_eq4` or
`compete_eq4`. -/
theorem clause_den4 (hpreTop : c.clausesPreTop = true) {f : Sym} {fn : Fn} {cl : Clause} {ws : List GroundTerm} {σ' : Subst}
    {L : List CtorSig} {r : Option GroundTerm}
    (hfn : c.lookupFn f = some fn) (hmem : fn ∈ c.allFns) (hcl : cl ∈ fn.clauses)
    (hws : c.sortsOf ws = some fn.args) (hσ' : c.WellSorted cl.vars σ') (hmatch : PatVals c σ' cl.pats ws)
    (hpats : sortsOfTerms c.patCtxNF cl.vars cl.pats = some fn.args)
    (hbinds : ∀ i < cl.vars.length, i ∈ varOccsList cl.pats) (hL : HeadsOK c L)
    (hreqs : ∀ t, cl.req = some t → sortOfTerm (c.rhsCtx L) cl.vars t = some Srt.bool)
    (hrhss : sortOfTerm (c.rhsCtx L) cl.vars cl.rhs = some fn.result)
    (henss : ∀ t, cl.ens = some t → sortOfTerm (c.rhsCtx L) cl.vars t = some Srt.bool)
    (hr : ∀ v, r = some v → c.sortOf v = some fn.result)
    (ihright : ∀ (tbl : VarTable) (e' : Valuation M), Agrees c I tbl (canonVars c cl.vars) σ' e' →
      ∀ m', (KoreAML.tr ⟨tbl, []⟩ (clauseRight c fn cl)).interpret I e' m' ↔ Res c I e' r m')
    (ihreq : ∀ t, cl.req = some t → ∀ (tbl : VarTable) (e' : Valuation M), Agrees c I tbl (canonVars c cl.vars) σ' e' →
      ∀ m', (KoreAML.tr ⟨tbl, []⟩ (Term.kore c (canonVars c cl.vars) t)).interpret I e' m' ↔
        (den c (bool true)).interpret I e' m')
    (hfails : ∀ cl' ∈ fn.clauses, cl'.aside = false → cl'.prio < cl.prio → ModelFails c I cl' ws)
    (e : Valuation M) (m : M) :
    (KoreAML.den (symApp c f (GroundTerm.koreList c ws))).interpret I e m ↔ Res c I e r m := by
  have hreqv : ∀ t, cl.req = some t → ∀ i ∈ varOccs t, i < cl.vars.length := fun t ht => varOccs_lt t (hreqs t ht)
  have hrhsv := varOccs_lt _ hrhss
  have hensv : ∀ t, cl.ens = some t → ∀ i ∈ varOccs t, i < cl.vars.length := fun t ht => varOccs_lt t (henss t ht)
  have ihreq' := fun tbl e' hag t ht m' => ihreq t ht tbl e' hag m'
  by_cases hlow : lowerClauses fn cl = []
  · exact plain_eq4 hI hnn hph hsc.trans hfn (clauseEquation_mem hcl hlow) (clause_preTop (hpreTop := hpreTop) hok hmem hcl) (clause_exsNil hok hbc hmem hcl) hws hσ' hmatch hpats
      hbinds hreqv hrhsv hensv hr ihreq' ihright e m
  · refine compete_eq4 hI hnn hph hsc.trans hfn (competingEquation_mem hcl hlow) (clause_preTop (hpreTop := hpreTop) hok hmem hcl)
      (clause_exsNil hok hbc hmem hcl)
      (fun cl' hcl' => clause_preTop (hpreTop := hpreTop) hok hmem (mem_lowerClauses.mp hcl').1) hws (fun cl' hcl' => ?_) hσ' hmatch hpats
      hbinds hreqv hrhsv hensv hr ihreq' ihright e m
    obtain ⟨hcl'', hna'', hlt⟩ := mem_lowerClauses.mp hcl'
    obtain ⟨hp', hb', L', hL', hrq', -⟩ := clause_ctx hok hbc hmem hcl''
    exact ⟨Semantics.pats_nf (OvlOK.hyp inferInstance hsc.trans) hmem hcl'' hp', hb', fun t ht => varOccs_lt t (hrq' t ht),
      hneg fn hmem cl' hcl'' ⟨cl, hcl, hlt⟩, hfails cl' hcl'' hna'' hlt⟩

mutual
  /-- **L3, functions, fourth stage.** A function of the semantics, at arguments of its sorts,
  applied to their elements, is what its result denotes, defined or not: through its clause's
  equation (whose right-hand side may denote nothing), the clauses of a smaller priority it negates
  failing at the arguments; or, where every clause fails, through its rest's graph
  (`rest_den`). -/
  theorem eval_den4 (hpreTop : c.clausesPreTop = true) : ∀ {f : Sym} {ws : List GroundTerm} {r : Option GroundTerm}, Eval c f ws r →
      ∀ {fn : Fn}, c.lookupFn f = some fn → c.sortsOf ws = some fn.args →
      ∀ (e : Valuation M) m, (KoreAML.den (symApp c f (GroundTerm.koreList c ws))).interpret I e m ↔ Res c I e r m
    | _, _, _, .clause (fn := fn') (cl := cl) (σ := σ') hfn' hcl hσ' hmatch hreq _ hprio _ hrhs hens _,
        fn, hfn, hws, e, m => by
      rw [hfn] at hfn'; cases hfn'
      have hmem := (lookupFn_spec hfn).1
      obtain ⟨hpats, hbinds, L, hL, hreqs, hrhss, henss⟩ := clause_ctxE hok hbc hmem hcl
      have hr : ∀ v, _ = some v → c.sortOf v = some fn'.result := fun v hv => EvalTerm.sorted hsc hrhs hL hσ' hrhss hv
      exact clause_den4 (hpreTop := hpreTop) hI hnn hsc hok hbc hph hneg hfn hmem hcl hws hσ' hmatch
        (Semantics.pats_nf (OvlOK.hyp inferInstance hsc.trans) hmem hcl hpats) hbinds hL hreqs hrhss
        henss hr (fun tbl e' hag => right_iff hI hnn hmem hr
          (fun m' => evalTerm_den4 (hpreTop := hpreTop) hrhs hL hσ' (canonVars_length c cl.vars) hag hrhss m')
          (fun t ht m' => evalTerm_den4 (hpreTop := hpreTop) (hens t ht) hL hσ' (canonVars_length c cl.vars) hag (henss t ht) m'))
        (fun t ht tbl e' hag m' => evalTerm_den4 (hpreTop := hpreTop) (hreq t ht) hL hσ' (canonVars_length c cl.vars) hag (hreqs t ht) m')
        (fun cl' hcl'' hna'' hlt => fails_den4 (hpreTop := hpreTop) (hprio cl' hcl'' hna'' hlt) hmem hcl'') e m
    | _, _, _, .ensFails (fn := fn') (cl := cl) (σ := σ') (t := t) hfn' hcl hσ' hmatch hreq _ hprio _ ht he hw,
        fn, hfn, hws, e, m => by
      rw [hfn] at hfn'; cases hfn'
      have hmem := (lookupFn_spec hfn).1
      obtain ⟨hpats, hbinds, L, hL, hreqs, hrhss, henss⟩ := clause_ctxE hok hbc hmem hcl
      exact clause_den4 (hpreTop := hpreTop) hI hnn hsc hok hbc hph hneg hfn hmem hcl hws hσ' hmatch
        (Semantics.pats_nf (OvlOK.hyp inferInstance hsc.trans) hmem hcl hpats) hbinds hL hreqs hrhss
        henss (fun v hv => by cases hv) (fun tbl e' hag => right_empty hI hnn hmem ht hw
          (fun v hv => EvalTerm.sorted hsc he hL hσ' (henss t ht) hv)
          (fun m' => evalTerm_den4 (hpreTop := hpreTop) he hL hσ' (canonVars_length c cl.vars) hag (henss t ht) m'))
        (fun t ht tbl e' hag m' => evalTerm_den4 (hpreTop := hpreTop) (hreq t ht) hL hσ' (canonVars_length c cl.vars) hag (hreqs t ht) m')
        (fun cl' hcl'' hna'' hlt => fails_den4 (hpreTop := hpreTop) (hprio cl' hcl'' hna'' hlt) hmem hcl'') e m
    | _, ws, _, .rest (fn := fn') hfn' hnone, fn, hfn, hws, e, m => by
      rw [hfn] at hfn'; cases hfn'
      obtain ⟨hmem, hlab⟩ := lookupFn_spec hfn
      have h := rest_den hI hmem hws hnone e m
      rwa [hlab] at h
    | _, _, _, .clauseEx (fn := fn') hfn' hcl _ _ _ _ _ hne _ _ _ _, fn, hfn, _, _, _ => by
      rw [hfn] at hfn'; cases hfn'
      exact absurd (clause_exsNil hok hbc (lookupFn_spec hfn).1 hcl) hne
    | _, _, _, .exNone (fn := fn') hfn' hcl hne _ _ _ _ _ _ _, fn, hfn, _, _, _ => by
      rw [hfn] at hfn'; cases hfn'
      exact absurd (clause_exsNil hok hbc (lookupFn_spec hfn).1 hcl) hne
  termination_by structural _ _ _ h => h
  /-- A clause that fails at arguments of its function's sorts fails in the model. -/
  theorem fails_den4 (hpreTop : c.clausesPreTop = true) : ∀ {ws : List GroundTerm} {cl : Clause}, Fails c ws cl →
      ∀ {fn : Fn}, fn ∈ c.allFns → cl ∈ fn.clauses → ModelFails c I cl ws
    | _, _, .intro h, fn, hfn, hcl => fun σ hσ hpv tbl e hag => reqFails_den4 (hpreTop := hpreTop) (h σ (hσ.at _) hpv) hfn hcl hσ tbl e hag
  termination_by structural _ _ h => h
  theorem reqFails_den4 (hpreTop : c.clausesPreTop = true) : ∀ {σ : Subst} {cl : Clause}, ReqFails c σ cl →
      ∀ {fn : Fn}, fn ∈ c.allFns → cl ∈ fn.clauses → c.WellSorted cl.vars σ →
      ∀ (tbl : VarTable) (e : Valuation M), Agrees c I tbl (canonVars c cl.vars) σ e →
      ∃ t r, cl.req = some t ∧ r ≠ some (bool true) ∧ (∀ v, r = some v → c.sortOf v = some Srt.bool) ∧
        ∀ m, (KoreAML.tr ⟨tbl, []⟩ (Term.kore c (canonVars c cl.vars) t)).interpret I e m ↔ Res c I e r m
    | _, cl, .pre h, fn, hfn, hcl, hσ, tbl, e, hag => by
      rw [clause_preTop (hpreTop := hpreTop) hok hfn hcl] at h; exact absurd h.top_eq (by simp)
    | _, cl, .intro (t := t) (r := r) ht he hr, fn, hfn, hcl, hσ, tbl, e, hag => by
      obtain ⟨-, -, L, hL, hreqs, -⟩ := clause_ctx hok hbc hfn hcl
      exact ⟨t, r, ht, hr, fun v hv => EvalTerm.sorted hsc he hL hσ (hreqs t ht) hv,
        evalTerm_den4 (hpreTop := hpreTop) he hL hσ (canonVars_length c cl.vars) hag (hreqs t ht)⟩
  termination_by structural _ _ h => h
  /-- **L3, terms, fourth stage.** A well-sorted right-hand side or `requires`, at a valuation that
  agrees with a well-sorted σ, translates to what its result under σ denotes: the value's element,
  or nothing where it is undefined. -/
  theorem evalTerm_den4 (hpreTop : c.clausesPreTop = true) : ∀ {σ : Subst} {t : Term} {r : Option GroundTerm}, EvalTerm c σ t r →
      ∀ {L : List CtorSig} {vars : List Srt} {vs : List KoreAML.Var} {tbl : VarTable} {e : Valuation M} {s : Srt},
      HeadsOK c L → c.WellSorted vars σ → vs.length = vars.length → Agrees c I tbl vs σ e →
      sortOfTerm (c.rhsCtx L) vars t = some s →
      ∀ m, (KoreAML.tr ⟨tbl, []⟩ (Term.kore c vs t)).interpret I e m ↔ Res c I e r m
    | _, _, _, .var (i := i), L, vars, vs, tbl, e, s, hL, hσ, hvs, hag, ht, m => by
      have hi := sortOfTerm_var.mp ht
      have hlt : i < vs.length := by rw [hvs]; exact (List.getElem?_eq_some_iff.mp hi).1
      obtain ⟨v, hv, -⟩ := hσ i s hi
      rw [hv, tr_var]
      exact hag i v hlt hv m
    | _, _, _, .dv (s := s') (lit := lit), _, _, vs, tbl, e, _, _, _, _, _, _, m => by
      show _ ↔ (den c (.dv s' lit)).interpret I e m
      rw [Term.kore]; unfold den KoreAML.den; rw [GroundTerm.kore]; unfold srtOf
      rw [KoreAML.tr_dv, KoreAML.tr_dv]
    | _, _, _, .inj (a := a) (b := b) (t := t) (r := r) h', L, vars, vs, tbl, e, s, hL, hσ, hvs, hag, ht, m => by
      obtain ⟨hab, ht', -⟩ := sortOfTerm_inj.mp ht
      have ih := evalTerm_den4 (hpreTop := hpreTop) h' hL hσ hvs hag ht'
      rw [Term.kore, KoreAML.tr_injP]
      cases r with
      | none =>
        simp only [Option.map_none, Res, iff_false]
        exact injApp_empty (fun m h => ((ih m).mp h)) m
      | some w =>
        have hw := EvalTerm.sorted hsc h' hL hσ ht' rfl
        simp only [Option.map_some, Res]
        rcases injNormal_cases a b w with ⟨a', a'', w', rfl, hn⟩ | hn
        · rw [hn]
          obtain ⟨h1, -, h3, rfl⟩ := sortOf_inj.mp hw
          obtain ⟨x, hx, hxs⟩ := den_single hI h3 e
          rw [injApp_congr ih m]
          show (KoreAML.appList _ [_, _, den c (.inj a' a w')]).interpret I e m ↔ _
          rw [den_inj, den_inj]
          exact coh_at hI h1 hab hx hxs m
        · rw [hn, den_inj]
          exact injApp_congr ih m
    | _, _, _, .ctor (f := f) (ts := ts) (rs := rs) hk hts, L, vars, vs, tbl, e, s, hL, hσ, hvs, hag, ht, m => by
      obtain ⟨k, hk', hargs, -⟩ := sortOfTerm_app.mp ht
      obtain ⟨k0, hk0⟩ := Option.isSome_iff_exists.mp hk
      have ih := evalTerms_den4 (hpreTop := hpreTop) hts hL hσ hvs hag hargs
      rw [kore_app_plain hnn.1 hk0]
      cases hall : allSome rs with
      | none =>
        simp only [Option.map_none, Res, iff_false]
        exact ih.2 hall _ m
      | some ws =>
        simp only [Option.map_some, Res]
        rw [den_ctor]
        exact ih.1 ws hall _ _ (fun _ => Iff.rfl) m
    | _, _, _, .hook (f := f) (rs := rs) (r := r) hk hhk hts hh hund, L, vars, vs, tbl, e, s, hL, hσ, hvs, hag, ht, m => by
      obtain ⟨k, hk', hargs, -⟩ := sortOfTerm_app.mp ht
      obtain ⟨hks, hkn⟩ := rhs_lookup_hook hk hhk hk'
      have ih := evalTerms_den4 (hpreTop := hpreTop) hts hL hσ hvs hag hargs
      rw [kore_app, tr_symApp]
      cases hall : allSome rs with
      | none =>
        rw [hund hall]
        simp only [Res, iff_false]
        exact ih.2 hall _ m
      | some ws =>
        have hv := hh ws hall
        have hws := EvalTerms.sorted hsc hts hL hσ hargs hall
        have hax := sat_hookRes hI hks hws (by rw [hkn]; exact hv)
        have hgr := (KoreAML.interp_equal (defOK hI)).mp (hax e default) m
        rw [hkn] at hgr
        unfold KoreAML.den at hgr
        rw [tr_symApp] at hgr
        rw [ih.1 ws hall _ _ (fun _ => Iff.rfl) m, hgr]
        cases r with
        | none => simp [Res, Pattern.interpret]
        | some v => rfl
    | _, _, _, .param (f := f) (rs := rs) (r := r) hk hhk hp hts hr, L, vars, vs, tbl, e, s, hL, hσ, hvs, hag, ht, m => by
      obtain ⟨k, hk', hargs, -⟩ := sortOfTerm_app.mp ht
      obtain ⟨kp, hkp, rfl, hkn⟩ := rhs_lookup_param hk hhk hp hk'
      have ih := evalTerms_den4 (hpreTop := hpreTop) hts hL hσ hvs hag hargs
      rw [kore_app, tr_symApp]
      cases hall : allSome rs with
      | none =>
        rw [hr, hall]
        simp only [Option.bind_none, Res, iff_false]
        exact ih.2 hall _ m
      | some ws =>
        have hws := EvalTerms.sorted hsc hts hL hσ hargs hall
        have hax := sat_dom hI (Or.inr (Or.inl ⟨kp, ws, hkp, hws, rfl⟩))
        have hgr := (KoreAML.interp_equal (defOK hI)).mp (hax e default) m
        rw [hkn] at hgr
        unfold KoreAML.den at hgr
        rw [tr_symApp] at hgr
        rw [ih.1 ws hall _ _ (fun _ => Iff.rfl) m, hgr, hr, hall]
        simp only [Option.bind_some]
        cases c.paramVal f ws with
        | none => simp [Res, Pattern.interpret]
        | some v => rfl
    | _, _, _, .call (f := f) (rs := rs) (vs := ws) hk hh hts hvs' hf hp, L, vars, vs, tbl, e, s, hL, hσ, hvs, hag, ht, m => by
      obtain ⟨k, hk', hargs, -⟩ := sortOfTerm_app.mp ht
      obtain ⟨fn, hfnm, rfl, hlook⟩ := rhs_lookup_call hsc hL hk hh hp (Eval.lookupFn_ne hf) hk'
      have ih := evalTerms_den4 (hpreTop := hpreTop) hts hL hσ hvs hag hargs
      have hws := EvalTerms.sorted hsc hts hL hσ hargs hvs'
      rw [kore_app, tr_symApp, ih.1 ws hvs' _ _ (fun _ => Iff.rfl) m]
      have := eval_den4 (hpreTop := hpreTop) hf hlook hws e m
      unfold KoreAML.den at this
      rw [tr_symApp] at this
      exact this
    | _, _, _, .callUndef (f := f) (rs := rs) hk hh hts hvs' hp, L, vars, vs, tbl, e, s, hL, hσ, hvs, hag, ht, m => by
      obtain ⟨k, hk', hargs, -⟩ := sortOfTerm_app.mp ht
      have ih := evalTerms_den4 (hpreTop := hpreTop) hts hL hσ hvs hag hargs
      rw [kore_app, tr_symApp]
      simp only [Res, iff_false]
      exact ih.2 hvs' _ m
    | _, _, _, .ovlFn (f := f) (rs := rs) (vs := ws) (o := o) (kg := kg) (r := r) hk ho hts hvs' hlo hcov hf,
        L, vars, vs, tbl, e, s, hL, hσ, hvs, hag, ht, m => by
      obtain ⟨k, hk', hargs, -⟩ := sortOfTerm_app.mp ht
      obtain ⟨o', hlo', rfl⟩ := rhs_lookup_ovl hsc hL hk' ho
      rw [hlo] at hlo'; cases hlo'
      have ih := evalTerms_den4 (hpreTop := hpreTop) hts hL hσ hvs hag hargs
      have hws := EvalTerms.sorted hsc hts hL hσ hargs hvs'
      obtain ⟨fn, hfn, hlook, hsig, hkg, hb, -, hus⟩ :=
        OvlLaws.fnCover_fn_ovlF ((inferInstance : OvlOK c).hyp hsc.trans).fnFacts hlo hws hcov
      have hname : kg.name = fn.label := by rw [hsig]
      have hres : kg.result = fn.result := by rw [hsig]
      have hgd := eval_den4 (hpreTop := hpreTop) hf hlook hus e
      rw [kore_app, tr_symApp, ih.1 ws hvs' _ _ (fun _ => Iff.rfl) m]
      have := covDen_of hI hsc.trans hlo hws hcov (namesNumbered_cover hnn hlo hcov)
        (fun v hv => by rw [hres]; exact Eval.sorted hsc hf hlook hus hv) e hgd m
      unfold KoreAML.den at this
      rw [tr_symApp] at this
      exact this
    | _, _, _, .ovl (f := f) (rs := rs) hk ho hts hnf, L, vars, vs, tbl, e, s, hL, hσ, hvs, hag, ht, m => by
      obtain ⟨k, hk', hargs, -⟩ := sortOfTerm_app.mp ht
      obtain ⟨o, hlo, rfl⟩ := rhs_lookup_ovl hsc hL hk' ho
      have ih := evalTerms_den4 (hpreTop := hpreTop) hts hL hσ hvs hag hargs
      rw [kore_app, tr_symApp]
      cases hall : allSome rs with
      | none =>
        simp only [Option.map_none, Res, iff_false]
        exact ih.2 hall _ m
      | some ws =>
        have hws := EvalTerms.sorted hsc hts hL hσ hargs hall
        simp only [Option.map_some, Res]
        rw [ih.1 ws hall _ _ (fun _ => Iff.rfl) m]
        have := (normDen_of hI hsc.trans).1 hlo hws (hnf ws hall) e m
        unfold KoreAML.den at this
        rw [tr_symApp] at this
        exact this
  termination_by structural _ _ _ h => h
  theorem evalTerms_den4 (hpreTop : c.clausesPreTop = true) : ∀ {σ : Subst} {ts : List Term} {rs : List (Option GroundTerm)}, EvalTerms c σ ts rs →
      ∀ {L : List CtorSig} {vars : List Srt} {vs : List KoreAML.Var} {tbl : VarTable} {e : Valuation M} {ss : List Srt},
      HeadsOK c L → c.WellSorted vars σ → vs.length = vars.length → Agrees c I tbl vs σ e →
      sortsOfTerms (c.rhsCtx L) vars ts = some ss →
      (∀ ws, allSome rs = some ws → ∀ (acc acc' : KoreAML.P), (∀ m, acc.interpret I e m ↔ acc'.interpret I e m) →
        ∀ m, (KoreAML.trArgs ⟨tbl, []⟩ acc (Term.koreList c vs ts)).interpret I e m ↔
          (KoreAML.trArgs ⟨[], []⟩ acc' (GroundTerm.koreList c ws)).interpret I e m) ∧
      (allSome rs = none → ∀ (acc : KoreAML.P) m, ¬ (KoreAML.trArgs ⟨tbl, []⟩ acc (Term.koreList c vs ts)).interpret I e m)
    | _, _, _, .nil, _, _, _, _, _, _, _, _, _, _, _ => by
      refine ⟨fun ws hws acc acc' hacc m => ?_, fun h => by simp [allSome] at h⟩
      simp only [allSome, Option.some.injEq] at hws
      subst hws
      rw [Term.koreList, GroundTerm.koreList, KoreAML.trArgs_nil, KoreAML.trArgs_nil]
      exact hacc m
    | _, _, _, .cons (t := t) (ts := ts) (r := r) (rs := rs) h hs, L, vars, vs, tbl, e, ss, hL, hσ, hvs, hag, ht => by
      obtain ⟨s, ss', h1, h2, -⟩ := sortsOfTerms_cons.mp ht
      have ih1 := evalTerm_den4 (hpreTop := hpreTop) h hL hσ hvs hag h1
      have ih2 := evalTerms_den4 (hpreTop := hpreTop) hs hL hσ hvs hag h2
      constructor
      · intro ws hws acc acc' hacc m
        simp only [allSome, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hws
        obtain ⟨w, rfl, ws', hws', rfl⟩ := hws
        rw [Term.koreList, GroundTerm.koreList, KoreAML.trArgs_cons, KoreAML.trArgs_cons]
        exact ih2.1 ws' hws' _ _ (KoreAML.interp_app_congr hacc ih1) m
      · intro hn acc m
        rw [Term.koreList, KoreAML.trArgs_cons]
        cases r with
        | none =>
          exact trArgs_empty (fun m' hm' => by
            obtain ⟨_, b, _, hb, _⟩ := KoreAML.interp_app.mp hm'
            exact (ih1 b).mp hb) _ m
        | some w =>
          cases hrs : allSome rs with
          | none => exact ih2.2 hrs _ m
          | some ws' => simp [allSome, hrs] at hn
  termination_by structural _ _ _ h => h
end

/-! ## L4, fourth stage: a rule's step -/

/-- A rule that does not apply to a configuration (`NotApplies`) does not apply in the model, its
`requires` read whether defined or not. -/
theorem notApplies_model4 (hpreTop : c.clausesPreTop = true) {r : Rule} (hr : r ∈ c.rules) (hpre : r.pre = .top) {x : GroundTerm} (h : NotApplies c r x) :
    ModelNotApplies c I r x := by
  intro σ hσ hpv tbl e hag
  obtain ⟨-, hreqs, -⟩ := rule_ctx hok hr
  obtain ⟨_, _, ht, he, hv⟩ := (h σ (hσ.at _) hpv).req_of_top hpre
  · exact ⟨_, _, ht, hv, fun u hu => EvalTerm.sorted hsc he fns_headsOK hσ (hreqs _ ht) hu,
      evalTerm_den4 (hpreTop := hpreTop) hI hnn hsc hok hbc hph hneg he fns_headsOK hσ (canonVars_length c r.vars) hag (hreqs _ ht)⟩

/-- **A rule's axiom, read in a model**, whatever its left-hand part `L` (`rule_at`, with the
right-hand side read by `evalTerm_den4`). -/
theorem rule_at4 (hpreTop : c.clausesPreTop = true) {r : Rule} (hr : r ∈ c.rules) {L : Kore.Pattern}
    (hpat : prioRuleK c r = .rewrites (srtOf c topCellSort) L
      (.and (srtOf c topCellSort) [Term.kore c (canonVars c r.vars) r.rhs,
        reqPat (srtOf c topCellSort) (r.ens.map (Term.kore c (canonVars c r.vars)))]))
    (hVin : ∀ i < r.vars.length, canonKey c r.vars i ∈ KoreAML.varsOf L)
    (hfree : ∀ k ∈ KoreAML.freeOf [] L, ∃ i < r.vars.length, k = canonKey c r.vars i)
    {σ : Subst} (hσ : c.WellSorted r.vars σ) {x y : Config c} (heval : EvalTerm c σ r.rhs (some y.val))
    (hens : ∀ t, r.ens = some t → EvalTerm c σ t (some (bool true)))
    (hL : ∀ (tbl : VarTable) (e : Valuation M), (∀ k ∈ KoreAML.varsOf L, k ∈ tbl) →
      Agrees c I tbl (canonVars c r.vars) σ e →
      (∀ b, (KoreAML.tr ⟨tbl, []⟩ (.and (srtOf c topCellSort) [Term.kore c (canonVars c r.vars) r.rhs,
        reqPat (srtOf c topCellSort) (r.ens.map (Term.kore c (canonVars c r.vars)))])).interpret I e b ↔ (den c y.val).interpret I e b) →
      (KoreAML.tr ⟨tbl, []⟩ L).interpret I e (elemOf c I x.val))
    (e : Valuation M) (m : M) (hm : (den c x.val).interpret I e m) :
    (KoreAML.sNext (den c y.val)).interpret I e m := by
  have hD := defOK hI
  obtain ⟨-, -, hrhss⟩ := rule_ctx hok hr
  have hax := sat_rules hI (Or.inl ⟨_, List.mem_map.mpr ⟨r, hr, rfl⟩, rfl⟩)
  rw [hpat] at hax
  let C := srtOf c topCellSort
  let vs := canonVars c r.vars
  let ax : Kore.Axiom :=
    { sortVars := [], pattern := .rewrites C L (.and C [Term.kore c vs r.rhs, reqPat C (r.ens.map (Term.kore c vs))]),
      attributes := [] }
  let tbl : VarTable := KoreAML.tableOf ax.sortVars ax.pattern
  let e' : Valuation M := valOf tbl (ruleVal c I r.vars.length σ)
  have hvarsL : ∀ k ∈ KoreAML.varsOf L, k ∈ tbl := fun k hk => by
    refine List.mem_eraseDups.mpr (List.mem_append_right _ ?_)
    show k ∈ KoreAML.varsOf (.rewrites C L _)
    rw [KoreAML.varsOf]
    exact List.mem_append_left _ (List.mem_append_right _ hk)
  have hVmem : ∀ i, i < r.vars.length → canonKey c r.vars i ∈ tbl := fun i hi => hvarsL _ (hVin i hi)
  have hVv : ∀ i, i < r.vars.length → e'.evalEvar (tbl.ev (canonKey c r.vars i)) =
      (match σ.lookup i with | some v => elemOf c I v | none => default) := fun i hi => by
    rw [valOf_ev (hVmem i hi), canonKey_eq c hi]
    simp only [ruleVal]
    rw [varIdx_eq hi]
    all_goals rfl
  have hvsort : ∀ i, i < r.vars.length → ∃ v, σ.lookup i = some v ∧ c.sortOf v = some (r.vars.getD i 0) :=
    fun i hi => hσ i _ (by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; rfl)
  have hag : Agrees c I tbl vs σ e' := fun i v hi hl m => by
    rw [canonVars_length] at hi
    show m = e'.evalEvar (tbl.ev (canonKey c r.vars i)) ↔ _
    rw [hVv i hi, hl]
    obtain ⟨w, hw, hsw⟩ := hvsort i hi
    rw [hl] at hw; cases hw
    exact ((elemOf_spec hI hsw e').1 m).symm
  have hfree' : ∀ k, k ∈ KoreAML.freeOf [] ax.pattern → ∃ i, i < r.vars.length ∧ k = canonKey c r.vars i := by
    intro k hk
    change k ∈ KoreAML.freeOf [] (.rewrites C L _) at hk
    rw [KoreAML.freeOf] at hk
    rcases List.mem_append.mp hk with hk | hk
    · obtain ⟨i, hi, h⟩ := hfree k hk; exact ⟨i, hi, h⟩
    · obtain ⟨i, hi, h⟩ := freeOf_right hok hr hk; exact ⟨i, hi, h⟩
  have hg : ∀ k ∈ (ax.sortVars.map KoreAML.sortVarKey ++ KoreAML.freeOf [] ax.pattern).eraseDups, ∀ m,
      (KoreAML.guardOf tbl k).interpret I e' m := by
    intro k hk m'
    have hk' : k ∈ KoreAML.freeOf [] ax.pattern := by simpa [ax] using List.mem_eraseDups.mp hk
    obtain ⟨i, hi, rfl⟩ := hfree' k hk'
    obtain ⟨w, hw, hsw⟩ := hvsort i hi
    have hkk := canonKey_eq c hi
    rw [hkk, KoreAML.interp_guard_evar hD, trSort_srt, ← hkk, hVv i hi, hw]
    exact (elemOf_spec hI hsw e').2
  obtain ⟨a, ha, has⟩ := den_single hI x.property e'
  have hxa : elemOf c I x.val = a := (ha _).mp ((elemOf_spec hI x.property e').1 _ |>.mpr rfl)
  have hP := (KoreAML.trAxiom_at hD hax e' hg a).mpr (by
    show (KoreAML.inhOf (KoreAML.trSort tbl (srtOf c topCellSort))).interpret I e' a
    unfold srtOf; rw [trSort_srt]; exact has)
  have hP' : (KoreAML.tr ⟨tbl, []⟩ ax.pattern).interpret I e' a := hP
  change (KoreAML.tr ⟨tbl, []⟩ (.rewrites C L _)).interpret I e' a at hP'
  rw [KoreAML.tr] at hP'
  unfold KoreAML.sRewrites at hP'
  rw [KoreAML.interp_sImp] at hP'
  obtain ⟨-, himp⟩ := hP'
  have hrhsR : ∀ b, (KoreAML.tr ⟨tbl, []⟩ (Term.kore c vs r.rhs)).interpret I e' b ↔ (den c y.val).interpret I e' b :=
    fun b => evalTerm_den4 (hpreTop := hpreTop) hI hnn hsc hok hbc hph hneg heval fns_headsOK hσ (canonVars_length c r.vars) hag hrhss b
  have hensS := rule_ctx_ens hok hr
  have hrightR := right_den hI hrhsR (fun a' ha' => reqPat_holds hI (fun t ht b =>
    evalTerm_den4 (hpreTop := hpreTop) hI hnn hsc hok hbc hph hneg (hens t ht) fns_headsOK hσ (canonVars_length c r.vars) hag (hensS t ht) b) ha')
  have hL' := himp (by rw [← hxa]; exact hL tbl e' hvarsL hag hrightR)
  obtain ⟨n, b, hn, hb, happ⟩ := KoreAML.interp_app.mp hL'
  rw [tr_and2, KoreAML.interp_sAnd] at hb
  have hby := (hrhsR b).mp hb.1
  have hma : m = a := by
    have := ((den_closed c x.val).interp e e' m).mp hm
    exact (ha m).mp this
  rw [hma]
  exact KoreAML.interp_app.mpr ⟨n, b, hn, ((den_closed c y.val).interp e' e b).mp hby, happ⟩

/-- The left-hand side and the `requires` of a rule's axiom hold of the configuration it
matches, at a valuation that agrees with the match. -/
theorem lhs_req_hold4 (hpreTop : c.clausesPreTop = true) {r : Rule} (hr : r ∈ c.rules) {σ : Subst} (hσ : c.WellSorted r.vars σ) {x : Config c}
    (hmatch : PatVal c σ r.lhs x.val) (hreq : ∀ t, r.req = some t → EvalTerm c σ t (some (bool true)))
    {tbl : VarTable} {e : Valuation M} (hag : Agrees c I tbl (canonVars c r.vars) σ e) :
    (KoreAML.tr ⟨tbl, []⟩ (Term.kore c (canonVars c r.vars) r.lhs)).interpret I e (elemOf c I x.val) ∧
      (KoreAML.tr ⟨tbl, []⟩ (reqPat (srtOf c topCellSort) (r.req.map (Term.kore c (canonVars c r.vars))))).interpret I e
        (elemOf c I x.val) := by
  have hD := defOK hI
  have hc := sat_sigItem hI (sig_ceilDef (c := c))
  obtain ⟨hlhs, hreqs, -⟩ := rule_ctx hok hr
  obtain ⟨σC, hσC1, hσC2⟩ := sortSing hI (top_numbered (c := c))
  obtain ⟨σB, hσB1, hσB2⟩ := sortSing hI (bool_numbered (c := c))
  rw [sortName_bool] at hσB1
  have hxs := elemOf_spec hI x.property e
  have hSC : ∀ b, (KoreAML.trSort tbl (srtOf c topCellSort)).interpret I e b ↔ b = σC := by
    unfold srtOf; rw [trSort_srt]; exact hσC1
  have haC : Inh I σC (elemOf c I x.val) := by
    have := hxs.2
    exact (KoreAML.interp_inhOf_of (S := KoreAML.sym _) hσC1).mp this
  refine ⟨(patVal_den4 hI hnn.1 hph hsc.trans hσ (canonVars_length c r.vars) hag hmatch
    (Semantics.lhs_nf OvlOK.ok hr hlhs)).2 _ |>.mpr
    ((hxs.1 _).mpr rfl), ?_⟩
  cases hq : r.req with
  | none =>
    simp only [Option.map_none, reqPat]
    rw [KoreAML.tr, KoreAML.interp_sTop hD (by unfold srtOf; rw [trSort_srt]; rfl), KoreAML.interp_inhOf_of hSC]
    exact haC
  | some t =>
    simp only [Option.map_some, reqPat]
    rw [KoreAML.tr, KoreAML.interp_sEquals hD hc (by rw [trSort_srt]; exact hσB1) hSC hσB2 hσC2]
    refine ⟨haC, fun b _ => ?_⟩
    rw [evalTerm_den4 (hpreTop := hpreTop) hI hnn hsc hok hbc hph hneg (hreq t hq) fns_headsOK hσ (canonVars_length c r.vars) hag (hreqs t hq) b,
      KoreAML.tr_dv]
    show (den c (bool true)).interpret I e b ↔ _
    unfold den KoreAML.den bool
    rw [GroundTerm.kore, sortName_bool, KoreAML.tr_dv]
    exact Iff.rfl

/-- **L4, fourth stage, in a model.** In a model of `Γ` in which every clause read negatively has
an empty exclusion where it fails (`hneg`), and every rule read negatively has an empty `applies` where it
does not apply (`hnegr`), the configuration `x` has each of its `Step` successors `y` as a
successor. Left-hand sides and clause patterns read positively may be collection patterns
(`patVal_den4`). -/
theorem step_at4 (hpreTop : c.clausesPreTop = true) (hb : ∀ r ∈ c.rules, binds r.vars.length (varOccs r.lhs) = true) (htop : ∀ r ∈ c.rules, r.pre = .top ∧ r.post = .top) (hnegr : ∀ r ∈ c.rules, RuleNeg c r → AppEmpty c I r) {x y : Config c} (hstep : Step c x y)
    (e : Valuation M) (m : M) (hm : (den c x.val).interpret I e m) :
    (KoreAML.sNext (den c y.val)).interpret I e m := by
  obtain ⟨r, hr, σ, hσ, hmatch, hreq, -, heval, hens, -, hprio⟩ := hstep
  obtain ⟨hpre₀, hpost₀⟩ := htop _ hr
  have hex₀ : r.exs = [] := Semantics.sortedOK_exsNil hok hr (hb r hr)
  have hD := defOK hI
  obtain ⟨hlhs, hreqs, -⟩ := rule_ctx hok hr
  have hbinds := Exec.binds_all (hb _ hr)
  let C := srtOf c topCellSort
  let vs := canonVars c r.vars
  let comps := (c.rules.filter (·.prio < r.prio)).map fun r' => applies c r' (canonRulePres r')
  let L0 : Kore.Pattern := .and C [Term.kore c vs r.lhs, reqPat C (r.req.map (Term.kore c vs)),
    .ceil C C (.and C [Term.kore c vs r.rhs, reqPat C (r.ens.map (Term.kore c vs))])]
  have hV0 : ∀ i < r.vars.length, canonKey c r.vars i ∈ KoreAML.varsOf (Term.kore c vs r.lhs) :=
    fun i hi => varsOf_kore c vs r.lhs (hbinds i hi)
  have hfree0 : ∀ k ∈ KoreAML.freeOf [] (Term.kore c vs r.lhs) ++ KoreAML.freeOf [] (reqPat C (r.req.map (Term.kore c vs))),
      ∃ i < r.vars.length, k = canonKey c r.vars i := by
    intro k hk
    rcases List.mem_append.mp hk with hk | hk
    · obtain ⟨i, hi, rfl⟩ := freeOf_kore c vs r.lhs hk
      exact ⟨i, varOccs_lt r.lhs hlhs i hi, rfl⟩
    · cases hq : r.req with
      | none => rw [hq] at hk; simp only [Option.map_none, reqPat] at hk; rw [KoreAML.freeOf] at hk; cases hk
      | some t =>
        rw [hq] at hk; simp only [Option.map_some, reqPat] at hk
        rw [KoreAML.freeOf] at hk
        rcases List.mem_append.mp hk with hk | hk
        · obtain ⟨i, hi, rfl⟩ := freeOf_kore c vs t hk
          exact ⟨i, varOccs_lt t (hreqs t hq) i hi, rfl⟩
        · rw [KoreAML.freeOf] at hk; cases hk
  by_cases hce : comps.isEmpty
  · -- no competitor: the rule's axiom as written
    have hpat : prioRuleK c r = .rewrites C L0
        (.and C [Term.kore c vs r.rhs, reqPat C (r.ens.map (Term.kore c vs))]) := by
      rw [prioRuleK_top hex₀ hpre₀ hpost₀]; dsimp only; rw [if_pos hce]
    refine rule_at4 (hpreTop := hpreTop) hI hnn hsc hok hbc hph hneg hr hpat (fun i hi => ?_) (fun k hk => ?_) hσ heval hens
      (fun tbl e' _ hag hrhsR => ?_) e m hm
    · show _ ∈ KoreAML.varsOf (.and C _)
      rw [KoreAML.varsOf, KoreAML.varsOfList]
      exact List.mem_append_right _ (List.mem_append_left _ (hV0 i hi))
    · change k ∈ KoreAML.freeOf [] (.and C _) at hk
      simp only [KoreAML.freeOf, KoreAML.freeOfList, List.append_nil, List.mem_append] at hk
      exact freeOf_rule_parts hok hr hk
    · have h := lhs_req_hold4 (hpreTop := hpreTop) hI hnn hsc hok hbc hph hneg hr hσ hmatch hreq hag
      show (KoreAML.tr ⟨tbl, []⟩ (.and C _)).interpret I e' _
      rw [tr_and3, KoreAML.interp_sAnd, KoreAML.interp_sAnd]
      exact ⟨h.1, h.2, ceil_rhs_at hI hrhsR (elemOf_top hI x tbl e')⟩
  · -- competitors: the axiom with their `applies` negated
    have hpat : prioRuleK c r = .rewrites C (.and C [Term.kore c vs r.lhs, reqPat C (r.req.map (Term.kore c vs)),
        .not C (anyOfC C comps), .ceil C C (.and C [Term.kore c vs r.rhs, reqPat C (r.ens.map (Term.kore c vs))])])
        (.and C [Term.kore c vs r.rhs, reqPat C (r.ens.map (Term.kore c vs))]) := by
      rw [prioRuleK_top hex₀ hpre₀ hpost₀]; dsimp only; rw [if_neg hce]
    have hcomp : ∀ φ ∈ comps, ∃ r' ∈ c.rules, r'.prio < r.prio ∧ φ = applies c r' (canonRulePres r') := by
      intro φ hφ
      obtain ⟨r', hr', rfl⟩ := List.mem_map.mp hφ
      obtain ⟨hr'm, hp⟩ := List.mem_filter.mp hr'
      exact ⟨r', hr'm, by simpa using hp, rfl⟩
    refine rule_at4 (hpreTop := hpreTop) hI hnn hsc hok hbc hph hneg hr hpat (fun i hi => ?_) (fun k hk => ?_) hσ heval hens
      (fun tbl e' hkeys hag hrhsR => ?_) e m hm
    · show _ ∈ KoreAML.varsOf (.and C _)
      rw [KoreAML.varsOf, KoreAML.varsOfList]
      exact List.mem_append_right _ (List.mem_append_left _ (hV0 i hi))
    · change k ∈ KoreAML.freeOf [] (.and C _) at hk
      simp only [KoreAML.freeOf, KoreAML.freeOfList, List.append_nil, List.mem_append] at hk
      rcases hk with hk | hk | hk | hk
      · exact freeOf_rule_parts hok hr (Or.inl hk)
      · exact freeOf_rule_parts hok hr (Or.inr (Or.inl hk))
      · exfalso
        obtain ⟨φ, hφ, hk⟩ := mem_freeOf_anyOfC hk
        obtain ⟨r', hr', -, rfl⟩ := hcomp φ hφ
        obtain ⟨hlhs', hreqs', -⟩ := rule_ctx hok hr'
        exact freeOf_applies hlhs' (fun t ht => varOccs_lt t (hreqs' t ht)) (htop _ hr').1 (hb _ hr') hk
      · exact freeOf_rule_parts hok hr (Or.inr (Or.inr hk))
    · have h := lhs_req_hold4 (hpreTop := hpreTop) hI hnn hsc hok hbc hph hneg hr hσ hmatch hreq hag
      show (KoreAML.tr ⟨tbl, []⟩ (.and C _)).interpret I e' _
      rw [tr_and4, KoreAML.interp_sAnd, KoreAML.interp_sAnd, KoreAML.interp_sAnd]
      refine ⟨h.1, h.2, ?_, ceil_rhs_at hI hrhsR (elemOf_top hI x tbl e')⟩
      rw [KoreAML.tr, KoreAML.interp_sNot]
      refine ⟨anyOfC_empty hD (by
        show (KoreAML.trSort tbl (KoreAML.srt (c.sortName topCellSort))).isFreeEvar KoreAML.topVar = false
        rw [trSort_srt]; rfl) comps (fun φ hφ => ?_), ?_⟩
      · obtain ⟨r', hr', hp, rfl⟩ := hcomp φ hφ
        refine hnegr r' hr' ⟨r, hr, hp⟩ x.property
          (fun i hi => hkeys _ ?_) e' (notApplies_model4 (hpreTop := hpreTop) hI hnn hsc hok hbc hph hneg hr' (htop _ hr').1 (hprio r' hr' hp))
        rw [KoreAML.varsOf, KoreAML.varsOfList, KoreAML.varsOfList, KoreAML.varsOfList, KoreAML.varsOf]
        exact List.mem_append_right _ (List.mem_append_right _ (List.mem_append_right _ (List.mem_append_left _
          (List.mem_append_right _ (mem_varsOf_anyOfC hφ (varsOf_applies (htop _ hr').1 (hb _ hr') hi))))))
      · have hxs := elemOf_spec hI x.property e'
        show (KoreAML.inhOf (KoreAML.trSort tbl (KoreAML.srt (c.sortName topCellSort)))).interpret I e' _
        rw [trSort_srt]
        exact hxs.2

end

/-! ## The fourth stage, its negated premises plain -/

/-- **The fourth stage's scope, positive collection patterns.** A rule's left-hand side and a
clause's patterns may be collection patterns (map or collection pattern symbols) wherever they are
read positively only; every rule and clause read negatively (`RuleNeg`, `ClauseNeg`: a competitor
of a rule or a clause of a larger priority) is plain. The values are generated
(`genWf`) and the map pattern symbols are not constructors (`patHooksApart`); both are decidable
on the data. -/
def Stage4a (c : Semantics) : Prop :=
  genWf c = true ∧ patHooksApart c = true ∧
  (∀ r ∈ c.rules, RuleNeg c r → plainPat c r.lhs = true) ∧
  (∀ fn ∈ c.allFns, ∀ cl ∈ fn.clauses, ClauseNeg c fn cl → plainPats c cl.pats = true)

/-- **L4, fourth stage, positive collection patterns.** Every step of `Step` is a consequence of
`Γ`, for a semantics in `Stage4a`: in every model, the configuration `x` has the configuration `y`
as a successor. Its rules' left-hand sides and its clauses' patterns may hold map and collection
patterns where no negated premise reads them; those are read through the collection symbols'
graphs on values (`patVal_den4`). -/
theorem step_sound_stage4a (c : Semantics) [OvlOK c] (hy : Hyp c) (hb : ∀ r ∈ c.rules, binds r.vars.length (varOccs r.lhs) = true) (htop : ∀ r ∈ c.rules, r.pre = .top ∧ r.post = .top)
    (hbc : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, binds cl.vars.length (varOccsList cl.pats) = true) (hs : Stage4a c) :
    ∀ x y : Config c, Step c x y → Γ c ⊧ (den c x.val ⇒ KoreAML.sNext (den c y.val)) := by
  have hpreTop := Semantics.preTop_of_okAll hy.1
  have hy : HypCore c := hy.core (Semantics.overloadsOK_pats OvlOK.ok)
  have hnn : NamesNumbered c := hy.2.2.2.2.2.2
  have hsc := sortCtx_of_all hy.1 hy.2.1 (OvlOK.ovlCase inferInstance)
  intro x y hstep M _ I hI e m hm
  refine step_at4 (hpreTop := hpreTop) hI hnn hsc hy.1 hbc hs.2.1 (fun fn hfn cl hcl hn => ?_) hb htop (fun r hr hn => ?_) hstep e m hm
  · obtain ⟨hp', hb', -⟩ := clause_ctx hy.1 hbc hfn hcl
    exact exclEmpty_of_plain hI hs.1 hsc.trans hnn.1 (clause_preTop (hpreTop := hpreTop) hy.1 hfn hcl) hp' hb' (hs.2.2.2 fn hfn cl hcl hn)
  · obtain ⟨hlhs, -⟩ := rule_ctx hy.1 hr
    exact appEmpty_of_plain hI hs.1 hsc.trans hnn.1 hlhs (Exec.binds_all (hb _ hr)) (hs.2.2.1 r hr hn) (htop _ hr).1

end Faithful

end KCore
