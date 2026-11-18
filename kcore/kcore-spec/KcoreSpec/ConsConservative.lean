/-
  Removing the registry family at detached names changes nothing a model of the smaller theory
  holds of its own symbols (`registry_conservative`), and no step at values (`exact_own`), at the
  decided form of `Detached` (`detachedB`, DetachedB.lean).

  The model is the extension of a model of `Γown` (`extModel`, ConsExtModel.lean), with `Sum.inl`
  as the embedding (`ext_embeds`). A premise that names nothing detached holds in it because it
  held in the model: the signature, the constructors and the collections (`sat_own_sig_cons`), the
  functions, the rules, the step's closure, the domains, the fallbacks and the closure axiom of
  Bool (`sat_own_fns_rules`). A premise that names a detached name is of the registry family
  (`detached_of_decided`), which the extension satisfies (`sat_registry`).

  Some sort of a model of `Γown` has an element: no function has a detached sort in its signature
  and `isK` is a function into Bool, so Bool is not detached and the value `true` is an element of
  it (`ownSort_inhabited_cv`).
-/
import KcoreSpec.ConsTransferFns
import KcoreSpec.ModelFnsPre

set_option autoImplicit false

namespace KCore

open ML Faithful Faithful.Model
open KoreAML (DefOK Inh IsSort)
open DetachedB

namespace Cons

section
variable {c : Semantics} {ss : List Srt} {ks : List Sym} (hd : detachedB c ss ks = true)
include hd

/-- No function has a detached sort in its signature. -/
theorem fnSorts_ok_cv {fn : Fn} (hfn : fn ∈ c.allFns) : ∀ s ∈ fn.result :: fn.args, sOK c ss ks s = true := by
  simp only [detachedB, Bool.and_eq_true] at hd
  have hG := hd.2
  simp only [graphsB, Bool.and_eq_true, List.all_eq_true] at hG
  exact (hG.2 fn hfn).2

/-- Bool is not detached: it is the result sort of the sort predicate `isK`. -/
theorem bool_ok_cv : sOK c ss ks Srt.bool = true := by
  have hmem : ∃ fn ∈ c.sortPreds, fn.result = Srt.bool := by
    unfold Semantics.sortPreds
    exact ⟨_, List.mem_append_left _ (List.mem_cons_self ..), rfl⟩
  obtain ⟨fn, hfn, hr⟩ := hmem
  exact hr ▸ fnSorts_ok_cv hd (List.mem_append_right _ hfn) fn.result (List.mem_cons_self ..)

/-- **Some sort of a model of the theory without the detached names has an element**: the value
`true` of Bool. -/
theorem ownSort_inhabited_cv {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
    (hI : I ⊧ᴵP Γown c (DetachedB.names c ss ks)) : ∃ τ, IsSort I τ ∧ ∃ m, Inh I τ m := by
  have hb := bool_ok_cv hd
  have hnD : ¬ DetachedB.names c ss ks (.sort ("Sort" ++ c.sortName Srt.bool)) := fun hh => by
    have := isName_iff.mpr hh
    simp only [sOK, this] at hb
    cases hb
  obtain ⟨a, -, hinh⟩ := own_single hd hI (sortOf_bool (c := c) true) hb KoreAML.val0
  obtain ⟨σ, hσ, hσN⟩ := sortSing_own_fn names_plain_rs hI (bool_numbered (c := c)) hnD
  have hS : ∀ a, (sortP (c.sortName Srt.bool)).interpret I KoreAML.val0 a ↔ a = σ := fun a => hσN a
  exact ⟨σ, hσ, a, (KoreAML.interp_inhOf_of hS).mp hinh⟩

/-- The head symbol of an application. -/
def headSym_cv : KoreAML.P → Option KoreAML.Sym
  | .symbol σ => some σ
  | .application f _ => headSym_cv f
  | _ => none

omit hd in
theorem headSym_appList_cv : ∀ (l : List KoreAML.P) (h : KoreAML.P),
    headSym_cv (KoreAML.appList h l) = headSym_cv h
  | [], _ => rfl
  | a :: l, h => by rw [KoreAML.appList, headSym_appList_cv l]; rfl

/-- The sort of configurations is not detached: the arity of next names it, and that item is
neither a sort constant nor the arity of a hook. -/
theorem top_ok_cv : sOK c ss ks topCellSort = true := by
  simp only [detachedB, Bool.and_eq_true] at hd
  have hL := hd.1.1.2
  simp only [listsB, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true] at hL
  have hmem : KoreAML.nextArityItem [] (srtOf c topCellSort) ∈ sigItems c := by
    unfold sigItems
    exact List.mem_append_right _ (by simp)
  have hpat : (KoreAML.nextArityItem [] (srtOf c topCellSort)).pat =
      (KoreAML.sNext (KoreAML.inhOf (sortP (c.sortName topCellSort))) ⊆⊆
        KoreAML.inhOf (sortP (c.sortName topCellSort))) := by
    unfold KoreAML.nextArityItem srtOf KoreAML.srt
    simp [KoreAML.sortVarsOf, KoreAML.sortVarsOfList, KoreAML.trSort_const, KoreAML.guarded, sortP,
      KoreAML.paramTable]
  rcases hL.1.1.1 _ hmem with h' | h'
  · rw [hpat] at h'
    have := List.all_eq_true.mp h' (.sort ("Sort" ++ c.sortName topCellSort)) (by
      simp [psyms, sortP, KoreAML.sNext, KoreAML.inhOf, KoreAML.sym, ML.included, ML.total,
        Pattern.negation])
    exact this
  · rw [hpat] at h'
    simp only [regSig, Bool.or_eq_true, List.any_eq_true, beq_iff_eq, Bool.and_eq_true] at h'
    rcases h' with ⟨s, -, he⟩ | ⟨g, -, -, he⟩
    · change _ = KoreAML.sExists ⟨1⟩ (KoreAML.sym .sortSort)
        (KoreAML.sym (.sort ("Sort" ++ c.sortName s)) ≡ .evar ⟨1⟩) at he
      simp [ML.included, ML.total, Pattern.negation, KoreAML.sExists] at he
    · exfalso
      have hh : ∀ {a b a' b' : KoreAML.P}, (a ⊆⊆ b) = (a' ⊆⊆ b') → headSym_cv a = headSym_cv a' :=
        fun {a b a' b'} hab => by
          simp only [ML.included, ML.total, Pattern.negation, Pattern.implication.injEq,
            Pattern.application.injEq, and_true, true_and] at hab
          rw [hab.1]
      unfold symArityItem at he
      split at he
      · unfold KoreAML.arityItem at he
        simp only [KoreAML.guarded, List.map_nil, KoreAML.appList] at he
        have := hh he
        rw [headSym_appList_cv] at this
        cases this
      · have := hh he
        rw [headSym_appList_cv] at this
        cases this

end

end Cons

/-- What the transfer of the functions' equations reads of the clauses, from `coreOK`, `FnHyp`,
`clausesPreTop` and `FnsNoExs`:
every clause of a function has `\top` for its predicate, every clause variable's sort is numbered,
and no clause binds a variable on its right. -/
theorem Cons.clauseFacts_cv {c : Semantics} (hpreTop : c.clausesPreTop = true) (hnoEx : c.FnsNoExs) (h : c.coreOK = true) (hf : FnHyp c) :
    (∀ fn ∈ c.allFns, ∀ cl ∈ fn.clauses, cl.pre = .top) ∧
    (∀ fn ∈ c.allFns, ∀ cl ∈ fn.clauses, ∀ s ∈ cl.vars, s < nRegSorts + c.sortNames.length) ∧
    (∀ fn ∈ c.allFns, ∀ cl ∈ fn.clauses, cl.exs = []) := by
  have hm : HypModelCore c := hypModel_of_fnHyp h hf
  have hpre := Semantics.allFns_preTop hpreTop
  have hF : ∀ fn ∈ c.allFns, ∀ cl ∈ fn.clauses, EqnFactsPre c fn cl := fun fn hfn cl hcl =>
    clause_eqnFactsPre hm hfn hcl (hnoEx.allFns fn hfn cl hcl) (by
      rcases List.mem_append.mp hfn with hu | hp
      · exact hm.preOK fn hu cl hcl
      · rw [Semantics.sortPreds_pre hp cl hcl]; rfl)
  refine ⟨hpre, fun fn hfn cl hcl s hs => ?_, fun fn hfn cl hcl => (hF fn hfn cl hcl).exs⟩
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hs
  have := vars_numPre hm hfn (hF fn hfn cl hcl) i hi
  rwa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi] at this

open Cons in
/-- **The extension of a model of the theory without the detached names is a model of the whole
theory**, at the decided form of `Detached`, for a definition `coreOK` accepts whose functions meet
`FnHyp`. The three facts
of the clauses the functions' equations are transferred by are hypotheses (`clauseFacts_cv` gives
them). -/
theorem Cons.ext_model_cv {c : Semantics} {ss : List Srt} {ks : List Sym} (h : c.coreOK = true) (hf : FnHyp c)
    (hd : detachedB c ss ks = true)
    (hpre : ∀ fn ∈ c.allFns, ∀ cl ∈ fn.clauses, cl.pre = .top)
    (hvars : ∀ fn ∈ c.allFns, ∀ cl ∈ fn.clauses, ∀ s ∈ cl.vars, s < nRegSorts + c.sortNames.length)
    (hexs : ∀ fn ∈ c.allFns, ∀ cl ∈ fn.clauses, cl.exs = [])
    {M : Type} [Inhabited M]
    {I : Interpretation KoreAML.Sym M} (hI : I ⊧ᴵP Γown c (DetachedB.names c ss ks)) :
    extModel c (DetachedB.names c ss ks) I ⊧ᴵP (Γc c ∪ Γstep c) := by
  have hD : ∀ σ, DetachedB.names c ss ks σ → plainSym σ := names_plain_rs
  have hm : HypModelCore c := hypModel_of_fnHyp h hf
  obtain ⟨-, -, -, hg, -, -, -, -, hno⟩ := hypSound_of_core h
  haveI : OvlOK c := hno
  have hdet := detached_of_decided c ss ks h hd
  have hne := ownSort_inhabited_cv hd hI
  have hlaw : ∀ p ∈ c.params, p.raw = true →
      ¬ DetachedB.names c ss ks (.sort ("Sort" ++ c.sortName p.sig.result)) ∧
      ¬ DetachedB.names c ss ks (.symbol (c.symName p.sig.name)) ∧
      ∃ σ, IsSort I σ ∧ ∀ a, I.evalSymb (.sort ("Sort" ++ c.sortName p.sig.result)) a ↔ a = σ :=
    fun p hp hr => by
      have hG : graphsB c ss ks = true := by
        simp only [detachedB, Bool.and_eq_true] at hd
        exact hd.2
      simp only [graphsB, Bool.and_eq_true, List.all_eq_true] at hG
      obtain ⟨hap, hso⟩ := hG.1.2 p hp
      have hite := (Semantics.raw_of_paramsPlain (Semantics.sortedOKClEx_parts hm.hyp.1).2.2.2.2 hp hr).2.2.2.1
      have hk : kOK c ss ks p.sig.name = true := by
        unfold appOK at hap
        rw [hite] at hap
        exact hap
      have hns : ¬ DetachedB.names c ss ks (.sort ("Sort" ++ c.sortName p.sig.result)) := fun hh => by
        have h1 := isName_iff.mpr hh
        have h2 := hso p.sig.result (List.mem_cons_self ..)
        simp only [sOK, h1] at h2
        cases h2
      have hnf : ¬ DetachedB.names c ss ks (.symbol (c.symName p.sig.name)) := fun hh => by
        have h1 := isName_iff.mpr hh
        simp only [kOK, h1] at hk
        cases hk
      exact ⟨hns, hnf, sortSing_own_fn hD hI (consSorts_numbered hm (genWf_raw_cons hg hp hr)) hns⟩
  intro φ hφ
  by_cases hcl : ∀ σ ∈ psyms φ, ¬ DetachedB.names c ss ks σ
  · have hfr : ΓFns c φ ∨ ΓRules c φ ∨ Γstep c φ ∨ ΓDomains c φ ∨ ΓFallback c φ ∨ Γcl c φ →
        extModel c (DetachedB.names c ss ks) I ⊧ᴵ φ := fun hφ' =>
      sat_own_fns_rules hD hI hne (fun fn hfn => hm.fnSorts hfn) hvars hpre hexs hφ' hcl
    rcases hφ with (((((((hφ | hφ) | hφ) | hφ) | hφ) | hφ) | hφ) | hφ) | hφ
    · exact sat_own_sig_cons hD hlaw hI (.inl hφ) hcl
    · exact sat_own_sig_cons hD hlaw hI (.inr (.inl hφ)) hcl
    · exact hfr (.inr (.inr (.inr (.inl hφ))))
    · exact sat_own_sig_cons hD hlaw hI (.inr (.inr hφ)) hcl
    · exact hfr (.inl hφ)
    · exact hfr (.inr (.inl hφ))
    · exact hfr (.inr (.inr (.inr (.inr (.inl hφ)))))
    · exact hfr (.inr (.inr (.inr (.inr (.inr hφ)))))
    · exact hfr (.inr (.inr (.inl hφ)))
  · have hname : ∃ σ ∈ psyms φ, DetachedB.names c ss ks σ :=
      Classical.byContradiction fun hno' => hcl fun σ hσ hn => hno' ⟨σ, hσ, hn⟩
    exact sat_registry hd hI hm hg hm.trans (hdet.2.2 φ hφ hname)

open Cons in
/-- **The registry family at detached names is conservative**, at the decided form of `Detached`:
a model of the theory without the premises that name a sort of `ss` or a hook of `ks` embeds into
a model of the whole theory, its extension, in which a symbol outside those names and application
hold of old elements what they held. For a definition `coreOK` accepts whose functions meet
`FnHyp`; `coreOK` gives that no clause of a function has an existential variable
(`Semantics.fnsNoExs_of_coreOK`), which the transfer of the functions' equations reads. -/
theorem registry_conservative (c : Semantics) (hpreTop : c.clausesPreTop = true) (ss : List Srt) (ks : List Sym) (h : c.coreOK = true)
    (hf : FnHyp c) (hd : detachedB c ss ks = true) :
    RegistryConservative c (DetachedB.names c ss ks) := by
  intro M _ I hI
  have hemb := ext_embeds c (DetachedB.names c ss ks) I
  have hc := clauseFacts_cv (hpreTop := hpreTop) (hnoEx := Semantics.fnsNoExs_of_coreOK h) h hf
  exact ⟨Ext M, ⟨.inl default⟩, extModel c (DetachedB.names c ss ks) I, Sum.inl, hemb.1,
    ext_model_cv h hf hd hc.1 hc.2.1 hc.2.2 hI, hemb.2.1, hemb.2.2⟩

open Cons in
/-- **No step at values rests on the registry family at detached names**, at the decided form of
`Detached`, under the hypotheses of `registry_conservative`: the steps of `Step` are the steps at
values that some model of the theory without the detached names has. Right to left, the model's extension is a model of the whole theory
(`ext_model_cv`), and it has the step: the patterns of the two configurations name nothing
detached (the sort of configurations is not detached, `top_ok_cv`), so the sentence that there is
no step, if the extension satisfied it, would hold in the model (`transfer_back`). -/
theorem exact_own (c : Semantics) (hpreTop : c.clausesPreTop = true) (ss : List Srt) (ks : List Sym) (h : c.coreOK = true)
    (hf : FnHyp c) (hd : detachedB c ss ks = true) :
    ExactOwn c (DetachedB.names c ss ks) := by
  intro x y
  refine ⟨exact_own_mp c _ h hf, ?_⟩
  rintro ⟨M, _, I, hI, hn⟩
  have hD : ∀ σ, DetachedB.names c ss ks σ → plainSym σ := names_plain_rs
  have hc := clauseFacts_cv (hpreTop := hpreTop) (hnoEx := Semantics.fnsNoExs_of_coreOK h) h hf
  have hV : valuesB c ss ks = true := by
    simp only [detachedB, Bool.and_eq_true] at hd
    exact hd.1.2
  have hden : ∀ v : Config c, OwnSorted (DetachedB.names c ss ks) [] [] .ex (den c v.val) := fun v =>
    ownEx_kground_rs (kore_ground c v.val) fun σ hσ hn' =>
      clean_spec (clean_val hV v.val _ v.property (top_ok_cv hd)) ⟨σ, hσ, hn'⟩
  have hnext : ¬ DetachedB.names c ss ks .next := by
    rintro (⟨_, _, hh⟩ | ⟨_, _, hh⟩) <;> cases hh
  have hb : OwnSorted (DetachedB.names c ss ks) [] [] .co
      (den c x.val ⇒ ∼ KoreAML.sNext (den c y.val)) :=
    .impEO (hden x) (OwnSorted.toOld (.neg_ex (.appE (.sym trivial hnext) (hden y).toOld)))
  refine (exact_hyp c h hf x y).mpr ⟨Ext M, ⟨.inl default⟩, extModel c (DetachedB.names c ss ks) I,
    ext_model_cv h hf hd hc.1 hc.2.1 hc.2.2 hI, fun hall => hn ?_⟩
  exact transfer_back (gs := []) hD (defOK_own_sg hD hI) nil_sub hb hall

open Classical in
/-- **A detached set of names is the names of two lists**: `Detached`'s first conjunct puts every
name of `D` among the registry sorts' and the interpreted hooked symbols', which are finitely
many, so `D` is `DetachedB.names` at the registry sorts and the hooked symbols it holds. -/
theorem Detached.eq_names_cv {c : Semantics} {D : KoreAML.Sym → Prop} (hd : Detached c D) :
    ∃ (ss : List Srt) (ks : List Sym), (∀ s ∈ ss, s < nRegSorts) ∧ (∀ k ∈ ks, ∃ h ∈ hookSigs, h.name = k) ∧
      D = DetachedB.names c ss ks := by
  refine ⟨(List.range nRegSorts).filter fun s => decide (D (.sort ("Sort" ++ c.sortName s))),
    (hookSigs.map (·.name)).filter fun k => decide (D (.symbol (c.symName k))),
    fun s hs => List.mem_range.mp (List.mem_filter.mp hs).1,
    fun k hk => by
      obtain ⟨h, hh, rfl⟩ := List.mem_map.mp (List.mem_filter.mp hk).1
      exact ⟨h, hh, rfl⟩, ?_⟩
  funext σ
  refine propext ⟨fun hσ => ?_, ?_⟩
  · rcases hd.1 σ hσ with ⟨s, hs, rfl⟩ | ⟨k, hk, rfl⟩
    · exact .inl ⟨s, List.mem_filter.mpr ⟨List.mem_range.mpr hs, decide_eq_true hσ⟩, rfl⟩
    · exact .inr ⟨k.name, List.mem_filter.mpr ⟨List.mem_map_of_mem hk, decide_eq_true hσ⟩, rfl⟩
  · rintro (⟨s, hs, rfl⟩ | ⟨k, hk, rfl⟩)
    · exact of_decide_eq_true (List.mem_filter.mp hs).2
    · exact of_decide_eq_true (List.mem_filter.mp hk).2

/-- **The two statements at a set of names `D`**, where the decided check holds of some lists whose
names are `D`. With `Detached.eq_names_cv`, what separates this from the statements at every
detached `D` is whether the decided check holds of such lists whenever `D` is detached. -/
theorem registry_conservative_names_cv (c : Semantics) (hpreTop : c.clausesPreTop = true) (D : KoreAML.Sym → Prop) (ss : List Srt) (ks : List Sym)
    (h : c.coreOK = true) (hf : FnHyp c) (hD : D = DetachedB.names c ss ks) (hd : detachedB c ss ks = true) :
    RegistryConservative c D ∧ ExactOwn c D :=
  hD ▸ ⟨registry_conservative (hpreTop := hpreTop) c ss ks h hf hd, exact_own (hpreTop := hpreTop) c ss ks h hf hd⟩

end KCore
