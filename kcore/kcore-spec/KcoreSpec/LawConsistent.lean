/-
  KCore. The laws of functions in the value model.

  A law the text writes for a function is the sentence `\equals{S,R}(lhs, rhs)` with its variables
  free (`lawPattern`). Where the interpretation satisfies the law at values (`LawAt`) and the law
  is sorted (`lawSorted`), the value model satisfies the sentence (`sat_lawPattern`): the guards
  give each variable a value of its sort, each side denotes the values `EvalTerm` gives it under
  the substitution those values are (`tr_term`), and `LawAt` says the two sides have the same
  results there. So the theory with the laws' sentences has the model `consistent_of` exhibits
  (`consistent_with_laws`).

  What is read of `lawSorted`: both sides have one sort, a sort of the definition, and each
  variable occurs in a side. The sort of the definition is what makes the sentence's sort symbol
  and its variables' guards denote the sorts the law names: a sort that is none of the definition's
  has the name `sortName` gives outside its table, which is not apart from the definition's names.
-/
import KcoreSpec.Sound
import KcoreSpec.DataCmd

set_option autoImplicit false

namespace KCore

/-- What `lawSorted` holds: the two sides have one sort, a sort of the definition, and each
variable occurs in a side. -/
theorem lawSorted_parts {c : Semantics} {l : LawEq} (h : lawSorted c l = true) :
    ∃ s, sortOfTerm (c.rhsCtx (c.fns.map Fn.sig)) l.vars l.lhs = some s ∧
      sortOfTerm (c.rhsCtx (c.fns.map Fn.sig)) l.vars l.rhs = some s ∧
      s < nRegSorts + c.sortNames.length ∧
      binds l.vars.length (varOccs l.lhs ++ varOccs l.rhs) = true := by
  simp only [lawSorted, Bool.and_eq_true, beq_iff_eq, Option.any_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨s, hl, hs⟩, he⟩, hb⟩ := h
  exact ⟨s, hl, he ▸ hl, hs, hb⟩

/-! `lawSorted` reads no interpretation. -/
kernel_rfl lawSorted_withHooks :
  ∀ (c : Semantics) (H : HookParams) (l : LawEq), lawSorted (c.withHooks H) l = lawSorted c l

namespace Faithful

namespace Model

open ML

variable {c : Semantics}

namespace AtT

variable {T : GroundTerm → GroundTerm → Prop}

/-- **A law's sentence holds in the value model at the transition `T`** where the interpretation
satisfies the law at values: for a law whose sides have one sort of the definition and whose
variables each occur in a side. -/
theorem sat_lawPattern (h : HypModelCore c) {l : LawEq} (hla : LawAt c l) {s : Srt}
    (hl : sortOfTerm (c.rhsCtx (c.fns.map Fn.sig)) l.vars l.lhs = some s)
    (hr : sortOfTerm (c.rhsCtx (c.fns.map Fn.sig)) l.vars l.rhs = some s)
    (hs : s < nRegSorts + c.sortNames.length)
    (hb : binds l.vars.length (varOccs l.lhs ++ varOccs l.rhs) = true) :
    stdI_T c T ⊧ᴵ lawPattern c l := by
  have hn := h.namesK
  have hx : ∀ k ∈ (c.rhsCtx (c.fns.map Fn.sig)).heads, k ∈ kernelSyms c :=
    fun k hk => rhsHead_kernel fns_headsOK hk
  have hsub : ∀ a b, (a, b) ∈ (c.rhsCtx (c.fns.map Fn.sig)).subs → (a, b) ∈ c.subsorts := fun _ _ h' => h'
  have hocc : ∀ i < l.vars.length, i ∈ varOccs l.lhs ∨ i ∈ varOccs l.rhs := fun i hi => by
    have := List.all_eq_true.mp hb i (List.mem_range.mpr hi)
    exact List.mem_append.mp (List.contains_iff_mem.mp this)
  have hnum : ∀ i < l.vars.length, l.vars.getD i 0 < nRegSorts + c.sortNames.length := fun i hi => by
    have hg : l.vars[i]? = some (l.vars.getD i 0) := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; rfl
    rcases hocc i hi with ho | ho
    · exact varOccs_numOpen h hx hsub l.lhs hl hs i ho _ hg
    · exact varOccs_numOpen h hx hsub l.rhs hr hs i ho _ hg
  have hlOK := termOK_of_sorted h fns_headsOK hl
  have hrOK := termOK_of_sorted h fns_headsOK hr
  intro e m
  unfold lawPattern KoreAML.trAxiom
  dsimp only
  rw [hl, Option.getD_some]
  generalize hP : Kore.Pattern.equals (srtOf c s) KoreAML.R (Term.kore c (canonVars c l.vars) l.lhs)
    (Term.kore c (canonVars c l.vars) l.rhs) = P
  have hsortP : KoreAML.sortOf [] P = some KoreAML.R := by rw [← hP]; rfl
  simp only [hsortP]
  rw [interpret_impl]
  intro hgs
  generalize htb : KoreAML.tableOf [KoreAML.Rv] P = tbl at hgs ⊢
  have hguard : ∀ k ∈ (([KoreAML.Rv].map KoreAML.sortVarKey) ++ KoreAML.freeOf [] P).eraseDups,
      (KoreAML.guardOf tbl k).interpret (stdI_T c T) e m := fun k hk =>
    conjList_elim hgs _ (List.mem_map.mpr ⟨k, hk, rfl⟩)
  have hRs : KoreAML.IsSort (stdI_T c T) (e.evalEvar (tbl.ev (.sortVar "R"))) := by
    have := hguard (.sortVar "R") (List.mem_eraseDups.mpr (List.mem_append_left _
      (List.mem_map.mpr ⟨KoreAML.Rv, List.mem_singleton_self _, rfl⟩)))
    obtain ⟨s', hs', he⟩ := sortGuard_iff.mp this
    rw [he]; exact (isSort_iff _).mpr ⟨s', hs', rfl⟩
  have hfree : ∀ i < l.vars.length, canonKey c l.vars i ∈ KoreAML.freeOf [] P := fun i hi => by
    rw [← hP, KoreAML.freeOf]
    rcases hocc i hi with ho | ho
    · exact List.mem_append_left _ (kore_freeOf c _ l.lhs ho)
    · exact List.mem_append_right _ (kore_freeOf c _ l.rhs ho)
  have hvin : ∀ i < l.vars.length,
      InSort c (l.vars.getD i 0) (e.evalEvar (tbl.ev (canonKey c l.vars i))) := by
    intro i hi
    have hg := hguard _ (List.mem_eraseDups.mpr (List.mem_append_right _ (hfree i hi)))
    have hkk := canonKey_eq c hi
    rw [hkk, KoreAML.interp_guard_evar defOK_std, trSort_srt, ← hkk] at hg
    exact (inhOf_sort hn (hnum i hi) e _).mp hg
  obtain ⟨hσ, hvar⟩ := substE_ok (T := T) hvin
  have hSres : ∀ x, (KoreAML.trSort tbl (srtOf c s)).interpret (stdI_T c T) e x ↔ x = .srt s := fun x => by
    unfold srtOf; rw [trSort_srt]; exact sort_den hn hs e x
  have hresS : KoreAML.IsSort (stdI_T c T) (.srt s) := (isSort_iff _).mpr ⟨_, List.mem_range.mpr hs, rfl⟩
  rw [KoreAML.interp_equal defOK_std]
  intro x
  rw [← hP, KoreAML.tr, KoreAML.interp_sEquals defOK_std sat_ceilDef hSres (R_read e) hresS hRs,
    KoreAML.interp_inhOf_of (R_read e)]
  refine ⟨fun hx => hx.1, fun hx => ⟨hx, fun y _ => ?_⟩⟩
  rw [tr_term h hvar hlOK, tr_term h hvar hrOK]
  constructor
  · rintro ⟨v, hv, rfl⟩; exact ⟨v, (hla _ hσ _).mp hv, rfl⟩
  · rintro ⟨v, hv, rfl⟩; exact ⟨v, (hla _ hσ _).mpr hv, rfl⟩

end AtT

/-- **A law's sentence holds in the value model** where the interpretation satisfies the law at
values, for a sorted law. -/
theorem sat_lawPattern (h : HypModelCore c) {l : LawEq} (hla : LawAt c l)
    (hsort : lawSorted c l = true) : stdI c ⊧ᴵ lawPattern c l := by
  obtain ⟨s, hl, hr, hs, hb⟩ := lawSorted_parts hsort
  exact AtT.sat_lawPattern (T := StepM c) h hla hl hr hs hb

end Model

end Faithful

open Faithful Faithful.Model ML in
/-- **Under the obligation the theory with the laws' sentences has a model**: for a semantics
that `coreOK` accepts, whose functions have at most one result (`FnDet`), whose evaluation solves
the equations (`FnSolves`), whose clauses' predicates have a truth value wherever their patterns
match (`ClausePreDecided`) and at each well-sorted instance on the right side
(`ClausePostDecided`), and whose interpretation satisfies the open generators' laws (`OpenLaws`)
and, at values, the laws the text writes for its functions (`FnLaws`), each of them
sorted, the value model (`consistent_of`'s) satisfies each law's sentence. -/
theorem consistent_with_laws {c : Semantics} (h : c.coreOK = true) (hd : FnDet c) (hs : FnSolves c)
    (hp : ClausePreDecided c) (hq : ClausePostDecided c) (ho : OpenLaws c) {ls : List LawEq} (hl : FnLaws c ls) (hsort : ∀ l ∈ ls, lawSorted c l = true) :
    ∃ (M : Type) (_ : Inhabited M) (I : ML.Interpretation KoreAML.Sym M),
      (I ⊧ᴵP (Γc c ∪ Γstep c)) ∧ ∀ l ∈ ls, I ⊧ᴵ lawPattern c l :=
  ⟨Elem, inferInstance, stdI_T c (StepV c),
    stdI_T_model_heldCEx c (hypModel_of_fn h hd hs) hp hq ho (Semantics.ruleFactsHeld_of_core h) (StepV c)
      (fun _ _ _ _ hT => hT) (fun r σ _ _ hb _ => ⟨r, σ, hb⟩)
      (fun r σ _ y hb _ => ⟨y, σ, fun _ _ => rfl, hb, ⟨r, σ, hb⟩⟩),
    fun l hmem => by
      obtain ⟨s, hl', hr, hs', hb⟩ := lawSorted_parts (hsort l hmem)
      exact AtT.sat_lawPattern (T := StepV c) (hypModel_of_fn h hd hs) (hl l hmem) hl' hr hs' hb⟩

end KCore
