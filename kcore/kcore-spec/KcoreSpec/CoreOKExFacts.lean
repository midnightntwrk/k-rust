/-
  KCore. What `coreOKEx` gives, beside what `coreOK` gives: step soundness's facts of a semantics
  (`Faithful.HypSoundCoreEx`, `hypSoundEx_of_coreEx`), the facts subject reduction reads
  (`sortCtx_of_allCEx`), and in a model of `Γc` the constructors', atoms' and binders' facts
  (`HoldsShape.nodeFacts_of_coreEx`, `atomFacts_of_coreEx`, `binderFacts_of_coreEx`), the values of
  confined sorts and of injections (`confined_valueCEx`, `CE.inj_valueCEx`), and the values of
  fixed and existential variables (`CE.fixes_value_readTCEx`, `CE.exs_values_hrCEx`).

  Each is its `coreOK` counterpart's statement with `coreOKEx` for `coreOK` (`sortedOKEx` for
  `sortedOK`, `HypSoundCoreEx` for `HypSoundCore`), proved as it is: those proofs read of the
  clauses that they are sorted (`clauseSorted`), never `clausesPlain`.
-/
import KcoreSpec.CoreOKEx
import KcoreSpec.OpenClauseFam
import KcoreSpec.HoldsFactsCore
import KcoreSpec.ClausePreTie

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace KCore

namespace NamesApart

variable {c : KCore.Semantics}

/-- `subsorts_trans_of` for a semantics `sortedOKEx` accepts. -/
theorem subsorts_trans_ofCEx (hids : c.idsOK = true) (hok : c.sortedOKEx = true) :
    ∀ a b e, (a, b) ∈ c.subsorts → (b, e) ∈ c.subsorts → (a, e) ∈ c.subsorts := by
  have hso := (KCore.Semantics.sortedOKEx_parts hok).1
  obtain ⟨-, hk⟩ := sorts_facts hids
  intro a b e hab hbe
  rw [mem_subsorts] at hab hbe ⊢
  rcases hab with hab | ⟨rfl, ha⟩
  · have hs := closure_sorts (lib_ok hids) hso hab
    rcases hbe with hbe | ⟨rfl, -⟩
    · exact Or.inl (declaredClosure_trans hab hbe)
    · exact Or.inr ⟨rfl, (ul_facts hids hs.1).1⟩
  · rcases hbe with hbe | ⟨-, hb⟩
    · exact absurd rfl (ul_facts hids (closure_sorts (lib_ok hids) hso hbe).1).2
    · exact absurd hb hk

/-- `subsorts_irrefl_of` for a semantics `sortedOKEx` accepts. -/
theorem subsorts_irrefl_ofCEx (hids : c.idsOK = true) (hok : c.sortedOKEx = true) :
    ∀ a, (a, a) ∉ c.subsorts := by
  have hso := (KCore.Semantics.sortedOKEx_parts hok).1
  obtain ⟨-, hk⟩ := sorts_facts hids
  intro a h
  rw [mem_subsorts] at h
  rcases h with h | ⟨rfl, ha⟩
  · exact (subsortsOK_parts hso).2 a h
  · exact hk ha

/-- `srReady_of` for a semantics `sortedOKEx` accepts. -/
theorem srReady_ofCEx (hp : c.predsApart = true) (hids : c.idsOK = true) (hok : c.sortedOKEx = true)
    (hg : KCore.Faithful.genWf c = true) (hov : c.overloadsOK = true) :
    c.srReady = true := by
  have htr := subsorts_trans_ofCEx hids hok
  unfold KCore.Semantics.srReady
  rw [Bool.and_eq_true, Bool.and_eq_true]
  refine ⟨⟨hp, ?_⟩, KCore.rangeKeysOK_of_genWf hg hov⟩
  simp only [List.all_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq, List.contains_iff_mem]
  rintro ⟨a, b⟩ hab ⟨b', e⟩ hbe
  by_cases h : b = b'
  · subst h; exact Or.inr (htr a b e hab hbe)
  · exact Or.inl h

end NamesApart

/-- `sortCtx_of_all` for a semantics `sortedOKEx` accepts. -/
theorem sortCtx_of_allCEx {c : Semantics} (hok : c.sortedOKEx = true) (hr : c.srReady = true)
    (hov : c.OvlCase) : SortCtx c := by
  simp only [Semantics.srReady, Bool.and_eq_true, List.all_eq_true] at hr
  obtain ⟨⟨hnd, htr⟩, hrk⟩ := hr
  replace hok := Semantics.sortedOKEx_sorted hok
  simp only [Bool.and_eq_true, List.all_eq_true] at hok
  obtain ⟨⟨_, hfns⟩, _⟩ := hok
  have htr' : ∀ a b d, (a, b) ∈ c.subsorts → (b, d) ∈ c.subsorts → (a, d) ∈ c.subsorts := fun a b d hab hbd => by
    have := htr (a, b) hab (b, d) hbd
    simp only [bne_self_eq_false, Bool.false_or, List.contains_iff_mem] at this
    exact this
  refine ⟨htr', nodup_of_eq_true hnd, fun fn hfn' => ?_, hov, rangeBelow_of_keysOK hrk⟩
  · rcases List.mem_append.mp hfn' with hfn | hfn
    rotate_left
    · exact ⟨[], fun k hk => (nomatch hk), fun cl h => (sortPreds_ctx hfn cl h).2.2.2.2.1⟩
    refine ⟨c.fns.map Fn.sig, fun k hk => ?_, fun cl hcl => ?_⟩
    · obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hk
      exact ⟨g, List.mem_append_left _ hg, rfl⟩
    · have := hfns fn hfn cl hcl
      simp only [Semantics.clauseSorted, Bool.and_eq_true, beq_iff_eq] at this
      replace this := this.1
      exact this.1.1.2

namespace Faithful

open ML

/-- `HypSoundCore` with `sortedOKEx` in place of `sortedOK`. -/
def HypSoundCoreEx (c : Semantics) : Prop :=
  c.sortedOKEx = true ∧ c.srReady = true ∧ NamesNumbered c ∧ genWf c = true ∧ patHooksApart c = true ∧
    collSortsOK c = true ∧ collsOK c = true ∧ patHeadsOK c = true ∧ OvlOK c

/-- `HypSoundCore` gives `HypSoundCoreEx`. -/
theorem HypSoundCore.toEx {c : Semantics} (h : HypSoundCore c) : HypSoundCoreEx c :=
  ⟨Semantics.sortedOKEx_of_sortedOK h.1, h.2⟩

end Faithful

/-- What subject reduction reads of the overloading symbols, from `coreOKEx`. -/
theorem Semantics.ovlCase_of_coreEx {c : Semantics} (h : c.coreOKEx = true) : c.OvlCase := by
  obtain ⟨hok, -, -, -, hids⟩ := Semantics.coreOKEx_parts h
  exact .inr ⟨Semantics.coreOKEx_ovls h, NamesApart.subsorts_irrefl_ofCEx hids hok⟩

/-- What `coreOKEx` asks of an open generator (`paramsPlain`'s raw branch). -/
theorem Semantics.raw_of_coreEx {c : Semantics} (h : c.coreOKEx = true) {k : ParamSig}
    (hk : k ∈ c.params) (hr : k.raw = true) :
    k.impl = none ∧
    ((k.assoc || k.idem) = true → k.sig.args = [k.sig.result, k.sig.result]) ∧
    nRegSyms ≤ k.sig.name ∧ iteSort? (c.symName k.sig.name) = none ∧
    c.shapesOK = true :=
  Semantics.raw_of_sortedOKEx (Semantics.coreOKEx_parts h).1 hk hr

section Core
variable {c : Semantics}
open ML Faithful Faithful.Model

/-- `ovlOK_of_core` for a semantics `coreOKEx` accepts. -/
theorem ovlOK_of_coreEx (h : c.coreOKEx = true) : OvlOK c := by
  obtain ⟨hok, hfa, -, -, hids⟩ := Semantics.coreOKEx_parts h
  obtain ⟨-, -, -, -, -, hn, -, hs, -, -, -, hfns⟩ := faithCoreOK_parts hfa
  refine ⟨Semantics.coreOKEx_ovls h, NamesApart.subsorts_irrefl_ofCEx hids hok, ?_,
    fnOver_of_apart (Semantics.coreOKEx_ovls h) hfns⟩
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

/-- **What step soundness reads, from `coreOKEx`**: `hypSound_of_core` with `sortedOKEx`. -/
theorem hypSoundEx_of_coreEx (h : c.coreOKEx = true) : HypSoundCoreEx c := by
  obtain ⟨hok, hfa, hha, hp, hids⟩ := Semantics.coreOKEx_parts h
  obtain ⟨hnn, hg, hcso, hcs, hph, -⟩ := faithCoreOK_parts hfa
  refine ⟨hok, NamesApart.srReady_ofCEx hp hids hok
    (NamesApart.rangeKeys_genWf_of_faithCore (Semantics.coreOKEx_parts h).2.1) (Semantics.coreOKEx_ovls h), namesNumbered_spec hnn, hg, ?_, hcso, hcs, hph,
    ovlOK_of_coreEx h⟩
  exact List.all_eq_true.mpr fun f hf => by
    simp [NamesApart.patHooks_of hha hids f hf]

end Core

namespace Faithful

open ML

section
variable {c : Semantics}

/-- `coreOKEx`'s numbering of sorts. -/
theorem sortsNumbered_of_coreEx (h : c.coreOKEx = true) : Model.sortsNumbered c = true :=
  (faithCoreOK_parts (Semantics.coreOKEx_parts h).2.1).2.2.2.2.2.2.2.1

/-- The sort of a value is numbered, under the conditions `coreOKEx` gives (`sortOf_numbered_ofCl`). -/
theorem sortOf_numbered_ofCEx (hs : HypSoundCoreEx c) (hsorts : Model.sortsNumbered c = true)
    (hov : c.overloadsOK = true) {v : GroundTerm} {s : Srt} (hv : c.sortOf v = some s) :
    s < nRegSorts + c.sortNames.length :=
  haveI : OvlOK c := hs.2.2.2.2.2.2.2.2
  sortOf_numbered_ofCl hs.2.2.2.1 hsorts hov hv

end

section
variable {c : Semantics} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}

/-- `confinedAt_value` for a semantics `coreOKEx` accepts. -/
theorem confinedAt_valueCEx (h : c.coreOKEx = true) (hr : c.readsConfined = true) (hI : I ⊧ᴵP Γc c) :
    ∀ (k : Nat) (s : Srt), c.confinedAt k s = true → ∀ x, InS I (c.sortName s) x →
      ∃ v, c.sortOf v = some s ∧ elemOf c I v = x := by
  obtain ⟨hok, hsr, -, -, -, -, -, -, hno⟩ := hypSoundEx_of_coreEx h
  haveI : OvlOK c := hno
  exact confinedAt_valueCl (sortCtx_of_allCEx hok hsr (OvlOK.ovlCase hno)).trans
    (Model.namesApartK_spec (faithCoreOK_parts (Semantics.coreOKEx_parts h).2.1).2.2.2.2.2.1)
    (fun k hk hkr => (Semantics.raw_of_coreEx h hk hkr).2.2.2.1) hr hI

end

end Faithful

open ML Faithful

/-- **Every element of a confined sort is a value's**: `confined_value` for a semantics `coreOKEx` accepts. -/
theorem confined_valueCEx {c : Semantics} (h : c.coreOKEx = true) (hr : c.readsConfined = true)
    {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hI : I ⊧ᴵP Γc c)
    {s : Srt} (hs : c.confined s = true) (ρ : Valuation M) (e : M)
    (he : (KoreAML.inhOf (sortP (c.sortName s))).interpret I ρ e) :
    ∃ v, c.sortOf v = some s ∧ ∀ m, (den c v).interpret I ρ m ↔ m = e := by
  have hIΓ : I ⊧ᴵP Γ c := fun φ hφ => hI φ (Or.inl hφ)
  obtain ⟨v, hv, rfl⟩ := confinedAt_valueCEx h hr hI _ s hs e ((inS_iff ρ).mp he)
  exact ⟨v, hv, (elemOf_spec hIΓ hv ρ).1⟩

namespace CE

open ML Faithful HoldsShape

section InjValueEx
variable {c : Semantics} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}

/-- `injValue_subsorts_trans` for a semantics `coreOKEx` accepts. -/
theorem injValue_subsorts_transCEx (h : c.coreOKEx = true) :
    ∀ a b d, (a, b) ∈ c.subsorts → (b, d) ∈ c.subsorts → (a, d) ∈ c.subsorts := by
  obtain ⟨hok, hsr, -, -, -, -, -, -, hno⟩ := hypSoundEx_of_coreEx h
  exact (sortCtx_of_allCEx hok hsr (OvlOK.ovlCase hno)).trans

/-- `inj_defined` for a semantics `coreOKEx` accepts. -/
theorem inj_definedCEx (h : c.coreOKEx = true) (hI : I ⊧ᴵP Γ c) {a b : Srt} (hab : c.subsorts.contains (a, b) = true)
    {e : M} (he : InS I (c.sortName a) e) :
    ∃ y, InS I (c.sortName b) y ∧ ∀ m, GS I (c.sortName b) (.inj (c.sortName a)) [e] m ↔ m = y := by
  obtain ⟨-, -, -, hg, -, -, -, -, hno⟩ := hypSoundEx_of_coreEx h
  haveI : OvlOK c := hno
  have hab' : (a, b) ∈ c.subsorts := by simpa using hab
  exact gen_fun hI (genWf_sub hg hab').1 (gensF_inj hab') rfl (xs := [e]) rfl (single_sorts he)

/-- `inj_value` for a semantics `coreOKEx` accepts. -/
theorem inj_valueCEx (h : c.coreOKEx = true) (hI : I ⊧ᴵP Γ c) {a b : Srt} (hab : c.subsorts.contains (a, b) = true)
    {v : GroundTerm} (hv : c.sortOf v = some b) {e : M} (he : InS I (c.sortName a) e)
    (hm : GS I (c.sortName b) (.inj (c.sortName a)) [e] (elemOf c I v)) :
    ∃ w, c.sortOf w = some a ∧ v = injNormal a b w ∧ e = elemOf c I w := by
  obtain ⟨-, -, -, hg, -, -, -, -, hno⟩ := hypSoundEx_of_coreEx h
  haveI : OvlOK c := hno
  exact inj_back hI hg (injValue_subsorts_transCEx h) v (by simpa using hab) hv he hm

/-- `fixSide_read` for a semantics `coreOKEx` accepts. -/
theorem fixSide_readCEx (h : c.coreOKEx = true) (hI : I ⊧ᴵP Γ c) {vars : List Srt} {tbl : KoreAML.VarTable}
    {e : Valuation M} {i : Nat} {t : Term} {s : Srt}
    (hin : InS I (c.sortName (vars.getD i 0)) (e.evalEvar (tbl.ev (canonKey c vars i))))
    (ht : sortOfTerm (c.rhsCtx (c.fns.map Fn.sig)) vars t = some s)
    (hsh : t = .var i ∨ ∃ a b, t = .inj a b (.var i)) :
    ∃ y, InS I (c.sortName s) y ∧
      (∀ m, (KoreAML.tr ⟨tbl, []⟩ (Term.kore c (canonVars c vars) t)).interpret I e m ↔ m = y) ∧
      ∀ v, c.sortOf v = some s → y = elemOf c I v → Witnessed c I tbl (canonVars c vars) vars e i := by
  rcases hsh with rfl | ⟨a, b, rfl⟩
  · have hs : vars[i]? = some s := by simpa [sortOfTerm] using ht
    have hg : vars.getD i 0 = s := by rw [List.getD_eq_getElem?_getD, hs]; rfl
    rw [hg] at hin
    refine ⟨e.evalEvar (tbl.ev (canonKey c vars i)), hin, fun m => tr_var i m, fun v hv hy => ?_⟩
    exact ⟨v, by rw [hg]; exact hv, hy.symm⟩
  · obtain ⟨hab, hs, rfl⟩ := sortOfTerm_inj_var ht
    have hab' : c.subsorts.contains (a, s) = true := hab
    have hg : vars.getD i 0 = a := by rw [List.getD_eq_getElem?_getD, hs]; rfl
    rw [hg] at hin
    obtain ⟨y, hy, hgs⟩ := inj_definedCEx h hI hab' hin
    refine ⟨y, hy, fun m => ?_, fun v hv hyv => ?_⟩
    · rw [Term.kore, KoreAML.tr_injP, interp_injApp]
      constructor
      · rintro ⟨x, hx, hm⟩
        rw [(tr_var i x).mp hx] at hm
        exact (hgs m).mp hm
      · intro hm
        exact ⟨_, (tr_var i _).mpr rfl, (hgs m).mpr hm⟩
    · obtain ⟨w, hw, -, hew⟩ := inj_valueCEx h hI hab' hv hin (by rw [← hyv]; exact (hgs y).mpr rfl)
      exact ⟨w, by rw [hg]; exact hw, hew.symm⟩

/-- `fixesBy_valueT` for a semantics `coreOKEx` accepts. -/
theorem fixesBy_valueTCEx (h : c.coreOKEx = true) (hI : I ⊧ᴵP Γ c) (N : NodeFacts c I)
    {w : Prop} {T : Subst → Term → Option GroundTerm → Prop} (hT : TermUse c I w T) (τ : Subst)
    {vars : List Srt} {ok : Nat → Bool} {R : Nat → Prop} {i : Nat} {t u : Term} {s : Srt}
    {tbl : KoreAML.VarTable} {e : Valuation M}
    (hi : i < vars.length) (hRi : R i) (hRu : ∀ j ∈ varOccs u, R j)
    (ht : sortOfTerm (c.rhsCtx (c.fns.map Fn.sig)) vars t = some s)
    (hu : sortOfTerm (c.rhsCtx (c.fns.map Fn.sig)) vars u = some s)
    (hfb : fixesBy ok i t u = true) (hσ0 : ∃ σ, SortedOn c vars (fun j => R j ∨ w) σ)
    (hdec : ∀ σ, (∀ j, vars.length ≤ j → σ.lookup j = τ.lookup j) → SortedOn c vars (fun j => R j ∨ w) σ →
      AtElems c I tbl vars e ok R σ → ∃ r, EvalTerm c σ u r ∧ T σ u r)
    (hw : ∀ j, ok j = true → R j → j < vars.length → Witnessed c I tbl (canonVars c vars) vars e j)
    (hin : ∀ j, R j → j < vars.length → canonKey c vars j ∈ tbl ∧
      InS I (c.sortName (vars.getD j 0)) (e.evalEvar (tbl.ev (canonKey c vars j))))
    (hsat : ∀ y, InS I (c.sortName s) y →
      (∀ m, (KoreAML.tr ⟨tbl, []⟩ (Term.kore c (canonVars c vars) t)).interpret I e m ↔ m = y) →
      (KoreAML.tr ⟨tbl, []⟩ (Term.kore c (canonVars c vars) u)).interpret I e y) :
    Witnessed c I tbl (canonVars c vars) vars e i := by
  obtain ⟨hsh, hoku⟩ := fixesBy_shape hfb
  obtain ⟨y, hy, hty, hfin⟩ := fixSide_readCEx h hI (hin i hRi hi).2 ht hsh
  obtain ⟨σ0, hσ0⟩ := hσ0
  obtain ⟨σ1, hσ1, hσw1⟩ := subst_atElems (I := I) (tbl := tbl) (e := e) hσ0
  -- the substitution with τ beyond the variables in scope
  have hlo : ∀ j, j < vars.length → (overAt vars.length σ1 τ).lookup j = σ1.lookup j :=
    fun j hj => by rw [lookup_overAt, if_pos hj]
  have hσ : SortedOn c vars (fun j => R j ∨ w) (overAt vars.length σ1 τ) := fun j s' hRj hj => by
    rw [hlo j (List.getElem?_eq_some_iff.mp hj).1]; exact hσ1 j s' hRj hj
  have hσw : ∀ j, j < vars.length → Witnessed c I tbl (canonVars c vars) vars e j →
      ∃ v, (overAt vars.length σ1 τ).lookup j = some v ∧ c.sortOf v = some (vars.getD j 0) ∧
        elemOf c I v = e.evalEvar (tbl.ev (canonKey c vars j)) := fun j hj hwj => by
    rw [hlo j hj]; exact hσw1 j hj hwj
  have hat : AtElems c I tbl vars e ok R (overAt vars.length σ1 τ) := fun j hj hR hjl => by
    obtain ⟨v, hv, -, hev⟩ := hσw j hjl (hw j hj hR hjl)
    exact ⟨v, hv, hev⟩
  obtain ⟨r, hev, hTr⟩ := hdec _ (fun j hj => by rw [lookup_overAt, if_neg (by omega)]) hσ hat
  have hr : Reads c I vars (fun j => j ∈ varOccs u) (overAt vars.length σ1 τ) tbl e := fun j hj => by
    have hjl := varOccs_lt u hu j hj
    obtain ⟨v, hv, hsv, hev⟩ := hσw j hjl (hw j (hoku j hj) (hRu j hj) hjl)
    refine ⟨hjl, (hin j (hRu j hj) hjl).1, v, hv, hsv, fun m => ?_⟩
    rw [(elemOf_spec hI hsv e).1 m, hev]
  have hsatU : c.WellSortedAt vars (varOccs u) (overAt vars.length σ1 τ) := by
    intro j hj s' hs'
    obtain ⟨-, -, v, hv, hsv, -⟩ := hr j hj
    refine ⟨v, hv, ?_⟩
    rw [hsv, List.getD_eq_getElem?_getD, hs']; rfl
  have hread := hT hTr (hσ.mono fun _ hw' => Or.inr hw') (fun j hj => hj) hr hu
  have hres := (hread y).mp (hsat y hy hty)
  cases r with
  | none => exact hres.elim
  | some v =>
    have hv := EvalTerm.sorted_at N.sortCtx hev fns_headsOK hsatU hu rfl
    exact hfin v hv (((elemOf_spec hI hv e).1 y).mp hres)

/-- `fixes_value_readT` for a semantics `coreOKEx` accepts. -/
theorem fixes_value_readTCEx (h : c.coreOKEx = true) (hrc : c.readsConfined = true) (hIc : I ⊧ᴵP Γc c)
    (N : NodeFacts c I) {w : Prop} {T : Subst → Term → Option GroundTerm → Prop} (hT : TermUse c I w T)
    {val : Srt → Bool} (hval : ∀ s, val s = true → ∃ v, c.sortOf v = some s) (tl : Subst) :
    ∀ (p : Cond) (ok : Nat → Bool) (R : Nat → Prop) (i : Nat) (vars : List Srt) (tbl : KoreAML.VarTable)
      (e : Valuation M) (S : Srt),
    c.condOK vars p = true → Cond.boundV c val vars.length p = true →
    Cond.fixes c.confined val ok i vars.length p = true → i < vars.length → R i →
    (∀ j ∈ varOccsCond vars.length p, j < vars.length → R j) →
    (∃ σ, SortedOn c vars (fun j => R j ∨ w) σ) →
    (∀ σ, (∀ j, vars.length ≤ j → σ.lookup j = tl.lookup j) → SortedOn c vars (fun j => R j ∨ w) σ →
      AtElems c I tbl vars e ok R σ → ∃ b, HoldsReadT c T vars.length σ p b) →
    (∀ j, ok j = true → R j → j < vars.length → Witnessed c I tbl (canonVars c vars) vars e j) →
    (∀ j, R j → j < vars.length → canonKey c vars j ∈ tbl ∧
      InS I (c.sortName (vars.getD j 0)) (e.evalEvar (tbl.ev (canonKey c vars j)))) →
    (∀ k ∈ KoreAML.varsOf (Cond.kore c (canonVars c vars) (srtOf c S) p), k ∈ tbl) →
    S < nRegSorts + c.sortNames.length →
    (∃ a, (KoreAML.inhOf (KoreAML.trSort tbl (srtOf c S))).interpret I e a ∧
      (KoreAML.tr ⟨tbl, []⟩ (Cond.kore c (canonVars c vars) (srtOf c S) p)).interpret I e a) →
    Witnessed c I tbl (canonVars c vars) vars e i
  | .mem s t u, ok, R, i, vars, tbl, e, S, hok, _, hfix, hi, hRi, hR, hσ0, hdec, hw, hin, _, hS, ⟨a, ha, hpa⟩ => by
    have hI : I ⊧ᴵP Γ c := fun φ hφ => hIc φ (Or.inl hφ)
    rw [Semantics.condOK, Bool.and_eq_true] at hok
    have hs : s < nRegSorts + c.sortNames.length := of_decide_eq_true hok.2
    replace hok := hok.1; rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at hok
    rw [Cond.fixes] at hfix
    obtain ⟨τ, hτ, hτd⟩ := N.sort hs
    obtain ⟨τS, hτS, hτSd⟩ := N.sort hS
    have hRu : ∀ j ∈ varOccs u, R j := fun j hj =>
      hR j (by rw [varOccsCond]; exact List.mem_append_right _ hj) (varOccs_lt u hok.2 j hj)
    refine fixesBy_valueTCEx h hI N hT tl hi hRi hRu hok.1 hok.2 hfix hσ0 (fun σ htl hσ hat => ?_) hw hin fun y hy hty => ?_
    · obtain ⟨b, hb⟩ := hdec σ htl hσ hat
      cases hb with
      | mem _ _ hev' hT' => exact ⟨_, hev', hT'⟩
    · rw [Cond.kore, KoreAML.tr, KoreAML.interp_sIn N.defOK N.ceilDef (hτd tbl e) (hτSd tbl e) hτ hτS (fun m hm => by
        rw [(hty m).mp hm]
        exact (KoreAML.interp_inhOf_of (hτd tbl e)).mp (inhOf_srtOf_inS.mpr hy))] at hpa
      obtain ⟨⟨x, h1, h2⟩, -⟩ := hpa
      rw [(hty x).mp h1] at h2
      exact h2
  | .equals s t u, ok, R, i, vars, tbl, e, S, hok, _, hfix, hi, hRi, hR, hσ0, hdec, hw, hin, _, hS, ⟨a, ha, hpa⟩ => by
    have hI : I ⊧ᴵP Γ c := fun φ hφ => hIc φ (Or.inl hφ)
    rw [Semantics.condOK, Bool.and_eq_true] at hok
    have hs : s < nRegSorts + c.sortNames.length := of_decide_eq_true hok.2
    replace hok := hok.1; rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at hok
    rw [Cond.fixes, Bool.or_eq_true] at hfix
    obtain ⟨τ, hτ, hτd⟩ := N.sort hs
    obtain ⟨τS, hτS, hτSd⟩ := N.sort hS
    rw [Cond.kore, KoreAML.tr, KoreAML.interp_sEquals N.defOK N.ceilDef (hτd tbl e) (hτSd tbl e) hτ hτS] at hpa
    have hinh : ∀ y, InS I (c.sortName s) y → KoreAML.Inh I τ y := fun y hy =>
      (KoreAML.interp_inhOf_of (hτd tbl e)).mp (inhOf_srtOf_inS.mpr hy)
    have hRt : ∀ j ∈ varOccs t, R j := fun j hj =>
      hR j (by rw [varOccsCond]; exact List.mem_append_left _ hj) (varOccs_lt t hok.1 j hj)
    have hRu : ∀ j ∈ varOccs u, R j := fun j hj =>
      hR j (by rw [varOccsCond]; exact List.mem_append_right _ hj) (varOccs_lt u hok.2 j hj)
    rcases hfix with hfix | hfix
    · refine fixesBy_valueTCEx h hI N hT tl hi hRi hRu hok.1 hok.2 hfix hσ0 (fun σ htl hσ hat => ?_) hw hin fun y hy hty =>
        (hpa.2 y (hinh y hy)).mp ((hty y).mpr rfl)
      obtain ⟨b, hb⟩ := hdec σ htl hσ hat
      cases hb with
      | equals _ _ hev' hT' => exact ⟨_, hev', hT'⟩
    · refine fixesBy_valueTCEx h hI N hT tl hi hRi hRt hok.2 hok.1 hfix hσ0 (fun σ htl hσ hat => ?_) hw hin fun y hy hty =>
        (hpa.2 y (hinh y hy)).mpr ((hty y).mpr rfl)
      obtain ⟨b, hb⟩ := hdec σ htl hσ hat
      cases hb with
      | equals hev hT' _ _ => exact ⟨_, hev, hT'⟩
  | .and p q, ok, R, i, vars, tbl, e, S, hok, hbd, hfix, hi, hRi, hR, hσ0, hdec, hw, hin, hk, hS, ⟨a, ha, hpa⟩ => by
    rw [Semantics.condOK, Bool.and_eq_true] at hok
    rw [Cond.boundV, Bool.and_eq_true] at hbd
    rw [Cond.fixes, Bool.or_eq_true] at hfix
    rw [Cond.kore, tr_and2, KoreAML.interp_sAnd] at hpa
    have hRp : ∀ j ∈ varOccsCond vars.length p, j < vars.length → R j := fun j hj =>
      hR j (by rw [varOccsCond]; exact List.mem_append_left _ hj)
    have hRq : ∀ j ∈ varOccsCond vars.length q, j < vars.length → R j := fun j hj =>
      hR j (by rw [varOccsCond]; exact List.mem_append_right _ hj)
    have hkp : ∀ k ∈ KoreAML.varsOf (Cond.kore c (canonVars c vars) (srtOf c S) p), k ∈ tbl := fun k hk0 =>
      hk k (by rw [Cond.kore, KoreAML.varsOf, KoreAML.varsOfList]
               exact List.mem_append_right _ (List.mem_append_left _ hk0))
    have hkq : ∀ k ∈ KoreAML.varsOf (Cond.kore c (canonVars c vars) (srtOf c S) q), k ∈ tbl := fun k hk0 =>
      hk k (by rw [Cond.kore, KoreAML.varsOf, KoreAML.varsOfList, KoreAML.varsOfList]
               exact List.mem_append_right _ (List.mem_append_right _ (List.mem_append_left _ hk0)))
    rcases hfix with hfix | hfix
    · exact fixes_value_readTCEx h hrc hIc N hT hval tl p ok R i vars tbl e S hok.1 hbd.1 hfix hi hRi hRp hσ0 (fun σ htl hσ hat => by
        obtain ⟨b, hb⟩ := hdec σ htl hσ hat
        cases hb with
        | and h1 _ => exact ⟨_, h1⟩) hw hin hkp hS ⟨a, ha, hpa.1⟩
    · exact fixes_value_readTCEx h hrc hIc N hT hval tl q ok R i vars tbl e S hok.2 hbd.2 hfix hi hRi hRq hσ0 (fun σ htl hσ hat => by
        obtain ⟨b, hb⟩ := hdec σ htl hσ hat
        cases hb with
        | and _ h2 => exact ⟨_, h2⟩) hw hin hkq hS ⟨a, ha, hpa.2⟩
  | .or p q, ok, R, i, vars, tbl, e, S, hok, hbd, hfix, hi, hRi, hR, hσ0, hdec, hw, hin, hk, hS, ⟨a, ha, hpa⟩ => by
    rw [Semantics.condOK, Bool.and_eq_true] at hok
    rw [Cond.boundV, Bool.and_eq_true] at hbd
    rw [Cond.fixes, Bool.and_eq_true] at hfix
    rw [Cond.kore, Model.tr_or2Stdi, KoreAML.interp_sOr] at hpa
    have hRp : ∀ j ∈ varOccsCond vars.length p, j < vars.length → R j := fun j hj =>
      hR j (by rw [varOccsCond]; exact List.mem_append_left _ hj)
    have hRq : ∀ j ∈ varOccsCond vars.length q, j < vars.length → R j := fun j hj =>
      hR j (by rw [varOccsCond]; exact List.mem_append_right _ hj)
    have hkp : ∀ k ∈ KoreAML.varsOf (Cond.kore c (canonVars c vars) (srtOf c S) p), k ∈ tbl := fun k hk0 =>
      hk k (by rw [Cond.kore, KoreAML.varsOf, KoreAML.varsOfList]
               exact List.mem_append_right _ (List.mem_append_left _ hk0))
    have hkq : ∀ k ∈ KoreAML.varsOf (Cond.kore c (canonVars c vars) (srtOf c S) q), k ∈ tbl := fun k hk0 =>
      hk k (by rw [Cond.kore, KoreAML.varsOf, KoreAML.varsOfList, KoreAML.varsOfList]
               exact List.mem_append_right _ (List.mem_append_right _ (List.mem_append_left _ hk0)))
    rcases hpa.2 with hpa' | hpa'
    · exact fixes_value_readTCEx h hrc hIc N hT hval tl p ok R i vars tbl e S hok.1 hbd.1 hfix.1 hi hRi hRp hσ0 (fun σ htl hσ hat => by
        obtain ⟨b, hb⟩ := hdec σ htl hσ hat
        cases hb with
        | or h1 _ => exact ⟨_, h1⟩) hw hin hkp hS ⟨a, ha, hpa'⟩
    · exact fixes_value_readTCEx h hrc hIc N hT hval tl q ok R i vars tbl e S hok.2 hbd.2 hfix.2 hi hRi hRq hσ0 (fun σ htl hσ hat => by
        obtain ⟨b, hb⟩ := hdec σ htl hσ hat
        cases hb with
        | or _ h2 => exact ⟨_, h2⟩) hw hin hkq hS ⟨a, ha, hpa'⟩
  | .ex s body, ok, R, i, vars, tbl, e, S, hok, hbd, hfix, hi, hRi, hR, hσ0, hdec, hw, hin, hk, hS, ⟨a, ha, hpa⟩ => by
    have hI : I ⊧ᴵP Γ c := fun φ hφ => hIc φ (Or.inl hφ)
    rw [Semantics.condOK] at hok
    rw [Cond.boundV, Bool.and_eq_true, Bool.or_eq_true, Bool.and_eq_true] at hbd
    have hfix : Cond.fixes c.confined val (fun j => if j == vars.length then
        (c.confined s || (val s && Cond.fixes c.confined val (fun j => j != vars.length && ok j) vars.length
          (vars.length + 1) body)) else ok j) i (vars.length + 1) body = true := hfix
    have hlen : (vars ++ [s]).length = vars.length + 1 := by simp
    obtain ⟨τS, hτS, hτSd⟩ := N.sort hS
    let K := canonKey c (vars ++ [s]) vars.length
    have hkb : KoreAML.evarKey (Cond.binder c (canonVars c vars).length s).kore = K := Model.binder_keyStdI vars s
    have hkore : Cond.kore c (canonVars c vars) (srtOf c S) (.ex s body) =
        .exist (srtOf c S) (Cond.binder c (canonVars c vars).length s).kore
          (Cond.kore c (canonVars c (vars ++ [s])) (srtOf c S) body) := by
      rw [← Model.canonVars_snocStdI c vars s]; rfl
    rw [hkore] at hk hpa
    have hK : K ∈ tbl := hk _ (by rw [KoreAML.varsOf, hkb]; simp)
    have hkB : ∀ k ∈ KoreAML.varsOf (Cond.kore c (canonVars c (vars ++ [s])) (srtOf c S) body), k ∈ tbl :=
      fun k hk0 => hk k (by rw [KoreAML.varsOf]; exact List.mem_append_right _ hk0)
    rw [KoreAML.tr, KoreAML.interp_sExists, hkb] at hpa
    obtain ⟨a0, hmem, hbody⟩ := hpa
    simp only [KoreAML.interp_member N.defOK, Function.update_same] at hmem
    have ha0 : InS I (c.sortName s) a0 :=
      (inhOf_srtOf_inS (c := c) (I := I) (tbl := tbl) (s := s) (a := a0)).mp hmem
    -- the valuation under the binder, and what it keeps of the variables in scope
    have hkey : ∀ j, j < vars.length → canonKey c (vars ++ [s]) j = canonKey c vars j :=
      fun j hj => Model.canonKey_appendStdI (c := c) (ys := [s]) hj
    have hev : ∀ j, j < vars.length → R j →
        Function.update e.evalEvar (tbl.ev K) a0 (tbl.ev (canonKey c vars j)) = e.evalEvar (tbl.ev (canonKey c vars j)) := by
      intro j hj hRj
      rw [Function.update_noteq]
      intro he
      have := canonKey_inj (vars := vars ++ [s]) (c := c) (i := j) (j := vars.length) (by simp; omega) (by simp)
        ((hkey j hj).trans (ev_inj (hin j hRj hj).1 hK he))
      omega
    have hgd : ∀ j, j < vars.length → (vars ++ [s]).getD j 0 = vars.getD j 0 :=
      fun j hj => Model.getD_appendL_stdI _ _ _ hj
    have hWiff : ∀ j, j < vars.length → R j →
        (Witnessed c I tbl (canonVars c (vars ++ [s])) (vars ++ [s])
            ⟨Function.update e.evalEvar (tbl.ev K) a0, e.evalSvar⟩ j ↔
          Witnessed c I tbl (canonVars c vars) vars e j) := by
      intro j hj hRj
      show (∃ v, c.sortOf v = some ((vars ++ [s]).getD j 0) ∧
          elemOf c I v = Function.update e.evalEvar (tbl.ev K) a0 (tbl.ev (canonKey c (vars ++ [s]) j))) ↔
        ∃ v, c.sortOf v = some (vars.getD j 0) ∧ elemOf c I v = e.evalEvar (tbl.ev (canonKey c vars j))
      rw [hgd j hj, hkey j hj, hev j hj hRj]
    have hin' : ∀ j, (R j ∨ j = vars.length) → j < (vars ++ [s]).length → canonKey c (vars ++ [s]) j ∈ tbl ∧
        InS I (c.sortName ((vars ++ [s]).getD j 0))
          (Function.update e.evalEvar (tbl.ev K) a0 (tbl.ev (canonKey c (vars ++ [s]) j))) := by
      intro j hRj hj
      rw [hlen] at hj
      by_cases hjl : j < vars.length
      · have hRj' : R j := hRj.resolve_right (by omega)
        rw [hgd j hjl, hkey j hjl, hev j hjl hRj']; exact hin j hRj' hjl
      · have hjn : j = vars.length := by omega
        subst hjn
        refine ⟨hK, ?_⟩
        show InS I (c.sortName ((vars ++ [s]).getD vars.length 0)) (Function.update e.evalEvar (tbl.ev K) a0 (tbl.ev K))
        rw [Function.update_same, Model.getD_appendR_stdI _ _ _ (Nat.le_refl _)]
        simpa using ha0
    have hat : ∀ (ok' : Nat → Bool), (∀ j, j < vars.length → ok j = true → ok' j = true) → ∀ σ',
        AtElems c I tbl (vars ++ [s]) ⟨Function.update e.evalEvar (tbl.ev K) a0, e.evalSvar⟩ ok'
          (fun j => R j ∨ j = vars.length) σ' →
        AtElems c I tbl vars e ok R σ' := by
      intro ok' hok' σ' hat j hj hRj hjl
      obtain ⟨v, hv, hve⟩ := hat j (hok' j hjl hj) (Or.inl hRj) (by rw [hlen]; omega)
      refine ⟨v, hv, ?_⟩
      rw [← hev j hjl hRj, ← hkey j hjl]; exact hve
    -- the body has a truth value at each substitution under the binder: the condition's at the
    -- substitution that is σ' on the variables in scope and τ beyond them
    have hdec' : ∀ (ok' : Nat → Bool), (∀ j, j < vars.length → ok j = true → ok' j = true) → ∀ σ',
        (∀ j, (vars ++ [s]).length ≤ j → σ'.lookup j = tl.lookup j) →
        SortedOn c (vars ++ [s]) (fun j => (R j ∨ j = vars.length) ∨ w) σ' →
        AtElems c I tbl (vars ++ [s]) ⟨Function.update e.evalEvar (tbl.ev K) a0, e.evalSvar⟩ ok'
          (fun j => R j ∨ j = vars.length) σ' →
        ∃ b, HoldsReadT c T (vars ++ [s]).length σ' body b := by
      intro ok' hok' σ' _ hσ' hat'
      have hlo : ∀ j, j < vars.length → (overAt vars.length σ' tl).lookup j = σ'.lookup j :=
        fun j hj => by rw [lookup_overAt, if_pos hj]
      have hσ : SortedOn c vars (fun j => R j ∨ w) (overAt vars.length σ' tl) := fun j s' hRj hj => by
        have hjl := (List.getElem?_eq_some_iff.mp hj).1
        rw [hlo j hjl]
        exact hσ' j s' (hRj.elim (fun hR' => Or.inl (Or.inl hR')) Or.inr)
          (by rw [List.getElem?_append_left hjl]; exact hj)
      obtain ⟨b, hb⟩ := hdec _ (fun j hj => by rw [lookup_overAt, if_neg (by omega)]) hσ
        (fun j hj hRj hjl => by rw [hlo j hjl]; exact hat ok' hok' σ' hat' j hj hRj hjl)
      cases hb with
      | ex g hb _ =>
        refine ⟨g σ', ?_⟩
        rw [hlen]
        refine hb σ' ⟨fun j hj => (hlo j hj).symm, fun j s' hj => ?_⟩
        cases j with
        | zero =>
          simp at hj; subst hj
          exact hσ' vars.length _ (Or.inl (Or.inr rfl)) (by simp)
        | succ j => simp at hj
    have haS : (KoreAML.inhOf (KoreAML.trSort tbl (srtOf c S))).interpret I
        ⟨Function.update e.evalEvar (tbl.ev K) a0, e.evalSvar⟩ a :=
      (KoreAML.interp_inhOf_of (hτSd tbl _)).mpr ((KoreAML.interp_inhOf_of (hτSd tbl e)).mp ha)
    -- a value of the binder's sort: the element's where the sort is confined, `val`'s otherwise
    have hconf : c.confined s = true → Witnessed c I tbl (canonVars c (vars ++ [s])) (vars ++ [s])
        ⟨Function.update e.evalEvar (tbl.ev K) a0, e.evalSvar⟩ vars.length := by
      intro hc
      obtain ⟨v, hv, hd⟩ := confined_valueCEx h hrc hIc hc ⟨Function.update e.evalEvar (tbl.ev K) a0, e.evalSvar⟩ a0
        ((inS_iff _).mpr ha0)
      refine ⟨v, by rw [Model.getD_appendR_stdI _ _ _ (Nat.le_refl _)]; simpa using hv, ?_⟩
      show elemOf c I v = Function.update e.evalEvar (tbl.ev K) a0 (tbl.ev K)
      rw [Function.update_same]
      exact (hd _).mp (((elemOf_spec hI hv _).1 _).mpr rfl)
    have hvs : ∃ v, c.sortOf v = some s := by
      rcases hbd.1 with hc | ⟨hv, -⟩
      · obtain ⟨v, hv, -⟩ := hconf hc
        exact ⟨v, by rw [Model.getD_appendR_stdI _ _ _ (Nat.le_refl _)] at hv; simpa using hv⟩
      · exact hval s hv
    have hσ0' : ∃ σ, SortedOn c (vars ++ [s]) (fun j => (R j ∨ j = vars.length) ∨ w) σ := by
      obtain ⟨σ0, hσ0⟩ := hσ0
      obtain ⟨v, hv⟩ := hvs
      exact ⟨_, (sortedOn_snocFV hσ0 hv).mono fun j hj =>
        hj.elim (fun hj' => hj'.elim (fun hR' => Or.inl (Or.inl hR')) Or.inr) fun hw' => Or.inl (Or.inr hw')⟩
    have hrest : ∀ j, j < vars.length → ok j = true → R j →
        Witnessed c I tbl (canonVars c (vars ++ [s])) (vars ++ [s])
          ⟨Function.update e.evalEvar (tbl.ev K) a0, e.evalSvar⟩ j :=
      fun j hjl hj hRj => (hWiff j hjl hRj).mpr (hw j hj hRj hjl)
    have hRB : ∀ j ∈ varOccsCond (vars ++ [s]).length body, j < (vars ++ [s]).length → R j ∨ j = vars.length := by
      intro j hj hjl
      rw [hlen] at hj hjl
      by_cases hlt : j < vars.length
      · exact .inl (hR j (by rw [varOccsCond]; exact List.mem_filter.mpr ⟨hj, by simpa using hlt⟩) hlt)
      · exact .inr (by omega)
    refine (hWiff i hi hRi).mp (fixes_value_readTCEx h hrc hIc N hT hval tl body (fun j => if j == vars.length then
        (c.confined s || (val s && Cond.fixes c.confined val (fun j => j != vars.length && ok j) vars.length
          (vars.length + 1) body)) else ok j) (fun j => R j ∨ j = vars.length) i (vars ++ [s]) tbl _ S hok
      (by rw [hlen]; exact hbd.2)
      (by rw [hlen]; exact hfix) (by rw [hlen]; omega) (Or.inl hRi) hRB hσ0'
      (hdec' _ fun j hjl hj => by simp [Nat.ne_of_lt hjl, hj]) (fun j hj hRj hjl => ?_) hin' hkB hS ⟨a, haS, hbody⟩)
    rw [hlen] at hjl
    by_cases hjn : j = vars.length
    · subst hjn
      simp only [beq_self_eq_true, ↓reduceIte, Bool.or_eq_true, Bool.and_eq_true] at hj
      rcases hj with hc | ⟨-, hfx⟩
      · exact hconf hc
      · exact fixes_value_readTCEx h hrc hIc N hT hval tl body (fun j => j != vars.length && ok j)
          (fun j => R j ∨ j = vars.length) vars.length (vars ++ [s]) tbl _ S hok (by rw [hlen]; exact hbd.2)
          (by rw [hlen]; exact hfx) (by rw [hlen]; omega) (Or.inr rfl) hRB hσ0'
          (hdec' _ fun j hjl hj => by simp [Nat.ne_of_lt hjl, hj])
          (fun j hj hRj hjl => by
            simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hj
            rw [hlen] at hjl
            exact hrest j (by omega) hj.2 (hRj.resolve_right hj.1)) hin' hkB hS ⟨a, haS, hbody⟩
    · have hjl' : j < vars.length := by omega
      have hb : (j == vars.length) = false := by simp [hjn]
      simp only [hb, Bool.false_eq_true, ↓reduceIte] at hj
      exact hrest j hjl' hj (hRj.resolve_right hjn)
  | .top, _, _, _, _, _, _, _, _, _, hfix, _, _, _, _, _, _, _, _, _, _ => by simp [Cond.fixes] at hfix
  | .bot, _, _, _, _, _, _, _, _, _, hfix, _, _, _, _, _, _, _, _, _, _ => by simp [Cond.fixes] at hfix
  | .not _, _, _, _, _, _, _, _, _, _, hfix, _, _, _, _, _, _, _, _, _, _ => by simp [Cond.fixes] at hfix
  | .implies .., _, _, _, _, _, _, _, _, _, hfix, _, _, _, _, _, _, _, _, _, _ => by simp [Cond.fixes] at hfix
  | .ceil .., _, _, _, _, _, _, _, _, _, hfix, _, _, _, _, _, _, _, _, _, _ => by simp [Cond.fixes] at hfix
  | .exMatch .., _, _, _, _, _, _, _, _, _, hfix, _, _, _, _, _, _, _, _, _, _ => by simp [Cond.fixes] at hfix
  | .all .., _, _, _, _, _, _, _, _, _, hfix, _, _, _, _, _, _, _, _, _, _ => by simp [Cond.fixes] at hfix

/-- `fixes_value_read_hr` for a semantics `coreOKEx` accepts. -/
theorem fixes_value_read_hrCEx (h : c.coreOKEx = true) (hrc : c.readsConfined = true) (hIc : I ⊧ᴵP Γc c)
    (N : NodeFacts c I) {val : Srt → Bool} (hval : ∀ s, val s = true → ∃ v, c.sortOf v = some s) (τ : Subst)
    (p : Cond) (ok : Nat → Bool) (R : Nat → Prop) (i : Nat) (vars : List Srt) (tbl : KoreAML.VarTable)
    (e : Valuation M) (S : Srt)
    (hok : c.condOK vars p = true) (hbd : Cond.boundV c val vars.length p = true)
    (hfix : Cond.fixes c.confined val ok i vars.length p = true) (hi : i < vars.length) (hRi : R i)
    (hR : ∀ j ∈ varOccsCond vars.length p, j < vars.length → R j)
    (hσ0 : ∃ σ, c.WellSorted vars σ)
    (hdec : ∀ σ, (∀ j, vars.length ≤ j → σ.lookup j = τ.lookup j) → c.WellSorted vars σ →
      AtElems c I tbl vars e ok R σ → ∃ b, HoldsRead c I vars.length σ p b)
    (hw : ∀ j, ok j = true → R j → j < vars.length → Witnessed c I tbl (canonVars c vars) vars e j)
    (hin : ∀ j, R j → j < vars.length → canonKey c vars j ∈ tbl ∧
      InS I (c.sortName (vars.getD j 0)) (e.evalEvar (tbl.ev (canonKey c vars j))))
    (hk : ∀ k ∈ KoreAML.varsOf (Cond.kore c (canonVars c vars) (srtOf c S) p), k ∈ tbl)
    (hS : S < nRegSorts + c.sortNames.length)
    (hsat : ∃ a, (KoreAML.inhOf (KoreAML.trSort tbl (srtOf c S))).interpret I e a ∧
      (KoreAML.tr ⟨tbl, []⟩ (Cond.kore c (canonVars c vars) (srtOf c S) p)).interpret I e a) :
    Witnessed c I tbl (canonVars c vars) vars e i := by
  obtain ⟨σ0, hσ0⟩ := hσ0
  exact fixes_value_readTCEx h hrc hIc N termUse_termAt hval τ p ok R i vars tbl e S hok hbd hfix hi hRi hR
    ⟨σ0, fun j s _ hs => hσ0 j s hs⟩
    (fun σ htl hσ hat => hdec σ htl (fun j s hs => hσ j s (Or.inr trivial) hs) hat) hw hin hk hS hsat

/-- `fixes_value_hr` for a semantics `coreOKEx` accepts. -/
theorem fixes_value_hrCEx (h : c.coreOKEx = true) (hrc : c.readsConfined = true) (hIc : I ⊧ᴵP Γc c)
    (N : NodeFacts c I) {val : Srt → Bool} (hval : ∀ s, val s = true → ∃ v, c.sortOf v = some s) (τ : Subst)
    (p : Cond) (ok : Nat → Bool) (i : Nat) (vars : List Srt) (tbl : KoreAML.VarTable) (e : Valuation M) (S : Srt)
    (hok : c.condOK vars p = true) (hbd : Cond.boundV c val vars.length p = true)
    (hfix : Cond.fixes c.confined val ok i vars.length p = true) (hi : i < vars.length)
    (hσ0 : ∃ σ, c.WellSorted vars σ)
    (hdec : ∀ σ, (∀ j, vars.length ≤ j → σ.lookup j = τ.lookup j) → c.WellSorted vars σ →
      AtElems c I tbl vars e ok (fun _ => True) σ → ∃ b, HoldsRead c I vars.length σ p b)
    (hw : ∀ j, ok j = true → j < vars.length → Witnessed c I tbl (canonVars c vars) vars e j)
    (hin : ∀ j, j < vars.length → canonKey c vars j ∈ tbl ∧
      InS I (c.sortName (vars.getD j 0)) (e.evalEvar (tbl.ev (canonKey c vars j))))
    (hk : ∀ k ∈ KoreAML.varsOf (Cond.kore c (canonVars c vars) (srtOf c S) p), k ∈ tbl)
    (hS : S < nRegSorts + c.sortNames.length)
    (hsat : ∃ a, (KoreAML.inhOf (KoreAML.trSort tbl (srtOf c S))).interpret I e a ∧
      (KoreAML.tr ⟨tbl, []⟩ (Cond.kore c (canonVars c vars) (srtOf c S) p)).interpret I e a) :
    Witnessed c I tbl (canonVars c vars) vars e i :=
  fixes_value_read_hrCEx h hrc hIc N hval τ p ok (fun _ => True) i vars tbl e S hok hbd hfix hi trivial
    (fun _ _ _ => trivial) hσ0 hdec (fun j hj _ hjl => hw j hj hjl) (fun j _ hjl => hin j hjl) hk hS hsat

end InjValueEx

end CE

namespace HoldsShape

open ML Faithful

section CoreEx
variable {c : Semantics} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}

/-- **A model of `Γc` of a definition `coreOKEx` accepts has the constructors' facts.** -/
theorem nodeFacts_of_coreEx (h : c.coreOKEx = true) (hIc : I ⊧ᴵP Γc c) : NodeFacts c I := by
  have htn : ∀ {vars : List Srt} {t : Term} {s : Srt}, sortOfTerm (c.rhsCtx (c.fns.map Fn.sig)) vars t = some s →
      (∀ i ∈ varOccs t, ∀ s', vars[i]? = some s' → s' < nRegSorts + c.sortNames.length) →
      s < nRegSorts + c.sortNames.length := fun {vars t s} ht hv =>
    sortOfTerm_numbered (sortOf_numbered_ofCEx (hypSoundEx_of_coreEx h) (sortsNumbered_of_coreEx h) (Semantics.coreOKEx_ovls h)) (sortsNumbered_of_coreEx h) (Semantics.coreOKEx_ovls h)
      (fun k hk => Model.rhsHead_kernel fns_headsOK hk) (fun _ _ h' => h') rfl t ht hv
  have hvn : ∀ {v : GroundTerm} {s : Srt}, c.sortOf v = some s → s < nRegSorts + c.sortNames.length :=
    fun hv => sortOf_numbered_ofCEx (hypSoundEx_of_coreEx h) (sortsNumbered_of_coreEx h) (Semantics.coreOKEx_ovls h) hv
  have hI : I ⊧ᴵP Γ c := fun φ hφ => hIc φ (Or.inl hφ)
  obtain ⟨hok, hsr, hnn, hg, hph, hcso, hcs, hph', hno⟩ := hypSoundEx_of_coreEx h
  haveI : OvlOK c := hno
  have hsc := sortCtx_of_allCEx hok hsr (OvlOK.ovlCase hno)
  refine ⟨defOK hI, sat_sigItem hI (by simp [sigItems]), fun {s} hs => ?_, fun {v s} hv tbl e => ?_,
    fun {v w s} hv hw e a h1 h2 => ?_, hsc, htn, hvn⟩
  · obtain ⟨τ, hτ, hτs⟩ := sortSing hI hs
    exact ⟨τ, hτs, fun tbl e a => by unfold srtOf; rw [trSort_srt]; exact hτ a⟩
  · refine ⟨elemOf c I v, (elemOf_spec hI hv e).1, ?_⟩
    have := (elemOf_spec hI hv e).2
    unfold srtOf; rw [trSort_srt]; exact this
  · exact values_apart hI hg hsc.trans (apartSort_of_sorted hg hv) hv hw
      (((elemOf_spec hI hv e).1 a).mp h1 ▸ ((elemOf_spec hI hw e).1 a).mp h2 ▸ rfl)

/-- `atomFacts_of_core` for a semantics `coreOKEx` accepts. -/
theorem atomFacts_of_coreEx (h : c.coreOKEx = true) (hIc : I ⊧ᴵP Γc c) (hT : TermSound c I) :
    AtomFacts c I := by
  have htn : ∀ {vars : List Srt} {t : Term} {s : Srt}, sortOfTerm (c.rhsCtx (c.fns.map Fn.sig)) vars t = some s →
      (∀ i ∈ varOccs t, ∀ s', vars[i]? = some s' → s' < nRegSorts + c.sortNames.length) →
      s < nRegSorts + c.sortNames.length := fun {vars t s} ht hv =>
    sortOfTerm_numbered (sortOf_numbered_ofCEx (hypSoundEx_of_coreEx h) (sortsNumbered_of_coreEx h) (Semantics.coreOKEx_ovls h)) (sortsNumbered_of_coreEx h) (Semantics.coreOKEx_ovls h)
      (fun k hk => Model.rhsHead_kernel fns_headsOK hk) (fun _ _ h' => h') rfl t ht hv
  have hvn : ∀ {v : GroundTerm} {s : Srt}, c.sortOf v = some s → s < nRegSorts + c.sortNames.length :=
    fun hv => sortOf_numbered_ofCEx (hypSoundEx_of_coreEx h) (sortsNumbered_of_coreEx h) (Semantics.coreOKEx_ovls h) hv
  have hI : I ⊧ᴵP Γ c := fun φ hφ => hIc φ (Or.inl hφ)
  obtain ⟨hok, hsr, hnn, hg, hph, hcso, hcs, hph', hno⟩ := hypSoundEx_of_coreEx h
  haveI : OvlOK c := hno
  have hsc := sortCtx_of_allCEx hok hsr (OvlOK.ovlCase hno)
  refine ⟨defOK hI, sat_sigItem hI (by simp [sigItems]), fun {s} hs => ?_, fun {v s} hv tbl e => ?_,
    fun {v w s} hv hw e a h1 h2 => ?_, termSoundAt_of hI hT, hsc, htn, hvn⟩
  · obtain ⟨τ, hτ, hτs⟩ := sortSing hI hs
    exact ⟨τ, hτs, fun tbl e a => by unfold srtOf; rw [trSort_srt]; exact hτ a⟩
  · refine ⟨elemOf c I v, (elemOf_spec hI hv e).1, ?_⟩
    have := (elemOf_spec hI hv e).2
    unfold srtOf; rw [trSort_srt]; exact this
  · exact values_apart hI hg hsc.trans (apartSort_of_sorted hg hv) hv hw
      (((elemOf_spec hI hv e).1 a).mp h1 ▸ ((elemOf_spec hI hw e).1 a).mp h2 ▸ rfl)

/-- `patReading_of_core` for a semantics `coreOKEx` accepts. -/
theorem patReading_of_coreEx (h : c.coreOKEx = true) (hIc : I ⊧ᴵP Γc c) : PatReading c I := by
  have hI : I ⊧ᴵP Γ c := fun φ hφ => hIc φ (Or.inl hφ)
  obtain ⟨hok, hsr, hnn, hg, hph, hcso, hcs, hph', hno⟩ := hypSoundEx_of_coreEx h
  haveI : OvlOK c := hno
  have hsc := sortCtx_of_allCEx hok hsr (OvlOK.ovlCase hno)
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

/-- `binderFacts_of_core` for a semantics `coreOKEx` accepts. -/
theorem binderFacts_of_coreEx (h : c.coreOKEx = true) (hrc : c.readsConfined = true) (hIc : I ⊧ᴵP Γc c) :
    BinderFacts c I :=
  ⟨fun {s} hs tbl e a ha => confined_valueCEx h hrc hIc hs e a (by
    unfold srtOf at ha; rw [trSort_srt] at ha; exact ha),
   fun hs => confinedAt_numbered_ids (Semantics.coreOKEx_parts h).2.2.2.2 _ hs, patReading_of_coreEx h hIc⟩

end CoreEx

end HoldsShape

namespace CE

open ML Faithful HoldsShape

section ExsValuesEx
variable {c : Semantics} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}

/-- **An element valuation that extends a match of values and satisfies `post` gives each existential variable a value's element**: `exs_values_hr` for a semantics `coreOKEx` accepts. -/
theorem exs_values_hrCEx (h : c.coreOKEx = true) (hrc : c.readsConfined = true) (hIc : I ⊧ᴵP Γc c)
    (N : NodeFacts c I) {cl : Clause} (hs : c.clauseExOK cl = true)
    (hb : Cond.bound c cl.vars.length cl.post = true) (hp : c.clausePlainEx cl = true)
    {σ : Subst} (hσ : c.WellSortedAt cl.vars cl.univ σ)
    (hsome : ∃ σ', AgreeOff (cl.exs.filter (!cl.leftVars.contains ·)) σ σ' ∧ c.WellSorted cl.vars σ')
    (hdec : ∀ σ', AgreeOff (cl.exs.filter (!cl.leftVars.contains ·)) σ σ' → c.WellSorted cl.vars σ' →
      ∃ b, HoldsRead c I cl.vars.length σ' cl.post b)
    {tbl : KoreAML.VarTable} {e : Valuation M} {S : Srt}
    (hag : ∀ i ∈ cl.univ, ∀ v, σ.lookup i = some v →
      ∀ m, m = e.evalEvar (tbl.ev (keyAt (canonVars c cl.vars) i)) ↔ (den c v).interpret I e m)
    (hin : ∀ i ∈ cl.exs, ∀ s, cl.vars[i]? = some s →
      (KoreAML.inhOf (sortP (c.sortName s))).interpret I e (e.evalEvar (tbl.ev (keyAt (canonVars c cl.vars) i))))
    (hkv : ∀ j, j < cl.vars.length → keyAt (canonVars c cl.vars) j ∈ tbl)
    (hk : ∀ k ∈ KoreAML.varsOf (Cond.kore c (canonVars c cl.vars) (srtOf c S) cl.post), k ∈ tbl)
    (hS : S < nRegSorts + c.sortNames.length)
    (hpost : ∃ a, (KoreAML.inhOf (KoreAML.trSort tbl (srtOf c S))).interpret I e a ∧
      (KoreAML.tr ⟨tbl, []⟩ (Cond.kore c (canonVars c cl.vars) (srtOf c S) cl.post)).interpret I e a) :
    ∀ i ∈ cl.exs, Witnessed c I tbl (canonVars c cl.vars) cl.vars e i := by
  have hI : I ⊧ᴵP Γ c := fun φ hφ => hIc φ (Or.inl hφ)
  simp only [Semantics.clauseExOK, Bool.and_eq_true] at hs
  obtain ⟨⟨⟨hlt, -⟩, hleft⟩, hok⟩ := hs
  have hlt : ∀ i ∈ cl.exs, i < cl.vars.length := fun i hi => of_decide_eq_true (List.all_eq_true.mp hlt i hi)
  have hfree : cl.exs.filter (!cl.leftVars.contains ·) = cl.exs :=
    List.filter_eq_self.mpr fun i hi => List.all_eq_true.mp hleft i hi
  rw [hfree] at hsome hdec
  have hsj : ∀ j, j < cl.vars.length → cl.vars[j]? = some (cl.vars.getD j 0) := fun j hj => by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]
  have huniv : ∀ j, j < cl.vars.length → j ∉ cl.exs → j ∈ cl.univ := fun j hj hne => by
    simp [Clause.univ, hj, hne]
  -- a variable that is not existential is at the element of σ's value
  have hunivV : ∀ j, j < cl.vars.length → j ∉ cl.exs → ∃ v, σ.lookup j = some v ∧
      c.sortOf v = some (cl.vars.getD j 0) ∧ elemOf c I v = e.evalEvar (tbl.ev (keyAt (canonVars c cl.vars) j)) :=
    fun j hj hne => by
      obtain ⟨v, hv, hsv⟩ := hσ j (huniv j hj hne) _ (hsj j hj)
      exact ⟨v, hv, hsv, (((elemOf_spec hI hsv e).1 _).mp ((hag j (huniv j hj hne) v hv _).mp rfl)).symm⟩
  have hunivW : ∀ j, j < cl.vars.length → j ∉ cl.exs → Witnessed c I tbl (canonVars c cl.vars) cl.vars e j :=
    fun j hj hne => by
      obtain ⟨v, -, hsv, hev⟩ := hunivV j hj hne
      exact ⟨v, hsv, hev⟩
  -- every variable in scope is at an element of its sort
  have hinAll : ∀ j, j < cl.vars.length →
      InS I (c.sortName (cl.vars.getD j 0)) (e.evalEvar (tbl.ev (keyAt (canonVars c cl.vars) j))) := fun j hj => by
    by_cases hje : j ∈ cl.exs
    · exact (inS_iff e).mp (hin j hje _ (hsj j hj))
    · obtain ⟨v, hsv, hev⟩ := hunivW j hj hje
      rw [← hev]
      exact (inS_iff e).mp (elemOf_spec hI hsv e).2
  -- a variable of a confined sort is at the element of a value
  have hconfW : ∀ j, j < cl.vars.length → (cl.vars[j]?.map c.confined).getD false = true →
      Witnessed c I tbl (canonVars c cl.vars) cl.vars e j := fun j hj hc => by
    rw [hsj j hj] at hc
    obtain ⟨v, hv, hd⟩ := confined_valueCEx h hrc hIc (by simpa using hc) e _ ((inS_iff e).mpr (hinAll j hj))
    exact ⟨v, hv, (((elemOf_spec hI hv e).1 _).mp ((hd _).mpr rfl)).symm⟩
  have hσ0 : ∃ σ', c.WellSorted cl.vars σ' := by
    obtain ⟨σ', -, hw⟩ := hsome
    exact ⟨σ', hw⟩
  -- `post` has a truth value at a substitution of values that agrees with the valuation on the
  -- variables that are not existential and is σ beyond the variables in scope: an extension of σ
  have hdecG : ∀ (ok : Nat → Bool), (∀ j, j < cl.vars.length → j ∉ cl.exs → ok j = true) → ∀ σ₁,
      (∀ j, cl.vars.length ≤ j → σ₁.lookup j = σ.lookup j) → c.WellSorted cl.vars σ₁ →
      AtElems c I tbl cl.vars e ok (fun _ => True) σ₁ → ∃ b, HoldsRead c I cl.vars.length σ₁ cl.post b := by
    intro ok hokU σ₁ htl hσ₁ hat
    refine hdec σ₁ (fun i hi => ?_) hσ₁
    by_cases hil : i < cl.vars.length
    · obtain ⟨v, hv, hsv, hev⟩ := hunivV i hil hi
      obtain ⟨v₁, hv₁, hev₁⟩ := hat i (hokU i hil hi) trivial hil
      have hev₁ : elemOf c I v₁ = e.evalEvar (tbl.ev (keyAt (canonVars c cl.vars) i)) := hev₁
      obtain ⟨v₁', hv₁', hsv₁⟩ := hσ₁ i _ (hsj i hil)
      rw [hv₁] at hv₁'; cases hv₁'
      have hd : (den c v₁).interpret I e (elemOf c I v) := by
        rw [hev, ← hev₁]
        exact ((elemOf_spec hI hsv₁ e).1 _).mpr rfl
      rw [hv₁, hv, N.apart hsv₁ hsv e _ hd (((elemOf_spec hI hsv e).1 _).mpr rfl)]
    · exact htl i (by omega)
  -- the rounds of `fixedExs`
  have key : ∀ (l acc : List Nat), (∀ i ∈ acc, Witnessed c I tbl (canonVars c cl.vars) cl.vars e i) →
      ∀ i ∈ l.foldl (fun acc _ =>
        cl.exs.filter fun i => acc.contains i ||
          Cond.fixes c.confined (fun _ => false) (fun j => !cl.exs.contains j || acc.contains j ||
            (j != i && (cl.vars[j]?.map c.confined).getD false)) i cl.vars.length cl.post) acc,
        Witnessed c I tbl (canonVars c cl.vars) cl.vars e i := by
    intro l
    induction l with
    | nil => intro acc hacc i hi; exact hacc i hi
    | cons _ l ih =>
      intro acc hacc
      rw [List.foldl_cons]
      refine ih _ fun i hi => ?_
      obtain ⟨hie, hcond⟩ := List.mem_filter.mp hi
      rw [Bool.or_eq_true] at hcond
      rcases hcond with hc | hfix
      · exact hacc i (List.contains_iff_mem.mp hc)
      · refine fixes_value_hrCEx h hrc hIc N (val := fun _ => false) (fun s hs => by cases hs) σ cl.post _ i cl.vars tbl e S
          hok (Cond.boundV_of_bound c _ cl.post _ hb) hfix (hlt i hie) hσ0
          (hdecG _ fun j _ hne => by simp [hne]) (fun j hj hjl => ?_)
          (fun j hj => ⟨hkv j hj, hinAll j hj⟩) hk hS hpost
        simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hj
        rcases hj with (hj | hj) | hj
        · exact hunivW j hjl (by simpa using hj)
        · exact hacc j (List.contains_iff_mem.mp hj)
        · exact hconfW j hjl hj.2
  intro i hi
  simp only [Semantics.clausePlainEx, Bool.and_eq_true] at hp
  have hpi := List.all_eq_true.mp hp.2 i hi
  rw [Bool.or_eq_true] at hpi
  rcases hpi with hc | hf
  · exact hconfW i (hlt i hi) hc
  · exact key _ [] (fun _ hm => nomatch hm) i (List.contains_iff_mem.mp hf)

end ExsValuesEx

end CE

end KCore
