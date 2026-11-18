/-
  KCore. A variable a condition fixes is at a value's element (`fixes_value`).

  In a model of `Γc` of a definition with `coreOK` that reads confined sorts, with the soundness
  of `EvalTerm` in the model (`AtomFacts`), let p be a condition with
  `Cond.fixes c.confined val ok i n p = true`, `val` true only at sorts with a value, and e an
  element valuation over the n variables in scope that satisfies p and gives every variable `ok`
  admits the element of a value. Then e gives i the element of a value, provided
  - p has a truth value at every substitution of values that agrees with e on the variables `ok`
    admits (the term that fixes i then has a result there, which the model reads);
  - some substitution of values is well sorted on the variables in scope (a variable `ok` does
    not admit is asked a value of its sort, not an element);
  - each `ex` binder of p is of a confined sort or of a sort `val` admits (`Cond.boundV`): a
    binder of a sort without a value has no instance at a value, so its body is asked no truth
    value and the fixing term no result.

  `fixes_value_read` states it over the variables in scope a predicate R holds of, the fixed one
  and the condition's among them: nothing is asked of another variable in scope. `fixes_value` is
  it where R holds of every variable.

  By recursion on p through `mem`, `equals`, `and`, `or` and `ex`. At `mem` and `equals` the fixed
  side is the variable or its injection, one element of the atom's sort (`fixSide_read`,
  `inj_defined`); the other side has a result at the substitution `subst_atElems` builds, whose
  element the fixed side shares, and `inj_value` reads the injection back.
-/
import KcoreSpec.ClausePreCore
import KcoreSpec.HoldsModelFixed
import KcoreSpec.InjValue

set_option autoImplicit false

namespace KCore

open ML Faithful HoldsShape

namespace CE

section FixesValue
variable {c : Semantics} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}

/-- σ gives each variable in scope that R holds of a value of its sort. -/
def SortedOn (c : Semantics) (vars : List Srt) (R : Nat → Prop) (σ : Subst) : Prop :=
  ∀ (i : Nat) (s : Srt), R i → vars[i]? = some s → ∃ v, σ.lookup i = some v ∧ c.sortOf v = some s

/-- σ gives each variable in scope that `ok` admits and R holds of a value whose element the
valuation gives it. -/
def AtElems (c : Semantics) (I : Interpretation KoreAML.Sym M) (tbl : KoreAML.VarTable) (vars : List Srt)
    (e : Valuation M) (ok : Nat → Bool) (R : Nat → Prop) (σ : Subst) : Prop :=
  ∀ j, ok j = true → R j → j < vars.length →
    ∃ v, σ.lookup j = some v ∧ elemOf c I v = e.evalEvar (tbl.ev (canonKey c vars j))

/-- What `fixesBy` decides: t is the variable i or an injection of it, and `ok` admits every
variable of u. -/
theorem fixesBy_shape {ok : Nat → Bool} {i : Nat} {t u : Term} (h : fixesBy ok i t u = true) :
    (t = .var i ∨ ∃ a b, t = .inj a b (.var i)) ∧ ∀ j ∈ varOccs u, ok j = true := by
  unfold fixesBy at h
  rw [Bool.and_eq_true] at h
  refine ⟨?_, fun j hj => List.all_eq_true.mp h.2 j hj⟩
  have h1 := h.1
  split at h1
  · exact .inl (by rw [beq_iff_eq.mp h1])
  · exact .inr ⟨_, _, by rw [beq_iff_eq.mp h1]⟩
  · cases h1

/-- A substitution well sorted on the variables R holds of that gives each variable at a value's
element such a value, from one that is well sorted on them. -/
theorem subst_atElems {vars : List Srt} {R : Nat → Prop} {tbl : KoreAML.VarTable} {e : Valuation M} {σ0 : Subst}
    (hσ0 : SortedOn c vars R σ0) :
    ∃ σ, SortedOn c vars R σ ∧ ∀ j, j < vars.length → Witnessed c I tbl (canonVars c vars) vars e j →
      ∃ v, σ.lookup j = some v ∧ c.sortOf v = some (vars.getD j 0) ∧
        elemOf c I v = e.evalEvar (tbl.ev (canonKey c vars j)) := by
  classical
  let f : Nat → GroundTerm := fun j =>
    if hj : Witnessed c I tbl (canonVars c vars) vars e j then Classical.choose hj else (σ0.lookup j).getD default
  have hl : ∀ j, j < vars.length → ((List.range vars.length).map fun j => (j, f j)).lookup j = some (f j) := by
    intro j hj
    rw [List.range_eq_range', lookup_range', if_pos ⟨Nat.zero_le _, by omega⟩]
  refine ⟨(List.range vars.length).map fun j => (j, f j), fun j s hR hs => ?_, fun j hj hw => ?_⟩
  · have hj : j < vars.length := (List.getElem?_eq_some_iff.mp hs).1
    refine ⟨f j, hl j hj, ?_⟩
    by_cases hw : Witnessed c I tbl (canonVars c vars) vars e j
    · have hg : vars.getD j 0 = s := by rw [List.getD_eq_getElem?_getD, hs, Option.getD_some]
      have hf : f j = Classical.choose hw := dif_pos hw
      rw [hf]; exact (Classical.choose_spec hw).1.trans (congrArg some hg)
    · obtain ⟨v, hv, hsv⟩ := hσ0 j s hR hs
      have hf : f j = (σ0.lookup j).getD default := dif_neg hw
      rw [hf, hv]; exact hsv
  · refine ⟨f j, hl j hj, ?_⟩
    have hf : f j = Classical.choose hw := dif_pos hw
    rw [hf]
    exact Classical.choose_spec hw

/-- **The fixed side of an atom, read**: t, the variable i or an injection of it, of the sort s,
is one element y of s at a valuation that gives i an element of its sort; and where y is the
element of a value of s, the valuation gives i the element of a value (`inj_value` at an
injection). -/
theorem fixSide_read (h : c.coreOK = true) (hI : I ⊧ᴵP Γ c) {vars : List Srt} {tbl : KoreAML.VarTable}
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
    obtain ⟨y, hy, hgs⟩ := inj_defined h hI hab' hin
    refine ⟨y, hy, fun m => ?_, fun v hv hyv => ?_⟩
    · rw [Term.kore, KoreAML.tr_injP, interp_injApp]
      constructor
      · rintro ⟨x, hx, hm⟩
        rw [(tr_var i x).mp hx] at hm
        exact (hgs m).mp hm
      · intro hm
        exact ⟨_, (tr_var i _).mpr rfl, (hgs m).mpr hm⟩
    · obtain ⟨w, hw, -, hew⟩ := inj_value h hI hab' hv hin (by rw [← hyv]; exact (hgs y).mpr rfl)
      exact ⟨w, by rw [hg]; exact hw, hew.symm⟩

/-- **An atom that fixes i**: where the fixed side t, read as one element y of the atom's sort,
has y in the other side u, and u has a result at every substitution of values that agrees with the
valuation on the variables `ok` admits, the valuation gives i the element of a value. Only the
variables R holds of are read, i and those of u among them. -/
theorem fixesBy_value (h : c.coreOK = true) (hI : I ⊧ᴵP Γ c) (F : AtomFacts c I)
    {vars : List Srt} {ok : Nat → Bool} {R : Nat → Prop} {i : Nat} {t u : Term} {s : Srt}
    {tbl : KoreAML.VarTable} {e : Valuation M}
    (hi : i < vars.length) (hRi : R i) (hRu : ∀ j ∈ varOccs u, R j)
    (ht : sortOfTerm (c.rhsCtx (c.fns.map Fn.sig)) vars t = some s)
    (hu : sortOfTerm (c.rhsCtx (c.fns.map Fn.sig)) vars u = some s)
    (hfb : fixesBy ok i t u = true) (hσ0 : ∃ σ, SortedOn c vars R σ)
    (hdec : ∀ σ, SortedOn c vars R σ → AtElems c I tbl vars e ok R σ → ∃ r, EvalTerm c σ u r)
    (hw : ∀ j, ok j = true → R j → j < vars.length → Witnessed c I tbl (canonVars c vars) vars e j)
    (hin : ∀ j, R j → j < vars.length → canonKey c vars j ∈ tbl ∧
      InS I (c.sortName (vars.getD j 0)) (e.evalEvar (tbl.ev (canonKey c vars j))))
    (hsat : ∀ y, InS I (c.sortName s) y →
      (∀ m, (KoreAML.tr ⟨tbl, []⟩ (Term.kore c (canonVars c vars) t)).interpret I e m ↔ m = y) →
      (KoreAML.tr ⟨tbl, []⟩ (Term.kore c (canonVars c vars) u)).interpret I e y) :
    Witnessed c I tbl (canonVars c vars) vars e i := by
  obtain ⟨hsh, hoku⟩ := fixesBy_shape hfb
  obtain ⟨y, hy, hty, hfin⟩ := fixSide_read h hI (hin i hRi hi).2 ht hsh
  obtain ⟨σ0, hσ0⟩ := hσ0
  obtain ⟨σ, hσ, hσw⟩ := subst_atElems (I := I) (tbl := tbl) (e := e) hσ0
  have hat : AtElems c I tbl vars e ok R σ := fun j hj hR hjl => by
    obtain ⟨v, hv, -, hev⟩ := hσw j hjl (hw j hj hR hjl)
    exact ⟨v, hv, hev⟩
  obtain ⟨r, hev⟩ := hdec σ hσ hat
  have hr : Reads c I vars (fun j => j ∈ varOccs u) σ tbl e := fun j hj => by
    have hjl := varOccs_lt u hu j hj
    obtain ⟨v, hv, hsv, hev⟩ := hσw j hjl (hw j (hoku j hj) (hRu j hj) hjl)
    refine ⟨hjl, (hin j (hRu j hj) hjl).1, v, hv, hsv, fun m => ?_⟩
    rw [(elemOf_spec hI hsv e).1 m, hev]
  obtain ⟨-, hru⟩ := term_read F hr hu (fun j hj => hj)
  obtain ⟨hread, hsort⟩ := hru r hev
  have hres := (hread y).mp (hsat y hy hty)
  cases r with
  | none => exact hres.elim
  | some v =>
    have hv := hsort v rfl
    exact hfin v hv (((elemOf_spec hI hv e).1 y).mp hres)

/-- A substitution well sorted on the variables in scope R holds of, with a value of the sort s at
the next index, is well sorted under a binder of s on those variables and the bound one. -/
theorem sortedOn_snocFV {vars : List Srt} {R : Nat → Prop} {σ : Subst} (hσ : SortedOn c vars R σ) {s : Srt}
    {v : GroundTerm} (hv : c.sortOf v = some s) :
    SortedOn c (vars ++ [s]) (fun j => R j ∨ j = vars.length) (Model.extOneStdI σ vars.length v) := by
  intro j s' hR hj
  by_cases hjl : j < vars.length
  · rw [List.getElem?_append_left hjl] at hj
    rw [Model.extOneStdI_off σ v (by omega)]
    exact hσ j s' (hR.resolve_right (by omega)) hj
  · have hjn : j = vars.length := by
      have := (List.getElem?_eq_some_iff.mp hj).1
      simp at this; omega
    subst hjn
    rw [List.getElem?_append_right (Nat.le_refl _)] at hj
    simp at hj; subst hj
    exact ⟨v, Model.extOneStdI_at σ _ v, hv⟩

/-- **`fixes_value_read`.** In a model of `Γc` of a definition with `coreOK` that reads confined
sorts, with the soundness of `EvalTerm` in the model (`F`) and `val` true only at sorts with a
value: an element valuation over the variables in scope that gives every variable `ok` admits the
element of a value and satisfies a condition that fixes i (`Cond.fixes`) gives i the element of a
value. The condition has a truth value at every substitution of values that agrees with the
valuation on the variables `ok` admits, some substitution of values is well sorted on the
variables in scope, and each `ex` binder of the condition is of a confined sort or of a sort
`val` admits (`Cond.boundV`). Of the variables in scope only those R holds of are read, i and the
condition's among them: of another, neither a value of its sort, nor its key in the table, nor
its element is asked. -/
theorem fixes_value_read (h : c.coreOK = true) (hrc : c.readsConfined = true) (hIc : I ⊧ᴵP Γc c)
    (F : AtomFacts c I) {val : Srt → Bool} (hval : ∀ s, val s = true → ∃ v, c.sortOf v = some s) :
    ∀ (p : Cond) (ok : Nat → Bool) (R : Nat → Prop) (i : Nat) (vars : List Srt) (tbl : KoreAML.VarTable)
      (e : Valuation M) (S : Srt),
    c.condOK vars p = true → Cond.boundV c val vars.length p = true →
    Cond.fixes c.confined val ok i vars.length p = true → i < vars.length → R i →
    (∀ j ∈ varOccsCond vars.length p, j < vars.length → R j) →
    (∃ σ, SortedOn c vars R σ) →
    (∀ σ, SortedOn c vars R σ → AtElems c I tbl vars e ok R σ → ∃ b, Holds c vars.length σ p b) →
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
    obtain ⟨τ, hτ, hτd⟩ := F.sort hs
    obtain ⟨τS, hτS, hτSd⟩ := F.sort hS
    have hRu : ∀ j ∈ varOccs u, R j := fun j hj =>
      hR j (by rw [varOccsCond]; exact List.mem_append_right _ hj) (varOccs_lt u hok.2 j hj)
    refine fixesBy_value h hI F hi hRi hRu hok.1 hok.2 hfix hσ0 (fun σ hσ hat => ?_) hw hin fun y hy hty => ?_
    · obtain ⟨b, hb⟩ := hdec σ hσ hat
      cases hb with
      | mem _ hev' => exact ⟨_, hev'⟩
    · rw [Cond.kore, KoreAML.tr, KoreAML.interp_sIn F.defOK F.ceilDef (hτd tbl e) (hτSd tbl e) hτ hτS (fun m hm => by
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
    obtain ⟨τ, hτ, hτd⟩ := F.sort hs
    obtain ⟨τS, hτS, hτSd⟩ := F.sort hS
    rw [Cond.kore, KoreAML.tr, KoreAML.interp_sEquals F.defOK F.ceilDef (hτd tbl e) (hτSd tbl e) hτ hτS] at hpa
    have hinh : ∀ y, InS I (c.sortName s) y → KoreAML.Inh I τ y := fun y hy =>
      (KoreAML.interp_inhOf_of (hτd tbl e)).mp (inhOf_srtOf_inS.mpr hy)
    have hRt : ∀ j ∈ varOccs t, R j := fun j hj =>
      hR j (by rw [varOccsCond]; exact List.mem_append_left _ hj) (varOccs_lt t hok.1 j hj)
    have hRu : ∀ j ∈ varOccs u, R j := fun j hj =>
      hR j (by rw [varOccsCond]; exact List.mem_append_right _ hj) (varOccs_lt u hok.2 j hj)
    rcases hfix with hfix | hfix
    · refine fixesBy_value h hI F hi hRi hRu hok.1 hok.2 hfix hσ0 (fun σ hσ hat => ?_) hw hin fun y hy hty =>
        (hpa.2 y (hinh y hy)).mp ((hty y).mpr rfl)
      obtain ⟨b, hb⟩ := hdec σ hσ hat
      cases hb with
      | equals _ hev' => exact ⟨_, hev'⟩
    · refine fixesBy_value h hI F hi hRi hRt hok.2 hok.1 hfix hσ0 (fun σ hσ hat => ?_) hw hin fun y hy hty =>
        (hpa.2 y (hinh y hy)).mpr ((hty y).mpr rfl)
      obtain ⟨b, hb⟩ := hdec σ hσ hat
      cases hb with
      | equals hev _ => exact ⟨_, hev⟩
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
    · exact fixes_value_read h hrc hIc F hval p ok R i vars tbl e S hok.1 hbd.1 hfix hi hRi hRp hσ0 (fun σ hσ hat => by
        obtain ⟨b, hb⟩ := hdec σ hσ hat
        cases hb with
        | and h1 _ => exact ⟨_, h1⟩) hw hin hkp hS ⟨a, ha, hpa.1⟩
    · exact fixes_value_read h hrc hIc F hval q ok R i vars tbl e S hok.2 hbd.2 hfix hi hRi hRq hσ0 (fun σ hσ hat => by
        obtain ⟨b, hb⟩ := hdec σ hσ hat
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
    · exact fixes_value_read h hrc hIc F hval p ok R i vars tbl e S hok.1 hbd.1 hfix.1 hi hRi hRp hσ0 (fun σ hσ hat => by
        obtain ⟨b, hb⟩ := hdec σ hσ hat
        cases hb with
        | or h1 _ => exact ⟨_, h1⟩) hw hin hkp hS ⟨a, ha, hpa'⟩
    · exact fixes_value_read h hrc hIc F hval q ok R i vars tbl e S hok.2 hbd.2 hfix.2 hi hRi hRq hσ0 (fun σ hσ hat => by
        obtain ⟨b, hb⟩ := hdec σ hσ hat
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
    obtain ⟨τS, hτS, hτSd⟩ := F.sort hS
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
    simp only [KoreAML.interp_member F.defOK, Function.update_same] at hmem
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
    -- the body has a truth value at each substitution under the binder
    have hdec' : ∀ (ok' : Nat → Bool), (∀ j, j < vars.length → ok j = true → ok' j = true) → ∀ σ',
        SortedOn c (vars ++ [s]) (fun j => R j ∨ j = vars.length) σ' →
        AtElems c I tbl (vars ++ [s]) ⟨Function.update e.evalEvar (tbl.ev K) a0, e.evalSvar⟩ ok'
          (fun j => R j ∨ j = vars.length) σ' →
        ∃ b, Holds c (vars ++ [s]).length σ' body b := by
      intro ok' hok' σ' hσ' hat'
      have hσ : SortedOn c vars R σ' := fun j s' hRj hj =>
        hσ' j s' (Or.inl hRj) (by rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp hj).1]; exact hj)
      obtain ⟨b, hb⟩ := hdec σ' hσ (hat ok' hok' σ' hat')
      cases hb with
      | ex g hb _ =>
        refine ⟨g σ', ?_⟩
        rw [hlen]
        refine hb σ' ⟨fun _ _ => rfl, fun j s' hj => ?_⟩
        cases j with
        | zero =>
          simp at hj; subst hj
          exact hσ' vars.length _ (Or.inr rfl) (by simp)
        | succ j => simp at hj
    have haS : (KoreAML.inhOf (KoreAML.trSort tbl (srtOf c S))).interpret I
        ⟨Function.update e.evalEvar (tbl.ev K) a0, e.evalSvar⟩ a :=
      (KoreAML.interp_inhOf_of (hτSd tbl _)).mpr ((KoreAML.interp_inhOf_of (hτSd tbl e)).mp ha)
    -- a value of the binder's sort: the element's where the sort is confined, `val`'s otherwise
    have hconf : c.confined s = true → Witnessed c I tbl (canonVars c (vars ++ [s])) (vars ++ [s])
        ⟨Function.update e.evalEvar (tbl.ev K) a0, e.evalSvar⟩ vars.length := by
      intro hc
      obtain ⟨v, hv, hd⟩ := confined_value h hrc hIc hc ⟨Function.update e.evalEvar (tbl.ev K) a0, e.evalSvar⟩ a0
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
    have hσ0' : ∃ σ, SortedOn c (vars ++ [s]) (fun j => R j ∨ j = vars.length) σ := by
      obtain ⟨σ0, hσ0⟩ := hσ0
      obtain ⟨v, hv⟩ := hvs
      exact ⟨_, sortedOn_snocFV hσ0 hv⟩
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
    refine (hWiff i hi hRi).mp (fixes_value_read h hrc hIc F hval body (fun j => if j == vars.length then
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
      · exact fixes_value_read h hrc hIc F hval body (fun j => j != vars.length && ok j)
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

/-- **`fixes_value`.** `fixes_value_read` where every variable in scope is read: some substitution
of values is well sorted on all of them, each has its key in the table and its element in its
sort, and each one `ok` admits is at a value's element. -/
theorem fixes_value (h : c.coreOK = true) (hrc : c.readsConfined = true) (hIc : I ⊧ᴵP Γc c)
    (F : AtomFacts c I) {val : Srt → Bool} (hval : ∀ s, val s = true → ∃ v, c.sortOf v = some s)
    (p : Cond) (ok : Nat → Bool) (i : Nat) (vars : List Srt) (tbl : KoreAML.VarTable) (e : Valuation M) (S : Srt)
    (hok : c.condOK vars p = true) (hbd : Cond.boundV c val vars.length p = true)
    (hfix : Cond.fixes c.confined val ok i vars.length p = true) (hi : i < vars.length)
    (hσ0 : ∃ σ, c.WellSorted vars σ)
    (hdec : ∀ σ, c.WellSorted vars σ → AtElems c I tbl vars e ok (fun _ => True) σ → ∃ b, Holds c vars.length σ p b)
    (hw : ∀ j, ok j = true → j < vars.length → Witnessed c I tbl (canonVars c vars) vars e j)
    (hin : ∀ j, j < vars.length → canonKey c vars j ∈ tbl ∧
      InS I (c.sortName (vars.getD j 0)) (e.evalEvar (tbl.ev (canonKey c vars j))))
    (hk : ∀ k ∈ KoreAML.varsOf (Cond.kore c (canonVars c vars) (srtOf c S) p), k ∈ tbl)
    (hS : S < nRegSorts + c.sortNames.length)
    (hsat : ∃ a, (KoreAML.inhOf (KoreAML.trSort tbl (srtOf c S))).interpret I e a ∧
      (KoreAML.tr ⟨tbl, []⟩ (Cond.kore c (canonVars c vars) (srtOf c S) p)).interpret I e a) :
    Witnessed c I tbl (canonVars c vars) vars e i := by
  obtain ⟨σ0, hσ0⟩ := hσ0
  exact fixes_value_read h hrc hIc F hval p ok (fun _ => True) i vars tbl e S hok hbd hfix hi trivial
    (fun _ _ _ => trivial) ⟨σ0, fun j s _ hs => hσ0 j s hs⟩
    (fun σ hσ hat => hdec σ (fun j s hs => hσ j s trivial hs) hat)
    (fun j hj _ hjl => hw j hj hjl) (fun j _ hjl => hin j hjl) hk hS hsat

end FixesValue

end CE

end KCore
