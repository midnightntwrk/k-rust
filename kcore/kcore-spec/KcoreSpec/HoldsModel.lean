/-
  KCore. A rule's conditions in the value model at a transition T.

  In `stdI_T c T` an element of a numbered sort is a value of that sort exactly (`InSort`), a term
  denotes the values `EvalTerm` gives it (`AtT.tr_term`), and a pattern the values it matches
  (`AtT.tr_pat`). So a condition, written over the canonical names of the variables in scope at a
  valuation that reads them as their values under σ, holds at an element of the predicate sort
  exactly where the truth value `Holds` gives it is `true` (`holds_atT`); a binder ranges over the
  values of its sort, as `Extends` does. `holds_stdI`: where the condition has a truth value, it
  holds exactly where that value is `true`.
-/
import KcoreSpec.ExModelT

set_option autoImplicit false

namespace KCore

namespace Faithful

namespace Model

open ML

variable {c : Semantics} {T : GroundTerm → GroundTerm → Prop}

/-! ## Sorts in the value model -/

theorem srtOf_den_stdI (h : HypModelCore c) {tbl : KoreAML.VarTable} {s : Srt}
    (hs : s < nRegSorts + c.sortNames.length) (e : Valuation Elem) (a : Elem) :
    (KoreAML.trSort tbl (srtOf c s)).interpret (stdI_T c T) e a ↔ a = .srt s := by
  unfold srtOf; rw [trSort_srt]; exact AtT.sort_den h.namesK hs e a

theorem isSort_stdI {s : Srt} (hs : s < nRegSorts + c.sortNames.length) :
    KoreAML.IsSort (stdI_T c T) (.srt s) :=
  (AtT.isSort_iff _).mpr ⟨s, List.mem_range.mpr hs, rfl⟩

theorem inhOf_srtOf_stdI (h : HypModelCore c) {tbl : KoreAML.VarTable} {s : Srt}
    (hs : s < nRegSorts + c.sortNames.length) (e : Valuation Elem) (a : Elem) :
    (KoreAML.inhOf (KoreAML.trSort tbl (srtOf c s))).interpret (stdI_T c T) e a ↔ InSort c s a := by
  rw [KoreAML.interp_inhOf_of (srtOf_den_stdI h hs e), AtT.inh_srt]

theorem srtOf_free_stdI {tbl : KoreAML.VarTable} {s : Srt} :
    (KoreAML.trSort tbl (srtOf c s)).isFreeEvar KoreAML.topVar = false := by
  unfold srtOf; rw [trSort_srt]; rfl

/-- **A well-sorted term's sort is numbered** where its variables' sorts are, in a context whose
heads are kernel symbols and whose subsorts are the definition's. -/
theorem sortOfTerm_numStdI (h : HypModelCore c) {x : TermCtx} (hx : ∀ k ∈ x.heads, k ∈ kernelSyms c)
    (hsub : ∀ a b, (a, b) ∈ x.subs → (a, b) ∈ c.subsorts) (hlib : x.lib = c.lib) {vars : List Srt} :
    ∀ (t : Term) {s : Srt}, sortOfTerm x vars t = some s →
      (∀ i ∈ varOccs t, ∀ s', vars[i]? = some s' → s' < nRegSorts + c.sortNames.length) →
      s < nRegSorts + c.sortNames.length
  | .var j, s, ht, hv => hv j (by simp [varOccs]) s (sortOfTerm_var.mp ht)
  | .app f ts, s, ht, _ => by
    obtain ⟨k, hk, -, rfl⟩ := sortOfTerm_app.mp ht
    exact h.symSorts (hx _ (lookupSig_spec hk).1) _ (List.mem_cons_self ..)
  | .inj a b t, s, ht, _ => by
    obtain ⟨hab, -, rfl⟩ := sortOfTerm_inj.mp ht
    exact (h.subSorts (hsub _ _ hab)).2
  | .as t j, s, ht, hv => by
    obtain ⟨-, h'⟩ := Exec.sortOfTerm_as ht
    exact sortOfTerm_numStdI h hx hsub hlib t h' fun i hi s' hs' =>
      hv i (by rw [varOccs]; exact List.mem_append_left _ hi) s' hs'
  | .dv s' lit, s, ht, _ => by
    obtain ⟨hok, rfl⟩ := sortOfTerm_dv.mp ht
    exact h.dvSort (hlib ▸ hok)

/-- **A confined sort is numbered**: Bool, or a sort of constructor terms. -/
theorem confinedAt_numberedStdI (h : HypModelCore c) :
    ∀ (k : Nat) {s : Srt}, c.confinedAt k s = true → s < nRegSorts + c.sortNames.length
  | 0, s, hc => by
    simp only [Semantics.confinedAt, Bool.and_eq_true, beq_iff_eq] at hc
    rw [hc.1]; exact bool_numbered
  | k + 1, s, hc => by
    simp only [Semantics.confinedAt, Bool.or_eq_true, Bool.and_eq_true] at hc
    rcases hc with hc | ⟨⟨hN, -⟩, -⟩
    · simp only [beq_iff_eq] at hc
      rw [hc.1]; exact bool_numbered
    · exact consSorts_numbered h (by simpa using hN)

theorem confined_numberedStdI (h : HypModelCore c) {s : Srt} (hc : c.confined s = true) :
    s < nRegSorts + c.sortNames.length :=
  confinedAt_numberedStdI h _ hc

/-! ## The canonical variables under a binder -/

theorem getD_appendL_stdI {α : Type} (l l' : List α) (d : α) {i : Nat} (h : i < l.length) :
    (l ++ l').getD i d = l.getD i d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_appendR_stdI {α : Type} (l l' : List α) (d : α) {i : Nat} (h : l.length ≤ i) :
    (l ++ l').getD i d = l'.getD (i - l.length) d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right h]

theorem getD_eq_getElemStdI {α : Type} (l : List α) (d : α) {i : Nat} (h : i < l.length) : l.getD i d = l[i] := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

theorem canonVars_appendStdI (c : Semantics) (vars ys : List Srt) :
    canonVars c vars ++ ((List.range ys.length).zip ys).map (fun (j, y) => Cond.binder c ((canonVars c vars).length + j) y) =
      canonVars c (vars ++ ys) := by
  rw [canonVars_length]
  apply List.ext_getElem (by simp [canonVars_length])
  intro i h1 h2
  have h2' : i < (vars ++ ys).length := by rwa [canonVars_length] at h2
  have e2 := canonVars_getD c h2'
  rw [getD_eq_getElemStdI _ _ h2] at e2
  rw [e2]
  by_cases hi : i < vars.length
  · have hi' : i < (canonVars c vars).length := by rwa [canonVars_length]
    rw [List.getElem_append_left hi']
    have e1 := canonVars_getD c hi
    rw [getD_eq_getElemStdI _ _ hi'] at e1
    rw [e1, getD_appendL_stdI _ _ _ hi]
  · have hle : (canonVars c vars).length ≤ i := by rw [canonVars_length]; omega
    rw [List.getElem_append_right hle]
    have hj : i - vars.length < ys.length := by simp at h2'; omega
    simp only [List.getElem_map, List.getElem_zip, List.getElem_range, canonVars_length]
    rw [getD_appendR_stdI _ _ _ (by omega), getD_eq_getElemStdI _ _ hj]
    have hij : vars.length + (i - vars.length) = i := by omega
    simp only [Cond.binder, hij]

theorem canonVars_snocStdI (c : Semantics) (vars : List Srt) (s : Srt) :
    canonVars c vars ++ [Cond.binder c (canonVars c vars).length s] = canonVars c (vars ++ [s]) := by
  have := canonVars_appendStdI c vars [s]
  simpa using this

/-! ## The reading of a condition -/

/-- **The valuation reads the variables P as their values under σ**: each is a variable in scope,
its key is in the table, σ gives it a value of its sort, and the valuation that value's element. -/
def ReadsT (c : Semantics) (vars : List Srt) (P : Nat → Prop) (σ : Subst) (tbl : KoreAML.VarTable)
    (e : Valuation Elem) : Prop :=
  ∀ i, P i → i < vars.length ∧ canonKey c vars i ∈ tbl ∧
    ∃ v, σ.lookup i = some v ∧ c.sortOf v = some (vars.getD i 0) ∧ e.evalEvar (tbl.ev (canonKey c vars i)) = .val v

theorem ReadsT.hvar {vars : List Srt} {P : Nat → Prop} {σ : Subst} {tbl : KoreAML.VarTable} {e : Valuation Elem}
    (hr : ReadsT c vars P σ tbl e) :
    ∀ i, P i → ∀ m, (KoreAML.tr ⟨tbl, []⟩ (KoreAML.varAt (canonVars c vars) i)).interpret (stdI_T c T) e m ↔
      ∃ v, σ.lookup i = some v ∧ m = .val v := by
  intro i hi m
  rw [AtT.var_read]
  obtain ⟨-, -, v, hv, -, he⟩ := hr i hi
  show m = e.evalEvar (tbl.ev (canonKey c vars i)) ↔ _
  rw [he, hv]
  simp

theorem ReadsT.sortedAt {vars : List Srt} {P : Nat → Prop} {σ : Subst} {tbl : KoreAML.VarTable} {e : Valuation Elem}
    (hr : ReadsT c vars P σ tbl e) {is : List Nat} (his : ∀ i ∈ is, P i) : c.WellSortedAt vars is σ := by
  intro i hi s hs
  obtain ⟨-, -, v, hv, hsv, -⟩ := hr i (his i hi)
  refine ⟨v, hv, ?_⟩
  rw [hsv, List.getD_eq_getElem?_getD, hs]
  rfl

/-- Where the valuation reads a condition's free variables, they are well sorted under σ: what
`holds_decided` reads to give the condition a truth value. -/
theorem ReadsT.sortedCond {vars : List Srt} {P : Nat → Prop} {σ : Subst} {tbl : KoreAML.VarTable}
    {e : Valuation Elem} (hr : ReadsT c vars P σ tbl e) {p : Cond}
    (hP : ∀ i ∈ varOccsCond vars.length p, i < vars.length → P i) :
    c.WellSortedAt vars (varOccsCond vars.length p) σ := by
  intro i hi s hs
  refine hr.sortedAt (is := [i]) (fun j hj => ?_) i (List.mem_singleton_self i) s hs
  rw [List.mem_singleton] at hj
  subst hj
  exact hP j hi (List.getElem?_eq_some_iff.mp hs).1

/-- **The reading of a condition in the value model at T**: for a condition with `condOK` and
`Cond.bound`, written over the canonical names of the variables `vars` in scope, at a valuation that
reads its free variables as their values under σ (`ReadsT`), whose table holds the condition's
variables, and at every element of a numbered predicate sort S: the element is in the condition
exactly where the truth value `Holds` gives is `true`. -/
def HoldsT (c : Semantics) (T : GroundTerm → GroundTerm → Prop) (p : Cond) : Prop :=
  ∀ {vars : List Srt} {P : Nat → Prop} {σ : Subst} {b : Bool} {tbl : KoreAML.VarTable} {e : Valuation Elem} {S : Srt},
    c.condOK vars p = true → Cond.bound c vars.length p = true →
    (∀ i ∈ varOccsCond vars.length p, i < vars.length → P i) → ReadsT c vars P σ tbl e →
    (∀ k ∈ KoreAML.varsOf (Cond.kore c (canonVars c vars) (srtOf c S) p), k ∈ tbl) →
    S < nRegSorts + c.sortNames.length → Holds c vars.length σ p b →
    ∀ a, InSort c S a →
      ((KoreAML.tr ⟨tbl, []⟩ (Cond.kore c (canonVars c vars) (srtOf c S) p)).interpret (stdI_T c T) e a ↔ b = true)

/-! ### The connectives -/

theorem holdsT_top (h : HypModelCore c) : HoldsT c T .top := by
  intro vars P σ b tbl e S _ _ _ _ _ hS hh a ha
  cases hh
  rw [Cond.kore, KoreAML.tr, KoreAML.interp_sTop AtT.defOK_std srtOf_free_stdI, inhOf_srtOf_stdI h hS]
  exact ⟨fun _ => rfl, fun _ => ha⟩

theorem holdsT_bot : HoldsT c T .bot := by
  intro vars P σ b tbl e S _ _ _ _ _ _ hh a ha
  cases hh
  rw [Cond.kore, KoreAML.tr]
  unfold KoreAML.sBot
  rw [KoreAML.interp_sNot, KoreAML.interp_sTop AtT.defOK_std srtOf_free_stdI]
  exact ⟨fun hn => absurd hn.2 hn.1, fun hf => by cases hf⟩

theorem holdsT_not (h : HypModelCore c) {p : Cond} (ih : HoldsT c T p) : HoldsT c T (.not p) := by
  intro vars P σ b tbl e S hok hbd hP hr hk hS hh a ha
  rw [Semantics.condOK] at hok
  rw [Cond.bound] at hbd
  cases hh with
  | not hp =>
    rename_i b'
    have hk' : ∀ k ∈ KoreAML.varsOf (Cond.kore c (canonVars c vars) (srtOf c S) p), k ∈ tbl := fun k hk0 =>
      hk k (by rw [Cond.kore, KoreAML.varsOf]; exact List.mem_append_right _ hk0)
    have := ih hok hbd (fun i hi hl => hP i (by rw [varOccsCond]; exact hi) hl) hr hk' hS hp a ha
    rw [Cond.kore, KoreAML.tr, KoreAML.interp_sNot, this, inhOf_srtOf_stdI h hS]
    cases b' <;> simp [ha]

theorem holdsT_and {p q : Cond} (ihp : HoldsT c T p) (ihq : HoldsT c T q) : HoldsT c T (.and p q) := by
  intro vars P σ b tbl e S hok hbd hP hr hk hS hh a ha
  rw [Semantics.condOK, Bool.and_eq_true] at hok
  rw [Cond.bound, Bool.and_eq_true] at hbd
  cases hh with
  | and hp hq =>
    rename_i b1 b2
    have hkp : ∀ k ∈ KoreAML.varsOf (Cond.kore c (canonVars c vars) (srtOf c S) p), k ∈ tbl := fun k hk0 =>
      hk k (by rw [Cond.kore, KoreAML.varsOf, KoreAML.varsOfList]
               exact List.mem_append_right _ (List.mem_append_left _ hk0))
    have hkq : ∀ k ∈ KoreAML.varsOf (Cond.kore c (canonVars c vars) (srtOf c S) q), k ∈ tbl := fun k hk0 =>
      hk k (by rw [Cond.kore, KoreAML.varsOf, KoreAML.varsOfList, KoreAML.varsOfList]
               exact List.mem_append_right _ (List.mem_append_right _ (List.mem_append_left _ hk0)))
    have h1 := ihp hok.1 hbd.1 (fun i hi hl => hP i (by rw [varOccsCond]; exact List.mem_append_left _ hi) hl)
      hr hkp hS hp a ha
    have h2 := ihq hok.2 hbd.2 (fun i hi hl => hP i (by rw [varOccsCond]; exact List.mem_append_right _ hi) hl)
      hr hkq hS hq a ha
    rw [Cond.kore, tr_and2, KoreAML.interp_sAnd, h1, h2]
    cases b1 <;> cases b2 <;> simp

theorem tr_or2Stdi {ctx : KoreAML.Ctx} (s : Kore.KSort) (p q : Kore.Pattern) : KoreAML.tr ctx (.or s [p, q]) =
    KoreAML.sOr (KoreAML.trSort ctx.vars s) (KoreAML.tr ctx p) (KoreAML.tr ctx q) := by
  rw [KoreAML.tr]; simp only [KoreAML.trOrList]

theorem holdsT_or (h : HypModelCore c) {p q : Cond} (ihp : HoldsT c T p) (ihq : HoldsT c T q) :
    HoldsT c T (.or p q) := by
  intro vars P σ b tbl e S hok hbd hP hr hk hS hh a ha
  rw [Semantics.condOK, Bool.and_eq_true] at hok
  rw [Cond.bound, Bool.and_eq_true] at hbd
  cases hh with
  | or hp hq =>
    rename_i b1 b2
    have hkp : ∀ k ∈ KoreAML.varsOf (Cond.kore c (canonVars c vars) (srtOf c S) p), k ∈ tbl := fun k hk0 =>
      hk k (by rw [Cond.kore, KoreAML.varsOf, KoreAML.varsOfList]
               exact List.mem_append_right _ (List.mem_append_left _ hk0))
    have hkq : ∀ k ∈ KoreAML.varsOf (Cond.kore c (canonVars c vars) (srtOf c S) q), k ∈ tbl := fun k hk0 =>
      hk k (by rw [Cond.kore, KoreAML.varsOf, KoreAML.varsOfList, KoreAML.varsOfList]
               exact List.mem_append_right _ (List.mem_append_right _ (List.mem_append_left _ hk0)))
    have h1 := ihp hok.1 hbd.1 (fun i hi hl => hP i (by rw [varOccsCond]; exact List.mem_append_left _ hi) hl)
      hr hkp hS hp a ha
    have h2 := ihq hok.2 hbd.2 (fun i hi hl => hP i (by rw [varOccsCond]; exact List.mem_append_right _ hi) hl)
      hr hkq hS hq a ha
    rw [Cond.kore, tr_or2Stdi, KoreAML.interp_sOr, h1, h2, inhOf_srtOf_stdI h hS]
    cases b1 <;> cases b2 <;> simp [ha]

theorem holdsT_implies (h : HypModelCore c) {p q : Cond} (ihp : HoldsT c T p) (ihq : HoldsT c T q) :
    HoldsT c T (.implies p q) := by
  intro vars P σ b tbl e S hok hbd hP hr hk hS hh a ha
  rw [Semantics.condOK, Bool.and_eq_true] at hok
  rw [Cond.bound, Bool.and_eq_true] at hbd
  cases hh with
  | implies hp hq =>
    rename_i b1 b2
    have hkp : ∀ k ∈ KoreAML.varsOf (Cond.kore c (canonVars c vars) (srtOf c S) p), k ∈ tbl := fun k hk0 =>
      hk k (by rw [Cond.kore, KoreAML.varsOf]
               exact List.mem_append_left _ (List.mem_append_right _ hk0))
    have hkq : ∀ k ∈ KoreAML.varsOf (Cond.kore c (canonVars c vars) (srtOf c S) q), k ∈ tbl := fun k hk0 =>
      hk k (by rw [Cond.kore, KoreAML.varsOf]; exact List.mem_append_right _ hk0)
    have h1 := ihp hok.1 hbd.1 (fun i hi hl => hP i (by rw [varOccsCond]; exact List.mem_append_left _ hi) hl)
      hr hkp hS hp a ha
    have h2 := ihq hok.2 hbd.2 (fun i hi hl => hP i (by rw [varOccsCond]; exact List.mem_append_right _ hi) hl)
      hr hkq hS hq a ha
    rw [Cond.kore, KoreAML.tr, KoreAML.interp_sImp, h1, h2, inhOf_srtOf_stdI h hS]
    cases b1 <;> cases b2 <;> simp [ha]

/-! ### The atoms -/

/-- A term of a condition, read: its sort is numbered, it denotes the values `EvalTerm` gives it,
and those are of its sort. -/
theorem term_readStdI (h : HypModelCore c) {vars : List Srt} {P : Nat → Prop} {σ : Subst}
    {tbl : KoreAML.VarTable} {e : Valuation Elem} (hr : ReadsT c vars P σ tbl e) {t : Term} {s : Srt}
    (ht : sortOfTerm (c.rhsCtx (c.fns.map Fn.sig)) vars t = some s) (hP : ∀ i ∈ varOccs t, P i) :
    s < nRegSorts + c.sortNames.length ∧
      (∀ m, (KoreAML.tr ⟨tbl, []⟩ (Term.kore c (canonVars c vars) t)).interpret (stdI_T c T) e m ↔
        ∃ v, EvalTerm c σ t (some v) ∧ m = .val v) ∧
      ∀ v, EvalTerm c σ t (some v) → c.sortOf v = some s := by
  obtain ⟨hok, hsr, -, -, -, -, -, -, hno⟩ := h.sound
  haveI : OvlOK c := hno
  have hsc := sortCtx_of_allCl hok hsr (OvlOK.ovlCase hno)
  refine ⟨sortOfTerm_numStdI h (fun k hk => rhsHead_kernel fns_headsOK hk) (fun _ _ h' => h') rfl t ht
      fun i hi s' hs' => ?_,
    AtT.tr_term h hr.hvar ((termOK_of_sorted h fns_headsOK ht).monoOpen hP),
    fun v hv => EvalTerm.sorted_at hsc hv fns_headsOK (hr.sortedAt hP) ht rfl⟩
  obtain ⟨-, -, v, -, hsv, -⟩ := hr i (hP i hi)
  have : vars.getD i 0 = s' := by rw [List.getD_eq_getElem?_getD, hs']; rfl
  rw [this] at hsv
  exact sortOf_numbered h hsv

theorem holdsT_ceil (h : HypModelCore c) (s : Srt) (t : Term) : HoldsT c T (.ceil s t) := by
  intro vars P σ b tbl e S hok _ hP hr _ hS hh a ha
  rw [Semantics.condOK, beq_iff_eq] at hok
  have hPt : ∀ i ∈ varOccs t, P i := fun i hi => hP i (by rw [varOccsCond]; exact hi) (varOccs_lt t hok i hi)
  obtain ⟨hs, hread, hsort⟩ := term_readStdI (T := T) h hr hok hPt
  cases hh with
  | ceil hev =>
    rename_i r
    rw [Cond.kore, KoreAML.tr, KoreAML.interp_sCeil AtT.defOK_std AtT.sat_ceilDef (srtOf_den_stdI h hs e)
      (srtOf_den_stdI h hS e) (isSort_stdI hs) (isSort_stdI hS) (fun m hm => by
        obtain ⟨v, hv, rfl⟩ := (hread m).mp hm
        exact (AtT.inh_srt _ _).mpr (hsort v hv)), AtT.inh_srt]
    simp only [hread]
    constructor
    · rintro ⟨⟨m, v, hv, -⟩, -⟩
      cases EvalTerm.functional_of_fnDet h.det hev hv
      rfl
    · intro hb
      obtain ⟨v, rfl⟩ := Option.isSome_iff_exists.mp hb
      exact ⟨⟨_, v, hev, rfl⟩, ha⟩

theorem holdsT_equals (h : HypModelCore c) (s : Srt) (t u : Term) : HoldsT c T (.equals s t u) := by
  intro vars P σ b tbl e S hok _ hP hr _ hS hh a ha
  rw [Semantics.condOK, Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at hok
  have hPt : ∀ i ∈ varOccs t, P i := fun i hi =>
    hP i (by rw [varOccsCond]; exact List.mem_append_left _ hi) (varOccs_lt t hok.1 i hi)
  have hPu : ∀ i ∈ varOccs u, P i := fun i hi =>
    hP i (by rw [varOccsCond]; exact List.mem_append_right _ hi) (varOccs_lt u hok.2 i hi)
  obtain ⟨hs, hreadt, hsortt⟩ := term_readStdI (T := T) h hr hok.1 hPt
  obtain ⟨-, hreadu, hsortu⟩ := term_readStdI (T := T) h hr hok.2 hPu
  cases hh with
  | equals hev hev' =>
    rename_i r r'
    rw [Cond.kore, KoreAML.tr, KoreAML.interp_sEquals AtT.defOK_std AtT.sat_ceilDef (srtOf_den_stdI h hs e)
      (srtOf_den_stdI h hS e) (isSort_stdI hs) (isSort_stdI hS), AtT.inh_srt]
    simp only [AtT.inh_srt, hreadt, hreadu]
    have hfn := fun {w : Term} {q q' : Option GroundTerm} (h1 : EvalTerm c σ w q) (h2 : EvalTerm c σ w q') =>
      EvalTerm.functional_of_fnDet h.det h1 h2
    cases r with
    | none =>
      cases r' with
      | none =>
        simp only [sameResult]
        exact ⟨fun _ => trivial, fun _ => ⟨ha, fun m _ =>
          ⟨fun ⟨v, hv, _⟩ => (by cases hfn hev hv), fun ⟨v, hv, _⟩ => (by cases hfn hev' hv)⟩⟩⟩
      | some w =>
        simp only [sameResult]
        refine ⟨fun ⟨_, hall⟩ => ?_, fun hf => by cases hf⟩
        obtain ⟨v, hv, -⟩ := (hall (.val w) (hsortu w hev')).mpr ⟨w, hev', rfl⟩
        cases hfn hev hv
    | some v =>
      cases r' with
      | none =>
        simp only [sameResult]
        refine ⟨fun ⟨_, hall⟩ => ?_, fun hf => by cases hf⟩
        obtain ⟨w, hw, -⟩ := (hall (.val v) (hsortt v hev)).mp ⟨v, hev, rfl⟩
        cases hfn hev' hw
      | some w =>
        simp only [sameResult, beq_iff_eq, cmp_eq_iff]
        constructor
        · rintro ⟨-, hall⟩
          obtain ⟨w', hw', he⟩ := (hall (.val v) (hsortt v hev)).mp ⟨v, hev, rfl⟩
          cases hfn hev' hw'
          cases he
          rfl
        · rintro rfl
          refine ⟨ha, fun m _ => ⟨fun ⟨v', hv', hm⟩ => ⟨v', ?_, hm⟩, fun ⟨v', hv', hm⟩ => ⟨v', ?_, hm⟩⟩⟩
          · cases hfn hev hv'; exact hev'
          · cases hfn hev' hv'; exact hev

theorem holdsT_mem (h : HypModelCore c) (s : Srt) (t u : Term) : HoldsT c T (.mem s t u) := by
  intro vars P σ b tbl e S hok _ hP hr _ hS hh a ha
  rw [Semantics.condOK, Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at hok
  have hPt : ∀ i ∈ varOccs t, P i := fun i hi =>
    hP i (by rw [varOccsCond]; exact List.mem_append_left _ hi) (varOccs_lt t hok.1 i hi)
  have hPu : ∀ i ∈ varOccs u, P i := fun i hi =>
    hP i (by rw [varOccsCond]; exact List.mem_append_right _ hi) (varOccs_lt u hok.2 i hi)
  obtain ⟨hs, hreadt, hsortt⟩ := term_readStdI (T := T) h hr hok.1 hPt
  obtain ⟨-, hreadu, -⟩ := term_readStdI (T := T) h hr hok.2 hPu
  cases hh with
  | mem hev hev' =>
    rename_i r r'
    rw [Cond.kore, KoreAML.tr, KoreAML.interp_sIn AtT.defOK_std AtT.sat_ceilDef (srtOf_den_stdI h hs e)
      (srtOf_den_stdI h hS e) (isSort_stdI hs) (isSort_stdI hS) (fun m hm => by
        obtain ⟨v, hv, rfl⟩ := (hreadt m).mp hm
        exact (AtT.inh_srt _ _).mpr (hsortt v hv)), AtT.inh_srt]
    simp only [hreadt, hreadu]
    have hfn := fun {w : Term} {q q' : Option GroundTerm} (h1 : EvalTerm c σ w q) (h2 : EvalTerm c σ w q') =>
      EvalTerm.functional_of_fnDet h.det h1 h2
    constructor
    · rintro ⟨⟨m, ⟨v, hv, rfl⟩, ⟨w, hw, hvw⟩⟩, -⟩
      cases hvw
      cases hfn hev hv
      cases hfn hev' hw
      simp [sameResult, cmp_eq_iff]
    · intro hb
      cases r with
      | none => simp at hb
      | some v =>
        cases r' with
        | none => simp [sameResult] at hb
        | some w =>
          simp only [Option.isSome_some, sameResult, Bool.true_and, beq_iff_eq, cmp_eq_iff] at hb
          subst hb
          exact ⟨⟨.val v, ⟨v, hev, rfl⟩, ⟨v, hev', rfl⟩⟩, ha⟩

/-! ### The quantifiers over a sort -/

/-- σ with the value v at the index n. -/
def extOneStdI (σ : Subst) (n : Nat) (v : GroundTerm) : Subst := (n, v) :: σ

theorem extOneStdI_at (σ : Subst) (n : Nat) (v : GroundTerm) : (extOneStdI σ n v).lookup n = some v := by
  simp [extOneStdI]

theorem extOneStdI_off (σ : Subst) {n i : Nat} (v : GroundTerm) (hi : i ≠ n) :
    (extOneStdI σ n v).lookup i = σ.lookup i := by
  have hb : (i == n) = false := by simp [hi]
  simp [extOneStdI, List.lookup, hb]

/-- The canonical key of a variable in scope is its key under one more binder. -/
theorem canonKey_appendStdI {vars ys : List Srt} {i : Nat} (hi : i < vars.length) :
    canonKey c (vars ++ ys) i = canonKey c vars i := by
  unfold canonKey
  rw [← canonVars_appendStdI c vars ys, getD_appendL_stdI _ _ _ (by rwa [canonVars_length])]

/-- The key of the binder of `ex` or `all`. -/
theorem binder_keyStdI (vars : List Srt) (s : Srt) :
    KoreAML.evarKey (Cond.binder c (canonVars c vars).length s).kore = canonKey c (vars ++ [s]) vars.length := by
  unfold canonKey
  rw [← canonVars_snocStdI c vars s, getD_appendR_stdI _ _ _ (Nat.le_of_eq (canonVars_length c vars)),
    canonVars_length, Nat.sub_self]
  rfl

/-- The reading under one more binder, at a value of its sort. -/
theorem ReadsT.snocStdI {vars : List Srt} {P : Nat → Prop} {σ σ' : Subst} {tbl : KoreAML.VarTable}
    {e : Valuation Elem} (hr : ReadsT c vars P σ tbl e) {s : Srt} {v : GroundTerm}
    (hk : canonKey c (vars ++ [s]) vars.length ∈ tbl) (hσ' : ∀ i < vars.length, σ'.lookup i = σ.lookup i)
    (hn : σ'.lookup vars.length = some v) (hv : c.sortOf v = some s) :
    ReadsT c (vars ++ [s]) (fun i => P i ∨ i = vars.length) σ' tbl
      ⟨Function.update e.evalEvar (tbl.ev (canonKey c (vars ++ [s]) vars.length)) (.val v), e.evalSvar⟩ := by
  intro i hi
  rcases hi with hi | rfl
  · obtain ⟨hl, hki, w, hw, hsw, hew⟩ := hr i hi
    have hk' := canonKey_appendStdI (c := c) (ys := [s]) hl
    refine ⟨by simp; omega, hk' ▸ hki, w, (hσ' i hl).trans hw, by rw [getD_appendL_stdI _ _ _ hl]; exact hsw, ?_⟩
    show Function.update e.evalEvar _ _ _ = _
    rw [Function.update_noteq, hk', hew]
    intro he
    have := canonKey_inj (vars := vars ++ [s]) (c := c) (by simp; omega) (by simp)
      (ev_inj (hk'.symm ▸ hki) hk he)
    omega
  · refine ⟨by simp, hk, v, hn, by simpa using hv, ?_⟩
    show Function.update e.evalEvar _ _ _ = _
    rw [Function.update_same]

theorem holdsT_ex (h : HypModelCore c) (s : Srt) {body : Cond} (ih : HoldsT c T body) : HoldsT c T (.ex s body) := by
  intro vars P σ b tbl e S hok hbd hP hr hk hS hh a ha
  rw [Semantics.condOK] at hok
  rw [Cond.bound, Bool.and_eq_true] at hbd
  have hlen : (vars ++ [s]).length = vars.length + 1 := by simp
  have hsn : s < nRegSorts + c.sortNames.length := confined_numberedStdI h hbd.1
  let K := canonKey c (vars ++ [s]) vars.length
  have hkb : KoreAML.evarKey (Cond.binder c (canonVars c vars).length s).kore = K := binder_keyStdI vars s
  have hkore : Cond.kore c (canonVars c vars) (srtOf c S) (.ex s body) =
      .exist (srtOf c S) (Cond.binder c (canonVars c vars).length s).kore
        (Cond.kore c (canonVars c (vars ++ [s])) (srtOf c S) body) := by
    rw [← canonVars_snocStdI c vars s]; rfl
  rw [hkore] at hk ⊢
  have hK : K ∈ tbl := hk _ (by rw [KoreAML.varsOf, hkb]; simp)
  have hkB : ∀ k ∈ KoreAML.varsOf (Cond.kore c (canonVars c (vars ++ [s])) (srtOf c S) body), k ∈ tbl :=
    fun k hk0 => hk k (by rw [KoreAML.varsOf]; exact List.mem_append_right _ hk0)
  have hPB : ∀ i ∈ varOccsCond (vars ++ [s]).length body, i < (vars ++ [s]).length → P i ∨ i = vars.length := by
    intro i hi hl
    rw [hlen] at hi hl
    by_cases hlt : i < vars.length
    · exact .inl (hP i (by rw [varOccsCond]; exact List.mem_filter.mpr ⟨hi, by simpa using hlt⟩) hlt)
    · exact .inr (by omega)
  -- the body at an extension of σ by a value of the binder's sort
  have hread : ∀ σ' v, (∀ i < vars.length, σ'.lookup i = σ.lookup i) → σ'.lookup vars.length = some v →
      c.sortOf v = some s → ∀ b', Holds c (vars.length + 1) σ' body b' →
      ((KoreAML.tr ⟨tbl, []⟩ (Cond.kore c (canonVars c (vars ++ [s])) (srtOf c S) body)).interpret (stdI_T c T)
        ⟨Function.update e.evalEvar (tbl.ev K) (.val v), e.evalSvar⟩ a ↔ b' = true) := by
    intro σ' v hσ' hn hv b' hb'
    exact ih hok (by rw [hlen]; exact hbd.2) hPB (hr.snocStdI hK hσ' hn hv) hkB hS
      (by rw [hlen]; exact hb') a ha
  have hsrt : ∀ m, (KoreAML.inhOf (KoreAML.trSort tbl (Cond.binder c (canonVars c vars).length s).kore.sort)).interpret
      (stdI_T c T) ⟨Function.update e.evalEvar (tbl.ev K) m, e.evalSvar⟩ m ↔ InSort c s m := fun m => by
    show (KoreAML.inhOf (KoreAML.trSort tbl (KoreAML.srt (c.sortName s)))).interpret _ _ m ↔ _
    rw [trSort_srt]
    exact AtT.inhOf_sort h.namesK hsn _ m
  cases hh with
  | ex g hb hr' =>
    rw [KoreAML.tr, KoreAML.interp_sExists, hkb]
    simp only [KoreAML.interp_member AtT.defOK_std, Function.update_same, hsrt]
    constructor
    · rintro ⟨m, hm, hbody⟩
      obtain ⟨v, rfl, hv⟩ := inSort_val hm
      have hσ'' : ∀ i < vars.length, (extOneStdI σ vars.length v).lookup i = σ.lookup i :=
        fun i hi => extOneStdI_off σ v (by omega)
      have hext : Extends c vars.length [s] σ (extOneStdI σ vars.length v) :=
        ⟨hσ'', fun j s' hj => by
          cases j with
          | zero => simp at hj; subst hj; exact ⟨v, extOneStdI_at σ _ v, hv⟩
          | succ j => simp at hj⟩
      exact hr'.mpr ⟨_, hext, (hread _ v hσ'' (extOneStdI_at σ _ v) hv _ (hb _ hext)).mp hbody⟩
    · intro hbt
      obtain ⟨σ', hext, hg⟩ := hr'.mp hbt
      obtain ⟨v, hv, hsv⟩ := hext.2 0 s rfl
      rw [Nat.add_zero] at hv
      exact ⟨.val v, hsv, (hread σ' v hext.1 hv hsv _ (hb σ' hext)).mpr hg⟩

theorem holdsT_all (h : HypModelCore c) (s : Srt) {body : Cond} (ih : HoldsT c T body) : HoldsT c T (.all s body) := by
  intro vars P σ b tbl e S hok hbd hP hr hk hS hh a ha
  rw [Semantics.condOK] at hok
  rw [Cond.bound, Bool.and_eq_true] at hbd
  have hlen : (vars ++ [s]).length = vars.length + 1 := by simp
  have hsn : s < nRegSorts + c.sortNames.length := confined_numberedStdI h hbd.1
  let K := canonKey c (vars ++ [s]) vars.length
  have hkb : KoreAML.evarKey (Cond.binder c (canonVars c vars).length s).kore = K := binder_keyStdI vars s
  have hkore : Cond.kore c (canonVars c vars) (srtOf c S) (.all s body) =
      .forall (srtOf c S) (Cond.binder c (canonVars c vars).length s).kore
        (Cond.kore c (canonVars c (vars ++ [s])) (srtOf c S) body) := by
    rw [← canonVars_snocStdI c vars s]; rfl
  rw [hkore] at hk ⊢
  have hK : K ∈ tbl := hk _ (by rw [KoreAML.varsOf, hkb]; simp)
  have hkB : ∀ k ∈ KoreAML.varsOf (Cond.kore c (canonVars c (vars ++ [s])) (srtOf c S) body), k ∈ tbl :=
    fun k hk0 => hk k (by rw [KoreAML.varsOf]; exact List.mem_append_right _ hk0)
  have hPB : ∀ i ∈ varOccsCond (vars ++ [s]).length body, i < (vars ++ [s]).length → P i ∨ i = vars.length := by
    intro i hi hl
    rw [hlen] at hi hl
    by_cases hlt : i < vars.length
    · exact .inl (hP i (by rw [varOccsCond]; exact List.mem_filter.mpr ⟨hi, by simpa using hlt⟩) hlt)
    · exact .inr (by omega)
  have hread : ∀ σ' v, (∀ i < vars.length, σ'.lookup i = σ.lookup i) → σ'.lookup vars.length = some v →
      c.sortOf v = some s → ∀ b', Holds c (vars.length + 1) σ' body b' →
      ((KoreAML.tr ⟨tbl, []⟩ (Cond.kore c (canonVars c (vars ++ [s])) (srtOf c S) body)).interpret (stdI_T c T)
        ⟨Function.update e.evalEvar (tbl.ev K) (.val v), e.evalSvar⟩ a ↔ b' = true) := by
    intro σ' v hσ' hn hv b' hb'
    exact ih hok (by rw [hlen]; exact hbd.2) hPB (hr.snocStdI hK hσ' hn hv) hkB hS
      (by rw [hlen]; exact hb') a ha
  have hsrt : ∀ m, (KoreAML.inhOf (KoreAML.trSort tbl (Cond.binder c (canonVars c vars).length s).kore.sort)).interpret
      (stdI_T c T) ⟨Function.update e.evalEvar (tbl.ev K) m, e.evalSvar⟩ m ↔ InSort c s m := fun m => by
    show (KoreAML.inhOf (KoreAML.trSort tbl (KoreAML.srt (c.sortName s)))).interpret _ _ m ↔ _
    rw [trSort_srt]
    exact AtT.inhOf_sort h.namesK hsn _ m
  have hinS : ∀ e' : Valuation Elem, (KoreAML.inhOf (KoreAML.trSort tbl (srtOf c S))).interpret (stdI_T c T) e' a :=
    fun e' => (inhOf_srtOf_stdI h hS e' a).mpr ha
  cases hh with
  | all g hb hr' =>
    rw [KoreAML.tr]
    unfold KoreAML.sForall
    rw [KoreAML.interp_sNot, KoreAML.interp_sExists, hkb]
    simp only [KoreAML.interp_member AtT.defOK_std, Function.update_same, hsrt,
      KoreAML.interp_sNot, hinS, and_true, not_exists, not_and, Classical.not_not]
    constructor
    · intro hall
      refine hr'.mpr fun σ' hext => ?_
      obtain ⟨v, hv, hsv⟩ := hext.2 0 s rfl
      rw [Nat.add_zero] at hv
      exact (hread σ' v hext.1 hv hsv _ (hb σ' hext)).mp (hall (.val v) hsv)
    · intro hbt m hm
      obtain ⟨v, rfl, hv⟩ := inSort_val hm
      have hσ'' : ∀ i < vars.length, (extOneStdI σ vars.length v).lookup i = σ.lookup i :=
        fun i hi => extOneStdI_off σ v (by omega)
      have hext : Extends c vars.length [s] σ (extOneStdI σ vars.length v) :=
        ⟨hσ'', fun j s' hj => by
          cases j with
          | zero => simp at hj; subst hj; exact ⟨v, extOneStdI_at σ _ v, hv⟩
          | succ j => simp at hj⟩
      exact (hread _ v hσ'' (extOneStdI_at σ _ v) hv _ (hb _ hext)).mpr (hr'.mp hbt _ hext)

/-! ### A match under binders -/

mutual
  /-- The variables a term holds under constructors are among its variables. -/
  theorem ctorOccs_varOccsStdI : ∀ (t : Term), ∀ i ∈ ctorOccs c t, i ∈ varOccs t
    | .var j, i, hi => by simpa [ctorOccs, varOccs] using hi
    | .app f ts, i, hi => by
      rw [ctorOccs] at hi
      rw [varOccs]
      split at hi
      · exact ctorOccsList_varOccsStdI ts i hi
      · cases hi
    | .inj _ _ t, i, hi => by
      rw [ctorOccs] at hi
      rw [varOccs]
      exact ctorOccs_varOccsStdI t i hi
    | .as t j, i, hi => by
      rw [ctorOccs] at hi
      rw [varOccs]
      rcases List.mem_append.mp hi with hi | hi
      · exact List.mem_append_left _ (ctorOccs_varOccsStdI t i hi)
      · exact List.mem_append_right _ hi
    | .dv _ _, i, hi => by rw [ctorOccs] at hi; cases hi
  theorem ctorOccsList_varOccsStdI : ∀ (ts : List Term), ∀ i ∈ ctorOccsList c ts, i ∈ varOccsList ts
    | [], i, hi => by rw [ctorOccsList] at hi; cases hi
    | t :: ts, i, hi => by
      rw [ctorOccsList] at hi
      rw [varOccsList]
      rcases List.mem_append.mp hi with hi | hi
      · exact List.mem_append_left _ (ctorOccs_varOccsStdI t i hi)
      · exact List.mem_append_right _ (ctorOccsList_varOccsStdI ts i hi)
end

theorem lookup_append_noneStdI : ∀ (l l' : Subst) (i : Nat), l.lookup i = none → (l ++ l').lookup i = l'.lookup i
  | [], _, _, _ => rfl
  | (k, v) :: l, l', i, hl => by
    cases hik : i == k
    · simp only [List.lookup, hik, List.cons_append] at hl ⊢
      exact lookup_append_noneStdI l l' i hl
    · simp [List.lookup, hik] at hl

theorem lookup_append_someStdI : ∀ (l l' : Subst) (i : Nat) (v : GroundTerm), l.lookup i = some v →
    (l ++ l').lookup i = some v
  | [], _, _, _, hl => by cases hl
  | (k, w) :: l, l', i, v, hl => by
    cases hik : i == k
    · simp only [List.lookup, hik, List.cons_append] at hl ⊢
      exact lookup_append_someStdI l l' i v hl
    · simp only [List.lookup, hik, List.cons_append] at hl ⊢
      exact hl

/-- The binders of a match: the canonical variables of the extended sorts past those in scope. -/
theorem binders_eqStdI (vars ys : List Srt) :
    (((List.range ys.length).zip ys).map (fun (j, y) => Cond.binder c ((canonVars c vars).length + j) y)).map
        KoreAML.Var.kore =
      (List.range' vars.length ys.length).map fun i => ((canonVars c (vars ++ ys)).getD i default).kore := by
  apply List.ext_getElem (by simp)
  intro j h1 h2
  have hj : j < ys.length := by simpa using h2
  simp only [List.getElem_map, List.getElem_zip, List.getElem_range, List.getElem_range', canonVars_length]
  rw [canonVars_getD c (by simp; omega), getD_appendR_stdI _ _ _ (by omega), getD_eq_getElemStdI _ _ (by omega)]
  simp only [Cond.binder, Nat.one_mul, Nat.add_sub_cancel_left]

theorem holdsT_exMatch (h : HypModelCore c) (ys : List Srt) (s : Srt) (p t : Term) {body : Cond}
    (ih : HoldsT c T body) : HoldsT c T (.exMatch ys s p t body) := by
  intro vars P σ b tbl e S hok hbd hP hr hk hS hh a ha
  simp only [Semantics.condOK, Bool.and_eq_true, beq_iff_eq] at hok
  obtain ⟨⟨hpS, htS⟩, hokB⟩ := hok
  rw [Cond.bound, Bool.and_eq_true] at hbd
  obtain ⟨hbnd, hbdB⟩ := hbd
  have hn := h.namesK
  have hlen : (vars ++ ys).length = vars.length + ys.length := by simp
  let Bs := (List.range' vars.length ys.length).map fun i => ((canonVars c (vars ++ ys)).getD i default).kore
  have hkore : Cond.kore c (canonVars c vars) (srtOf c S) (.exMatch ys s p t body) =
      KoreAML.existsAll (srtOf c S) Bs (.and (srtOf c S)
        [.in (srtOf c s) (srtOf c S) (Term.kore c (canonVars c vars) t) (Term.kore c (canonVars c (vars ++ ys)) p),
         Cond.kore c (canonVars c (vars ++ ys)) (srtOf c S) body]) := by
    simp only [Cond.kore]
    rw [canonVars_appendStdI, binders_eqStdI]
  rw [hkore] at hk ⊢
  have hBk : ∀ i, vars.length ≤ i → i < vars.length + ys.length → canonKey c (vars ++ ys) i ∈ tbl :=
    fun i h1 h2 => hk _ (varsOf_existsAll_binder Bs (List.mem_map_of_mem (List.mem_range'_1.mpr ⟨h1, by omega⟩)))
  have hkB : ∀ k ∈ KoreAML.varsOf (Cond.kore c (canonVars c (vars ++ ys)) (srtOf c S) body), k ∈ tbl :=
    fun k hk0 => hk k (Model.varsOf_existsAll_bodyEx
      (Model.varsOf_and_mem (List.mem_cons_of_mem _ (List.mem_cons_self ..)) hk0) _)
  have hPt : ∀ i ∈ varOccs t, P i := fun i hi =>
    hP i (by rw [varOccsCond]; exact List.mem_append_left _ hi) (varOccs_lt t htS i hi)
  obtain ⟨hs, -, hsortt⟩ := term_readStdI (T := T) h hr htS hPt
  -- the binders' sorts are numbered: held by the pattern under constructors, or confined
  have hnumB : ∀ i, vars.length ≤ i → i < vars.length + ys.length →
      (vars ++ ys).getD i 0 < nRegSorts + c.sortNames.length := by
    intro i h1 h2
    have hj := (List.all_eq_true.mp hbnd) (i - vars.length) (List.mem_range.mpr (by omega))
    have hg : (vars ++ ys).getD i 0 = ys.getD (i - vars.length) 0 := getD_appendR_stdI _ _ _ h1
    rw [Bool.or_eq_true] at hj
    rcases hj with hj | hj
    · have hi' : vars.length + (i - vars.length) ∈ varOccs p :=
        ctorOccs_varOccsStdI p _ (by simpa using hj)
      rw [show vars.length + (i - vars.length) = i by omega] at hi'
      exact varOccs_num h p hpS hs i hi' _
        (by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp; omega)]; rfl)
    · cases hy : ys[i - vars.length]? with
      | none => simp [hy] at hj
      | some y =>
        simp only [hy, Option.map_some, Option.getD_some] at hj
        rw [hg, List.getD_eq_getElem?_getD, hy, Option.getD_some]
        exact confined_numberedStdI h hj
  have hnd : (Bs.map fun b => tbl.ev (KoreAML.evarKey b)).Nodup := by
    rw [List.map_map]
    refine nodup_map_of_injOn _ (fun i hi j hj he => ?_) List.nodup_range'
    obtain ⟨hi1, hi2⟩ := List.mem_range'_1.mp hi
    obtain ⟨hj1, hj2⟩ := List.mem_range'_1.mp hj
    exact canonKey_inj (by simp; omega) (by simp; omega) (ev_inj (hBk i hi1 hi2) (hBk j hj1 hj2) he)
  have hsrt : ∀ b ∈ Bs, ∃ n, b.sort = KoreAML.srt n := fun b hb => by
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
    obtain ⟨-, hi2⟩ := List.mem_range'_1.mp hi
    show ∃ n, ((canonVars c (vars ++ ys)).getD i default).kore.sort = KoreAML.srt n
    rw [canonVars_getD c (by simp; omega)]; exact ⟨_, rfl⟩
  -- a variable in scope is no binder
  have hne : ∀ i, P i → ∀ j, vars.length ≤ j → j < vars.length + ys.length →
      tbl.ev (canonKey c vars i) ≠ tbl.ev (canonKey c (vars ++ ys) j) := by
    intro i hi j h1 h2 he
    obtain ⟨hl, hki, -⟩ := hr i hi
    rw [← canonKey_appendStdI (ys := ys) hl] at he hki
    have := canonKey_inj (by simp; omega) (by simp; omega) (ev_inj hki (hBk j h1 h2) he)
    omega
  have hPp : ∀ i ∈ varOccs p, P i ∨ (vars.length ≤ i ∧ i < vars.length + ys.length) := by
    intro i hi
    have hl := varOccs_lt p hpS i hi
    rw [hlen] at hl
    by_cases hlt : i < vars.length
    · refine .inl (hP i ?_ hlt)
      rw [varOccsCond]
      exact List.mem_append_right _ (List.mem_filter.mpr ⟨List.mem_append_left _ hi, by simpa using hlt⟩)
    · exact .inr ⟨by omega, hl⟩
  have hPB : ∀ i ∈ varOccsCond (vars ++ ys).length body, i < (vars ++ ys).length →
      P i ∨ (vars.length ≤ i ∧ i < vars.length + ys.length) := by
    intro i hi hl
    rw [hlen] at hi hl
    by_cases hlt : i < vars.length
    · refine .inl (hP i ?_ hlt)
      rw [varOccsCond]
      exact List.mem_append_right _ (List.mem_filter.mpr ⟨List.mem_append_right _ hi, by simpa using hlt⟩)
    · exact .inr ⟨by omega, hl⟩
  -- the body of the match at a valuation that reads the binders as σ' does
  have hread : ∀ (e' : Valuation Elem) (σ' : Subst),
      (∀ i, P i → e'.evalEvar (tbl.ev (canonKey c vars i)) = e.evalEvar (tbl.ev (canonKey c vars i))) →
      ReadsT c (vars ++ ys) (fun i => P i ∨ (vars.length ≤ i ∧ i < vars.length + ys.length)) σ' tbl e' →
      ((KoreAML.tr ⟨tbl, []⟩ (.and (srtOf c S)
        [.in (srtOf c s) (srtOf c S) (Term.kore c (canonVars c vars) t) (Term.kore c (canonVars c (vars ++ ys)) p),
         Cond.kore c (canonVars c (vars ++ ys)) (srtOf c S) body])).interpret (stdI_T c T) e' a ↔
        (∃ v, EvalTerm c σ t (some v) ∧ PatVal c σ' p v) ∧
          (KoreAML.tr ⟨tbl, []⟩ (Cond.kore c (canonVars c (vars ++ ys)) (srtOf c S) body)).interpret (stdI_T c T) e' a) := by
    intro e' σ' hoff hr'
    have hrt : ReadsT c vars P σ tbl e' := fun i hi => by
      obtain ⟨a1, a2, v, a3, a4, a5⟩ := hr i hi
      exact ⟨a1, a2, v, a3, a4, (hoff i hi).trans a5⟩
    obtain ⟨-, hreadt, -⟩ := term_readStdI (T := T) h hrt htS hPt
    have hreadp := AtT.tr_pat (T := T) h hr'.hvar ((patOK_of_sorted h hpS).monoOpen hPp)
    rw [tr_and2, KoreAML.interp_sAnd, KoreAML.tr, KoreAML.interp_sIn AtT.defOK_std AtT.sat_ceilDef
      (srtOf_den_stdI h hs e') (srtOf_den_stdI h hS e') (isSort_stdI hs) (isSort_stdI hS) (fun m hm => by
        obtain ⟨v, hv, rfl⟩ := (hreadt m).mp hm
        exact (AtT.inh_srt _ _).mpr (hsortt v hv)), AtT.inh_srt]
    simp only [hreadt, hreadp]
    constructor
    · rintro ⟨⟨⟨m, ⟨v, hv, rfl⟩, ⟨w, hw, hvw⟩⟩, -⟩, hb⟩
      cases hvw
      exact ⟨⟨v, hv, hw⟩, hb⟩
    · rintro ⟨⟨v, hv, hw⟩, hb⟩
      exact ⟨⟨⟨.val v, ⟨v, hv, rfl⟩, ⟨v, hw, rfl⟩⟩, ha⟩, hb⟩
  -- the body by the lemma for it
  have hbody : ∀ (e' : Valuation Elem) (σ' : Subst) (b' : Bool),
      ReadsT c (vars ++ ys) (fun i => P i ∨ (vars.length ≤ i ∧ i < vars.length + ys.length)) σ' tbl e' →
      Holds c (vars.length + ys.length) σ' body b' →
      ((KoreAML.tr ⟨tbl, []⟩ (Cond.kore c (canonVars c (vars ++ ys)) (srtOf c S) body)).interpret (stdI_T c T) e' a ↔
        b' = true) := fun e' σ' b' hr' hb' =>
    ih hokB (by rw [hlen]; exact hbdB) hPB hr' hkB hS (by rw [hlen]; exact hb') a ha
  -- an element of the match gives an extension of σ on the binders where it holds
  have hfwd : (KoreAML.tr ⟨tbl, []⟩ (KoreAML.existsAll (srtOf c S) Bs (.and (srtOf c S)
        [.in (srtOf c s) (srtOf c S) (Term.kore c (canonVars c vars) t) (Term.kore c (canonVars c (vars ++ ys)) p),
         Cond.kore c (canonVars c (vars ++ ys)) (srtOf c S) body]))).interpret (stdI_T c T) e a →
      ∃ σ' v, Extends c vars.length ys σ σ' ∧ EvalTerm c σ t (some v) ∧ PatVal c σ' p v ∧
        ∀ b', Holds c (vars.length + ys.length) σ' body b' → b' = true := by
    intro hm
    obtain ⟨e', hoff, hguard, hb⟩ := existsAll_elim AtT.defOK_std Bs e a hnd hsrt hm
    have hoffP : ∀ i, P i → e'.evalEvar (tbl.ev (canonKey c vars i)) = e.evalEvar (tbl.ev (canonKey c vars i)) :=
      fun i hi => hoff _ fun b hb' he => by
        obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hb'
        obtain ⟨hj1, hj2⟩ := List.mem_range'_1.mp hj
        exact hne i hi j hj1 hj2 he
    have hval : ∀ i, vars.length ≤ i → i < vars.length + ys.length → ∃ w,
        e'.evalEvar (tbl.ev (canonKey c (vars ++ ys) i)) = .val w ∧ c.sortOf w = some ((vars ++ ys).getD i 0) := by
      intro i h1 h2
      have hb' : ((canonVars c (vars ++ ys)).getD i default).kore ∈ Bs :=
        List.mem_map_of_mem (List.mem_range'_1.mpr ⟨h1, h2⟩)
      have := hguard _ hb' _ (by rw [canonVars_getD c (by simp; omega)]; rfl)
      exact inSort_val ((AtT.inhOf_sort (T := T) hn (hnumB i h1 h2) KoreAML.val0 _).mp this)
    let σE : Subst := ((List.range' vars.length ys.length).map fun i =>
      (i, toVal (e'.evalEvar (tbl.ev (canonKey c (vars ++ ys) i))))) ++ σ
    have hlo : ∀ i < vars.length, σE.lookup i = σ.lookup i := fun i hi =>
      lookup_append_noneStdI _ _ _ (by rw [lookup_range', if_neg (by omega)])
    have hhi : ∀ i, vars.length ≤ i → i < vars.length + ys.length →
        σE.lookup i = some (toVal (e'.evalEvar (tbl.ev (canonKey c (vars ++ ys) i)))) := fun i h1 h2 =>
      lookup_append_someStdI _ _ _ _ (by rw [lookup_range', if_pos ⟨h1, h2⟩])
    have hrE : ReadsT c (vars ++ ys) (fun i => P i ∨ (vars.length ≤ i ∧ i < vars.length + ys.length)) σE tbl e' := by
      intro i hi
      rcases hi with hi | ⟨h1, h2⟩
      · obtain ⟨hl, hki, v, hv, hsv, hev⟩ := hr i hi
        have hk' := canonKey_appendStdI (c := c) (ys := ys) hl
        refine ⟨by simp; omega, hk' ▸ hki, v, (hlo i hl).trans hv, by rw [getD_appendL_stdI _ _ _ hl]; exact hsv, ?_⟩
        rw [hk', hoffP i hi, hev]
      · obtain ⟨w, hw, hsw⟩ := hval i h1 h2
        exact ⟨by simp; omega, hBk i h1 h2, w, by rw [hhi i h1 h2, hw]; rfl, hsw, hw⟩
    have hext : Extends c vars.length ys σ σE := ⟨hlo, fun j s' hj => by
      have hjl : j < ys.length := (List.getElem?_eq_some_iff.mp hj).1
      obtain ⟨w, hw, hsw⟩ := hval (vars.length + j) (by omega) (by omega)
      refine ⟨w, by rw [hhi _ (by omega) (by omega), hw]; rfl, ?_⟩
      rw [hsw, getD_appendR_stdI _ _ _ (by omega), Nat.add_sub_cancel_left, List.getD_eq_getElem?_getD, hj]
      rfl⟩
    obtain ⟨⟨v, hv, hpv⟩, hbd⟩ := (hread e' σE hoffP hrE).mp hb
    exact ⟨σE, v, hext, hv, hpv, fun b' hb' => (hbody e' σE b' hrE hb').mp hbd⟩
  -- an extension of σ on the binders where the match holds gives an element of it
  have hbwd : ∀ σ' v b', Extends c vars.length ys σ σ' → EvalTerm c σ t (some v) → PatVal c σ' p v →
      Holds c (vars.length + ys.length) σ' body b' → b' = true →
      (KoreAML.tr ⟨tbl, []⟩ (KoreAML.existsAll (srtOf c S) Bs (.and (srtOf c S)
        [.in (srtOf c s) (srtOf c S) (Term.kore c (canonVars c vars) t) (Term.kore c (canonVars c (vars ++ ys)) p),
         Cond.kore c (canonVars c (vars ++ ys)) (srtOf c S) body]))).interpret (stdI_T c T) e a := by
    intro σ' v b' hext hv hpv hb' hbt
    let is := List.range' vars.length ys.length
    have hkis : ∀ i < (vars ++ ys).length, i ∈ is → canonKey c (vars ++ ys) i ∈ tbl := fun i _ his => by
      obtain ⟨h1, h2⟩ := List.mem_range'_1.mp his
      exact hBk i h1 h2
    let f : Nat → Elem := fun i => .val ((σ'.lookup i).getD default)
    let e' := setV c tbl (vars ++ ys) is f e
    have hval : ∀ i, vars.length ≤ i → i < vars.length + ys.length → ∃ w,
        σ'.lookup i = some w ∧ c.sortOf w = some ((vars ++ ys).getD i 0) := by
      intro i h1 h2
      obtain ⟨w, hw, hsw⟩ := hext.2 (i - vars.length) (ys.getD (i - vars.length) 0)
        (by rw [List.getElem?_eq_getElem (by omega), List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem (by omega)]; rfl)
      rw [show vars.length + (i - vars.length) = i by omega] at hw
      exact ⟨w, hw, by rw [hsw, getD_appendR_stdI _ _ _ h1]⟩
    have hoffP : ∀ i, P i → e'.evalEvar (tbl.ev (canonKey c vars i)) = e.evalEvar (tbl.ev (canonKey c vars i)) := by
      intro i hi
      obtain ⟨hl, -⟩ := hr i hi
      rw [← canonKey_appendStdI (ys := ys) hl]
      exact setV_off hkis (by simp; omega) (fun his => by have := (List.mem_range'_1.mp his).1; omega)
    have hr'' : ReadsT c (vars ++ ys) (fun i => P i ∨ (vars.length ≤ i ∧ i < vars.length + ys.length)) σ' tbl e' := by
      intro i hi
      rcases hi with hi | ⟨h1, h2⟩
      · obtain ⟨hl, hki, w, hw, hsw, hew⟩ := hr i hi
        have hk' := canonKey_appendStdI (c := c) (ys := ys) hl
        refine ⟨by simp; omega, hk' ▸ hki, w, (hext.1 i hl).trans hw,
          by rw [getD_appendL_stdI _ _ _ hl]; exact hsw, ?_⟩
        rw [hk', hoffP i hi, hew]
      · obtain ⟨w, hw, hsw⟩ := hval i h1 h2
        refine ⟨by simp; omega, hBk i h1 h2, w, hw, hsw, ?_⟩
        rw [setV_on hkis (by simp; omega) (List.mem_range'_1.mpr ⟨h1, h2⟩)]
        simp [f, hw]
    refine AtT.existsAll_intro _ e e' a hnd hsrt (fun z hz => ?_) rfl (fun b hb k hk => ?_)
      ((hread e' σ' hoffP hr'').mpr ⟨⟨v, hv, hpv⟩, (hbody e' σ' b' hr'' hb').mpr hbt⟩)
    · show (if h : _ then _ else _) = _
      rw [dif_neg]
      rintro ⟨i, -, hix, rfl⟩
      exact hz _ (List.mem_map_of_mem hix) rfl
    · obtain ⟨i, hix, rfl⟩ := List.mem_map.mp hb
      obtain ⟨h1, h2⟩ := List.mem_range'_1.mp hix
      have hs' : ((canonVars c (vars ++ ys)).getD i default).kore.sort =
          KoreAML.srt (c.sortName ((vars ++ ys).getD i 0)) := by
        rw [canonVars_getD c (by simp; omega)]; rfl
      rw [hs'] at hk
      rw [← srt_inj hk]
      show InS (stdI_T c T) _ (e'.evalEvar (tbl.ev (canonKey c (vars ++ ys) i)))
      rw [setV_on hkis (by simp; omega) hix]
      obtain ⟨w, hw, hsw⟩ := hval i h1 h2
      show InS (stdI_T c T) _ (Elem.val ((σ'.lookup i).getD default))
      rw [hw, Option.getD_some]
      exact (AtT.inhOf_sort (T := T) hn (hnumB i h1 h2) KoreAML.val0 _).mpr hsw
  cases hh with
  | exNone hev =>
    refine ⟨fun hm => ?_, fun hf => by cases hf⟩
    obtain ⟨_, v, -, hv, -⟩ := hfwd hm
    cases EvalTerm.functional_of_fnDet h.det hev hv
  | exSome g hev hb hr' =>
    rename_i v
    constructor
    · intro hm
      obtain ⟨σ', v', hext, hv', hpv, hbt⟩ := hfwd hm
      cases EvalTerm.functional_of_fnDet h.det hev hv'
      exact hr'.mpr ⟨σ', hext, hpv, hbt _ (hb σ' hext hpv)⟩
    · intro hbt
      obtain ⟨σ', hext, hpv, hg⟩ := hr'.mp hbt
      exact hbwd σ' v _ hext hev hpv (hb σ' hext hpv) hg

/-! ### The lemma, by structural recursion -/

/-- **A condition in the value model at T**, by structural recursion on the condition. -/
theorem holds_atT (h : HypModelCore c) : ∀ p : Cond, HoldsT c T p
  | .top => holdsT_top h
  | .bot => holdsT_bot
  | .not p => holdsT_not h (holds_atT h p)
  | .and p q => holdsT_and (holds_atT h p) (holds_atT h q)
  | .or p q => holdsT_or h (holds_atT h p) (holds_atT h q)
  | .implies p q => holdsT_implies h (holds_atT h p) (holds_atT h q)
  | .ceil s t => holdsT_ceil h s t
  | .equals s t u => holdsT_equals h s t u
  | .mem s t u => holdsT_mem h s t u
  | .exMatch ys s p t body => holdsT_exMatch h ys s p t (holds_atT h body)
  | .ex s body => holdsT_ex h s (holds_atT h body)
  | .all s body => holdsT_all h s (holds_atT h body)

/-- A valuation that reads the variables P as their values under σ (`tr_term`'s form), with their
keys in the table and σ giving them values of their sorts, reads them so in `ReadsT`'s form. -/
theorem readsT_of_hvar {vars : List Srt} {P : Nat → Prop} {σ : Subst} {tbl : KoreAML.VarTable}
    {e : Valuation Elem} (hP : ∀ i, P i → i < vars.length ∧ canonKey c vars i ∈ tbl)
    (hσ : ∀ i, P i → ∃ v, σ.lookup i = some v ∧ c.sortOf v = some (vars.getD i 0))
    (hvar : ∀ i, P i → ∀ m, (KoreAML.tr ⟨tbl, []⟩ (KoreAML.varAt (canonVars c vars) i)).interpret (stdI_T c T) e m ↔
      ∃ v, σ.lookup i = some v ∧ m = .val v) :
    ReadsT c vars P σ tbl e := by
  intro i hi
  obtain ⟨v, hv, hsv⟩ := hσ i hi
  obtain ⟨v', hv', he⟩ := (hvar i hi (e.evalEvar (tbl.ev (canonKey c vars i)))).mp ((AtT.var_read (T := T) i _).mpr rfl)
  rw [hv] at hv'
  cases hv'
  exact ⟨(hP i hi).1, (hP i hi).2, v, hv, hsv, he⟩

end Model

open ML Model

/-- **A rule's condition in the value model at any transition T**: for a condition with `condOK` and
`Cond.bound` that has a truth value at σ, written over the canonical names of the variables in
scope, at a valuation that reads its free variables as their values under σ and whose table holds
the condition's variables, an element of a numbered predicate sort is in `Cond.kore p` exactly where
`Holds … p true`. Binders range over the values of their sorts, which are the elements of those
sorts in the value model. -/
theorem holds_stdI {c : Semantics} (h : HypModelCore c) (T : GroundTerm → GroundTerm → Prop) (p : Cond)
    {vars : List Srt} {P : Nat → Prop} {σ : Subst} {tbl : KoreAML.VarTable} {e : Valuation Elem} {S : Srt}
    (hok : c.condOK vars p = true) (hbd : Cond.bound c vars.length p = true)
    (hP : ∀ i ∈ varOccsCond vars.length p, i < vars.length → P i) (hr : ReadsT c vars P σ tbl e)
    (hk : ∀ k ∈ KoreAML.varsOf (Cond.kore c (canonVars c vars) (srtOf c S) p), k ∈ tbl)
    (hS : S < nRegSorts + c.sortNames.length) (hd : ∃ b, Holds c vars.length σ p b)
    (a : Elem) (ha : InSort c S a) :
    (KoreAML.tr ⟨tbl, []⟩ (Cond.kore c (canonVars c vars) (srtOf c S) p)).interpret (stdI_T c T) e a ↔
      Holds c vars.length σ p true := by
  obtain ⟨b, hb⟩ := hd
  rw [holds_atT (T := T) h p hok hbd hP hr hk hS hb a ha]
  constructor
  · rintro rfl; exact hb
  · intro ht
    exact (holds_atT (T := T) h p hok hbd hP hr hk hS hb a ha).mp
      ((holds_atT (T := T) h p hok hbd hP hr hk hS ht a ha).mpr rfl)


end Faithful

end KCore
