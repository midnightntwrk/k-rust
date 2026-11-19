/-
  KCore. A rule's conditions in the value model at a transition T.

  In `stdI_T c T` an element of a numbered sort is a value of that sort exactly (`InSort`), a term
  denotes the values `EvalTerm` gives it (`AtT.tr_term`), and a pattern the values it matches
  (`AtT.tr_pat`). So a condition, written over the canonical names of the variables in scope at a
  valuation that reads them as their values under σ, holds at an element of the predicate sort
  exactly where the truth value `Holds` gives it is `true` (`holds_atT`, the value model's instance of
  `HoldsShape.holds_denB`, from `atomFacts_stdI`, `binderFacts_stdI` and `boundReads_bound_stdI`); a binder ranges over the
  values of its sort, as `Extends` does: its sort is confined, or has a value and so is numbered
  (`boundReads_boundV_stdI`). `holds_stdI`: where the condition has a truth value, it
  holds exactly where that value is `true`.
-/
import KcoreSpec.ExModelT
import KcoreSpec.HoldsFacts

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

/-- **A well-sorted term's sort is numbered** where its variables' sorts are, in a context whose
heads are kernel symbols and whose subsorts are the definition's. -/
theorem sortOfTerm_numStdI (h : HypModelCore c) {x : TermCtx} (hx : ∀ k ∈ x.heads, k ∈ kernelSyms c)
    (hsub : ∀ a b, (a, b) ∈ x.subs → (a, b) ∈ c.subsorts) (hlib : x.lib = c.lib) {vars : List Srt} :
    ∀ (t : Term) {s : Srt}, sortOfTerm x vars t = some s →
      (∀ i ∈ varOccs t, ∀ s', vars[i]? = some s' → s' < nRegSorts + c.sortNames.length) →
      s < nRegSorts + c.sortNames.length :=
  HoldsShape.sortOfTerm_numbered (fun hv => sortOf_numbered h hv) h.sorts h.ovlOK hx hsub hlib

/-- **A confined sort is numbered**: Bool, or a sort of constructor terms. -/
theorem confinedAt_numberedStdI (h : HypModelCore c) :
    ∀ (k : Nat) {s : Srt}, c.confinedAt k s = true → s < nRegSorts + c.sortNames.length :=
  HoldsShape.confinedAt_numbered_ids h.ids

theorem confined_numberedStdI (h : HypModelCore c) {s : Srt} (hc : c.confined s = true) :
    s < nRegSorts + c.sortNames.length :=
  confinedAt_numberedStdI h _ hc

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

/-! ### The value model has the facts the Holds lemma reads -/

/-- A valuation that reads the variables P in `ReadsT`'s form reads them in `Reads`' form at the
value model: a value denotes itself. -/
theorem reads_of_readsT (h : HypModelCore c) {vars : List Srt} {P : Nat → Prop} {σ : Subst}
    {tbl : KoreAML.VarTable} {e : Valuation Elem} (hr : ReadsT c vars P σ tbl e) :
    HoldsShape.Reads c (stdI_T c T) vars P σ tbl e := by
  intro i hi
  obtain ⟨hl, hk, v, hv, hsv, he⟩ := hr i hi
  exact ⟨hl, hk, v, hv, hsv, fun m => by rw [den_val_T h T v hsv, he]⟩

/-- A valuation that reads the variables P in `Reads`' form at the value model reads them in
`ReadsT`'s form. -/
theorem readsT_of_reads (h : HypModelCore c) {vars : List Srt} {P : Nat → Prop} {σ : Subst}
    {tbl : KoreAML.VarTable} {e : Valuation Elem} (hr : HoldsShape.Reads c (stdI_T c T) vars P σ tbl e) :
    ReadsT c vars P σ tbl e := by
  intro i hi
  obtain ⟨hl, hk, v, hv, hsv, hd⟩ := hr i hi
  exact ⟨hl, hk, v, hv, hsv, (den_val_T h T v hsv e _).mp ((hd _).mp rfl)⟩

/-- **`HoldsT` is `HoldsDenB` at `Cond.bound` at the value model.** -/
theorem holdsT_of_den (h : HypModelCore c) {p : Cond} (hp : HoldsShape.HoldsDenB (Cond.bound c) c (stdI_T c T) p) :
    HoldsT c T p :=
  fun hok hbd hP hr hk hS hh a ha =>
    hp hok hbd hP (reads_of_readsT h hr) hk hS hh a ((inhOf_srtOf_stdI h hS _ a).mpr ha)

/-- `HoldsDenB` at `Cond.bound` at the value model is `HoldsT`. -/
theorem den_of_holdsT (h : HypModelCore c) {p : Cond} (hp : HoldsT c T p) :
    HoldsShape.HoldsDenB (Cond.bound c) c (stdI_T c T) p :=
  fun hok hbd hP hr hk hS hh a ha =>
    hp hok hbd hP (readsT_of_reads h hr) hk hS hh a ((inhOf_srtOf_stdI h hS _ a).mp ha)

/-- **The soundness of `EvalTerm` in the value model at T**, from `FnDet`: a term denotes the values
`EvalTerm` gives it (`AtT.tr_term`), and it has one result. -/
theorem termSoundAt_stdI (h : HypModelCore c) : HoldsShape.TermSoundAt c (stdI_T c T) := by
  intro σ t r he vars P tbl e s hP hr ht m
  obtain ⟨hok, hsr, -, -, -, -, -, -, hno⟩ := h.sound
  haveI : OvlOK c := hno
  have hsc := sortCtx_of_allClEx hok hsr (OvlOK.ovlCase hno)
  have hvar : ∀ i, P i → ∀ m, (KoreAML.tr ⟨tbl, []⟩ (KoreAML.varAt (canonVars c vars) i)).interpret (stdI_T c T) e m ↔
      ∃ v, σ.lookup i = some v ∧ m = .val v := by
    intro i hi m
    rw [AtT.var_read]
    obtain ⟨-, -, v, hv, hsv, hd⟩ := hr i hi
    show m = e.evalEvar (tbl.ev (canonKey c vars i)) ↔ _
    rw [hd m, den_val_T h T v hsv, hv]
    simp
  have hsat : c.WellSortedAt vars (varOccs t) σ := by
    intro i hi s' hs'
    obtain ⟨-, -, v, hv, hsv, -⟩ := hr i (hP i hi)
    refine ⟨v, hv, ?_⟩
    rw [hsv, List.getD_eq_getElem?_getD, hs']; rfl
  rw [AtT.tr_term h hvar ((termOK_of_sorted h fns_headsOK ht).monoOpen hP)]
  cases r with
  | none =>
    show _ ↔ False
    constructor
    · rintro ⟨v, hv, -⟩
      cases EvalTerm.functional_of_fnDet h.det he hv
    · exact False.elim
  | some w =>
    show _ ↔ (den c w).interpret (stdI_T c T) e m
    rw [den_val_T h T w (EvalTerm.sorted_at hsc he fns_headsOK hsat ht rfl)]
    constructor
    · rintro ⟨v, hv, rfl⟩
      cases EvalTerm.functional_of_fnDet h.det he hv
      rfl
    · rintro rfl
      exact ⟨w, he, rfl⟩

/-- **The value model at T has the atoms' facts**, from `HypModelCore`. -/
theorem atomFacts_stdI (h : HypModelCore c) : HoldsShape.AtomFacts c (stdI_T c T) := by
  obtain ⟨hok, hsr, -, -, -, -, -, -, hno⟩ := h.sound
  haveI : OvlOK c := hno
  refine ⟨AtT.defOK_std, AtT.sat_ceilDef, fun {s} hs => ⟨.srt s, isSort_stdI hs, fun tbl e a => srtOf_den_stdI h hs e a⟩,
    fun {v s} hv tbl e => ⟨.val v, den_val_T h T v hv e, (inhOf_srtOf_stdI h (sortOf_numbered h hv) e _).mpr hv⟩,
    fun {v w s} hv hw e a h1 h2 => ?_, termSoundAt_stdI h, sortCtx_of_allClEx hok hsr (OvlOK.ovlCase hno),
    fun {vars t s} ht hv => sortOfTerm_numStdI h (fun k hk => rhsHead_kernel fns_headsOK hk) (fun _ _ h' => h') rfl t ht hv,
    fun hv => sortOf_numbered h hv⟩
  have e1 := (den_val_T h T v hv e a).mp h1
  have e2 := (den_val_T h T w hw e a).mp h2
  rw [e1] at e2
  cases e2
  rfl

/-- **The value model at T reads a pattern at a value's element**: an element of a numbered sort is a
value, and the pattern denotes what `tr_pat` gives. -/
theorem patReading_stdI (h : HypModelCore c) : HoldsShape.PatReading c (stdI_T c T) := by
  intro vars p s w tbl e hpSN hw hin m hm
  have hpS := sortOfTerm_all_of_nf hpSN
  have hmw : m = .val w := (den_val_T h T w hw e m).mp hm
  subst hmw
  have hsn := sortOf_numbered h hw
  have hvx : ∀ i ∈ varOccs p, ∃ x, e.evalEvar (tbl.ev (canonKey c vars i)) = .val x ∧
      c.sortOf x = some (vars.getD i 0) := by
    intro i hi
    have hl := varOccs_lt p hpS i hi
    have hg : vars.getD i 0 = vars[i] := by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl]; rfl
    have hnum := varOccs_num h p hpS hsn i hi _ (List.getElem?_eq_getElem hl)
    rw [← hg] at hnum
    exact inSort_val ((inhOf_srtOf_stdI h hnum e _).mp (hin i hi).2)
  have hPO := (patOK_of_sorted h hpSN).monoOpen (Q := (· ∈ varOccs p)) fun i hi => hi
  constructor
  · intro hp
    let σ' : Subst := (varOccs p).map fun i => (i, toVal (e.evalEvar (tbl.ev (canonKey c vars i))))
    have hlk : ∀ i ∈ varOccs p, σ'.lookup i = some (toVal (e.evalEvar (tbl.ev (canonKey c vars i)))) :=
      fun i hi => HoldsShape.lookup_tab _ _ i hi
    have hrt : ReadsT c vars (· ∈ varOccs p) σ' tbl e := by
      intro i hi
      obtain ⟨x, hx, hsx⟩ := hvx i hi
      exact ⟨varOccs_lt p hpS i hi, (hin i hi).1, x, by rw [hlk i hi, hx]; rfl, hsx, hx⟩
    obtain ⟨v, hv, he⟩ := (AtT.tr_pat (T := T) h hrt.hvar hPO _).mp hp
    cases he
    refine ⟨σ', hv, fun i hi => ?_⟩
    obtain ⟨x, hx, hsx⟩ := hvx i hi
    exact ⟨x, by rw [hlk i hi, hx]; rfl, hsx, fun m' => by rw [den_val_T h T x hsx, hx]⟩
  · rintro ⟨σ', hv, hwit⟩
    have hrt : ReadsT c vars (· ∈ varOccs p) σ' tbl e := readsT_of_reads h fun i hi => by
      obtain ⟨u, hu, hsu, hdu⟩ := hwit i hi
      exact ⟨varOccs_lt p hpS i hi, (hin i hi).1, u, hu, hsu, fun m' => (hdu m').symm⟩
    exact (AtT.tr_pat (T := T) h hrt.hvar hPO _).mpr ⟨w, hv, rfl⟩

/-- The value model at T has the binders' facts: an element of any numbered sort is a value's, and
the reading of a pattern at a value's element. -/
theorem binderFacts_stdI (h : HypModelCore c) : HoldsShape.BinderFacts c (stdI_T c T) :=
  ⟨fun {s} hs tbl e a ha => by
    have hin := (inhOf_srtOf_stdI h (confined_numberedStdI h hs) e a).mp ha
    cases a with
    | val v => exact ⟨v, hin, den_val_T h T v hin e⟩
    | _ => exact hin.elim, fun hs => confined_numberedStdI h hs, patReading_stdI h⟩

/-! ### The connectives -/

theorem holdsT_top (h : HypModelCore c) : HoldsT c T .top :=
  holdsT_of_den h (HoldsShape.holds_top' (atomFacts_stdI h))

theorem holdsT_bot : HoldsT c T .bot := by
  intro vars P σ b tbl e S _ _ _ _ _ _ hh a ha
  cases hh
  rw [Cond.kore, KoreAML.tr]
  unfold KoreAML.sBot
  rw [KoreAML.interp_sNot, KoreAML.interp_sTop AtT.defOK_std srtOf_free_stdI]
  exact ⟨fun hn => absurd hn.2 hn.1, fun hf => by cases hf⟩

theorem holdsT_not (h : HypModelCore c) {p : Cond} (ih : HoldsT c T p) : HoldsT c T (.not p) :=
  holdsT_of_den h (HoldsShape.holds_notB (bd := Cond.bound c) (fun hb => by rw [Cond.bound] at hb; exact hb)
    (den_of_holdsT h ih))

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

theorem holdsT_or (h : HypModelCore c) {p q : Cond} (ihp : HoldsT c T p) (ihq : HoldsT c T q) :
    HoldsT c T (.or p q) :=
  holdsT_of_den h (HoldsShape.holds_orB (bd := Cond.bound c)
    (fun hb => by rw [Cond.bound, Bool.and_eq_true] at hb; exact hb) (den_of_holdsT h ihp) (den_of_holdsT h ihq))

theorem holdsT_implies (h : HypModelCore c) {p q : Cond} (ihp : HoldsT c T p) (ihq : HoldsT c T q) :
    HoldsT c T (.implies p q) :=
  holdsT_of_den h (HoldsShape.holds_impliesB (bd := Cond.bound c)
    (fun hb => by rw [Cond.bound, Bool.and_eq_true] at hb; exact hb) (den_of_holdsT h ihp) (den_of_holdsT h ihq))

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
  have hsc := sortCtx_of_allClEx hok hsr (OvlOK.ovlCase hno)
  refine ⟨sortOfTerm_numStdI h (fun k hk => rhsHead_kernel fns_headsOK hk) (fun _ _ h' => h') rfl t ht
      fun i hi s' hs' => ?_,
    AtT.tr_term h hr.hvar ((termOK_of_sorted h fns_headsOK ht).monoOpen hP),
    fun v hv => EvalTerm.sorted_at hsc hv fns_headsOK (hr.sortedAt hP) ht rfl⟩
  obtain ⟨-, -, v, -, hsv, -⟩ := hr i (hP i hi)
  have : vars.getD i 0 = s' := by rw [List.getD_eq_getElem?_getD, hs']; rfl
  rw [this] at hsv
  exact sortOf_numbered h hsv

theorem holdsT_ceil (h : HypModelCore c) (s : Srt) (t : Term) : HoldsT c T (.ceil s t) :=
  holdsT_of_den h (HoldsShape.holds_ceil' (atomFacts_stdI h) s t)

theorem holdsT_equals (h : HypModelCore c) (s : Srt) (t u : Term) : HoldsT c T (.equals s t u) :=
  holdsT_of_den h (HoldsShape.holds_equals' (atomFacts_stdI h) s t u)

theorem holdsT_mem (h : HypModelCore c) (s : Srt) (t u : Term) : HoldsT c T (.mem s t u) :=
  holdsT_of_den h (HoldsShape.holds_mem' (atomFacts_stdI h) s t u)

/-! ### The quantifiers over a sort -/

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

/-- In the value model at T, the elements of a numbered sort are values'. -/
theorem elemsValues_stdI (h : HypModelCore c) {s : Srt} (hs : s < nRegSorts + c.sortNames.length) :
    HoldsShape.ElemsValues c (stdI_T c T) s :=
  ⟨hs, fun tbl e a ha => by
    have hin := (inhOf_srtOf_stdI h hs e a).mp ha
    cases a with
    | val v => exact ⟨v, hin, den_val_T h T v hin e⟩
    | _ => exact hin.elim⟩

/-- **The value model at T reads `Cond.boundV c val`** where `val` admits numbered sorts only: at
an `ex` binder of a sort `val` admits, the elements of the sort are values' because the sort is
numbered. -/
theorem boundReads_boundV_stdI (h : HypModelCore c) {val : Srt → Bool}
    (hval : ∀ s, val s = true → s < nRegSorts + c.sortNames.length) :
    HoldsShape.BoundReads c (stdI_T c T) (Cond.boundV c val) where
  not := fun hb => by rw [Cond.boundV] at hb; exact hb
  and := fun hb => by rw [Cond.boundV, Bool.and_eq_true] at hb; exact hb
  or := fun hb => by rw [Cond.boundV, Bool.and_eq_true] at hb; exact hb
  implies := fun hb => by rw [Cond.boundV, Bool.and_eq_true] at hb; exact hb
  exMatch := fun hb => by rw [Cond.boundV, Bool.and_eq_true] at hb; exact hb
  ex := fun {n s body} hb => by
    rw [Cond.boundV, Bool.and_eq_true, Bool.or_eq_true, Bool.and_eq_true] at hb
    refine ⟨elemsValues_stdI h ?_, hb.2⟩
    rcases hb.1 with hc | ⟨hv, -⟩
    · exact confined_numberedStdI h hc
    · exact hval s hv
  all := fun hb => by
    rw [Cond.boundV, Bool.and_eq_true] at hb
    exact ⟨elemsValues_stdI h (confined_numberedStdI h hb.1), hb.2⟩

/-- **The value model at T reads `Cond.bound`**: at an `ex` or `all` binder the elements of the
sort are values', the sort being confined or of a value (`Semantics.valued_value`), hence numbered. -/
theorem boundReads_bound_stdI (h : HypModelCore c) : HoldsShape.BoundReads c (stdI_T c T) (Cond.bound c) := by
  rw [Cond.bound_eq_boundV]
  exact boundReads_boundV_stdI h fun _ hs =>
    let ⟨_, hv⟩ := Semantics.valued_value hs; sortOf_numbered h hv

theorem holdsT_ex (h : HypModelCore c) (s : Srt) {body : Cond} (ih : HoldsT c T body) : HoldsT c T (.ex s body) :=
  holdsT_of_den h (HoldsShape.holds_exB (atomFacts_stdI h) (bd := Cond.bound c) s (boundReads_bound_stdI h).ex
    (den_of_holdsT h ih))

theorem holdsT_all (h : HypModelCore c) (s : Srt) {body : Cond} (ih : HoldsT c T body) : HoldsT c T (.all s body) :=
  holdsT_of_den h (HoldsShape.holds_allB (atomFacts_stdI h) (bd := Cond.bound c) s
    (fun hb => by
      rw [Cond.bound, Bool.and_eq_true] at hb; exact ⟨(binderFacts_stdI h).elemsValues hb.1, hb.2⟩)
    (den_of_holdsT h ih))

/-! ### A match under binders -/

theorem holdsT_exMatch (h : HypModelCore c) (ys : List Srt) (s : Srt) (p t : Term) {body : Cond}
    (ih : HoldsT c T body) : HoldsT c T (.exMatch ys s p t body) :=
  holdsT_of_den h (HoldsShape.holds_exMatchB (atomFacts_stdI h) (binderFacts_stdI h) (bd := Cond.bound c)
    (fun hb => by rw [Cond.bound, Bool.and_eq_true] at hb; exact hb) ys s p t (den_of_holdsT h ih))

/-! ### The lemma: the value model's instance -/

/-- **A condition in the value model at T**: the Holds lemma for every interpretation with the facts,
at the value model. -/
theorem holds_atT (h : HypModelCore c) : ∀ p : Cond, HoldsT c T p :=
  fun p => holdsT_of_den h (HoldsShape.holds_denB (atomFacts_stdI h) (binderFacts_stdI h) (boundReads_bound_stdI h) p)

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
