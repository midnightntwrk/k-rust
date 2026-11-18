/-
  KCore. A rule's conditions in an interpretation, from what the interpretation gives.

  `HoldsDen' c I p` is the reading of a condition in I over the variables it reads: at a valuation
  that gives each read variable the element its value under σ denotes (`Reads`), an element of the
  predicate sort is in `Cond.kore p` exactly where the truth value `Holds` gives is `true`. Each case
  is proved once, for every I, from two structures of what it reads of I: `AtomFacts` (definedness,
  the sorts, the values and the soundness of `EvalTerm` over the read variables) and `BinderFacts`
  (an element of a confined sort is a value's, and a pattern read at a value's element, `PatReading`).
  The recursion `holds_den_of` takes the `exMatch` case as a premise (`ExMatchCase`), which
  `holds_exMatch'` proves from the facts, so `holds_den'` is the lemma for every interpretation with
  them. The value model at every T and every model of `Γc` of a `coreOK` definition have the facts.
-/
import KcoreSpec.OpenCompete

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace KCore

namespace Faithful

namespace Model

open ML

variable {c : Semantics}

/-! ## Sorts, canonical variables and substitutions under binders -/

theorem srtOf_free_stdI {tbl : KoreAML.VarTable} {s : Srt} :
    (KoreAML.trSort tbl (srtOf c s)).isFreeEvar KoreAML.topVar = false := by
  unfold srtOf; rw [trSort_srt]; rfl

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

theorem tr_or2Stdi {ctx : KoreAML.Ctx} (s : Kore.KSort) (p q : Kore.Pattern) : KoreAML.tr ctx (.or s [p, q]) =
    KoreAML.sOr (KoreAML.trSort ctx.vars s) (KoreAML.tr ctx p) (KoreAML.tr ctx q) := by
  rw [KoreAML.tr]; simp only [KoreAML.trOrList]

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

end Model

end Faithful

open ML Faithful

namespace HoldsShape

/-! ## The shape: one statement per interpretation, over the variables the condition reads -/

section Shape
variable {c : Semantics} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}

/-- The valuation reads the variables P as their values under σ, in the interpretation I: each is a
variable in scope, σ gives it a value of its sort, and the valuation the element that value denotes. -/
def Reads (c : Semantics) {M : Type} (I : Interpretation KoreAML.Sym M) (vars : List Srt) (P : Nat → Prop)
    (σ : Subst) (tbl : KoreAML.VarTable) (e : Valuation M) : Prop :=
  ∀ i, P i → i < vars.length ∧ canonKey c vars i ∈ tbl ∧
    ∃ v, σ.lookup i = some v ∧ c.sortOf v = some (vars.getD i 0) ∧
      ∀ m, m = e.evalEvar (tbl.ev (canonKey c vars i)) ↔ (den c v).interpret I e m

/-- The soundness of `EvalTerm` in I, over the variables the term reads. -/
def TermSoundAt (c : Semantics) {M : Type} (I : Interpretation KoreAML.Sym M) : Prop :=
  ∀ {σ : Subst} {t : Term} {r : Option GroundTerm}, EvalTerm c σ t r →
    ∀ {vars : List Srt} {P : Nat → Prop} {tbl : KoreAML.VarTable} {e : Valuation M} {s : Srt},
    (∀ i ∈ varOccs t, P i) → Reads c I vars P σ tbl e →
    sortOfTerm (c.rhsCtx (c.fns.map Fn.sig)) vars t = some s →
    ∀ m, (KoreAML.tr ⟨tbl, []⟩ (Term.kore c (canonVars c vars) t)).interpret I e m ↔ Res c I e r m

/-- The Holds lemma for p in I, over the variables p reads: `HoldsT`'s statement with I for the
value model, `Reads` for `ReadsT` and the predicate sort's elements for `InSort`. -/
def HoldsDen' (c : Semantics) {M : Type} (I : Interpretation KoreAML.Sym M) (p : Cond) : Prop :=
  ∀ {vars : List Srt} {P : Nat → Prop} {σ : Subst} {b : Bool} {tbl : KoreAML.VarTable} {e : Valuation M} {S : Srt},
    c.condOK vars p = true → Cond.bound c vars.length p = true →
    (∀ i ∈ varOccsCond vars.length p, i < vars.length → P i) → Reads c I vars P σ tbl e →
    (∀ k ∈ KoreAML.varsOf (Cond.kore c (canonVars c vars) (srtOf c S) p), k ∈ tbl) →
    S < nRegSorts + c.sortNames.length → Holds c vars.length σ p b →
    ∀ a, (KoreAML.inhOf (KoreAML.trSort tbl (srtOf c S))).interpret I e a →
      ((KoreAML.tr ⟨tbl, []⟩ (Cond.kore c (canonVars c vars) (srtOf c S) p)).interpret I e a ↔ b = true)

/-- `HoldsDen'` with the Bool that bounds the condition's binders a parameter: `HoldsDen' c I p` is
`HoldsDenB (Cond.bound c) c I p`. -/
def HoldsDenB (bd : Nat → Cond → Bool) (c : Semantics) {M : Type} (I : Interpretation KoreAML.Sym M) (p : Cond) : Prop :=
  ∀ {vars : List Srt} {P : Nat → Prop} {σ : Subst} {b : Bool} {tbl : KoreAML.VarTable} {e : Valuation M} {S : Srt},
    c.condOK vars p = true → bd vars.length p = true →
    (∀ i ∈ varOccsCond vars.length p, i < vars.length → P i) → Reads c I vars P σ tbl e →
    (∀ k ∈ KoreAML.varsOf (Cond.kore c (canonVars c vars) (srtOf c S) p), k ∈ tbl) →
    S < nRegSorts + c.sortNames.length → Holds c vars.length σ p b →
    ∀ a, (KoreAML.inhOf (KoreAML.trSort tbl (srtOf c S))).interpret I e a →
      ((KoreAML.tr ⟨tbl, []⟩ (Cond.kore c (canonVars c vars) (srtOf c S) p)).interpret I e a ↔ b = true)

/-- The sort s is numbered and each of its elements in I is a value's: what the Holds lemma reads
of the sort of an `ex` or `all` binder. -/
def ElemsValues (c : Semantics) {M : Type} (I : Interpretation KoreAML.Sym M) (s : Srt) : Prop :=
  s < nRegSorts + c.sortNames.length ∧
  ∀ (tbl : KoreAML.VarTable) (e : Valuation M) (a : M),
    (KoreAML.inhOf (KoreAML.trSort tbl (srtOf c s))).interpret I e a →
    ∃ v, c.sortOf v = some s ∧ ∀ m, (den c v).interpret I e m ↔ m = a

/-- The Holds lemma for p in I over every variable in scope: σ well sorted on all of them, at a
valuation that agrees with it. -/
def HoldsDenAll (c : Semantics) {M : Type} (I : Interpretation KoreAML.Sym M) (p : Cond) : Prop :=
  ∀ {vars : List Srt} {σ : Subst} {b : Bool} {tbl : KoreAML.VarTable} {e : Valuation M} {S : Srt},
    c.condOK vars p = true → Cond.bound c vars.length p = true → c.WellSorted vars σ →
    Holds c vars.length σ p b → Agrees c I tbl (canonVars c vars) σ e →
    (∀ k ∈ KoreAML.varsOf (Cond.kore c (canonVars c vars) (srtOf c S) p), k ∈ tbl) →
    S < nRegSorts + c.sortNames.length →
    ∀ a, (KoreAML.inhOf (KoreAML.trSort tbl (srtOf c S))).interpret I e a →
      ((KoreAML.tr ⟨tbl, []⟩ (Cond.kore c (canonVars c vars) (srtOf c S) p)).interpret I e a ↔ b = true)

omit [Inhabited M] in
/-- A σ well sorted on every variable, at a valuation that agrees with it, is read at the variables
whose keys the table holds. -/
theorem reads_of_agrees {vars : List Srt} {P : Nat → Prop} {σ : Subst} {tbl : KoreAML.VarTable} {e : Valuation M}
    (hσ : c.WellSorted vars σ) (hag : Agrees c I tbl (canonVars c vars) σ e)
    (hP : ∀ i, P i → i < vars.length ∧ canonKey c vars i ∈ tbl) : Reads c I vars P σ tbl e := by
  intro i hi
  obtain ⟨hl, hk⟩ := hP i hi
  obtain ⟨v, hv, hsv⟩ := hσ i vars[i] (List.getElem?_eq_getElem hl)
  refine ⟨hl, hk, v, hv, ?_, hag i v (by rw [canonVars_length]; exact hl) hv⟩
  rw [hsv, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl]; rfl

omit [Inhabited M] in
/-- **The all-variables form is the read form at the condition's free
variables**, their keys in the table. -/
theorem holdsDenAll_of {p : Cond} (hp : HoldsDen' c I p)
    {vars : List Srt} {σ : Subst} {b : Bool} {tbl : KoreAML.VarTable} {e : Valuation M} {S : Srt}
    (hok : c.condOK vars p = true) (hbd : Cond.bound c vars.length p = true) (hσ : c.WellSorted vars σ)
    (hh : Holds c vars.length σ p b) (hag : Agrees c I tbl (canonVars c vars) σ e)
    (hk : ∀ k ∈ KoreAML.varsOf (Cond.kore c (canonVars c vars) (srtOf c S) p), k ∈ tbl)
    (hkeys : ∀ i ∈ varOccsCond vars.length p, i < vars.length → canonKey c vars i ∈ tbl)
    (hS : S < nRegSorts + c.sortNames.length) (a : M)
    (ha : (KoreAML.inhOf (KoreAML.trSort tbl (srtOf c S))).interpret I e a) :
    ((KoreAML.tr ⟨tbl, []⟩ (Cond.kore c (canonVars c vars) (srtOf c S) p)).interpret I e a ↔ b = true) :=
  hp (P := fun i => i ∈ varOccsCond vars.length p ∧ i < vars.length) hok hbd (fun i hi hl => ⟨hi, hl⟩)
    (reads_of_agrees hσ hag fun i hi => ⟨hi.2, hkeys i hi.1 hi.2⟩) hk hS hh a ha

omit [Inhabited M] in
/-- The "true" half: where `Holds` gives `true`, every element of the predicate sort is in the
condition. -/
theorem holds_true {p : Cond} (hp : HoldsDen' c I p) {vars : List Srt} {P : Nat → Prop} {σ : Subst}
    {tbl : KoreAML.VarTable} {e : Valuation M} {S : Srt}
    (hok : c.condOK vars p = true) (hbd : Cond.bound c vars.length p = true)
    (hP : ∀ i ∈ varOccsCond vars.length p, i < vars.length → P i) (hr : Reads c I vars P σ tbl e)
    (hk : ∀ k ∈ KoreAML.varsOf (Cond.kore c (canonVars c vars) (srtOf c S) p), k ∈ tbl)
    (hS : S < nRegSorts + c.sortNames.length) (hh : Holds c vars.length σ p true) (a : M)
    (ha : (KoreAML.inhOf (KoreAML.trSort tbl (srtOf c S))).interpret I e a) :
    (KoreAML.tr ⟨tbl, []⟩ (Cond.kore c (canonVars c vars) (srtOf c S) p)).interpret I e a :=
  (hp hok hbd hP hr hk hS hh a ha).mpr rfl

omit [Inhabited M] in
/-- The "false" half: where `Holds` gives `false`, every element of the predicate sort is in the
condition's negation `\not{S}(p)`. -/
theorem holds_false {p : Cond} (hp : HoldsDen' c I p) {vars : List Srt} {P : Nat → Prop} {σ : Subst}
    {tbl : KoreAML.VarTable} {e : Valuation M} {S : Srt}
    (hok : c.condOK vars p = true) (hbd : Cond.bound c vars.length p = true)
    (hP : ∀ i ∈ varOccsCond vars.length p, i < vars.length → P i) (hr : Reads c I vars P σ tbl e)
    (hk : ∀ k ∈ KoreAML.varsOf (Cond.kore c (canonVars c vars) (srtOf c S) p), k ∈ tbl)
    (hS : S < nRegSorts + c.sortNames.length) (hh : Holds c vars.length σ p false) (a : M)
    (ha : (KoreAML.inhOf (KoreAML.trSort tbl (srtOf c S))).interpret I e a) :
    (KoreAML.tr ⟨tbl, []⟩ (.not (srtOf c S) (Cond.kore c (canonVars c vars) (srtOf c S) p))).interpret I e a := by
  rw [KoreAML.tr, KoreAML.interp_sNot]
  exact ⟨fun hin => Bool.noConfusion ((hp hok hbd hP hr hk hS hh a ha).mp hin), ha⟩

omit [Inhabited M] in
/-- **Where the predicate sort has an element, a condition has at most one truth value**: the one
place the hypothesis "the predicate sort has an element" is read. At an empty sort both halves hold
of a condition with both truth values. -/
theorem holds_unique {p : Cond} (hp : HoldsDen' c I p) {vars : List Srt} {P : Nat → Prop} {σ : Subst}
    {tbl : KoreAML.VarTable} {e : Valuation M} {S : Srt}
    (hok : c.condOK vars p = true) (hbd : Cond.bound c vars.length p = true)
    (hP : ∀ i ∈ varOccsCond vars.length p, i < vars.length → P i) (hr : Reads c I vars P σ tbl e)
    (hk : ∀ k ∈ KoreAML.varsOf (Cond.kore c (canonVars c vars) (srtOf c S) p), k ∈ tbl)
    (hS : S < nRegSorts + c.sortNames.length)
    (hne : ∃ a, (KoreAML.inhOf (KoreAML.trSort tbl (srtOf c S))).interpret I e a)
    (ht : Holds c vars.length σ p true) (hf : Holds c vars.length σ p false) : False := by
  obtain ⟨a, ha⟩ := hne
  exact Bool.noConfusion ((hp hok hbd hP hr hk hS hf a ha).mp ((hp hok hbd hP hr hk hS ht a ha).mpr rfl))

/-! ### What the cases read of the interpretation -/

/-- What the connectives and the atoms read of I. -/
structure AtomFacts (c : Semantics) {M : Type} (I : Interpretation KoreAML.Sym M) : Prop where
  defOK : KoreAML.DefOK I
  ceilDef : I ⊧ᴵ KoreAML.ceilDefItem.pat
  /-- a numbered sort denotes one element, a sort -/
  sort : ∀ {s : Srt}, s < nRegSorts + c.sortNames.length → ∃ τ, KoreAML.IsSort I τ ∧
    ∀ (tbl : KoreAML.VarTable) (e : Valuation M) (a : M), (KoreAML.trSort tbl (srtOf c s)).interpret I e a ↔ a = τ
  /-- a value denotes one element, of its sort -/
  val : ∀ {v : GroundTerm} {s : Srt}, c.sortOf v = some s → ∀ (tbl : KoreAML.VarTable) (e : Valuation M),
    ∃ a, (∀ m, (den c v).interpret I e m ↔ m = a) ∧ (KoreAML.inhOf (KoreAML.trSort tbl (srtOf c s))).interpret I e a
  /-- distinct values of a sort denote distinct elements -/
  apart : ∀ {v w : GroundTerm} {s : Srt}, c.sortOf v = some s → c.sortOf w = some s → ∀ (e : Valuation M) (a : M),
    (den c v).interpret I e a → (den c w).interpret I e a → v = w
  termSound : TermSoundAt c I
  sortCtx : SortCtx c
  /-- the sort of a term over variables of numbered sorts is numbered -/
  termNum : ∀ {vars : List Srt} {t : Term} {s : Srt}, sortOfTerm (c.rhsCtx (c.fns.map Fn.sig)) vars t = some s →
    (∀ i ∈ varOccs t, ∀ s', vars[i]? = some s' → s' < nRegSorts + c.sortNames.length) →
    s < nRegSorts + c.sortNames.length
  valNum : ∀ {v : GroundTerm} {s : Srt}, c.sortOf v = some s → s < nRegSorts + c.sortNames.length

theorem holds_top' (F : AtomFacts c I) : HoldsDen' c I .top := by
  intro vars P σ b tbl e S _ _ _ _ _ _ hh a ha
  cases hh
  rw [Cond.kore, KoreAML.tr, KoreAML.interp_sTop F.defOK Model.srtOf_free_stdI]
  exact ⟨fun _ => rfl, fun _ => ha⟩

theorem holds_bot' (F : AtomFacts c I) : HoldsDen' c I .bot := by
  intro vars P σ b tbl e S _ _ _ _ _ _ hh a ha
  cases hh
  rw [Cond.kore, KoreAML.tr]
  unfold KoreAML.sBot
  rw [KoreAML.interp_sNot, KoreAML.interp_sTop F.defOK Model.srtOf_free_stdI]
  exact ⟨fun hn => absurd ha hn.1, fun hf => by cases hf⟩

theorem holds_notB {bd : Nat → Cond → Bool} {p : Cond} (L : ∀ {n}, bd n (.not p) = true → bd n p = true)
    (ih : HoldsDenB bd c I p) : HoldsDenB bd c I (.not p) := by
  intro vars P σ b tbl e S hok hbd hP hr hk hS hh a ha
  rw [Semantics.condOK] at hok
  replace hbd := L hbd
  cases hh with
  | not hp =>
    rename_i b'
    have hk' : ∀ k ∈ KoreAML.varsOf (Cond.kore c (canonVars c vars) (srtOf c S) p), k ∈ tbl := fun k hk0 =>
      hk k (by rw [Cond.kore, KoreAML.varsOf]; exact List.mem_append_right _ hk0)
    have := ih hok hbd (fun i hi hl => hP i (by rw [varOccsCond]; exact hi) hl) hr hk' hS hp a ha
    rw [Cond.kore, KoreAML.tr, KoreAML.interp_sNot, this]
    cases b' <;> simp [ha]

theorem holds_not' {p : Cond} (ih : HoldsDen' c I p) : HoldsDen' c I (.not p) :=
  holds_notB (bd := Cond.bound c) (fun h => by rw [Cond.bound] at h; exact h) ih

theorem holds_andB {bd : Nat → Cond → Bool} {p q : Cond}
    (L : ∀ {n}, bd n (.and p q) = true → bd n p = true ∧ bd n q = true)
    (ihp : HoldsDenB bd c I p) (ihq : HoldsDenB bd c I q) : HoldsDenB bd c I (.and p q) := by
  intro vars P σ b tbl e S hok hbd hP hr hk hS hh a ha
  rw [Semantics.condOK, Bool.and_eq_true] at hok
  replace hbd := L hbd
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

theorem holds_and' {p q : Cond} (ihp : HoldsDen' c I p) (ihq : HoldsDen' c I q) : HoldsDen' c I (.and p q) :=
  holds_andB (bd := Cond.bound c) (fun h => by rw [Cond.bound, Bool.and_eq_true] at h; exact h) ihp ihq

theorem holds_orB {bd : Nat → Cond → Bool} {p q : Cond}
    (L : ∀ {n}, bd n (.or p q) = true → bd n p = true ∧ bd n q = true)
    (ihp : HoldsDenB bd c I p) (ihq : HoldsDenB bd c I q) : HoldsDenB bd c I (.or p q) := by
  intro vars P σ b tbl e S hok hbd hP hr hk hS hh a ha
  rw [Semantics.condOK, Bool.and_eq_true] at hok
  replace hbd := L hbd
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
    rw [Cond.kore, Model.tr_or2Stdi, KoreAML.interp_sOr, h1, h2]
    cases b1 <;> cases b2 <;> simp [ha]

theorem holds_or' {p q : Cond} (ihp : HoldsDen' c I p) (ihq : HoldsDen' c I q) : HoldsDen' c I (.or p q) :=
  holds_orB (bd := Cond.bound c) (fun h => by rw [Cond.bound, Bool.and_eq_true] at h; exact h) ihp ihq

theorem holds_impliesB {bd : Nat → Cond → Bool} {p q : Cond}
    (L : ∀ {n}, bd n (.implies p q) = true → bd n p = true ∧ bd n q = true)
    (ihp : HoldsDenB bd c I p) (ihq : HoldsDenB bd c I q) : HoldsDenB bd c I (.implies p q) := by
  intro vars P σ b tbl e S hok hbd hP hr hk hS hh a ha
  rw [Semantics.condOK, Bool.and_eq_true] at hok
  replace hbd := L hbd
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
    rw [Cond.kore, KoreAML.tr, KoreAML.interp_sImp, h1, h2]
    cases b1 <;> cases b2 <;> simp [ha]

theorem holds_implies' {p q : Cond} (ihp : HoldsDen' c I p) (ihq : HoldsDen' c I q) :
    HoldsDen' c I (.implies p q) :=
  holds_impliesB (bd := Cond.bound c) (fun h => by rw [Cond.bound, Bool.and_eq_true] at h; exact h) ihp ihq

/-- **`ceil`, once for every interpretation with the atoms' facts.** -/
theorem holds_ceil' (F : AtomFacts c I) (s : Srt) (t : Term) : HoldsDen' c I (.ceil s t) := by
  intro vars P σ b tbl e S hok _ hP hr _ hS hh a ha
  rw [Semantics.condOK] at hok; replace hok := ((Bool.and_eq_true _ _).mp hok).1; rw [beq_iff_eq] at hok
  have hPt : ∀ i ∈ varOccs t, P i := fun i hi => hP i (by rw [varOccsCond]; exact hi) (varOccs_lt t hok i hi)
  have hs : s < nRegSorts + c.sortNames.length := F.termNum hok fun i hi s' hs' => by
    obtain ⟨-, -, v, -, hsv, -⟩ := hr i (hPt i hi)
    have : vars.getD i 0 = s' := by rw [List.getD_eq_getElem?_getD, hs']; rfl
    rw [this] at hsv
    exact F.valNum hsv
  have hsat : c.WellSortedAt vars (varOccs t) σ := by
    intro i hi s' hs'
    obtain ⟨-, -, v, hv, hsv, -⟩ := hr i (hPt i hi)
    refine ⟨v, hv, ?_⟩
    rw [hsv, List.getD_eq_getElem?_getD, hs']; rfl
  obtain ⟨τ, hτ, hτd⟩ := F.sort hs
  obtain ⟨τS, hτS, hτSd⟩ := F.sort hS
  have haS : KoreAML.Inh I τS a := (KoreAML.interp_inhOf_of (hτSd tbl e)).mp ha
  cases hh with
  | ceil hev =>
    rename_i r
    have hread := F.termSound hev hPt hr hok
    rw [Cond.kore, KoreAML.tr, KoreAML.interp_sCeil F.defOK F.ceilDef (hτd tbl e) (hτSd tbl e) hτ hτS (fun m hm => by
      cases r with
      | none => exact ((hread m).mp hm).elim
      | some w =>
        obtain ⟨a0, ha0, hin⟩ := F.val (EvalTerm.sorted_at F.sortCtx hev fns_headsOK hsat hok rfl) tbl e
        rw [(ha0 m).mp ((hread m).mp hm)]
        exact (KoreAML.interp_inhOf_of (hτd tbl e)).mp hin)]
    simp only [hread]
    cases r with
    | none => exact ⟨fun ⟨⟨_, hf⟩, _⟩ => hf.elim, fun hf => by cases hf⟩
    | some w =>
      obtain ⟨a0, ha0, -⟩ := F.val (EvalTerm.sorted_at F.sortCtx hev fns_headsOK hsat hok rfl) tbl e
      exact ⟨fun _ => rfl, fun _ => ⟨⟨a0, (ha0 a0).mpr rfl⟩, haS⟩⟩

/-- A term of a condition, read: its sort is numbered and denotes one element, a sort; the term
denotes what each of its results denotes, and a result that is a value is of the term's sort. -/
theorem term_read (F : AtomFacts c I) {vars : List Srt} {P : Nat → Prop} {σ : Subst} {tbl : KoreAML.VarTable}
    {e : Valuation M} (hr : Reads c I vars P σ tbl e) {t : Term} {s : Srt}
    (ht : sortOfTerm (c.rhsCtx (c.fns.map Fn.sig)) vars t = some s) (hP : ∀ i ∈ varOccs t, P i) :
    s < nRegSorts + c.sortNames.length ∧
      ∀ r, EvalTerm c σ t r →
        (∀ m, (KoreAML.tr ⟨tbl, []⟩ (Term.kore c (canonVars c vars) t)).interpret I e m ↔ Res c I e r m) ∧
        ∀ w, r = some w → c.sortOf w = some s := by
  have hsat : c.WellSortedAt vars (varOccs t) σ := by
    intro i hi s' hs'
    obtain ⟨-, -, v, hv, hsv, -⟩ := hr i (hP i hi)
    refine ⟨v, hv, ?_⟩
    rw [hsv, List.getD_eq_getElem?_getD, hs']; rfl
  refine ⟨F.termNum ht fun i hi s' hs' => ?_, fun r hev => ⟨F.termSound hev hP hr ht,
    fun w hw => EvalTerm.sorted_at F.sortCtx hev fns_headsOK hsat ht hw⟩⟩
  obtain ⟨-, -, v, -, hsv, -⟩ := hr i (hP i hi)
  have : vars.getD i 0 = s' := by rw [List.getD_eq_getElem?_getD, hs']; rfl
  rw [this] at hsv
  exact F.valNum hsv

/-- **`equals`, once for every interpretation with the atoms' facts.** -/
theorem holds_equals' (F : AtomFacts c I) (s : Srt) (t u : Term) : HoldsDen' c I (.equals s t u) := by
  intro vars P σ b tbl e S hok _ hP hr _ hS hh a ha
  rw [Semantics.condOK] at hok; replace hok := ((Bool.and_eq_true _ _).mp hok).1; rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at hok
  have hPt : ∀ i ∈ varOccs t, P i := fun i hi =>
    hP i (by rw [varOccsCond]; exact List.mem_append_left _ hi) (varOccs_lt t hok.1 i hi)
  have hPu : ∀ i ∈ varOccs u, P i := fun i hi =>
    hP i (by rw [varOccsCond]; exact List.mem_append_right _ hi) (varOccs_lt u hok.2 i hi)
  obtain ⟨hs, hrt⟩ := term_read F hr hok.1 hPt
  obtain ⟨-, hru⟩ := term_read F hr hok.2 hPu
  obtain ⟨τ, hτ, hτd⟩ := F.sort hs
  obtain ⟨τS, hτS, hτSd⟩ := F.sort hS
  have haS : KoreAML.Inh I τS a := (KoreAML.interp_inhOf_of (hτSd tbl e)).mp ha
  have elt : ∀ {w : GroundTerm}, c.sortOf w = some s → ∃ a0, (∀ m, (den c w).interpret I e m ↔ m = a0) ∧
      KoreAML.Inh I τ a0 := fun hw => by
    obtain ⟨a0, ha0, hin⟩ := F.val hw tbl e
    exact ⟨a0, ha0, (KoreAML.interp_inhOf_of (hτd tbl e)).mp hin⟩
  cases hh with
  | equals hev hev' =>
    rename_i r r'
    obtain ⟨hreadt, hsortt⟩ := hrt r hev
    obtain ⟨hreadu, hsortu⟩ := hru r' hev'
    rw [Cond.kore, KoreAML.tr, KoreAML.interp_sEquals F.defOK F.ceilDef (hτd tbl e) (hτSd tbl e) hτ hτS]
    constructor
    · rintro ⟨-, hall⟩
      cases r with
      | none =>
        cases r' with
        | none => rfl
        | some w =>
          obtain ⟨a0, ha0, hin⟩ := elt (hsortu w rfl)
          exact ((hreadt a0).mp ((hall a0 hin).mpr ((hreadu a0).mpr ((ha0 a0).mpr rfl)))).elim
      | some v =>
        obtain ⟨a0, ha0, hin⟩ := elt (hsortt v rfl)
        have hu := (hreadu a0).mp ((hall a0 hin).mp ((hreadt a0).mpr ((ha0 a0).mpr rfl)))
        cases r' with
        | none => exact hu.elim
        | some w =>
          cases F.apart (hsortt v rfl) (hsortu w rfl) e a0 ((ha0 a0).mpr rfl) hu
          simp only [sameResult, beq_iff_eq, cmp_eq_iff]
    · intro hb
      refine ⟨haS, fun x _ => ?_⟩
      rw [hreadt x, hreadu x]
      cases r with
      | none =>
        cases r' with
        | none => exact Iff.rfl
        | some w => simp [sameResult] at hb
      | some v =>
        cases r' with
        | none => simp [sameResult] at hb
        | some w =>
          simp only [sameResult, beq_iff_eq, cmp_eq_iff] at hb
          subst hb
          exact Iff.rfl

/-- **`mem`, once for every interpretation with the atoms' facts.** -/
theorem holds_mem' (F : AtomFacts c I) (s : Srt) (t u : Term) : HoldsDen' c I (.mem s t u) := by
  intro vars P σ b tbl e S hok _ hP hr _ hS hh a ha
  rw [Semantics.condOK] at hok; replace hok := ((Bool.and_eq_true _ _).mp hok).1; rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at hok
  have hPt : ∀ i ∈ varOccs t, P i := fun i hi =>
    hP i (by rw [varOccsCond]; exact List.mem_append_left _ hi) (varOccs_lt t hok.1 i hi)
  have hPu : ∀ i ∈ varOccs u, P i := fun i hi =>
    hP i (by rw [varOccsCond]; exact List.mem_append_right _ hi) (varOccs_lt u hok.2 i hi)
  obtain ⟨hs, hrt⟩ := term_read F hr hok.1 hPt
  obtain ⟨-, hru⟩ := term_read F hr hok.2 hPu
  obtain ⟨τ, hτ, hτd⟩ := F.sort hs
  obtain ⟨τS, hτS, hτSd⟩ := F.sort hS
  have haS : KoreAML.Inh I τS a := (KoreAML.interp_inhOf_of (hτSd tbl e)).mp ha
  have elt : ∀ {w : GroundTerm}, c.sortOf w = some s → ∃ a0, (∀ m, (den c w).interpret I e m ↔ m = a0) ∧
      KoreAML.Inh I τ a0 := fun hw => by
    obtain ⟨a0, ha0, hin⟩ := F.val hw tbl e
    exact ⟨a0, ha0, (KoreAML.interp_inhOf_of (hτd tbl e)).mp hin⟩
  cases hh with
  | mem hev hev' =>
    rename_i r r'
    obtain ⟨hreadt, hsortt⟩ := hrt r hev
    obtain ⟨hreadu, hsortu⟩ := hru r' hev'
    rw [Cond.kore, KoreAML.tr, KoreAML.interp_sIn F.defOK F.ceilDef (hτd tbl e) (hτSd tbl e) hτ hτS (fun m hm => by
      cases r with
      | none => exact ((hreadt m).mp hm).elim
      | some w =>
        obtain ⟨a0, ha0, hin⟩ := elt (hsortt w rfl)
        rw [(ha0 m).mp ((hreadt m).mp hm)]; exact hin)]
    constructor
    · rintro ⟨⟨x, h1, h2⟩, -⟩
      have h1' := (hreadt x).mp h1
      have h2' := (hreadu x).mp h2
      cases r with
      | none => exact h1'.elim
      | some v =>
        cases r' with
        | none => exact h2'.elim
        | some w =>
          cases F.apart (hsortt v rfl) (hsortu w rfl) e x h1' h2'
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
          obtain ⟨a0, ha0, -⟩ := elt (hsortt v rfl)
          exact ⟨⟨a0, (hreadt a0).mpr ((ha0 a0).mpr rfl), (hreadu a0).mpr ((ha0 a0).mpr rfl)⟩, haS⟩

/-! ### The sort binders: `ex` and `all` -/

/-- The reading of a pattern at a value's element: for a pattern sorted over the context of
the patterns that apply no function-overloaded symbol (`patCtxNF`, as `condOK` sorts an `exMatch`'s),
at a valuation that gives each of its variables an element of the variable's sort (its key in the
table), the element of a value of the pattern's sort lies in the pattern's translation exactly where
the pattern denotes the value under a substitution that gives each of its variables a value of its
sort whose element the valuation gives it. -/
def PatReading (c : Semantics) {M : Type} (I : Interpretation KoreAML.Sym M) : Prop :=
  ∀ {vars : List Srt} {p : Term} {s : Srt} {w : GroundTerm} {tbl : KoreAML.VarTable} {e : Valuation M},
    sortOfTerm c.patCtxNF vars p = some s → c.sortOf w = some s →
    (∀ i ∈ varOccs p, canonKey c vars i ∈ tbl ∧
      (KoreAML.inhOf (KoreAML.trSort tbl (srtOf c (vars.getD i 0)))).interpret I e
        (e.evalEvar (tbl.ev (canonKey c vars i)))) →
    ∀ m, (den c w).interpret I e m →
      ((KoreAML.tr ⟨tbl, []⟩ (Term.kore c (canonVars c vars) p)).interpret I e m ↔
        ∃ σ', PatVal c σ' p w ∧ ∀ i ∈ varOccs p, ∃ v, σ'.lookup i = some v ∧ c.sortOf v = some (vars.getD i 0) ∧
          ∀ m', (den c v).interpret I e m' ↔ m' = e.evalEvar (tbl.ev (canonKey c vars i)))

/-- A variable of the body of `existsAll` is a variable of it. -/
theorem varsOf_existsAll_bodyHF {S : Kore.KSort} {body : Kore.Pattern} {k : KoreAML.VarKey}
    (hk : k ∈ KoreAML.varsOf body) : ∀ (bs : List Kore.EVar), k ∈ KoreAML.varsOf (KoreAML.existsAll S bs body)
  | [] => hk
  | b :: bs => by
    show k ∈ KoreAML.varsOf (.exist S b (KoreAML.existsAll S bs body))
    rw [KoreAML.varsOf]
    exact List.mem_append_right _ (varsOf_existsAll_bodyHF hk bs)

/-- The elements of a sort, through any table: `InS`. -/
theorem inhOf_srtOf_inS {tbl : KoreAML.VarTable} {e : Valuation M} {s : Srt} {a : M} :
    (KoreAML.inhOf (KoreAML.trSort tbl (srtOf c s))).interpret I e a ↔ InS I (c.sortName s) a := by
  unfold srtOf; rw [trSort_srt]; exact inS_iff e

/-- A read variable's element is in its sort. -/
theorem Reads.inSort (F : AtomFacts c I) {vars : List Srt} {P : Nat → Prop} {σ : Subst} {tbl : KoreAML.VarTable}
    {e : Valuation M} (hr : Reads c I vars P σ tbl e) {i : Nat} (hi : P i) :
    (KoreAML.inhOf (KoreAML.trSort tbl (srtOf c (vars.getD i 0)))).interpret I e
      (e.evalEvar (tbl.ev (canonKey c vars i))) := by
  obtain ⟨-, -, u, -, hsu, hd⟩ := hr i hi
  obtain ⟨a0, ha0, hin⟩ := F.val hsu tbl e
  rw [(ha0 _).mp ((hd _).mp rfl)]
  exact hin

/-- What the sort binders read of I beside the atoms' facts. -/
structure BinderFacts (c : Semantics) {M : Type} (I : Interpretation KoreAML.Sym M) : Prop where
  /-- an element of a confined sort is a value's -/
  confined : ∀ {s : Srt}, c.confined s = true → ∀ (tbl : KoreAML.VarTable) (e : Valuation M) (a : M),
    (KoreAML.inhOf (KoreAML.trSort tbl (srtOf c s))).interpret I e a →
    ∃ v, c.sortOf v = some s ∧ ∀ m, (den c v).interpret I e m ↔ m = a
  confinedNum : ∀ {s : Srt}, c.confined s = true → s < nRegSorts + c.sortNames.length
  /-- a pattern at a value's element: `PatReading` -/
  pat : PatReading c I

/-- The reading under one more binder, at a value of its sort and the element it denotes. -/
theorem Reads.snoc {vars : List Srt} {P : Nat → Prop} {σ σ' : Subst} {tbl : KoreAML.VarTable}
    {e : Valuation M} (hr : Reads c I vars P σ tbl e) {s : Srt} {v : GroundTerm} {a0 : M}
    (hk : canonKey c (vars ++ [s]) vars.length ∈ tbl) (hσ' : ∀ i < vars.length, σ'.lookup i = σ.lookup i)
    (hn : σ'.lookup vars.length = some v) (hv : c.sortOf v = some s)
    (hd : ∀ m, (den c v).interpret I e m ↔ m = a0) :
    Reads c I (vars ++ [s]) (fun i => P i ∨ i = vars.length) σ' tbl
      ⟨Function.update e.evalEvar (tbl.ev (canonKey c (vars ++ [s]) vars.length)) a0, e.evalSvar⟩ := by
  intro i hi
  rcases hi with hi | rfl
  · obtain ⟨hl, hki, w, hw, hsw, hew⟩ := hr i hi
    have hk' := Model.canonKey_appendStdI (c := c) (ys := [s]) hl
    refine ⟨by simp; omega, hk' ▸ hki, w, (hσ' i hl).trans hw,
      by rw [Model.getD_appendL_stdI _ _ _ hl]; exact hsw, fun m => ?_⟩
    show m = Function.update e.evalEvar _ _ _ ↔ _
    rw [Function.update_noteq, hk']
    · exact (hew m).trans ((den_closed c w).interp _ _ m)
    · intro he
      have := canonKey_inj (vars := vars ++ [s]) (c := c) (by simp; omega) (by simp)
        (ev_inj (hk'.symm ▸ hki) hk he)
      omega
  · refine ⟨by simp, hk, v, hn, by simpa using hv, fun m => ?_⟩
    show m = Function.update e.evalEvar _ _ _ ↔ _
    rw [Function.update_same]
    exact (((den_closed c v).interp _ e m).trans (hd m)).symm

/-- **`ex`, once for every interpretation with the atoms' facts**, where the Bool that bounds the
binders gives that the elements of the binder's sort are values' (`ElemsValues`) and bounds the
body. -/
theorem holds_exB (F : AtomFacts c I) {bd : Nat → Cond → Bool} (s : Srt) {body : Cond}
    (L : ∀ {n}, bd n (.ex s body) = true → ElemsValues c I s ∧ bd (n + 1) body = true)
    (ih : HoldsDenB bd c I body) : HoldsDenB bd c I (.ex s body) := by
  intro vars P σ b tbl e S hok hbd hP hr hk hS hh a ha
  rw [Semantics.condOK] at hok
  replace hbd := L hbd
  have hlen : (vars ++ [s]).length = vars.length + 1 := by simp
  have hsn : s < nRegSorts + c.sortNames.length := hbd.1.1
  obtain ⟨τ, hτ, hτd⟩ := F.sort hsn
  obtain ⟨τS, hτS, hτSd⟩ := F.sort hS
  let K := canonKey c (vars ++ [s]) vars.length
  have hkb : KoreAML.evarKey (Cond.binder c (canonVars c vars).length s).kore = K := Model.binder_keyStdI vars s
  have hkore : Cond.kore c (canonVars c vars) (srtOf c S) (.ex s body) =
      .exist (srtOf c S) (Cond.binder c (canonVars c vars).length s).kore
        (Cond.kore c (canonVars c (vars ++ [s])) (srtOf c S) body) := by
    rw [← Model.canonVars_snocStdI c vars s]; rfl
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
  have hread : ∀ σ' v a0, (∀ i < vars.length, σ'.lookup i = σ.lookup i) → σ'.lookup vars.length = some v →
      c.sortOf v = some s → (∀ m, (den c v).interpret I e m ↔ m = a0) → ∀ b', Holds c (vars.length + 1) σ' body b' →
      ((KoreAML.tr ⟨tbl, []⟩ (Cond.kore c (canonVars c (vars ++ [s])) (srtOf c S) body)).interpret I
        ⟨Function.update e.evalEvar (tbl.ev K) a0, e.evalSvar⟩ a ↔ b' = true) := by
    intro σ' v a0 hσ' hn hv hd b' hb'
    exact ih hok (by rw [hlen]; exact hbd.2) hPB (hr.snoc hK hσ' hn hv hd) hkB hS
      (by rw [hlen]; exact hb') a ((KoreAML.interp_inhOf_of (hτSd tbl _)).mpr
        ((KoreAML.interp_inhOf_of (hτSd tbl e)).mp ha))
  have hsrt : ∀ (e' : Valuation M) m,
      (KoreAML.inhOf (KoreAML.trSort tbl (Cond.binder c (canonVars c vars).length s).kore.sort)).interpret I e' m ↔
        KoreAML.Inh I τ m := fun e' m => by
    show (KoreAML.inhOf (KoreAML.trSort tbl (srtOf c s))).interpret _ _ m ↔ _
    exact KoreAML.interp_inhOf_of (hτd tbl e')
  cases hh with
  | ex g hb hr' =>
    rw [KoreAML.tr, KoreAML.interp_sExists, hkb]
    simp only [KoreAML.interp_member F.defOK, Function.update_same, hsrt]
    constructor
    · rintro ⟨m, hm, hbody⟩
      obtain ⟨v, hv, hdv⟩ := hbd.1.2 tbl e m ((KoreAML.interp_inhOf_of (hτd tbl e)).mpr hm)
      have hσ'' : ∀ i < vars.length, (Model.extOneStdI σ vars.length v).lookup i = σ.lookup i :=
        fun i hi => Model.extOneStdI_off σ v (by omega)
      have hext : Extends c vars.length [s] σ (Model.extOneStdI σ vars.length v) :=
        ⟨hσ'', fun j s' hj => by
          cases j with
          | zero => simp at hj; subst hj; exact ⟨v, Model.extOneStdI_at σ _ v, hv⟩
          | succ j => simp at hj⟩
      exact hr'.mpr ⟨_, hext, (hread _ v m hσ'' (Model.extOneStdI_at σ _ v) hv hdv _ (hb _ hext)).mp hbody⟩
    · intro hbt
      obtain ⟨σ', hext, hg⟩ := hr'.mp hbt
      obtain ⟨v, hv, hsv⟩ := hext.2 0 s rfl
      rw [Nat.add_zero] at hv
      obtain ⟨a0, ha0, hin⟩ := F.val hsv tbl e
      exact ⟨a0, (KoreAML.interp_inhOf_of (hτd tbl e)).mp hin, (hread σ' v a0 hext.1 hv hsv ha0 _ (hb σ' hext)).mpr hg⟩

/-- The elements of a confined sort are values', from the binders' facts. -/
theorem BinderFacts.elemsValues (G : BinderFacts c I) {s : Srt} (hs : c.confined s = true) : ElemsValues c I s :=
  ⟨G.confinedNum hs, fun tbl e a => G.confined hs tbl e a⟩

/-- **`ex`, once for every interpretation with the facts.** -/
theorem holds_ex' (F : AtomFacts c I) (G : BinderFacts c I) (s : Srt) {body : Cond} (ih : HoldsDen' c I body) :
    HoldsDen' c I (.ex s body) :=
  holds_exB F (bd := Cond.bound c) s
    (fun h => by rw [Cond.bound, Bool.and_eq_true] at h; exact ⟨G.elemsValues h.1, h.2⟩) ih

/-- **`all`, once for every interpretation with the atoms' facts**, where the Bool that bounds the
binders gives that the elements of the binder's sort are values' and bounds the body. -/
theorem holds_allB (F : AtomFacts c I) {bd : Nat → Cond → Bool} (s : Srt) {body : Cond}
    (L : ∀ {n}, bd n (.all s body) = true → ElemsValues c I s ∧ bd (n + 1) body = true)
    (ih : HoldsDenB bd c I body) : HoldsDenB bd c I (.all s body) := by
  intro vars P σ b tbl e S hok hbd hP hr hk hS hh a ha
  rw [Semantics.condOK] at hok
  replace hbd := L hbd
  have hlen : (vars ++ [s]).length = vars.length + 1 := by simp
  have hsn : s < nRegSorts + c.sortNames.length := hbd.1.1
  obtain ⟨τ, hτ, hτd⟩ := F.sort hsn
  obtain ⟨τS, hτS, hτSd⟩ := F.sort hS
  let K := canonKey c (vars ++ [s]) vars.length
  have hkb : KoreAML.evarKey (Cond.binder c (canonVars c vars).length s).kore = K := Model.binder_keyStdI vars s
  have hkore : Cond.kore c (canonVars c vars) (srtOf c S) (.all s body) =
      .forall (srtOf c S) (Cond.binder c (canonVars c vars).length s).kore
        (Cond.kore c (canonVars c (vars ++ [s])) (srtOf c S) body) := by
    rw [← Model.canonVars_snocStdI c vars s]; rfl
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
  have hread : ∀ σ' v a0, (∀ i < vars.length, σ'.lookup i = σ.lookup i) → σ'.lookup vars.length = some v →
      c.sortOf v = some s → (∀ m, (den c v).interpret I e m ↔ m = a0) → ∀ b', Holds c (vars.length + 1) σ' body b' →
      ((KoreAML.tr ⟨tbl, []⟩ (Cond.kore c (canonVars c (vars ++ [s])) (srtOf c S) body)).interpret I
        ⟨Function.update e.evalEvar (tbl.ev K) a0, e.evalSvar⟩ a ↔ b' = true) := by
    intro σ' v a0 hσ' hn hv hd b' hb'
    exact ih hok (by rw [hlen]; exact hbd.2) hPB (hr.snoc hK hσ' hn hv hd) hkB hS
      (by rw [hlen]; exact hb') a ((KoreAML.interp_inhOf_of (hτSd tbl _)).mpr
        ((KoreAML.interp_inhOf_of (hτSd tbl e)).mp ha))
  have hsrt : ∀ (e' : Valuation M) m,
      (KoreAML.inhOf (KoreAML.trSort tbl (Cond.binder c (canonVars c vars).length s).kore.sort)).interpret I e' m ↔
        KoreAML.Inh I τ m := fun e' m => by
    show (KoreAML.inhOf (KoreAML.trSort tbl (srtOf c s))).interpret _ _ m ↔ _
    exact KoreAML.interp_inhOf_of (hτd tbl e')
  have hinS : ∀ e' : Valuation M, (KoreAML.inhOf (KoreAML.trSort tbl (srtOf c S))).interpret I e' a :=
    fun e' => (KoreAML.interp_inhOf_of (hτSd tbl e')).mpr ((KoreAML.interp_inhOf_of (hτSd tbl e)).mp ha)
  cases hh with
  | all g hb hr' =>
    rw [KoreAML.tr]
    unfold KoreAML.sForall
    rw [KoreAML.interp_sNot, KoreAML.interp_sExists, hkb]
    simp only [KoreAML.interp_member F.defOK, Function.update_same, hsrt,
      KoreAML.interp_sNot, hinS, and_true, not_exists, not_and, Classical.not_not]
    constructor
    · intro hall
      refine hr'.mpr fun σ' hext => ?_
      obtain ⟨v, hv, hsv⟩ := hext.2 0 s rfl
      rw [Nat.add_zero] at hv
      obtain ⟨a0, ha0, hin⟩ := F.val hsv tbl e
      exact (hread σ' v a0 hext.1 hv hsv ha0 _ (hb σ' hext)).mp
        (hall a0 ((KoreAML.interp_inhOf_of (hτd tbl e)).mp hin))
    · intro hbt m hm
      obtain ⟨v, hv, hdv⟩ := hbd.1.2 tbl e m ((KoreAML.interp_inhOf_of (hτd tbl e)).mpr hm)
      have hσ'' : ∀ i < vars.length, (Model.extOneStdI σ vars.length v).lookup i = σ.lookup i :=
        fun i hi => Model.extOneStdI_off σ v (by omega)
      have hext : Extends c vars.length [s] σ (Model.extOneStdI σ vars.length v) :=
        ⟨hσ'', fun j s' hj => by
          cases j with
          | zero => simp at hj; subst hj; exact ⟨v, Model.extOneStdI_at σ _ v, hv⟩
          | succ j => simp at hj⟩
      exact (hread _ v m hσ'' (Model.extOneStdI_at σ _ v) hv hdv _ (hb _ hext)).mpr (hr'.mp hbt _ hext)

/-- **`all`, once for every interpretation with the facts.** -/
theorem holds_all' (F : AtomFacts c I) (G : BinderFacts c I) (s : Srt) {body : Cond} (ih : HoldsDen' c I body) :
    HoldsDen' c I (.all s body) :=
  holds_allB F (bd := Cond.bound c) s
    (fun h => by rw [Cond.bound, Bool.and_eq_true] at h; exact ⟨G.elemsValues h.1, h.2⟩) ih

/-- The `exMatch` case of the Holds lemma in I: the lemma for a match under binders, given it for
the match's body. -/
def ExMatchCase (c : Semantics) {M : Type} (I : Interpretation KoreAML.Sym M) : Prop :=
  ∀ (ys : List Srt) (s : Srt) (p t : Term) {body : Cond}, HoldsDen' c I body → HoldsDen' c I (.exMatch ys s p t body)

/-- `ExMatchCase` with the Bool that bounds the binders a parameter. -/
def ExMatchCaseB (bd : Nat → Cond → Bool) (c : Semantics) {M : Type} (I : Interpretation KoreAML.Sym M) : Prop :=
  ∀ (ys : List Srt) (s : Srt) (p t : Term) {body : Cond},
    HoldsDenB bd c I body → HoldsDenB bd c I (.exMatch ys s p t body)

/-- **`exMatch`, once for every interpretation with the facts.** A binder the pattern holds is a
value's element by the pattern's reading (`BinderFacts.pat`); one it does not hold is of a confined
sort (`Cond.bound`). -/
theorem holds_exMatchB (F : AtomFacts c I) (G : BinderFacts c I) {bd : Nat → Cond → Bool}
    (L : ∀ {n : Nat} {ys : List Srt} {s : Srt} {p t : Term} {body : Cond}, bd n (.exMatch ys s p t body) = true →
      (List.range ys.length).all (fun j =>
        (ctorOccs c p).contains (n + j) || (ys[j]?.map c.confined).getD false) = true ∧
      bd (n + ys.length) body = true) : ExMatchCaseB bd c I := by
  intro ys s p t body ih vars P σ b tbl e S hok hbd hP hr hk hS hh a ha
  simp only [Semantics.condOK, Bool.and_eq_true, beq_iff_eq] at hok
  obtain ⟨⟨⟨hpS, htS⟩, hokB⟩, -⟩ := hok
  replace hbd := L hbd
  obtain ⟨hbnd, hbdB⟩ := hbd
  have hlen : (vars ++ ys).length = vars.length + ys.length := by simp
  let Bs := (List.range' vars.length ys.length).map fun i => ((canonVars c (vars ++ ys)).getD i default).kore
  have hkore : Cond.kore c (canonVars c vars) (srtOf c S) (.exMatch ys s p t body) =
      KoreAML.existsAll (srtOf c S) Bs (.and (srtOf c S)
        [.in (srtOf c s) (srtOf c S) (Term.kore c (canonVars c vars) t) (Term.kore c (canonVars c (vars ++ ys)) p),
         Cond.kore c (canonVars c (vars ++ ys)) (srtOf c S) body]) := by
    simp only [Cond.kore]
    rw [Model.canonVars_appendStdI, Model.binders_eqStdI]
  rw [hkore] at hk ⊢
  have hBk : ∀ i, vars.length ≤ i → i < vars.length + ys.length → canonKey c (vars ++ ys) i ∈ tbl :=
    fun i h1 h2 => hk _ (varsOf_existsAll_binder Bs (List.mem_map_of_mem (List.mem_range'_1.mpr ⟨h1, by omega⟩)))
  have hkB : ∀ k ∈ KoreAML.varsOf (Cond.kore c (canonVars c (vars ++ ys)) (srtOf c S) body), k ∈ tbl :=
    fun k hk0 => hk k (varsOf_existsAll_bodyHF
      (Model.varsOf_and_mem (List.mem_cons_of_mem _ (List.mem_cons_self ..)) hk0) _)
  have hPt : ∀ i ∈ varOccs t, P i := fun i hi =>
    hP i (by rw [varOccsCond]; exact List.mem_append_left _ hi) (varOccs_lt t htS i hi)
  obtain ⟨hs, -⟩ := term_read F hr htS hPt
  obtain ⟨τs, hτs, hτsd⟩ := F.sort hs
  obtain ⟨τS, hτS, hτSd⟩ := F.sort hS
  have haS : ∀ e' : Valuation M, (KoreAML.inhOf (KoreAML.trSort tbl (srtOf c S))).interpret I e' a :=
    fun e' => (KoreAML.interp_inhOf_of (hτSd tbl e')).mpr ((KoreAML.interp_inhOf_of (hτSd tbl e)).mp ha)
  have hnd : (Bs.map fun b => tbl.ev (KoreAML.evarKey b)).Nodup := by
    rw [List.map_map]
    refine Model.nodup_map_of_injOn _ (fun i hi j hj he => ?_) List.nodup_range'
    obtain ⟨hi1, hi2⟩ := List.mem_range'_1.mp hi
    obtain ⟨hj1, hj2⟩ := List.mem_range'_1.mp hj
    exact canonKey_inj (by simp; omega) (by simp; omega) (ev_inj (hBk i hi1 hi2) (hBk j hj1 hj2) he)
  have hsrt : ∀ b ∈ Bs, ∃ n, b.sort = KoreAML.srt n := fun b hb => by
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
    obtain ⟨-, hi2⟩ := List.mem_range'_1.mp hi
    show ∃ n, ((canonVars c (vars ++ ys)).getD i default).kore.sort = KoreAML.srt n
    rw [canonVars_getD c (by simp; omega)]; exact ⟨_, rfl⟩
  have hne : ∀ i, P i → ∀ j, vars.length ≤ j → j < vars.length + ys.length →
      tbl.ev (canonKey c vars i) ≠ tbl.ev (canonKey c (vars ++ ys) j) := by
    intro i hi j h1 h2 he
    obtain ⟨hl, hki, -⟩ := hr i hi
    rw [← Model.canonKey_appendStdI (ys := ys) hl] at he hki
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
  -- the reading of the outer variables at a valuation that agrees with e on them
  have hrOut : ∀ (e' : Valuation M) (σ' : Subst),
      (∀ i, P i → e'.evalEvar (tbl.ev (canonKey c vars i)) = e.evalEvar (tbl.ev (canonKey c vars i))) →
      (∀ i < vars.length, σ'.lookup i = σ.lookup i) →
      ∀ i, P i → i < (vars ++ ys).length ∧ canonKey c (vars ++ ys) i ∈ tbl ∧
        ∃ v, σ'.lookup i = some v ∧ c.sortOf v = some ((vars ++ ys).getD i 0) ∧
          ∀ m, m = e'.evalEvar (tbl.ev (canonKey c (vars ++ ys) i)) ↔ (den c v).interpret I e' m := by
    intro e' σ' hoff hlo i hi
    obtain ⟨hl, hki, v, hv, hsv, hev⟩ := hr i hi
    have hk' := Model.canonKey_appendStdI (c := c) (ys := ys) hl
    refine ⟨by simp; omega, hk' ▸ hki, v, (hlo i hl).trans hv,
      by rw [Model.getD_appendL_stdI _ _ _ hl]; exact hsv, fun m => ?_⟩
    rw [hk', hoff i hi]
    exact (hev m).trans ((den_closed c v).interp _ _ m)
  -- the match's conjunction at a valuation that agrees with e on the outer variables
  have hread : ∀ (e' : Valuation M) (r : Option GroundTerm), EvalTerm c σ t r →
      (∀ i, P i → e'.evalEvar (tbl.ev (canonKey c vars i)) = e.evalEvar (tbl.ev (canonKey c vars i))) →
      ((KoreAML.tr ⟨tbl, []⟩ (.and (srtOf c S)
        [.in (srtOf c s) (srtOf c S) (Term.kore c (canonVars c vars) t) (Term.kore c (canonVars c (vars ++ ys)) p),
         Cond.kore c (canonVars c (vars ++ ys)) (srtOf c S) body])).interpret I e' a ↔
        (∃ m, Res c I e' r m ∧ (KoreAML.tr ⟨tbl, []⟩ (Term.kore c (canonVars c (vars ++ ys)) p)).interpret I e' m) ∧
          (KoreAML.tr ⟨tbl, []⟩ (Cond.kore c (canonVars c (vars ++ ys)) (srtOf c S) body)).interpret I e' a) := by
    intro e' r hev hoff
    have hrt : Reads c I vars P σ tbl e' := fun i hi => by
      obtain ⟨a1, a2, v, a3, a4, a5⟩ := hr i hi
      exact ⟨a1, a2, v, a3, a4, fun m => by rw [hoff i hi]; exact (a5 m).trans ((den_closed c v).interp _ _ m)⟩
    obtain ⟨-, hrd⟩ := term_read F hrt htS hPt
    obtain ⟨hreadt, hsortt⟩ := hrd r hev
    rw [tr_and2, KoreAML.interp_sAnd, KoreAML.tr, KoreAML.interp_sIn F.defOK F.ceilDef
      (hτsd tbl e') (hτSd tbl e') hτs hτS (fun m hm => by
        have hm' := (hreadt m).mp hm
        cases r with
        | none => exact hm'.elim
        | some w =>
          obtain ⟨a0, ha0, hin⟩ := F.val (hsortt w rfl) tbl e'
          rw [(ha0 m).mp hm']
          exact (KoreAML.interp_inhOf_of (hτsd tbl e')).mp hin)]
    simp only [hreadt]
    constructor
    · rintro ⟨⟨hm, -⟩, hb⟩
      exact ⟨hm, hb⟩
    · rintro ⟨hm, hb⟩
      exact ⟨⟨hm, (KoreAML.interp_inhOf_of (hτSd tbl e')).mp (haS e')⟩, hb⟩
  cases hh with
  | exNone hev =>
    refine ⟨fun hm => ?_, fun hf => by cases hf⟩
    obtain ⟨e', hoff, -, hb⟩ := existsAll_elim F.defOK Bs e a hnd hsrt hm
    have hoffP : ∀ i, P i → e'.evalEvar (tbl.ev (canonKey c vars i)) = e.evalEvar (tbl.ev (canonKey c vars i)) :=
      fun i hi => hoff _ fun b hb' he => by
        obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hb'
        obtain ⟨hj1, hj2⟩ := List.mem_range'_1.mp hj
        exact hne i hi j hj1 hj2 he
    obtain ⟨⟨m, hm, -⟩, -⟩ := (hread e' none hev hoffP).mp hb
    exact hm.elim
  | exSome g hev hb hr' =>
    rename_i v
    obtain ⟨-, hrd⟩ := term_read F hr htS hPt
    have hsv : c.sortOf v = some s := (hrd _ hev).2 v rfl
    constructor
    · -- an element of the match: the binders are values' elements, by the pattern or by their sorts
      intro hm
      obtain ⟨e', hoff, hguard, hbm⟩ := existsAll_elim F.defOK Bs e a hnd hsrt hm
      have hoffP : ∀ i, P i → e'.evalEvar (tbl.ev (canonKey c vars i)) = e.evalEvar (tbl.ev (canonKey c vars i)) :=
        fun i hi => hoff _ fun b hb' he => by
          obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hb'
          obtain ⟨hj1, hj2⟩ := List.mem_range'_1.mp hj
          exact hne i hi j hj1 hj2 he
      have hinB : ∀ i, vars.length ≤ i → i < vars.length + ys.length →
          (KoreAML.inhOf (KoreAML.trSort tbl (srtOf c ((vars ++ ys).getD i 0)))).interpret I e'
            (e'.evalEvar (tbl.ev (canonKey c (vars ++ ys) i))) := by
        intro i h1 h2
        have hb' : ((canonVars c (vars ++ ys)).getD i default).kore ∈ Bs :=
          List.mem_map_of_mem (List.mem_range'_1.mpr ⟨h1, h2⟩)
        exact inhOf_srtOf_inS.mpr (hguard _ hb' _ (by rw [canonVars_getD c (by simp; omega)]; rfl))
      obtain ⟨⟨m, hmv, hpm⟩, hbodym⟩ := (hread e' (some v) hev hoffP).mp hbm
      have hpin : ∀ i ∈ varOccs p, canonKey c (vars ++ ys) i ∈ tbl ∧
          (KoreAML.inhOf (KoreAML.trSort tbl (srtOf c ((vars ++ ys).getD i 0)))).interpret I e'
            (e'.evalEvar (tbl.ev (canonKey c (vars ++ ys) i))) := by
        intro i hi
        rcases hPp i hi with hi' | ⟨h1, h2⟩
        · obtain ⟨-, hki, u, -, hsu, hd⟩ := hrOut e' σ hoffP (fun _ _ => rfl) i hi'
          obtain ⟨a0, ha0, hin⟩ := F.val hsu tbl e'
          refine ⟨hki, ?_⟩
          rw [(ha0 _).mp ((hd _).mp rfl)]
          exact hin
        · exact ⟨hBk i h1 h2, hinB i h1 h2⟩
      obtain ⟨σp, hpvp, hwp⟩ := (G.pat hpS hsv hpin m hmv).mp hpm
      have hval : ∀ i, ∃ w : GroundTerm, vars.length ≤ i → i < vars.length + ys.length →
          c.sortOf w = some ((vars ++ ys).getD i 0) ∧
            ∀ m', (den c w).interpret I e' m' ↔ m' = e'.evalEvar (tbl.ev (canonKey c (vars ++ ys) i)) := by
        intro i
        by_cases hb' : vars.length ≤ i ∧ i < vars.length + ys.length
        · obtain ⟨h1, h2⟩ := hb'
          by_cases hio : i ∈ varOccs p
          · obtain ⟨w, -, hsw, hdw⟩ := hwp i hio
            exact ⟨w, fun _ _ => ⟨hsw, hdw⟩⟩
          · have hj := (List.all_eq_true.mp hbnd) (i - vars.length) (List.mem_range.mpr (by omega))
            rw [Bool.or_eq_true] at hj
            have hg : (vars ++ ys).getD i 0 = ys.getD (i - vars.length) 0 := Model.getD_appendR_stdI _ _ _ h1
            rcases hj with hj | hj
            · exact absurd (by
                have := Model.ctorOccs_varOccsStdI (c := c) p _ (by simpa using hj)
                rwa [show vars.length + (i - vars.length) = i by omega] at this) hio
            · cases hy : ys[i - vars.length]? with
              | none => simp [hy] at hj
              | some y =>
                simp only [hy, Option.map_some, Option.getD_some] at hj
                have hgy : (vars ++ ys).getD i 0 = y := by
                  rw [hg, List.getD_eq_getElem?_getD, hy, Option.getD_some]
                obtain ⟨w, hsw, hdw⟩ := G.confined hj tbl e' _ (hgy ▸ hinB i h1 h2)
                exact ⟨w, fun _ _ => ⟨hgy ▸ hsw, hdw⟩⟩
        · exact ⟨.ctor 0 [], fun h1 h2 => absurd ⟨h1, h2⟩ hb'⟩
      let f : Nat → GroundTerm := fun i => Classical.choose (hval i)
      have hf : ∀ i, vars.length ≤ i → i < vars.length + ys.length →
          c.sortOf (f i) = some ((vars ++ ys).getD i 0) ∧
            ∀ m', (den c (f i)).interpret I e' m' ↔ m' = e'.evalEvar (tbl.ev (canonKey c (vars ++ ys) i)) :=
        fun i => Classical.choose_spec (hval i)
      let σE : Subst := ((List.range' vars.length ys.length).map fun i => (i, f i)) ++ σ
      have hlo : ∀ i < vars.length, σE.lookup i = σ.lookup i := fun i hi =>
        Model.lookup_append_noneStdI _ _ _ (by rw [lookup_range', if_neg (by omega)])
      have hhi : ∀ i, vars.length ≤ i → i < vars.length + ys.length → σE.lookup i = some (f i) := fun i h1 h2 =>
        Model.lookup_append_someStdI _ _ _ _ (by rw [lookup_range', if_pos ⟨h1, h2⟩])
      have hrE : Reads c I (vars ++ ys) (fun i => P i ∨ (vars.length ≤ i ∧ i < vars.length + ys.length)) σE tbl e' := by
        intro i hi
        rcases hi with hi | ⟨h1, h2⟩
        · exact hrOut e' σE hoffP hlo i hi
        · obtain ⟨hsf, hdf⟩ := hf i h1 h2
          exact ⟨by simp; omega, hBk i h1 h2, f i, hhi i h1 h2, hsf, fun m' => (hdf m').symm⟩
      have hext : Extends c vars.length ys σ σE := ⟨hlo, fun j s' hj => by
        have hjl : j < ys.length := (List.getElem?_eq_some_iff.mp hj).1
        refine ⟨f (vars.length + j), hhi _ (by omega) (by omega), ?_⟩
        rw [(hf _ (by omega) (by omega)).1, Model.getD_appendR_stdI _ _ _ (by omega), Nat.add_sub_cancel_left,
          List.getD_eq_getElem?_getD, hj]
        rfl⟩
      have hpvE : PatVal c σE p v := Faithful.PatVal.congr_lookup hpvp fun j hj => by
        obtain ⟨-, -, u, hu, hsu, hdu⟩ := hrE j (hPp j hj)
        obtain ⟨u', hu', hsu', hdu'⟩ := hwp j hj
        have := F.apart hsu hsu' e' _ ((hdu _).mp rfl) ((hdu' _).mpr rfl)
        rw [hu, hu', this]
      exact hr'.mpr ⟨σE, hext, hpvE,
        (ih hokB (by rw [hlen]; exact hbdB) hPB hrE hkB hS (by rw [hlen]; exact hb σE hext hpvE) a (haS e')).mp hbodym⟩
    · -- an extension where the match holds: the binders at the elements of their values
      intro hbt
      obtain ⟨σ', hext, hpv, hg⟩ := hr'.mp hbt
      have hvalB : ∀ i, vars.length ≤ i → i < vars.length + ys.length → ∃ w,
          σ'.lookup i = some w ∧ c.sortOf w = some ((vars ++ ys).getD i 0) := by
        intro i h1 h2
        obtain ⟨w, hw, hsw⟩ := hext.2 (i - vars.length) (ys.getD (i - vars.length) 0)
          (by rw [List.getElem?_eq_getElem (by omega), List.getD_eq_getElem?_getD,
            List.getElem?_eq_getElem (by omega)]; rfl)
        rw [show vars.length + (i - vars.length) = i by omega] at hw
        exact ⟨w, hw, by rw [hsw, Model.getD_appendR_stdI _ _ _ h1]⟩
      have hel : ∀ i, ∃ a0 : M, vars.length ≤ i → i < vars.length + ys.length →
          (∀ m', (den c ((σ'.lookup i).getD (.ctor 0 []))).interpret I e m' ↔ m' = a0) ∧
            InS I (c.sortName ((vars ++ ys).getD i 0)) a0 := by
        intro i
        by_cases hb' : vars.length ≤ i ∧ i < vars.length + ys.length
        · obtain ⟨w, hw, hsw⟩ := hvalB i hb'.1 hb'.2
          obtain ⟨a0, ha0, hin⟩ := F.val hsw tbl e
          exact ⟨a0, fun _ _ => ⟨by rw [hw]; exact ha0, inhOf_srtOf_inS.mp hin⟩⟩
        · exact ⟨default, fun h1 h2 => absurd ⟨h1, h2⟩ hb'⟩
      let is := List.range' vars.length ys.length
      have hkis : ∀ i < (vars ++ ys).length, i ∈ is → canonKey c (vars ++ ys) i ∈ tbl := fun i _ his => by
        obtain ⟨h1, h2⟩ := List.mem_range'_1.mp his
        exact hBk i h1 h2
      let fe : Nat → M := fun i => Classical.choose (hel i)
      have hfe : ∀ i, vars.length ≤ i → i < vars.length + ys.length →
          (∀ m', (den c ((σ'.lookup i).getD (.ctor 0 []))).interpret I e m' ↔ m' = fe i) ∧
            InS I (c.sortName ((vars ++ ys).getD i 0)) (fe i) := fun i => Classical.choose_spec (hel i)
      let e' := setV c tbl (vars ++ ys) is fe e
      have hoffP : ∀ i, P i → e'.evalEvar (tbl.ev (canonKey c vars i)) = e.evalEvar (tbl.ev (canonKey c vars i)) := by
        intro i hi
        obtain ⟨hl, -⟩ := hr i hi
        rw [← Model.canonKey_appendStdI (ys := ys) hl]
        exact setV_off hkis (by simp; omega) (fun his => by have := (List.mem_range'_1.mp his).1; omega)
      have hr'' : Reads c I (vars ++ ys) (fun i => P i ∨ (vars.length ≤ i ∧ i < vars.length + ys.length)) σ' tbl e' := by
        intro i hi
        rcases hi with hi | ⟨h1, h2⟩
        · exact hrOut e' σ' hoffP hext.1 i hi
        · obtain ⟨w, hw, hsw⟩ := hvalB i h1 h2
          refine ⟨by simp; omega, hBk i h1 h2, w, hw, hsw, fun m' => ?_⟩
          rw [setV_on hkis (by simp; omega) (List.mem_range'_1.mpr ⟨h1, h2⟩)]
          have := (hfe i h1 h2).1 m'
          rw [hw, Option.getD_some] at this
          exact (this.trans Iff.rfl).symm.trans ((den_closed c w).interp e e' m')
      obtain ⟨m0, hm0, -⟩ := F.val hsv tbl e'
      have hpm : (KoreAML.tr ⟨tbl, []⟩ (Term.kore c (canonVars c (vars ++ ys)) p)).interpret I e' m0 := by
        refine (G.pat hpS hsv (fun i hi => ⟨(hr'' i (hPp i hi)).2.1, Reads.inSort F hr'' (hPp i hi)⟩) m0
          ((hm0 m0).mpr rfl)).mpr ⟨σ', hpv, fun i hi => ?_⟩
        obtain ⟨-, -, u, hu, hsu, hdu⟩ := hr'' i (hPp i hi)
        exact ⟨u, hu, hsu, fun m' => (hdu m').symm⟩
      refine existsAll_intro_at F.defOK _ e e' a hnd hsrt (fun z hz => ?_) rfl (fun b hb' k hk => ?_)
        ((hread e' (some v) hev hoffP).mpr ⟨⟨m0, (hm0 m0).mpr rfl, hpm⟩,
          (ih hokB (by rw [hlen]; exact hbdB) hPB hr'' hkB hS (by rw [hlen]; exact hb σ' hext hpv) a (haS e')).mpr hg⟩)
      · show (if h : _ then _ else _) = _
        rw [dif_neg]
        rintro ⟨i, -, hix, rfl⟩
        exact hz _ (List.mem_map_of_mem hix) rfl
      · obtain ⟨i, hix, rfl⟩ := List.mem_map.mp hb'
        obtain ⟨h1, h2⟩ := List.mem_range'_1.mp hix
        have hs' : ((canonVars c (vars ++ ys)).getD i default).kore.sort =
            KoreAML.srt (c.sortName ((vars ++ ys).getD i 0)) := by
          rw [canonVars_getD c (by simp; omega)]; rfl
        rw [hs'] at hk
        rw [← srt_inj hk]
        show InS I _ (e'.evalEvar (tbl.ev (canonKey c (vars ++ ys) i)))
        rw [setV_on hkis (by simp; omega) hix]
        exact (hfe i h1 h2).2

/-- **`exMatch`, once for every interpretation with the facts**, at `Cond.bound`. -/
theorem holds_exMatch' (F : AtomFacts c I) (G : BinderFacts c I) : ExMatchCase c I :=
  holds_exMatchB F G (bd := Cond.bound c) (fun h => by rw [Cond.bound, Bool.and_eq_true] at h; exact h)

/-- What the Holds lemma reads of the Bool that bounds a condition's binders: it bounds the parts
of a connective, at a match under binders it is `Cond.bound`'s test of the binders with the body
bounded, and at an `ex` or `all` it gives that the elements of the binder's sort are values' with
the body bounded. -/
structure BoundReads (c : Semantics) {M : Type} (I : Interpretation KoreAML.Sym M) (bd : Nat → Cond → Bool) : Prop where
  not : ∀ {n : Nat} {p : Cond}, bd n (.not p) = true → bd n p = true
  and : ∀ {n : Nat} {p q : Cond}, bd n (.and p q) = true → bd n p = true ∧ bd n q = true
  or : ∀ {n : Nat} {p q : Cond}, bd n (.or p q) = true → bd n p = true ∧ bd n q = true
  implies : ∀ {n : Nat} {p q : Cond}, bd n (.implies p q) = true → bd n p = true ∧ bd n q = true
  exMatch : ∀ {n : Nat} {ys : List Srt} {s : Srt} {p t : Term} {body : Cond}, bd n (.exMatch ys s p t body) = true →
    (List.range ys.length).all (fun j =>
      (ctorOccs c p).contains (n + j) || (ys[j]?.map c.confined).getD false) = true ∧
    bd (n + ys.length) body = true
  ex : ∀ {n : Nat} {s : Srt} {body : Cond}, bd n (.ex s body) = true → ElemsValues c I s ∧ bd (n + 1) body = true
  all : ∀ {n : Nat} {s : Srt} {body : Cond}, bd n (.all s body) = true → ElemsValues c I s ∧ bd (n + 1) body = true

/-- `Cond.bound` is such a Bool, from the binders' facts. -/
theorem boundReads_bound (G : BinderFacts c I) : BoundReads c I (Cond.bound c) where
  not := fun h => by rw [Cond.bound] at h; exact h
  and := fun h => by rw [Cond.bound, Bool.and_eq_true] at h; exact h
  or := fun h => by rw [Cond.bound, Bool.and_eq_true] at h; exact h
  implies := fun h => by rw [Cond.bound, Bool.and_eq_true] at h; exact h
  exMatch := fun h => by rw [Cond.bound, Bool.and_eq_true] at h; exact h
  ex := fun h => by rw [Cond.bound, Bool.and_eq_true] at h; exact ⟨G.elemsValues h.1, h.2⟩
  all := fun h => by rw [Cond.bound, Bool.and_eq_true] at h; exact ⟨G.elemsValues h.1, h.2⟩

/-- **The Holds lemma for every interpretation with the facts, over a Bool that bounds the
binders** (`BoundReads`), by structural recursion. -/
theorem holds_denB (F : AtomFacts c I) (G : BinderFacts c I) {bd : Nat → Cond → Bool} (L : BoundReads c I bd) :
    ∀ p : Cond, HoldsDenB bd c I p
  | .top => fun hok _ hP hr hk hS hh a ha => holds_top' F hok rfl hP hr hk hS hh a ha
  | .bot => fun hok _ hP hr hk hS hh a ha => holds_bot' F hok rfl hP hr hk hS hh a ha
  | .not p => holds_notB (bd := bd) L.not (holds_denB F G L p)
  | .and p q => holds_andB (bd := bd) L.and (holds_denB F G L p) (holds_denB F G L q)
  | .or p q => holds_orB (bd := bd) L.or (holds_denB F G L p) (holds_denB F G L q)
  | .implies p q => holds_impliesB (bd := bd) L.implies (holds_denB F G L p) (holds_denB F G L q)
  | .ceil s t => fun hok _ hP hr hk hS hh a ha => holds_ceil' F s t hok rfl hP hr hk hS hh a ha
  | .equals s t u => fun hok _ hP hr hk hS hh a ha => holds_equals' F s t u hok rfl hP hr hk hS hh a ha
  | .mem s t u => fun hok _ hP hr hk hS hh a ha => holds_mem' F s t u hok rfl hP hr hk hS hh a ha
  | .exMatch ys s p t body => holds_exMatchB F G (bd := bd) L.exMatch ys s p t (holds_denB F G L body)
  | .ex s body => holds_exB F (bd := bd) (body := body) s L.ex (holds_denB F G L body)
  | .all s body => holds_allB F (bd := bd) (body := body) s L.all (holds_denB F G L body)

/-- **The Holds lemma for every interpretation with the facts and the `exMatch` case**, by structural
recursion. -/
theorem holds_den_of (F : AtomFacts c I) (G : BinderFacts c I) (X : ExMatchCase c I) : ∀ p : Cond, HoldsDen' c I p
  | .top => holds_top' F
  | .bot => holds_bot' F
  | .not p => holds_not' (holds_den_of F G X p)
  | .and p q => holds_and' (holds_den_of F G X p) (holds_den_of F G X q)
  | .or p q => holds_or' (holds_den_of F G X p) (holds_den_of F G X q)
  | .implies p q => holds_implies' (holds_den_of F G X p) (holds_den_of F G X q)
  | .ceil s t => holds_ceil' F s t
  | .equals s t u => holds_equals' F s t u
  | .mem s t u => holds_mem' F s t u
  | .exMatch ys s p t body => X ys s p t (holds_den_of F G X body)
  | .ex s body => holds_ex' F G s (holds_den_of F G X body)
  | .all s body => holds_all' F G s (holds_den_of F G X body)

export Cond (hasBinder)

/-- **The Holds lemma, the binders' facts and the `exMatch` case asked only of a condition with a
binder.** -/
theorem holds_den_binders_of (F : AtomFacts c I) :
    ∀ p : Cond, (hasBinder p = true → BinderFacts c I) → (hasBinder p = true → ExMatchCase c I) → HoldsDen' c I p
  | .top, _, _ => holds_top' F
  | .bot, _, _ => holds_bot' F
  | .not p, hG, hX => holds_not' (holds_den_binders_of F p hG hX)
  | .and p q, hG, hX => holds_and'
      (holds_den_binders_of F p (fun hp => hG (by rw [hasBinder, hp, Bool.true_or]))
        (fun hp => hX (by rw [hasBinder, hp, Bool.true_or])))
      (holds_den_binders_of F q (fun hq => hG (by rw [hasBinder, hq, Bool.or_true]))
        (fun hq => hX (by rw [hasBinder, hq, Bool.or_true])))
  | .or p q, hG, hX => holds_or'
      (holds_den_binders_of F p (fun hp => hG (by rw [hasBinder, hp, Bool.true_or]))
        (fun hp => hX (by rw [hasBinder, hp, Bool.true_or])))
      (holds_den_binders_of F q (fun hq => hG (by rw [hasBinder, hq, Bool.or_true]))
        (fun hq => hX (by rw [hasBinder, hq, Bool.or_true])))
  | .implies p q, hG, hX => holds_implies'
      (holds_den_binders_of F p (fun hp => hG (by rw [hasBinder, hp, Bool.true_or]))
        (fun hp => hX (by rw [hasBinder, hp, Bool.true_or])))
      (holds_den_binders_of F q (fun hq => hG (by rw [hasBinder, hq, Bool.or_true]))
        (fun hq => hX (by rw [hasBinder, hq, Bool.or_true])))
  | .ceil s t, _, _ => holds_ceil' F s t
  | .equals s t u, _, _ => holds_equals' F s t u
  | .mem s t u, _, _ => holds_mem' F s t u
  | .exMatch ys s p t body, hG, hX =>
      hX rfl ys s p t (holds_den_binders_of F body (fun _ => hG rfl) (fun _ => hX rfl))
  | .ex s body, hG, hX => holds_ex' F (hG rfl) s (holds_den_binders_of F body (fun _ => hG rfl) (fun _ => hX rfl))
  | .all s body, hG, hX => holds_all' F (hG rfl) s (holds_den_binders_of F body (fun _ => hG rfl) (fun _ => hX rfl))

/-- **The Holds lemma for every interpretation with the facts.** -/
theorem holds_den' (F : AtomFacts c I) (G : BinderFacts c I) : ∀ p : Cond, HoldsDen' c I p :=
  holds_den_of F G (holds_exMatch' F G)

/-- **The Holds lemma, the binders' facts asked only of a condition with a binder.** -/
theorem holds_den_binders' (F : AtomFacts c I) (p : Cond) (hG : hasBinder p = true → BinderFacts c I) :
    HoldsDen' c I p :=
  holds_den_binders_of F p hG fun hp => holds_exMatch' F (hG hp)

/-! ### Numbered sorts, from `idsOK` and `sortsNumbered` -/

section Numbered
open Model

/-- A constructor sort is numbered, from `idsOK`. -/
theorem consSorts_numbered_ids (hids : c.idsOK = true) {N : Srt} (hN : N ∈ consSorts c) :
    N < nRegSorts + c.sortNames.length := by
  have hreg : ∀ s, s < nRegSorts → s < nRegSorts + c.sortNames.length :=
    fun s hs => Nat.lt_of_lt_of_le hs (Nat.le_add_right _ _)
  have hown : ∀ s ∈ c.userSorts, s < nRegSorts + c.sortNames.length := by
    have hids' := hids
    unfold Semantics.idsOK at hids'
    simp only [Bool.and_eq_true, beq_iff_eq] at hids'
    have he : c.ownSorts = _ := hids'.1.1.1
    intro s hs
    by_cases hge : nRegSorts ≤ s
    · have hs' : s ∈ c.ownSorts := List.mem_filter.mpr ⟨hs, decide_eq_true hge⟩
      rw [he] at hs'
      exact (List.mem_range'_1.mp hs').2
    · exact hreg _ (Nat.lt_of_not_le hge)
  unfold consSorts at hN
  rcases List.mem_append.mp (List.mem_filter.mp hN).1 with h1 | h1
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h1
    rcases h1 with rfl | rfl <;> exact hreg _ (by decide)
  · rw [mem_sortBy] at h1
    simp only [List.mem_append] at h1
    rcases h1 with h1 | h1
    · exact hown _ h1
    · unfold Semantics.libCtorSorts at h1
      exact hreg _ (NamesApart.lib_sorts_lt (NamesApart.lib_ok hids) _ (List.mem_filter.mp h1).1).1

/-- A confined sort is numbered: Bool, or a sort of constructor terms; from `idsOK`. -/
theorem confinedAt_numbered_ids (hids : c.idsOK = true) :
    ∀ (k : Nat) {s : Srt}, c.confinedAt k s = true → s < nRegSorts + c.sortNames.length
  | 0, s, hc => by
    simp only [Semantics.confinedAt, Bool.and_eq_true, beq_iff_eq] at hc
    rw [hc.1]; exact bool_numbered
  | k + 1, s, hc => by
    simp only [Semantics.confinedAt, Bool.or_eq_true, Bool.and_eq_true] at hc
    rcases hc with hc | ⟨⟨hN, -⟩, -⟩
    · simp only [beq_iff_eq] at hc
      rw [hc.1]; exact bool_numbered
    · exact consSorts_numbered_ids hids (by simpa using hN)

/-- **A well-sorted term's sort is numbered** where its variables' sorts are, in a context whose
heads are kernel symbols and whose subsorts are the definition's: from `sortsNumbered`, and for a
domain value from the sorts of values (`hvn`). -/
theorem sortOfTerm_numbered
    (hvn : ∀ {v : GroundTerm} {s : Srt}, c.sortOf v = some s → s < nRegSorts + c.sortNames.length) (hsorts : Model.sortsNumbered c = true)
    (hov : c.overloadsOK = true) {x : TermCtx} (hx : ∀ k ∈ x.heads, k ∈ kernelSyms c)
    (hsub : ∀ a b, (a, b) ∈ x.subs → (a, b) ∈ c.subsorts) (hlib : x.lib = c.lib) {vars : List Srt} :
    ∀ (t : Term) {s : Srt}, sortOfTerm x vars t = some s →
      (∀ i ∈ varOccs t, ∀ s', vars[i]? = some s' → s' < nRegSorts + c.sortNames.length) →
      s < nRegSorts + c.sortNames.length
  | .var j, s, ht, hv => hv j (by simp [varOccs]) s (sortOfTerm_var.mp ht)
  | .app f ts, s, ht, _ => by
    have hn := hsorts
    simp only [Model.sortsNumbered, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hn
    obtain ⟨k, hk, -, rfl⟩ := sortOfTerm_app.mp ht
    exact hn.1.1.1 _ (hx _ (lookupSig_spec hk).1) _ (List.mem_cons_self ..)
  | .inj a b t, s, ht, _ => by
    have hn := hsorts
    simp only [Model.sortsNumbered, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hn
    obtain ⟨hab, -, rfl⟩ := sortOfTerm_inj.mp ht
    exact (hn.1.1.2 _ (hsub _ _ hab)).2
  | .as t j, s, ht, hv => by
    obtain ⟨-, h'⟩ := Exec.sortOfTerm_as ht
    exact sortOfTerm_numbered hvn hsorts hov hx hsub hlib t h' fun i hi s' hs' =>
      hv i (by rw [varOccs]; exact List.mem_append_left _ hi) s' hs'
  | .dv s' lit, s, ht, _ => by
    obtain ⟨hok, rfl⟩ := sortOfTerm_dv.mp ht
    exact hvn ((sortOf_dv (lit := lit)).mpr ⟨hlib ▸ hok, rfl⟩)

end Numbered

/-! ### The read form of the soundness of `EvalTerm` -/

/-- The soundness of `EvalTerm` in I over every variable in scope: σ well sorted on all of them, at a
valuation that agrees with it (the form `evalTerm_den4Cl` concludes). -/
def TermSound (c : Semantics) {M : Type} (I : Interpretation KoreAML.Sym M) : Prop :=
  ∀ {σ : Subst} {t : Term} {r : Option GroundTerm}, EvalTerm c σ t r →
    ∀ {vars : List Srt} {vs : List KoreAML.Var} {tbl : KoreAML.VarTable} {e : Valuation M} {s : Srt},
    c.WellSorted vars σ → vs.length = vars.length → Agrees c I tbl vs σ e →
    sortOfTerm (c.rhsCtx (c.fns.map Fn.sig)) vars t = some s →
    ∀ m, (KoreAML.tr ⟨tbl, []⟩ (Term.kore c vs t)).interpret I e m ↔ Res c I e r m

theorem lookup_tab (f : Nat → GroundTerm) : ∀ (l : List Nat) (i : Nat), i ∈ l →
    (l.map fun j => (j, f j)).lookup i = some (f i)
  | [], _, h => by cases h
  | j :: l, i, h => by
    rw [List.map_cons, List.lookup_cons]
    by_cases hij : i = j
    · subst hij; simp
    · have : (i == j) = false := by simpa using hij
      rw [this]
      exact lookup_tab f l i (by rcases List.mem_cons.mp h with h | h; exact absurd h hij; exact h)

/-- **The read form of the soundness of `EvalTerm` from the all-variables form**, in a model of Γ:
a variable the term does not read is given the sort Bool and `true`'s element. -/
theorem termSoundAt_of (hI : I ⊧ᴵP Γ c) [OvlOK c] (hT : TermSound c I) : TermSoundAt c I := by
  intro σ t r he vars P tbl e s hP hr ht m
  classical
  let v0 : GroundTerm := bool true
  let f : Nat → GroundTerm := fun i => if i ∈ varOccs t then (σ.lookup i).getD v0 else v0
  let vars' : List Srt := (List.range vars.length).map fun i => if i ∈ varOccs t then vars.getD i 0 else Srt.bool
  let σ' : Subst := (List.range vars.length).map fun j => (j, f j)
  let e1 := fillV c tbl vars (varOccs t) (elemOf c I v0) e
  have hlen : vars'.length = vars.length := by simp [vars']
  have hkeys : ∀ i < vars.length, i ∈ varOccs t → canonKey c vars i ∈ tbl := fun i _ hi => (hr i (hP i hi)).2.1
  have hσ'i : ∀ i < vars.length, σ'.lookup i = some (f i) := fun i hi =>
    lookup_tab f _ i (List.mem_range.mpr hi)
  have hcong : ∀ i ∈ varOccs t, σ.lookup i = σ'.lookup i := fun i hi => by
    obtain ⟨hl, -, v, hv, -, -⟩ := hr i (hP i hi)
    rw [hσ'i i hl, hv]; simp [f, hi, hv]
  have hσ' : c.WellSorted vars' σ' := by
    intro i s' hs'
    have hl : i < vars.length := by rw [← hlen]; exact (List.getElem?_eq_some_iff.mp hs').1
    refine ⟨f i, hσ'i i hl, ?_⟩
    have hs'' : s' = if i ∈ varOccs t then vars.getD i 0 else Srt.bool := by
      simp [vars', hl] at hs'; rw [← hs']; simp [List.getD_eq_getElem?_getD, hl]
    by_cases hi : i ∈ varOccs t
    · obtain ⟨-, -, v, hv, hsv, -⟩ := hr i (hP i hi)
      simp [f, hi, hv, hs'', hsv]
    · simp [f, hi, hs'']; exact sortOf_bool true
  have hag : Agrees c I tbl (canonVars c vars) σ' e1 := by
    intro i v hi hv m'
    rw [canonVars_length] at hi
    rw [hσ'i i hi] at hv
    cases hv
    show m' = e1.evalEvar (tbl.ev (canonKey c vars i)) ↔ _
    by_cases hio : i ∈ varOccs t
    · obtain ⟨-, -, v, hv, -, hd⟩ := hr i (hP i hio)
      rw [fillV_off hkeys hi hio, hd m']
      simp only [f, hio, ite_true, hv, Option.getD_some]
      exact (den_closed c v).interp e e1 m'
    · rw [fillV_on hi hio]
      simp only [f, hio, ite_false]
      exact ((elemOf_spec hI (sortOf_bool true) e1).1 m').symm
  have ht' : sortOfTerm (c.rhsCtx (c.fns.map Fn.sig)) vars' t = some s := by
    rw [sortOfTerm_congr t fun i hi => ?_]; exact ht
    have hl := (hr i (hP i hi)).1
    simp [vars', hl, hi, List.getD_eq_getElem?_getD]
  have key := hT (Exec.EvalTerm.congr he hcong) hσ' (by rw [canonVars_length, hlen]) hag ht' m
  rw [tr_kore_congr t (fun i hi => (fillV_off (a := elemOf c I v0) (e := e) hkeys (hr i (hP i hi)).1 hi).symm) m, key]
  exact Res_closed r e1 e m

end Shape

end HoldsShape

end KCore
