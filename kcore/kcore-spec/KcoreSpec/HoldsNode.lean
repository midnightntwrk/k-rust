/-
  KCore. The Holds lemma, one constructor of `Holds` at a time.

  `HoldsDen' c I p` (HoldsFacts.lean) reads a condition in I at every σ and every truth value
  `Holds` gives it, from the soundness of `EvalTerm` at every evaluation (`AtomFacts.termSound`).
  A proof by recursion on the evaluations of a function's clauses has that soundness only at the
  evaluations below the one at hand. `HoldsAt c I n σ p b` is the reading at one σ and one truth
  value, and each lemma here gives it at a constructor of `Holds` from the readings of the parts
  (`HoldsAt` of the conditions below, `TermAt` of the terms evaluated), so that a recursion on a
  derivation of `Holds` proves `HoldsAt` of its conclusion. `HoldsAtB bd` is the reading at the
  conditions whose binders the Bool `bd` bounds, and `HoldsAt` is it at `Cond.boundConf`. Neither asks anything of σ beyond the
  variables the valuation reads (`Reads`, which gives them values of their sorts), so a reading
  holds at a σ whatever it gives the other variables.
-/
import KcoreSpec.HoldsFacts

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace KCore

open ML Faithful

namespace Faithful

/-- `Agrees` on the variables `is`: the valuation `e` gives each variable `i` of `is` that σ binds
the element its value denotes, at the index the table `t` gives the variable's key. -/
def AgreesOn {M : Type} (c : Semantics) (I : Interpretation KoreAML.Sym M) (t : KoreAML.VarTable)
    (vs : List KoreAML.Var) (is : List Nat) (σ : Subst) (e : Valuation M) : Prop :=
  ∀ i ∈ is, ∀ v, i < vs.length → σ.lookup i = some v →
    ∀ m, m = e.evalEvar (t.ev (KoreAML.evarKey (vs.getD i default).kore)) ↔ (den c v).interpret I e m

theorem Agrees.on {M : Type} {c : Semantics} {I : Interpretation KoreAML.Sym M} {t : KoreAML.VarTable}
    {vs : List KoreAML.Var} {σ : Subst} {e : Valuation M} (h : Agrees c I t vs σ e) (is : List Nat) :
    AgreesOn c I t vs is σ e :=
  fun i _ => h i

theorem AgreesOn.mono {M : Type} {c : Semantics} {I : Interpretation KoreAML.Sym M} {t : KoreAML.VarTable}
    {vs : List KoreAML.Var} {is is' : List Nat} {σ : Subst} {e : Valuation M} (h : AgreesOn c I t vs is σ e)
    (hsub : ∀ i ∈ is', i ∈ is) : AgreesOn c I t vs is' σ e :=
  fun i hi => h i (hsub i hi)

end Faithful

namespace HoldsShape

section Node
variable {c : Semantics} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}

/-- The term t, with the result r under σ, is read in I: at every valuation that reads its
variables as their values under σ, its translation denotes what r denotes. `TermSoundAt` at one
evaluation. -/
def TermAt (c : Semantics) {M : Type} (I : Interpretation KoreAML.Sym M) (σ : Subst) (t : Term)
    (r : Option GroundTerm) : Prop :=
  ∀ {vars : List Srt} {P : Nat → Prop} {tbl : KoreAML.VarTable} {e : Valuation M} {s : Srt},
    (∀ i ∈ varOccs t, P i) → Reads c I vars P σ tbl e →
    sortOfTerm (c.rhsCtx (c.fns.map Fn.sig)) vars t = some s →
    ∀ m, (KoreAML.tr ⟨tbl, []⟩ (Term.kore c (canonVars c vars) t)).interpret I e m ↔ Res c I e r m

/-- The condition p, with n variables in scope and the truth value b under σ, is read in I where
the Bool `bd` bounds its binders: the conclusion of `HoldsDenB bd` at σ and b. -/
def HoldsAtB (bd : Nat → Cond → Bool) (c : Semantics) {M : Type} (I : Interpretation KoreAML.Sym M) (n : Nat)
    (σ : Subst) (p : Cond) (b : Bool) : Prop :=
  ∀ {vars : List Srt} {P : Nat → Prop} {tbl : KoreAML.VarTable} {e : Valuation M} {S : Srt},
    vars.length = n → c.condOK vars p = true → bd vars.length p = true →
    (∀ i ∈ varOccsCond vars.length p, i < vars.length → P i) → Reads c I vars P σ tbl e →
    (∀ k ∈ KoreAML.varsOf (Cond.kore c (canonVars c vars) (srtOf c S) p), k ∈ tbl) →
    S < nRegSorts + c.sortNames.length →
    ∀ a, (KoreAML.inhOf (KoreAML.trSort tbl (srtOf c S))).interpret I e a →
      ((KoreAML.tr ⟨tbl, []⟩ (Cond.kore c (canonVars c vars) (srtOf c S) p)).interpret I e a ↔ b = true)

/-- `HoldsAtB` at `Cond.boundConf`: every binder of the condition is of a sort where values and
elements agree by the sort alone. -/
abbrev HoldsAt (c : Semantics) {M : Type} (I : Interpretation KoreAML.Sym M) (n : Nat) (σ : Subst) (p : Cond)
    (b : Bool) : Prop :=
  HoldsAtB (Cond.boundConf c) c I n σ p b

/-- What the constructors' lemmas read of I: `AtomFacts` without the soundness of `EvalTerm`. -/
structure NodeFacts (c : Semantics) {M : Type} (I : Interpretation KoreAML.Sym M) : Prop where
  defOK : KoreAML.DefOK I
  ceilDef : I ⊧ᴵ KoreAML.ceilDefItem.pat
  sort : ∀ {s : Srt}, s < nRegSorts + c.sortNames.length → ∃ τ, KoreAML.IsSort I τ ∧
    ∀ (tbl : KoreAML.VarTable) (e : Valuation M) (a : M), (KoreAML.trSort tbl (srtOf c s)).interpret I e a ↔ a = τ
  val : ∀ {v : GroundTerm} {s : Srt}, c.sortOf v = some s → ∀ (tbl : KoreAML.VarTable) (e : Valuation M),
    ∃ a, (∀ m, (den c v).interpret I e m ↔ m = a) ∧ (KoreAML.inhOf (KoreAML.trSort tbl (srtOf c s))).interpret I e a
  apart : ∀ {v w : GroundTerm} {s : Srt}, c.sortOf v = some s → c.sortOf w = some s → ∀ (e : Valuation M) (a : M),
    (den c v).interpret I e a → (den c w).interpret I e a → v = w
  sortCtx : SortCtx c
  termNum : ∀ {vars : List Srt} {t : Term} {s : Srt}, sortOfTerm (c.rhsCtx (c.fns.map Fn.sig)) vars t = some s →
    (∀ i ∈ varOccs t, ∀ s', vars[i]? = some s' → s' < nRegSorts + c.sortNames.length) →
    s < nRegSorts + c.sortNames.length
  valNum : ∀ {v : GroundTerm} {s : Srt}, c.sortOf v = some s → s < nRegSorts + c.sortNames.length

/-- The atoms' facts give them. -/
theorem AtomFacts.node (F : AtomFacts c I) : NodeFacts c I :=
  ⟨F.defOK, F.ceilDef, F.sort, F.val, F.apart, F.sortCtx, F.termNum, F.valNum⟩

/-- With the atoms' facts, every evaluation of a term is read. -/
theorem AtomFacts.termAt (F : AtomFacts c I) {σ : Subst} {t : Term} {r : Option GroundTerm}
    (h : EvalTerm c σ t r) : TermAt c I σ t r :=
  fun hP hr ht m => F.termSound h hP hr ht m

/-- The Holds lemma for p gives the reading at each truth value `Holds` gives. -/
theorem holdsAt_of_den {bd : Nat → Cond → Bool} {p : Cond} (hp : HoldsDenB bd c I p) {n : Nat} {σ : Subst}
    {b : Bool} (hh : Holds c n σ p b) : HoldsAtB bd c I n σ p b := by
  intro vars P tbl e S hlenN hok hbd hP hr hk hS a ha
  subst hlenN
  exact hp hok hbd hP hr hk hS hh a ha

/-- The reading over a Bool gives it over a Bool that accepts less. -/
theorem HoldsAtB.mono {bd bd' : Nat → Cond → Bool} {n : Nat} {σ : Subst} {p : Cond} {b : Bool}
    (hb : ∀ m, bd m p = true → bd' m p = true) (h : HoldsAtB bd' c I n σ p b) : HoldsAtB bd c I n σ p b := by
  intro vars P tbl e S hlenN hok hbd
  exact h hlenN hok (hb _ hbd)

/-- A σ well sorted on the variables in scope, extended at binders, is well sorted on them all. -/
theorem wellSorted_extN {vars ys : List Srt} {σ σ' : Subst} (hσ : c.WellSorted vars σ)
    (hx : Extends c vars.length ys σ σ') : c.WellSorted (vars ++ ys) σ' := by
  intro i s hi
  by_cases hlt : i < vars.length
  · rw [List.getElem?_append_left hlt] at hi
    obtain ⟨v, hv, hs⟩ := hσ i s hi
    exact ⟨v, (hx.1 i hlt).trans hv, hs⟩
  · rw [List.getElem?_append_right (by omega)] at hi
    obtain ⟨v, hv, hs⟩ := hx.2 _ s hi
    rw [show vars.length + (i - vars.length) = i by omega] at hv
    exact ⟨v, hv, hs⟩

/-- A read variable's element is in its sort. -/
theorem Reads.inSortN (F : NodeFacts c I) {vars : List Srt} {P : Nat → Prop} {σ : Subst} {tbl : KoreAML.VarTable}
    {e : Valuation M} (hr : Reads c I vars P σ tbl e) {i : Nat} (hi : P i) :
    (KoreAML.inhOf (KoreAML.trSort tbl (srtOf c (vars.getD i 0)))).interpret I e
      (e.evalEvar (tbl.ev (canonKey c vars i))) := by
  obtain ⟨-, -, u, -, hsu, hd⟩ := hr i hi
  obtain ⟨a0, ha0, hin⟩ := F.val hsu tbl e
  rw [(ha0 _).mp ((hd _).mp rfl)]
  exact hin

theorem holdsAt_top (F : NodeFacts c I) {bd : Nat → Cond → Bool} {n : Nat} {σ : Subst} :
    HoldsAtB bd c I n σ .top true := by
  intro vars P tbl e S _ _ _ _ _ _ _ a ha
  rw [Cond.kore, KoreAML.tr, KoreAML.interp_sTop F.defOK Model.srtOf_free_stdI]
  exact ⟨fun _ => rfl, fun _ => ha⟩

theorem holdsAt_bot (F : NodeFacts c I) {bd : Nat → Cond → Bool} {n : Nat} {σ : Subst} :
    HoldsAtB bd c I n σ .bot false := by
  intro vars P tbl e S _ _ _ _ _ _ _ a ha
  rw [Cond.kore, KoreAML.tr]
  unfold KoreAML.sBot
  rw [KoreAML.interp_sNot, KoreAML.interp_sTop F.defOK Model.srtOf_free_stdI]
  exact ⟨fun hn => absurd ha hn.1, fun hf => by cases hf⟩

theorem holdsAt_not {n : Nat} {σ : Subst} {p : Cond} {b' : Bool} (ih : HoldsAt c I n σ p b') :
    HoldsAt c I n σ (.not p) (!b') := by
  intro vars P tbl e S hlenN hok hbd hP hr hk hS a ha
  subst hlenN
  rw [Semantics.condOK] at hok
  rw [Cond.boundConf] at hbd
  have hk' : ∀ k ∈ KoreAML.varsOf (Cond.kore c (canonVars c vars) (srtOf c S) p), k ∈ tbl := fun k hk0 =>
    hk k (by rw [Cond.kore, KoreAML.varsOf]; exact List.mem_append_right _ hk0)
  have := ih rfl hok hbd (fun i hi hl => hP i (by rw [varOccsCond]; exact hi) hl) hr hk' hS a ha
  rw [Cond.kore, KoreAML.tr, KoreAML.interp_sNot, this]
  cases b' <;> simp [ha]

theorem holdsAt_and {n : Nat} {σ : Subst} {p q : Cond} {b1 b2 : Bool} (ihp : HoldsAt c I n σ p b1)
    (ihq : HoldsAt c I n σ q b2) : HoldsAt c I n σ (.and p q) (b1 && b2) := by
  intro vars P tbl e S hlenN hok hbd hP hr hk hS a ha
  subst hlenN
  rw [Semantics.condOK, Bool.and_eq_true] at hok
  rw [Cond.boundConf, Bool.and_eq_true] at hbd
  have hkp : ∀ k ∈ KoreAML.varsOf (Cond.kore c (canonVars c vars) (srtOf c S) p), k ∈ tbl := fun k hk0 =>
    hk k (by rw [Cond.kore, KoreAML.varsOf, KoreAML.varsOfList]
             exact List.mem_append_right _ (List.mem_append_left _ hk0))
  have hkq : ∀ k ∈ KoreAML.varsOf (Cond.kore c (canonVars c vars) (srtOf c S) q), k ∈ tbl := fun k hk0 =>
    hk k (by rw [Cond.kore, KoreAML.varsOf, KoreAML.varsOfList, KoreAML.varsOfList]
             exact List.mem_append_right _ (List.mem_append_right _ (List.mem_append_left _ hk0)))
  have h1 := ihp rfl hok.1 hbd.1 (fun i hi hl => hP i (by rw [varOccsCond]; exact List.mem_append_left _ hi) hl)
    hr hkp hS a ha
  have h2 := ihq rfl hok.2 hbd.2 (fun i hi hl => hP i (by rw [varOccsCond]; exact List.mem_append_right _ hi) hl)
    hr hkq hS a ha
  rw [Cond.kore, tr_and2, KoreAML.interp_sAnd, h1, h2]
  cases b1 <;> cases b2 <;> simp

theorem holdsAt_or {n : Nat} {σ : Subst} {p q : Cond} {b1 b2 : Bool} (ihp : HoldsAt c I n σ p b1)
    (ihq : HoldsAt c I n σ q b2) : HoldsAt c I n σ (.or p q) (b1 || b2) := by
  intro vars P tbl e S hlenN hok hbd hP hr hk hS a ha
  subst hlenN
  rw [Semantics.condOK, Bool.and_eq_true] at hok
  rw [Cond.boundConf, Bool.and_eq_true] at hbd
  have hkp : ∀ k ∈ KoreAML.varsOf (Cond.kore c (canonVars c vars) (srtOf c S) p), k ∈ tbl := fun k hk0 =>
    hk k (by rw [Cond.kore, KoreAML.varsOf, KoreAML.varsOfList]
             exact List.mem_append_right _ (List.mem_append_left _ hk0))
  have hkq : ∀ k ∈ KoreAML.varsOf (Cond.kore c (canonVars c vars) (srtOf c S) q), k ∈ tbl := fun k hk0 =>
    hk k (by rw [Cond.kore, KoreAML.varsOf, KoreAML.varsOfList, KoreAML.varsOfList]
             exact List.mem_append_right _ (List.mem_append_right _ (List.mem_append_left _ hk0)))
  have h1 := ihp rfl hok.1 hbd.1 (fun i hi hl => hP i (by rw [varOccsCond]; exact List.mem_append_left _ hi) hl)
    hr hkp hS a ha
  have h2 := ihq rfl hok.2 hbd.2 (fun i hi hl => hP i (by rw [varOccsCond]; exact List.mem_append_right _ hi) hl)
    hr hkq hS a ha
  rw [Cond.kore, Model.tr_or2Stdi, KoreAML.interp_sOr, h1, h2]
  cases b1 <;> cases b2 <;> simp [ha]

theorem holdsAt_implies {n : Nat} {σ : Subst} {p q : Cond} {b1 b2 : Bool} (ihp : HoldsAt c I n σ p b1)
    (ihq : HoldsAt c I n σ q b2) : HoldsAt c I n σ (.implies p q) (!b1 || b2) := by
  intro vars P tbl e S hlenN hok hbd hP hr hk hS a ha
  subst hlenN
  rw [Semantics.condOK, Bool.and_eq_true] at hok
  rw [Cond.boundConf, Bool.and_eq_true] at hbd
  have hkp : ∀ k ∈ KoreAML.varsOf (Cond.kore c (canonVars c vars) (srtOf c S) p), k ∈ tbl := fun k hk0 =>
    hk k (by rw [Cond.kore, KoreAML.varsOf]
             exact List.mem_append_left _ (List.mem_append_right _ hk0))
  have hkq : ∀ k ∈ KoreAML.varsOf (Cond.kore c (canonVars c vars) (srtOf c S) q), k ∈ tbl := fun k hk0 =>
    hk k (by rw [Cond.kore, KoreAML.varsOf]; exact List.mem_append_right _ hk0)
  have h1 := ihp rfl hok.1 hbd.1 (fun i hi hl => hP i (by rw [varOccsCond]; exact List.mem_append_left _ hi) hl)
    hr hkp hS a ha
  have h2 := ihq rfl hok.2 hbd.2 (fun i hi hl => hP i (by rw [varOccsCond]; exact List.mem_append_right _ hi) hl)
    hr hkq hS a ha
  rw [Cond.kore, KoreAML.tr, KoreAML.interp_sImp, h1, h2]
  cases b1 <;> cases b2 <;> simp [ha]

/-- **`ceil`**, from the reading of its term's evaluation. -/
theorem holdsAt_ceil (F : NodeFacts c I) {n : Nat} {σ : Subst} {s : Srt} {t : Term} {r : Option GroundTerm}
    (hev : EvalTerm c σ t r) (hT : TermAt c I σ t r) : HoldsAt c I n σ (.ceil s t) r.isSome := by
  intro vars P tbl e S hlenN hok _ hP hr _ hS a ha
  subst hlenN
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
  have hread := hT hPt hr hok
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

/-- A term of a condition, read: its sort is numbered; the term denotes what a result whose
evaluation is read denotes, and a result that is a value is of the term's sort. -/
theorem term_readN (F : NodeFacts c I) {vars : List Srt} {P : Nat → Prop} {σ : Subst} {tbl : KoreAML.VarTable}
    {e : Valuation M} (hr : Reads c I vars P σ tbl e) {t : Term} {s : Srt}
    (ht : sortOfTerm (c.rhsCtx (c.fns.map Fn.sig)) vars t = some s) (hP : ∀ i ∈ varOccs t, P i) :
    s < nRegSorts + c.sortNames.length ∧
      ∀ r, EvalTerm c σ t r → TermAt c I σ t r →
        (∀ m, (KoreAML.tr ⟨tbl, []⟩ (Term.kore c (canonVars c vars) t)).interpret I e m ↔ Res c I e r m) ∧
        ∀ w, r = some w → c.sortOf w = some s := by
  have hsat : c.WellSortedAt vars (varOccs t) σ := by
    intro i hi s' hs'
    obtain ⟨-, -, v, hv, hsv, -⟩ := hr i (hP i hi)
    refine ⟨v, hv, ?_⟩
    rw [hsv, List.getD_eq_getElem?_getD, hs']; rfl
  refine ⟨F.termNum ht fun i hi s' hs' => ?_, fun r hev hT => ⟨hT hP hr ht,
    fun w hw => EvalTerm.sorted_at F.sortCtx hev fns_headsOK hsat ht hw⟩⟩
  obtain ⟨-, -, v, -, hsv, -⟩ := hr i (hP i hi)
  have : vars.getD i 0 = s' := by rw [List.getD_eq_getElem?_getD, hs']; rfl
  rw [this] at hsv
  exact F.valNum hsv

/-- **`equals`**, from the readings of its terms' evaluations. -/
theorem holdsAt_equals (F : NodeFacts c I) {n : Nat} {σ : Subst} {s : Srt} {t u : Term} {r r' : Option GroundTerm}
    (hev : EvalTerm c σ t r) (hT : TermAt c I σ t r) (hev' : EvalTerm c σ u r') (hT' : TermAt c I σ u r') :
    HoldsAt c I n σ (.equals s t u) (sameResult r r') := by
  intro vars P tbl e S hlenN hok _ hP hr _ hS a ha
  subst hlenN
  rw [Semantics.condOK] at hok; replace hok := ((Bool.and_eq_true _ _).mp hok).1; rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at hok
  have hPt : ∀ i ∈ varOccs t, P i := fun i hi =>
    hP i (by rw [varOccsCond]; exact List.mem_append_left _ hi) (varOccs_lt t hok.1 i hi)
  have hPu : ∀ i ∈ varOccs u, P i := fun i hi =>
    hP i (by rw [varOccsCond]; exact List.mem_append_right _ hi) (varOccs_lt u hok.2 i hi)
  obtain ⟨hs, hrt⟩ := term_readN F hr hok.1 hPt
  obtain ⟨-, hru⟩ := term_readN F hr hok.2 hPu
  obtain ⟨τ, hτ, hτd⟩ := F.sort hs
  obtain ⟨τS, hτS, hτSd⟩ := F.sort hS
  have haS : KoreAML.Inh I τS a := (KoreAML.interp_inhOf_of (hτSd tbl e)).mp ha
  have elt : ∀ {w : GroundTerm}, c.sortOf w = some s → ∃ a0, (∀ m, (den c w).interpret I e m ↔ m = a0) ∧
      KoreAML.Inh I τ a0 := fun hw => by
    obtain ⟨a0, ha0, hin⟩ := F.val hw tbl e
    exact ⟨a0, ha0, (KoreAML.interp_inhOf_of (hτd tbl e)).mp hin⟩
  obtain ⟨hreadt, hsortt⟩ := hrt r hev hT
  obtain ⟨hreadu, hsortu⟩ := hru r' hev' hT'
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

/-- **`mem`**, from the readings of its terms' evaluations. -/
theorem holdsAt_mem (F : NodeFacts c I) {n : Nat} {σ : Subst} {s : Srt} {t u : Term} {r r' : Option GroundTerm}
    (hev : EvalTerm c σ t r) (hT : TermAt c I σ t r) (hev' : EvalTerm c σ u r') (hT' : TermAt c I σ u r') :
    HoldsAt c I n σ (.mem s t u) (r.isSome && sameResult r r') := by
  intro vars P tbl e S hlenN hok _ hP hr _ hS a ha
  subst hlenN
  rw [Semantics.condOK] at hok; replace hok := ((Bool.and_eq_true _ _).mp hok).1; rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at hok
  have hPt : ∀ i ∈ varOccs t, P i := fun i hi =>
    hP i (by rw [varOccsCond]; exact List.mem_append_left _ hi) (varOccs_lt t hok.1 i hi)
  have hPu : ∀ i ∈ varOccs u, P i := fun i hi =>
    hP i (by rw [varOccsCond]; exact List.mem_append_right _ hi) (varOccs_lt u hok.2 i hi)
  obtain ⟨hs, hrt⟩ := term_readN F hr hok.1 hPt
  obtain ⟨-, hru⟩ := term_readN F hr hok.2 hPu
  obtain ⟨τ, hτ, hτd⟩ := F.sort hs
  obtain ⟨τS, hτS, hτSd⟩ := F.sort hS
  have haS : KoreAML.Inh I τS a := (KoreAML.interp_inhOf_of (hτSd tbl e)).mp ha
  have elt : ∀ {w : GroundTerm}, c.sortOf w = some s → ∃ a0, (∀ m, (den c w).interpret I e m ↔ m = a0) ∧
      KoreAML.Inh I τ a0 := fun hw => by
    obtain ⟨a0, ha0, hin⟩ := F.val hw tbl e
    exact ⟨a0, ha0, (KoreAML.interp_inhOf_of (hτd tbl e)).mp hin⟩
  obtain ⟨hreadt, hsortt⟩ := hrt r hev hT
  obtain ⟨hreadu, hsortu⟩ := hru r' hev' hT'
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

/-- **`ex`**, from the readings of its body at the extensions of σ. -/
theorem holdsAt_ex (F : NodeFacts c I) (G : BinderFacts c I) {n : Nat} {σ : Subst} {s : Srt} {body : Cond} {b : Bool}
    (g : Subst → Bool) (ih : ∀ σ', Extends c n [s] σ σ' → HoldsAt c I (n + 1) σ' body (g σ'))
    (hr' : b = true ↔ ∃ σ', Extends c n [s] σ σ' ∧ g σ' = true) : HoldsAt c I n σ (.ex s body) b := by
  intro vars P tbl e S hlenN hok hbd hP hr hk hS a ha
  subst hlenN
  rw [Semantics.condOK] at hok
  rw [Cond.boundConf, Bool.and_eq_true] at hbd
  replace hbd : ElemsValues c I s ∧ Cond.boundConf c (vars.length + 1) body = true := ⟨G.elemsValues hbd.1, hbd.2⟩
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
      c.sortOf v = some s → (∀ m, (den c v).interpret I e m ↔ m = a0) → Extends c vars.length [s] σ σ' →
      ((KoreAML.tr ⟨tbl, []⟩ (Cond.kore c (canonVars c (vars ++ [s])) (srtOf c S) body)).interpret I
        ⟨Function.update e.evalEvar (tbl.ev K) a0, e.evalSvar⟩ a ↔ g σ' = true) := by
    intro σ' v a0 hσ' hn hv hd hx
    exact ih σ' hx hlen hok (by rw [hlen]; exact hbd.2) hPB (hr.snoc hK hσ' hn hv hd) hkB hS
      a ((KoreAML.interp_inhOf_of (hτSd tbl _)).mpr
        ((KoreAML.interp_inhOf_of (hτSd tbl e)).mp ha))
  have hsrt : ∀ (e' : Valuation M) m,
      (KoreAML.inhOf (KoreAML.trSort tbl (Cond.binder c (canonVars c vars).length s).kore.sort)).interpret I e' m ↔
        KoreAML.Inh I τ m := fun e' m => by
    show (KoreAML.inhOf (KoreAML.trSort tbl (srtOf c s))).interpret _ _ m ↔ _
    exact KoreAML.interp_inhOf_of (hτd tbl e')
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
    exact hr'.mpr ⟨_, hext, (hread _ v m hσ'' (Model.extOneStdI_at σ _ v) hv hdv hext).mp hbody⟩
  · intro hbt
    obtain ⟨σ', hext, hg⟩ := hr'.mp hbt
    obtain ⟨v, hv, hsv⟩ := hext.2 0 s rfl
    rw [Nat.add_zero] at hv
    obtain ⟨a0, ha0, hin⟩ := F.val hsv tbl e
    exact ⟨a0, (KoreAML.interp_inhOf_of (hτd tbl e)).mp hin, (hread σ' v a0 hext.1 hv hsv ha0 hext).mpr hg⟩

/-- **`all`**, from the readings of its body at the extensions of σ. -/
theorem holdsAt_all (F : NodeFacts c I) (G : BinderFacts c I) {n : Nat} {σ : Subst} {s : Srt} {body : Cond} {b : Bool}
    (g : Subst → Bool) (ih : ∀ σ', Extends c n [s] σ σ' → HoldsAt c I (n + 1) σ' body (g σ'))
    (hr' : b = true ↔ ∀ σ', Extends c n [s] σ σ' → g σ' = true) : HoldsAt c I n σ (.all s body) b := by
  intro vars P tbl e S hlenN hok hbd hP hr hk hS a ha
  subst hlenN
  rw [Semantics.condOK] at hok
  rw [Cond.boundConf, Bool.and_eq_true] at hbd
  replace hbd : ElemsValues c I s ∧ Cond.boundConf c (vars.length + 1) body = true := ⟨G.elemsValues hbd.1, hbd.2⟩
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
      c.sortOf v = some s → (∀ m, (den c v).interpret I e m ↔ m = a0) → Extends c vars.length [s] σ σ' →
      ((KoreAML.tr ⟨tbl, []⟩ (Cond.kore c (canonVars c (vars ++ [s])) (srtOf c S) body)).interpret I
        ⟨Function.update e.evalEvar (tbl.ev K) a0, e.evalSvar⟩ a ↔ g σ' = true) := by
    intro σ' v a0 hσ' hn hv hd hx
    exact ih σ' hx hlen hok (by rw [hlen]; exact hbd.2) hPB (hr.snoc hK hσ' hn hv hd) hkB hS
      a ((KoreAML.interp_inhOf_of (hτSd tbl _)).mpr
        ((KoreAML.interp_inhOf_of (hτSd tbl e)).mp ha))
  have hsrt : ∀ (e' : Valuation M) m,
      (KoreAML.inhOf (KoreAML.trSort tbl (Cond.binder c (canonVars c vars).length s).kore.sort)).interpret I e' m ↔
        KoreAML.Inh I τ m := fun e' m => by
    show (KoreAML.inhOf (KoreAML.trSort tbl (srtOf c s))).interpret _ _ m ↔ _
    exact KoreAML.interp_inhOf_of (hτd tbl e')
  have hinS : ∀ e' : Valuation M, (KoreAML.inhOf (KoreAML.trSort tbl (srtOf c S))).interpret I e' a :=
    fun e' => (KoreAML.interp_inhOf_of (hτSd tbl e')).mpr ((KoreAML.interp_inhOf_of (hτSd tbl e)).mp ha)
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
    exact (hread σ' v a0 hext.1 hv hsv ha0 hext).mp
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
    exact (hread _ v m hσ'' (Model.extOneStdI_at σ _ v) hv hdv hext).mpr (hr'.mp hbt _ hext)

/-- **`exMatch`**, from the reading of its term's evaluation and, where the term has a value,
the readings of its body at the extensions of σ under which the pattern denotes the value. -/
theorem holdsAt_exMatch (F : NodeFacts c I) (G : BinderFacts c I) {n : Nat} {σ : Subst} {ys : List Srt} {s : Srt}
    {p t : Term} {body : Cond} {r : Option GroundTerm} {b : Bool}
    (hev : EvalTerm c σ t r) (hT : TermAt c I σ t r)
    (hh : (r = none ∧ b = false) ∨ ∃ (v : GroundTerm) (g : Subst → Bool), r = some v ∧
      (∀ σ', Extends c n ys σ σ' → PatVal c σ' p v → HoldsAt c I (n + ys.length) σ' body (g σ')) ∧
      (b = true ↔ ∃ σ', Extends c n ys σ σ' ∧ PatVal c σ' p v ∧ g σ' = true)) :
    HoldsAt c I n σ (.exMatch ys s p t body) b := by
  intro vars P tbl e S hlenN hok hbd hP hr hk hS a ha
  subst hlenN
  simp only [Semantics.condOK, Bool.and_eq_true, beq_iff_eq] at hok
  obtain ⟨⟨⟨hpS, htS⟩, hokB⟩, -⟩ := hok
  rw [Cond.boundConf, Bool.and_eq_true] at hbd
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
  obtain ⟨hs, -⟩ := term_readN F hr htS hPt
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
  have hread : ∀ (e' : Valuation M) (r : Option GroundTerm), EvalTerm c σ t r → TermAt c I σ t r →
      (∀ i, P i → e'.evalEvar (tbl.ev (canonKey c vars i)) = e.evalEvar (tbl.ev (canonKey c vars i))) →
      ((KoreAML.tr ⟨tbl, []⟩ (.and (srtOf c S)
        [.in (srtOf c s) (srtOf c S) (Term.kore c (canonVars c vars) t) (Term.kore c (canonVars c (vars ++ ys)) p),
         Cond.kore c (canonVars c (vars ++ ys)) (srtOf c S) body])).interpret I e' a ↔
        (∃ m, Res c I e' r m ∧ (KoreAML.tr ⟨tbl, []⟩ (Term.kore c (canonVars c (vars ++ ys)) p)).interpret I e' m) ∧
          (KoreAML.tr ⟨tbl, []⟩ (Cond.kore c (canonVars c (vars ++ ys)) (srtOf c S) body)).interpret I e' a) := by
    intro e' r hev hT' hoff
    have hrt : Reads c I vars P σ tbl e' := fun i hi => by
      obtain ⟨a1, a2, v, a3, a4, a5⟩ := hr i hi
      exact ⟨a1, a2, v, a3, a4, fun m => by rw [hoff i hi]; exact (a5 m).trans ((den_closed c v).interp _ _ m)⟩
    obtain ⟨-, hrd⟩ := term_readN F hrt htS hPt
    obtain ⟨hreadt, hsortt⟩ := hrd r hev hT'
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
  rcases hh with ⟨rfl, rfl⟩ | ⟨v, g, rfl, hb, hr'⟩
  · skip
    refine ⟨fun hm => ?_, fun hf => by cases hf⟩
    obtain ⟨e', hoff, -, hb⟩ := existsAll_elim F.defOK Bs e a hnd hsrt hm
    have hoffP : ∀ i, P i → e'.evalEvar (tbl.ev (canonKey c vars i)) = e.evalEvar (tbl.ev (canonKey c vars i)) :=
      fun i hi => hoff _ fun b hb' he => by
        obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hb'
        obtain ⟨hj1, hj2⟩ := List.mem_range'_1.mp hj
        exact hne i hi j hj1 hj2 he
    obtain ⟨⟨m, hm, -⟩, -⟩ := (hread e' none hev hT hoffP).mp hb
    exact hm.elim
  · skip
    obtain ⟨-, hrd⟩ := term_readN F hr htS hPt
    have hsv : c.sortOf v = some s := (hrd _ hev hT).2 v rfl
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
      obtain ⟨⟨m, hmv, hpm⟩, hbodym⟩ := (hread e' (some v) hev hT hoffP).mp hbm
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
        (hb σE hext hpvE hlen hokB (by rw [hlen]; exact hbdB) hPB hrE hkB hS a (haS e')).mp hbodym⟩
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
        refine (G.pat hpS hsv (fun i hi => ⟨(hr'' i (hPp i hi)).2.1, Reads.inSortN F hr'' (hPp i hi)⟩) m0
          ((hm0 m0).mpr rfl)).mpr ⟨σ', hpv, fun i hi => ?_⟩
        obtain ⟨-, -, u, hu, hsu, hdu⟩ := hr'' i (hPp i hi)
        exact ⟨u, hu, hsu, fun m' => (hdu m').symm⟩
      refine existsAll_intro_at F.defOK _ e e' a hnd hsrt (fun z hz => ?_) rfl (fun b hb' k hk => ?_)
        ((hread e' (some v) hev hT hoffP).mpr ⟨⟨m0, (hm0 m0).mpr rfl, hpm⟩,
          (hb σ' hext hpv hlen hokB (by rw [hlen]; exact hbdB) hPB hr'' hkB hS a (haS e')).mpr hg⟩)
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

/-- **A term's evaluation is read where its translation denotes its result at every valuation
that agrees with σ on the term's variables, σ well sorted on them** (the form a recursion on
evaluations concludes): a valuation that reads the term's variables gives both. -/
theorem termAt_of_all (hI : I ⊧ᴵP Γ c) {σ : Subst} {t : Term} {r : Option GroundTerm}
    (h : ∀ {vars : List Srt} {tbl : KoreAML.VarTable} {e : Valuation M} {s : Srt},
      c.WellSortedAt vars (varOccs t) σ → AgreesOn c I tbl (canonVars c vars) (varOccs t) σ e →
      sortOfTerm (c.rhsCtx (c.fns.map Fn.sig)) vars t = some s →
      ∀ m, (KoreAML.tr ⟨tbl, []⟩ (Term.kore c (canonVars c vars) t)).interpret I e m ↔ Res c I e r m) :
    TermAt c I σ t r := by
  intro vars P tbl e s hP hr ht m
  refine h (fun i hi s' hs' => ?_) (fun i hi v _ hl m' => ?_) ht m
  · obtain ⟨-, -, v, hv, hsv, -⟩ := hr i (hP i hi)
    exact ⟨v, hv, by rw [hsv, List.getD_eq_getElem?_getD, hs']; rfl⟩
  · obtain ⟨-, -, w, hw, -, hd⟩ := hr i (hP i hi)
    rw [hl] at hw; cases hw
    exact hd m'

/-- A valuation that reads variables as their values under σ reads them as their values under a σ'
that gives them the same values. -/
theorem Reads.congr_occ {vars : List Srt} {P : Nat → Prop} {σ σ' : Subst} {tbl : KoreAML.VarTable}
    {e : Valuation M} (hr : Reads c I vars P σ tbl e) (hag : ∀ i, P i → σ'.lookup i = σ.lookup i) :
    Reads c I vars P σ' tbl e := fun i hi => by
  rw [hag i hi]; exact hr i hi

/-- A valuation that reads the variables P reads those of a part of P. -/
theorem Reads.mono_occ {vars : List Srt} {P Q : Nat → Prop} {σ : Subst} {tbl : KoreAML.VarTable}
    {e : Valuation M} (hr : Reads c I vars P σ tbl e) (hQ : ∀ i, Q i → P i) : Reads c I vars Q σ tbl e :=
  fun i hi => hr i (hQ i hi)

/-- **A term's reading depends on σ at the term's variables only.** -/
theorem TermAt.congr_occ {σ σ' : Subst} {t : Term} {r : Option GroundTerm} (hT : TermAt c I σ t r)
    (hag : ∀ i ∈ varOccs t, σ'.lookup i = σ.lookup i) : TermAt c I σ' t r := by
  intro vars P tbl e s hP hr ht m
  exact hT (P := fun i => i ∈ varOccs t) (fun i hi => hi)
    ((hr.mono_occ fun i hi => hP i hi).congr_occ fun i hi => (hag i hi).symm) ht m

/-- **A condition's reading depends on σ at the condition's variables in scope only.** -/
theorem HoldsAt.congr_occ {bd : Nat → Cond → Bool} {n : Nat} {σ σ' : Subst} {p : Cond} {b : Bool}
    (hH : HoldsAtB bd c I n σ p b)
    (hag : ∀ i ∈ varOccsCond n p, i < n → σ'.lookup i = σ.lookup i) : HoldsAtB bd c I n σ' p b := by
  intro vars P tbl e S hlenN hok hbd hP hr hk hS a ha
  subst hlenN
  exact hH (P := fun i => i ∈ varOccsCond vars.length p ∧ i < vars.length) rfl hok hbd (fun i hi hl => ⟨hi, hl⟩)
    ((hr.mono_occ fun i hi => hP i hi.1 hi.2).congr_occ fun i hi => (hag i hi.1 hi.2).symm) hk hS a ha

end Node

end HoldsShape

end KCore
