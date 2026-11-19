/-
  KCore. The truth the value model gives a condition, decided or not.

  `Holds c n σ p b` is the evaluation's truth value of a condition: an atom reads the *result* of
  its terms, and a condition whose terms have no result has no truth value. The value model reads
  every condition: an atom reads the *values* of its terms, `{v | EvalTerm c σ t (some v)}`, and a
  term without a value (no result, or the result `none`) is the empty set, as `AtT.tr_term` reads it.
  `TrueV c n σ p` is that reading, a total one: `⌈t⌉` is "t has a value", `t = u` is "t and u have
  the same values", `t ∈ u` is "t and u have a common value", a match "t has a value the pattern
  matches under values of the binders' sorts, and the body holds there", and a sort binder ranges
  over the values of its sort (`Extends`).

  `holds_trueV`: where `Holds` gives a truth value, under `FnDet`, `TrueV` is that value.
  `trueV_stdI`: in the value model at every T, an element of a numbered predicate sort is in
  `Cond.kore p` exactly where `TrueV` holds; it is `holds_stdI`'s statement without the hypothesis
  that p has a truth value. Each case of it is proved for every interpretation with the facts the
  Holds lemma reads (`AtomFacts`, `BinderFacts`) and one more, `TermDenAt`: a term denotes the
  elements of its values, without a result in hand. The value model has it (`AtT.tr_term`).
  `holds_stdI_of_trueV` is `holds_stdI` again, from the two.
-/
import KcoreSpec.HoldsModel

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace KCore

/-- **The truth the value model gives a condition at σ**, with n variables in scope: an atom reads
the values its terms have under σ (none where a term has no result or the result `none`), a binder
ranges over the values of its sort. -/
def TrueV (c : Semantics) : Nat → Subst → Cond → Prop
  | _, _, .top => True
  | _, _, .bot => False
  | n, σ, .not p => ¬ TrueV c n σ p
  | n, σ, .and p q => TrueV c n σ p ∧ TrueV c n σ q
  | n, σ, .or p q => TrueV c n σ p ∨ TrueV c n σ q
  | n, σ, .implies p q => TrueV c n σ p → TrueV c n σ q
  | _, σ, .ceil _ t => ∃ v, EvalTerm c σ t (some v)
  | _, σ, .equals _ t u => ∀ v, EvalTerm c σ t (some v) ↔ EvalTerm c σ u (some v)
  | _, σ, .mem _ t u => ∃ v, EvalTerm c σ t (some v) ∧ EvalTerm c σ u (some v)
  | n, σ, .exMatch ys _ p t body => ∃ v σ', EvalTerm c σ t (some v) ∧ Extends c n ys σ σ' ∧
      PatVal c σ' p v ∧ TrueV c (n + ys.length) σ' body
  | n, σ, .ex s body => ∃ σ', Extends c n [s] σ σ' ∧ TrueV c (n + 1) σ' body
  | n, σ, .all s body => ∀ σ', Extends c n [s] σ σ' → TrueV c (n + 1) σ' body

/-- Under `FnDet`, the values of a term with a result are that result's. -/
theorem evalTerm_some_iff {c : Semantics} (hd : FnDet c) {σ : Subst} {t : Term} {r : Option GroundTerm}
    (h : EvalTerm c σ t r) (v : GroundTerm) : EvalTerm c σ t (some v) ↔ r = some v :=
  ⟨fun hv => EvalTerm.functional_of_fnDet hd h hv, fun he => he ▸ h⟩

/-- **(I1) Where `Holds` has a truth value, the value model's truth is that value**, under `FnDet`
(a term has at most one result, so its values are its result's). By structural recursion on
the derivation of `Holds` (no recursor of `Holds` is named, so the proof does not depend on which
mutual block `Holds` is declared in): a binder's case calls the theorem at each premise `hb σ' …`. -/
theorem holds_trueV {c : Semantics} (hd : FnDet c) {n : Nat} {σ : Subst} {p : Cond} {b : Bool}
    (h : Holds c n σ p b) : TrueV c n σ p ↔ b = true :=
  match n, σ, p, b, h with
  | _, _, _, _, .top => by
    exact ⟨fun _ => rfl, fun _ => trivial⟩
  | _, _, _, _, .bot => by
    exact ⟨fun hf => (hf : False).elim, fun hf => by cases hf⟩
  | _, _, _, _, @Holds.not _ n σ p b h => by
    have ih := holds_trueV hd h
    show ¬ TrueV c n σ p ↔ _
    rw [ih]; cases b <;> simp
  | _, _, _, _, @Holds.and _ n σ p q b b' h h' => by
    have ih := holds_trueV hd h
    have ih' := holds_trueV hd h'
    show TrueV c n σ p ∧ TrueV c n σ q ↔ _
    rw [ih, ih']; cases b <;> cases b' <;> simp
  | _, _, _, _, @Holds.or _ n σ p q b b' h h' => by
    have ih := holds_trueV hd h
    have ih' := holds_trueV hd h'
    show TrueV c n σ p ∨ TrueV c n σ q ↔ _
    rw [ih, ih']; cases b <;> cases b' <;> simp
  | _, _, _, _, @Holds.implies _ n σ p q b b' h h' => by
    have ih := holds_trueV hd h
    have ih' := holds_trueV hd h'
    show (TrueV c n σ p → TrueV c n σ q) ↔ _
    rw [ih, ih']; cases b <;> cases b' <;> simp
  | _, _, _, _, @Holds.ceil _ n σ s t r h => by
    show (∃ v, EvalTerm c σ t (some v)) ↔ _
    simp only [evalTerm_some_iff hd h]
    cases r <;> simp
  | _, _, _, _, @Holds.equals _ n σ s t u r r' h h' => by
    show (∀ v, EvalTerm c σ t (some v) ↔ EvalTerm c σ u (some v)) ↔ _
    simp only [evalTerm_some_iff hd h, evalTerm_some_iff hd h']
    cases r with
    | none =>
      cases r' with
      | none => simp [sameResult]
      | some w =>
        exact ⟨fun hh => absurd ((hh w).mpr rfl) (by simp), fun hf => by simp [sameResult] at hf⟩
    | some v =>
      cases r' with
      | none =>
        exact ⟨fun hh => absurd ((hh v).mp rfl) (by simp), fun hf => by simp [sameResult] at hf⟩
      | some w =>
        simp only [sameResult, beq_iff_eq, cmp_eq_iff]
        constructor
        · intro hh
          exact (Option.some.inj ((hh v).mp rfl)).symm
        · rintro rfl
          exact fun _ => Iff.rfl
  | _, _, _, _, @Holds.mem _ n σ s t u r r' h h' => by
    show (∃ v, EvalTerm c σ t (some v) ∧ EvalTerm c σ u (some v)) ↔ _
    simp only [evalTerm_some_iff hd h, evalTerm_some_iff hd h']
    cases r with
    | none => simp
    | some v =>
      cases r' with
      | none => simp [sameResult]
      | some w =>
        simp only [Option.isSome_some, sameResult, Bool.true_and, beq_iff_eq, cmp_eq_iff]
        constructor
        · rintro ⟨x, h1, h2⟩
          cases h1; cases h2; rfl
        · rintro rfl
          exact ⟨v, rfl, rfl⟩
  | _, _, _, _, @Holds.exNone _ n σ ys s p t body h => by
    show (∃ v σ', EvalTerm c σ t (some v) ∧ _) ↔ _
    constructor
    · rintro ⟨v, σ', hv, -⟩
      cases EvalTerm.functional_of_fnDet hd h hv
    · intro hf; cases hf
  | _, _, _, _, @Holds.exSome _ n σ ys s p t body v b g h hb hr => by
    have ih := fun σ' hx hm => holds_trueV hd (hb σ' hx hm)
    show (∃ v' σ', EvalTerm c σ t (some v') ∧ Extends c n ys σ σ' ∧ PatVal c σ' p v' ∧
      TrueV c (n + ys.length) σ' body) ↔ _
    rw [hr]
    constructor
    · rintro ⟨v', σ', hv', hext, hpv, ht⟩
      cases EvalTerm.functional_of_fnDet hd h hv'
      exact ⟨σ', hext, hpv, (ih σ' hext hpv).mp ht⟩
    · rintro ⟨σ', hext, hpv, hg⟩
      exact ⟨v, σ', h, hext, hpv, (ih σ' hext hpv).mpr hg⟩
  | _, _, _, _, @Holds.ex _ n σ s body b g hb hr => by
    have ih := fun σ' hx => holds_trueV hd (hb σ' hx)
    show (∃ σ', Extends c n [s] σ σ' ∧ TrueV c (n + 1) σ' body) ↔ _
    rw [hr]
    exact ⟨fun ⟨σ', he, ht⟩ => ⟨σ', he, (ih σ' he).mp ht⟩, fun ⟨σ', he, hg⟩ => ⟨σ', he, (ih σ' he).mpr hg⟩⟩
  | _, _, _, _, @Holds.all _ n σ s body b g hb hr => by
    have ih := fun σ' hx => holds_trueV hd (hb σ' hx)
    show (∀ σ', Extends c n [s] σ σ' → TrueV c (n + 1) σ' body) ↔ _
    rw [hr]
    exact ⟨fun ht σ' he => (ih σ' he).mp (ht σ' he), fun hg σ' he => (ih σ' he).mpr (hg σ' he)⟩

open ML Faithful

namespace HoldsShape

section TrueShape
variable {c : Semantics} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}

/-- **A term denotes the elements of its values**, over the variables it reads: with no result in
hand (`TermSoundAt` reads one), the elements of the values `EvalTerm` gives it, none where it has
none. -/
def TermDenAt (c : Semantics) {M : Type} (I : Interpretation KoreAML.Sym M) : Prop :=
  ∀ {σ : Subst} {t : Term} {vars : List Srt} {P : Nat → Prop} {tbl : KoreAML.VarTable} {e : Valuation M}
    {s : Srt}, (∀ i ∈ varOccs t, P i) → Reads c I vars P σ tbl e →
    sortOfTerm (c.rhsCtx (c.fns.map Fn.sig)) vars t = some s →
    ∀ m, (KoreAML.tr ⟨tbl, []⟩ (Term.kore c (canonVars c vars) t)).interpret I e m ↔
      ∃ v, EvalTerm c σ t (some v) ∧ (den c v).interpret I e m

/-- The reading of a condition in I as `TrueV` where the Bool `bd` bounds its binders:
`HoldsDenB`'s statement without a `Holds` derivation, `TrueV` on the right. -/
def TrueDenB (bd : Nat → Cond → Bool) (c : Semantics) {M : Type} (I : Interpretation KoreAML.Sym M) (p : Cond) :
    Prop :=
  ∀ {vars : List Srt} {P : Nat → Prop} {σ : Subst} {tbl : KoreAML.VarTable} {e : Valuation M} {S : Srt},
    c.condOK vars p = true → bd vars.length p = true →
    (∀ i ∈ varOccsCond vars.length p, i < vars.length → P i) → Reads c I vars P σ tbl e →
    (∀ k ∈ KoreAML.varsOf (Cond.kore c (canonVars c vars) (srtOf c S) p), k ∈ tbl) →
    S < nRegSorts + c.sortNames.length →
    ∀ a, (KoreAML.inhOf (KoreAML.trSort tbl (srtOf c S))).interpret I e a →
      ((KoreAML.tr ⟨tbl, []⟩ (Cond.kore c (canonVars c vars) (srtOf c S) p)).interpret I e a ↔
        TrueV c vars.length σ p)

/-- `TrueDenB` at `Cond.boundConf`: every binder of the condition is of a sort where values and
elements agree by the sort alone. -/
abbrev TrueDen (c : Semantics) {M : Type} (I : Interpretation KoreAML.Sym M) (p : Cond) : Prop :=
  TrueDenB (Cond.boundConf c) c I p

/-- A term of a condition, read without a result: its sort is numbered, it denotes the elements of
its values, and those are of its sort. -/
theorem term_readV (F : AtomFacts c I) (D : TermDenAt c I) {vars : List Srt} {P : Nat → Prop} {σ : Subst}
    {tbl : KoreAML.VarTable} {e : Valuation M} (hr : Reads c I vars P σ tbl e) {t : Term} {s : Srt}
    (ht : sortOfTerm (c.rhsCtx (c.fns.map Fn.sig)) vars t = some s) (hP : ∀ i ∈ varOccs t, P i) :
    s < nRegSorts + c.sortNames.length ∧
      (∀ m, (KoreAML.tr ⟨tbl, []⟩ (Term.kore c (canonVars c vars) t)).interpret I e m ↔
        ∃ v, EvalTerm c σ t (some v) ∧ (den c v).interpret I e m) ∧
      ∀ v, EvalTerm c σ t (some v) → c.sortOf v = some s := by
  obtain ⟨hs, hrd⟩ := term_read F hr ht hP
  exact ⟨hs, D hP hr ht, fun v hv => (hrd _ hv).2 v rfl⟩

/-! ### The connectives -/

theorem trueD_top (F : AtomFacts c I) : TrueDen c I .top := by
  intro vars P σ tbl e S _ _ _ _ _ _ a ha
  rw [Cond.kore, KoreAML.tr, KoreAML.interp_sTop F.defOK Model.srtOf_free_stdI]
  exact ⟨fun _ => trivial, fun _ => ha⟩

theorem trueD_bot (F : AtomFacts c I) : TrueDen c I .bot := by
  intro vars P σ tbl e S _ _ _ _ _ _ a ha
  rw [Cond.kore, KoreAML.tr]
  unfold KoreAML.sBot
  rw [KoreAML.interp_sNot, KoreAML.interp_sTop F.defOK Model.srtOf_free_stdI]
  exact ⟨fun hn => absurd ha hn.1, fun hf => (hf : False).elim⟩

theorem trueD_not {p : Cond} (ih : TrueDen c I p) : TrueDen c I (.not p) := by
  intro vars P σ tbl e S hok hbd hP hr hk hS a ha
  rw [Semantics.condOK] at hok
  rw [Cond.boundConf] at hbd
  have hk' : ∀ k ∈ KoreAML.varsOf (Cond.kore c (canonVars c vars) (srtOf c S) p), k ∈ tbl := fun k hk0 =>
    hk k (by rw [Cond.kore, KoreAML.varsOf]; exact List.mem_append_right _ hk0)
  have := ih hok hbd (fun i hi hl => hP i (by rw [varOccsCond]; exact hi) hl) hr hk' hS a ha
  rw [Cond.kore, KoreAML.tr, KoreAML.interp_sNot, this]
  exact ⟨fun h => h.1, fun h => ⟨h, ha⟩⟩

theorem trueD_and {p q : Cond} (ihp : TrueDen c I p) (ihq : TrueDen c I q) : TrueDen c I (.and p q) := by
  intro vars P σ tbl e S hok hbd hP hr hk hS a ha
  rw [Semantics.condOK, Bool.and_eq_true] at hok
  rw [Cond.boundConf, Bool.and_eq_true] at hbd
  have hkp : ∀ k ∈ KoreAML.varsOf (Cond.kore c (canonVars c vars) (srtOf c S) p), k ∈ tbl := fun k hk0 =>
    hk k (by rw [Cond.kore, KoreAML.varsOf, KoreAML.varsOfList]
             exact List.mem_append_right _ (List.mem_append_left _ hk0))
  have hkq : ∀ k ∈ KoreAML.varsOf (Cond.kore c (canonVars c vars) (srtOf c S) q), k ∈ tbl := fun k hk0 =>
    hk k (by rw [Cond.kore, KoreAML.varsOf, KoreAML.varsOfList, KoreAML.varsOfList]
             exact List.mem_append_right _ (List.mem_append_right _ (List.mem_append_left _ hk0)))
  have h1 := ihp hok.1 hbd.1 (fun i hi hl => hP i (by rw [varOccsCond]; exact List.mem_append_left _ hi) hl)
    hr hkp hS a ha
  have h2 := ihq hok.2 hbd.2 (fun i hi hl => hP i (by rw [varOccsCond]; exact List.mem_append_right _ hi) hl)
    hr hkq hS a ha
  rw [Cond.kore, tr_and2, KoreAML.interp_sAnd, h1, h2]
  exact Iff.rfl

theorem trueD_or {p q : Cond} (ihp : TrueDen c I p) (ihq : TrueDen c I q) : TrueDen c I (.or p q) := by
  intro vars P σ tbl e S hok hbd hP hr hk hS a ha
  rw [Semantics.condOK, Bool.and_eq_true] at hok
  rw [Cond.boundConf, Bool.and_eq_true] at hbd
  have hkp : ∀ k ∈ KoreAML.varsOf (Cond.kore c (canonVars c vars) (srtOf c S) p), k ∈ tbl := fun k hk0 =>
    hk k (by rw [Cond.kore, KoreAML.varsOf, KoreAML.varsOfList]
             exact List.mem_append_right _ (List.mem_append_left _ hk0))
  have hkq : ∀ k ∈ KoreAML.varsOf (Cond.kore c (canonVars c vars) (srtOf c S) q), k ∈ tbl := fun k hk0 =>
    hk k (by rw [Cond.kore, KoreAML.varsOf, KoreAML.varsOfList, KoreAML.varsOfList]
             exact List.mem_append_right _ (List.mem_append_right _ (List.mem_append_left _ hk0)))
  have h1 := ihp hok.1 hbd.1 (fun i hi hl => hP i (by rw [varOccsCond]; exact List.mem_append_left _ hi) hl)
    hr hkp hS a ha
  have h2 := ihq hok.2 hbd.2 (fun i hi hl => hP i (by rw [varOccsCond]; exact List.mem_append_right _ hi) hl)
    hr hkq hS a ha
  rw [Cond.kore, Model.tr_or2Stdi, KoreAML.interp_sOr, h1, h2]
  exact ⟨fun h => h.2, fun h => ⟨ha, h⟩⟩

theorem trueD_implies {p q : Cond} (ihp : TrueDen c I p) (ihq : TrueDen c I q) :
    TrueDen c I (.implies p q) := by
  intro vars P σ tbl e S hok hbd hP hr hk hS a ha
  rw [Semantics.condOK, Bool.and_eq_true] at hok
  rw [Cond.boundConf, Bool.and_eq_true] at hbd
  have hkp : ∀ k ∈ KoreAML.varsOf (Cond.kore c (canonVars c vars) (srtOf c S) p), k ∈ tbl := fun k hk0 =>
    hk k (by rw [Cond.kore, KoreAML.varsOf]
             exact List.mem_append_left _ (List.mem_append_right _ hk0))
  have hkq : ∀ k ∈ KoreAML.varsOf (Cond.kore c (canonVars c vars) (srtOf c S) q), k ∈ tbl := fun k hk0 =>
    hk k (by rw [Cond.kore, KoreAML.varsOf]; exact List.mem_append_right _ hk0)
  have h1 := ihp hok.1 hbd.1 (fun i hi hl => hP i (by rw [varOccsCond]; exact List.mem_append_left _ hi) hl)
    hr hkp hS a ha
  have h2 := ihq hok.2 hbd.2 (fun i hi hl => hP i (by rw [varOccsCond]; exact List.mem_append_right _ hi) hl)
    hr hkq hS a ha
  rw [Cond.kore, KoreAML.tr, KoreAML.interp_sImp, h1, h2]
  exact ⟨fun h => h.2, fun h => ⟨ha, h⟩⟩

/-! ### The atoms: the values of the terms, no case on a result -/

theorem trueD_ceil (F : AtomFacts c I) (D : TermDenAt c I) (s : Srt) (t : Term) : TrueDen c I (.ceil s t) := by
  intro vars P σ tbl e S hok _ hP hr _ hS a ha
  rw [Semantics.condOK] at hok; replace hok := ((Bool.and_eq_true _ _).mp hok).1; rw [beq_iff_eq] at hok
  have hPt : ∀ i ∈ varOccs t, P i := fun i hi => hP i (by rw [varOccsCond]; exact hi) (varOccs_lt t hok i hi)
  obtain ⟨hs, hread, hsort⟩ := term_readV F D hr hok hPt
  obtain ⟨τ, hτ, hτd⟩ := F.sort hs
  obtain ⟨τS, hτS, hτSd⟩ := F.sort hS
  have haS : KoreAML.Inh I τS a := (KoreAML.interp_inhOf_of (hτSd tbl e)).mp ha
  rw [Cond.kore, KoreAML.tr, KoreAML.interp_sCeil F.defOK F.ceilDef (hτd tbl e) (hτSd tbl e) hτ hτS (fun m hm => by
    obtain ⟨w, hw, hdw⟩ := (hread m).mp hm
    obtain ⟨a0, ha0, hin⟩ := F.val (hsort w hw) tbl e
    rw [(ha0 m).mp hdw]
    exact (KoreAML.interp_inhOf_of (hτd tbl e)).mp hin)]
  show _ ↔ ∃ v, EvalTerm c σ t (some v)
  constructor
  · rintro ⟨⟨m, hm⟩, -⟩
    obtain ⟨w, hw, -⟩ := (hread m).mp hm
    exact ⟨w, hw⟩
  · rintro ⟨w, hw⟩
    obtain ⟨a0, ha0, -⟩ := F.val (hsort w hw) tbl e
    exact ⟨⟨a0, (hread a0).mpr ⟨w, hw, (ha0 a0).mpr rfl⟩⟩, haS⟩

theorem trueD_equals (F : AtomFacts c I) (D : TermDenAt c I) (s : Srt) (t u : Term) :
    TrueDen c I (.equals s t u) := by
  intro vars P σ tbl e S hok _ hP hr _ hS a ha
  rw [Semantics.condOK] at hok; replace hok := ((Bool.and_eq_true _ _).mp hok).1
  rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at hok
  have hPt : ∀ i ∈ varOccs t, P i := fun i hi =>
    hP i (by rw [varOccsCond]; exact List.mem_append_left _ hi) (varOccs_lt t hok.1 i hi)
  have hPu : ∀ i ∈ varOccs u, P i := fun i hi =>
    hP i (by rw [varOccsCond]; exact List.mem_append_right _ hi) (varOccs_lt u hok.2 i hi)
  obtain ⟨hs, hreadt, hsortt⟩ := term_readV F D hr hok.1 hPt
  obtain ⟨-, hreadu, hsortu⟩ := term_readV F D hr hok.2 hPu
  obtain ⟨τ, hτ, hτd⟩ := F.sort hs
  obtain ⟨τS, hτS, hτSd⟩ := F.sort hS
  have haS : KoreAML.Inh I τS a := (KoreAML.interp_inhOf_of (hτSd tbl e)).mp ha
  have elt : ∀ {w : GroundTerm}, c.sortOf w = some s → ∃ a0, (∀ m, (den c w).interpret I e m ↔ m = a0) ∧
      KoreAML.Inh I τ a0 := fun hw => by
    obtain ⟨a0, ha0, hin⟩ := F.val hw tbl e
    exact ⟨a0, ha0, (KoreAML.interp_inhOf_of (hτd tbl e)).mp hin⟩
  rw [Cond.kore, KoreAML.tr, KoreAML.interp_sEquals F.defOK F.ceilDef (hτd tbl e) (hτSd tbl e) hτ hτS]
  show _ ↔ ∀ v, EvalTerm c σ t (some v) ↔ EvalTerm c σ u (some v)
  constructor
  · rintro ⟨-, hall⟩ v
    constructor
    · intro hv
      obtain ⟨a0, ha0, hin⟩ := elt (hsortt v hv)
      obtain ⟨w, hw, hdw⟩ := (hreadu a0).mp ((hall a0 hin).mp ((hreadt a0).mpr ⟨v, hv, (ha0 a0).mpr rfl⟩))
      rw [F.apart (hsortt v hv) (hsortu w hw) e a0 ((ha0 a0).mpr rfl) hdw]
      exact hw
    · intro hv
      obtain ⟨a0, ha0, hin⟩ := elt (hsortu v hv)
      obtain ⟨w, hw, hdw⟩ := (hreadt a0).mp ((hall a0 hin).mpr ((hreadu a0).mpr ⟨v, hv, (ha0 a0).mpr rfl⟩))
      rw [F.apart (hsortu v hv) (hsortt w hw) e a0 ((ha0 a0).mpr rfl) hdw]
      exact hw
  · intro hiff
    refine ⟨haS, fun x _ => ?_⟩
    rw [hreadt x, hreadu x]
    exact ⟨fun ⟨v, hv, hd⟩ => ⟨v, (hiff v).mp hv, hd⟩, fun ⟨v, hv, hd⟩ => ⟨v, (hiff v).mpr hv, hd⟩⟩

theorem trueD_mem (F : AtomFacts c I) (D : TermDenAt c I) (s : Srt) (t u : Term) :
    TrueDen c I (.mem s t u) := by
  intro vars P σ tbl e S hok _ hP hr _ hS a ha
  rw [Semantics.condOK] at hok; replace hok := ((Bool.and_eq_true _ _).mp hok).1
  rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at hok
  have hPt : ∀ i ∈ varOccs t, P i := fun i hi =>
    hP i (by rw [varOccsCond]; exact List.mem_append_left _ hi) (varOccs_lt t hok.1 i hi)
  have hPu : ∀ i ∈ varOccs u, P i := fun i hi =>
    hP i (by rw [varOccsCond]; exact List.mem_append_right _ hi) (varOccs_lt u hok.2 i hi)
  obtain ⟨hs, hreadt, hsortt⟩ := term_readV F D hr hok.1 hPt
  obtain ⟨-, hreadu, hsortu⟩ := term_readV F D hr hok.2 hPu
  obtain ⟨τ, hτ, hτd⟩ := F.sort hs
  obtain ⟨τS, hτS, hτSd⟩ := F.sort hS
  have haS : KoreAML.Inh I τS a := (KoreAML.interp_inhOf_of (hτSd tbl e)).mp ha
  have elt : ∀ {w : GroundTerm}, c.sortOf w = some s → ∃ a0, (∀ m, (den c w).interpret I e m ↔ m = a0) ∧
      KoreAML.Inh I τ a0 := fun hw => by
    obtain ⟨a0, ha0, hin⟩ := F.val hw tbl e
    exact ⟨a0, ha0, (KoreAML.interp_inhOf_of (hτd tbl e)).mp hin⟩
  rw [Cond.kore, KoreAML.tr, KoreAML.interp_sIn F.defOK F.ceilDef (hτd tbl e) (hτSd tbl e) hτ hτS (fun m hm => by
    obtain ⟨w, hw, hdw⟩ := (hreadt m).mp hm
    obtain ⟨a0, ha0, hin⟩ := elt (hsortt w hw)
    rw [(ha0 m).mp hdw]; exact hin)]
  show _ ↔ ∃ v, EvalTerm c σ t (some v) ∧ EvalTerm c σ u (some v)
  constructor
  · rintro ⟨⟨x, h1, h2⟩, -⟩
    obtain ⟨v, hv, hdv⟩ := (hreadt x).mp h1
    obtain ⟨w, hw, hdw⟩ := (hreadu x).mp h2
    have hvw := F.apart (hsortt v hv) (hsortu w hw) e x hdv hdw
    subst hvw
    exact ⟨v, hv, hw⟩
  · rintro ⟨v, hv, hw⟩
    obtain ⟨a0, ha0, -⟩ := elt (hsortt v hv)
    exact ⟨⟨a0, (hreadt a0).mpr ⟨v, hv, (ha0 a0).mpr rfl⟩, (hreadu a0).mpr ⟨v, hw, (ha0 a0).mpr rfl⟩⟩, haS⟩

/-! ### The sort binders -/

theorem trueD_ex (F : AtomFacts c I) (G : BinderFacts c I) (s : Srt) {body : Cond} (ih : TrueDen c I body) :
    TrueDen c I (.ex s body) := by
  intro vars P σ tbl e S hok hbd hP hr hk hS a ha
  rw [Semantics.condOK] at hok
  rw [Cond.boundConf, Bool.and_eq_true] at hbd
  have hlen : (vars ++ [s]).length = vars.length + 1 := by simp
  have hsn : s < nRegSorts + c.sortNames.length := G.confinedNum hbd.1
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
      c.sortOf v = some s → (∀ m, (den c v).interpret I e m ↔ m = a0) →
      ((KoreAML.tr ⟨tbl, []⟩ (Cond.kore c (canonVars c (vars ++ [s])) (srtOf c S) body)).interpret I
        ⟨Function.update e.evalEvar (tbl.ev K) a0, e.evalSvar⟩ a ↔ TrueV c (vars.length + 1) σ' body) := by
    intro σ' v a0 hσ' hn hv hd
    have := ih hok (by rw [hlen]; exact hbd.2) hPB (hr.snoc hK hσ' hn hv hd) hkB hS
      a ((KoreAML.interp_inhOf_of (hτSd tbl _)).mpr ((KoreAML.interp_inhOf_of (hτSd tbl e)).mp ha))
    rw [hlen] at this
    exact this
  have hsrt : ∀ (e' : Valuation M) m,
      (KoreAML.inhOf (KoreAML.trSort tbl (Cond.binder c (canonVars c vars).length s).kore.sort)).interpret I e' m ↔
        KoreAML.Inh I τ m := fun e' m => by
    show (KoreAML.inhOf (KoreAML.trSort tbl (srtOf c s))).interpret _ _ m ↔ _
    exact KoreAML.interp_inhOf_of (hτd tbl e')
  rw [KoreAML.tr, KoreAML.interp_sExists, hkb]
  simp only [KoreAML.interp_member F.defOK, Function.update_same, hsrt]
  show _ ↔ ∃ σ', Extends c vars.length [s] σ σ' ∧ TrueV c (vars.length + 1) σ' body
  constructor
  · rintro ⟨m, hm, hbody⟩
    obtain ⟨v, hv, hdv⟩ := G.confined hbd.1 tbl e m ((KoreAML.interp_inhOf_of (hτd tbl e)).mpr hm)
    have hσ'' : ∀ i < vars.length, (Model.extOneStdI σ vars.length v).lookup i = σ.lookup i :=
      fun i hi => Model.extOneStdI_off σ v (by omega)
    have hext : Extends c vars.length [s] σ (Model.extOneStdI σ vars.length v) :=
      ⟨hσ'', fun j s' hj => by
        cases j with
        | zero => simp at hj; subst hj; exact ⟨v, Model.extOneStdI_at σ _ v, hv⟩
        | succ j => simp at hj⟩
    exact ⟨_, hext, (hread _ v m hσ'' (Model.extOneStdI_at σ _ v) hv hdv).mp hbody⟩
  · rintro ⟨σ', hext, hg⟩
    obtain ⟨v, hv, hsv⟩ := hext.2 0 s rfl
    rw [Nat.add_zero] at hv
    obtain ⟨a0, ha0, hin⟩ := F.val hsv tbl e
    exact ⟨a0, (KoreAML.interp_inhOf_of (hτd tbl e)).mp hin, (hread σ' v a0 hext.1 hv hsv ha0).mpr hg⟩

theorem trueD_all (F : AtomFacts c I) (G : BinderFacts c I) (s : Srt) {body : Cond} (ih : TrueDen c I body) :
    TrueDen c I (.all s body) := by
  intro vars P σ tbl e S hok hbd hP hr hk hS a ha
  rw [Semantics.condOK] at hok
  rw [Cond.boundConf, Bool.and_eq_true] at hbd
  have hlen : (vars ++ [s]).length = vars.length + 1 := by simp
  have hsn : s < nRegSorts + c.sortNames.length := G.confinedNum hbd.1
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
      c.sortOf v = some s → (∀ m, (den c v).interpret I e m ↔ m = a0) →
      ((KoreAML.tr ⟨tbl, []⟩ (Cond.kore c (canonVars c (vars ++ [s])) (srtOf c S) body)).interpret I
        ⟨Function.update e.evalEvar (tbl.ev K) a0, e.evalSvar⟩ a ↔ TrueV c (vars.length + 1) σ' body) := by
    intro σ' v a0 hσ' hn hv hd
    have := ih hok (by rw [hlen]; exact hbd.2) hPB (hr.snoc hK hσ' hn hv hd) hkB hS
      a ((KoreAML.interp_inhOf_of (hτSd tbl _)).mpr ((KoreAML.interp_inhOf_of (hτSd tbl e)).mp ha))
    rw [hlen] at this
    exact this
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
  show _ ↔ ∀ σ', Extends c vars.length [s] σ σ' → TrueV c (vars.length + 1) σ' body
  constructor
  · intro hall σ' hext
    obtain ⟨v, hv, hsv⟩ := hext.2 0 s rfl
    rw [Nat.add_zero] at hv
    obtain ⟨a0, ha0, hin⟩ := F.val hsv tbl e
    exact (hread σ' v a0 hext.1 hv hsv ha0).mp (hall a0 ((KoreAML.interp_inhOf_of (hτd tbl e)).mp hin))
  · intro hbt m hm
    obtain ⟨v, hv, hdv⟩ := G.confined hbd.1 tbl e m ((KoreAML.interp_inhOf_of (hτd tbl e)).mpr hm)
    have hσ'' : ∀ i < vars.length, (Model.extOneStdI σ vars.length v).lookup i = σ.lookup i :=
      fun i hi => Model.extOneStdI_off σ v (by omega)
    have hext : Extends c vars.length [s] σ (Model.extOneStdI σ vars.length v) :=
      ⟨hσ'', fun j s' hj => by
        cases j with
        | zero => simp at hj; subst hj; exact ⟨v, Model.extOneStdI_at σ _ v, hv⟩
        | succ j => simp at hj⟩
    exact (hread _ v m hσ'' (Model.extOneStdI_at σ _ v) hv hdv).mpr (hbt _ hext)

/-! ### A match under binders -/

/-- **`exMatch` as `TrueV`**: an element of the match is a value of t (by `TermDenAt`, no result in
hand) that the pattern matches under values of the binders (by the pattern or by their sorts, as in
`holds_exMatch'`), with the body there; and back. -/
theorem trueD_exMatch (F : AtomFacts c I) (G : BinderFacts c I) (D : TermDenAt c I) (ys : List Srt) (s : Srt)
    (p t : Term) {body : Cond} (ih : TrueDen c I body) : TrueDen c I (.exMatch ys s p t body) := by
  intro vars P σ tbl e S hok hbd hP hr hk hS a ha
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
  obtain ⟨hs, -, hsortσ⟩ := term_readV F D hr htS hPt
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
  have hread : ∀ (e' : Valuation M),
      (∀ i, P i → e'.evalEvar (tbl.ev (canonKey c vars i)) = e.evalEvar (tbl.ev (canonKey c vars i))) →
      ((KoreAML.tr ⟨tbl, []⟩ (.and (srtOf c S)
        [.in (srtOf c s) (srtOf c S) (Term.kore c (canonVars c vars) t) (Term.kore c (canonVars c (vars ++ ys)) p),
         Cond.kore c (canonVars c (vars ++ ys)) (srtOf c S) body])).interpret I e' a ↔
        (∃ m, (∃ v, EvalTerm c σ t (some v) ∧ (den c v).interpret I e' m) ∧
            (KoreAML.tr ⟨tbl, []⟩ (Term.kore c (canonVars c (vars ++ ys)) p)).interpret I e' m) ∧
          (KoreAML.tr ⟨tbl, []⟩ (Cond.kore c (canonVars c (vars ++ ys)) (srtOf c S) body)).interpret I e' a) := by
    intro e' hoff
    have hrt : Reads c I vars P σ tbl e' := fun i hi => by
      obtain ⟨a1, a2, v, a3, a4, a5⟩ := hr i hi
      exact ⟨a1, a2, v, a3, a4, fun m => by rw [hoff i hi]; exact (a5 m).trans ((den_closed c v).interp _ _ m)⟩
    obtain ⟨-, hreadt, hsortt⟩ := term_readV F D hrt htS hPt
    rw [tr_and2, KoreAML.interp_sAnd, KoreAML.tr, KoreAML.interp_sIn F.defOK F.ceilDef
      (hτsd tbl e') (hτSd tbl e') hτs hτS (fun m hm => by
        obtain ⟨w, hw, hdw⟩ := (hreadt m).mp hm
        obtain ⟨a0, ha0, hin⟩ := F.val (hsortt w hw) tbl e'
        rw [(ha0 m).mp hdw]
        exact (KoreAML.interp_inhOf_of (hτsd tbl e')).mp hin)]
    simp only [hreadt]
    constructor
    · rintro ⟨⟨hm, -⟩, hb⟩
      exact ⟨hm, hb⟩
    · rintro ⟨hm, hb⟩
      exact ⟨⟨hm, (KoreAML.interp_inhOf_of (hτSd tbl e')).mp (haS e')⟩, hb⟩
  show _ ↔ ∃ v σ', EvalTerm c σ t (some v) ∧ Extends c vars.length ys σ σ' ∧ PatVal c σ' p v ∧
    TrueV c (vars.length + ys.length) σ' body
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
    obtain ⟨⟨m, ⟨v, hev, hmv⟩, hpm⟩, hbodym⟩ := (hread e' hoffP).mp hbm
    have hsv : c.sortOf v = some s := hsortσ v hev
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
    have hbody := ih hokB (by rw [hlen]; exact hbdB) hPB hrE hkB hS a (haS e')
    rw [hlen] at hbody
    exact ⟨v, σE, hev, hext, hpvE, hbody.mp hbodym⟩
  · -- a value of t and an extension where the match holds: the binders at the elements of their values
    rintro ⟨v, σ', hev, hext, hpv, hg⟩
    have hsv : c.sortOf v = some s := hsortσ v hev
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
    have hbody := ih hokB (by rw [hlen]; exact hbdB) hPB hr'' hkB hS a (haS e')
    rw [hlen] at hbody
    refine existsAll_intro_at F.defOK _ e e' a hnd hsrt (fun z hz => ?_) rfl (fun b hb' k hk => ?_)
      ((hread e' hoffP).mpr ⟨⟨m0, ⟨v, hev, (hm0 m0).mpr rfl⟩, hpm⟩, hbody.mpr hg⟩)
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

/-- **A condition as `TrueV` in every interpretation with the facts**, by structural recursion. -/
theorem trueDen_of (F : AtomFacts c I) (G : BinderFacts c I) (D : TermDenAt c I) : ∀ p : Cond, TrueDen c I p
  | .top => trueD_top F
  | .bot => trueD_bot F
  | .not p => trueD_not (trueDen_of F G D p)
  | .and p q => trueD_and (trueDen_of F G D p) (trueDen_of F G D q)
  | .or p q => trueD_or (trueDen_of F G D p) (trueDen_of F G D q)
  | .implies p q => trueD_implies (trueDen_of F G D p) (trueDen_of F G D q)
  | .ceil s t => trueD_ceil F D s t
  | .equals s t u => trueD_equals F D s t u
  | .mem s t u => trueD_mem F D s t u
  | .exMatch ys s p t body => trueD_exMatch F G D ys s p t (trueDen_of F G D body)
  | .ex s body => trueD_ex F G s (trueDen_of F G D body)
  | .all s body => trueD_all F G s (trueDen_of F G D body)

end TrueShape

end HoldsShape

namespace Faithful

namespace Model

open ML

variable {c : Semantics} {T : GroundTerm → GroundTerm → Prop}

/-- **The value model at T has `TermDenAt`**: a term denotes the values `EvalTerm` gives it
(`term_readStdI`), and a value denotes its own element. -/
theorem termDenAt_stdI (h : HypModelCore c) : HoldsShape.TermDenAt c (stdI_T c T) := by
  intro σ t vars P tbl e s hP hr ht m
  obtain ⟨-, hd, hs⟩ := term_readStdI (T := T) h (readsT_of_reads (T := T) h hr) ht hP
  rw [hd m]
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact ⟨v, hv, (den_val_T h T v (hs v hv) e _).mpr rfl⟩
  · rintro ⟨v, hv, hdv⟩
    exact ⟨v, hv, (den_val_T h T v (hs v hv) e _).mp hdv⟩

end Model

open ML Model

/-- **(I2) A rule's condition in the value model at any transition T, decided or not**: for a
condition with `condOK` and `Cond.bound`, written over the canonical names of the variables in
scope, at a valuation that reads its free variables as their values under σ and whose table holds
the condition's variables, an element of a numbered predicate sort is in `Cond.kore p` exactly where
`TrueV c vars.length σ p`. `holds_stdI`'s statement without the hypothesis that p has a truth
value; it reads `HypModelCore` only. -/
theorem trueV_stdI {c : Semantics} (h : HypModelCore c) (T : GroundTerm → GroundTerm → Prop) (p : Cond)
    {vars : List Srt} {P : Nat → Prop} {σ : Subst} {tbl : KoreAML.VarTable} {e : Valuation Elem} {S : Srt}
    (hok : c.condOK vars p = true) (hbd : Cond.bound c vars.length p = true)
    (hP : ∀ i ∈ varOccsCond vars.length p, i < vars.length → P i) (hr : ReadsT c vars P σ tbl e)
    (hk : ∀ k ∈ KoreAML.varsOf (Cond.kore c (canonVars c vars) (srtOf c S) p), k ∈ tbl)
    (hS : S < nRegSorts + c.sortNames.length) (a : Elem) (ha : InSort c S a) :
    (KoreAML.tr ⟨tbl, []⟩ (Cond.kore c (canonVars c vars) (srtOf c S) p)).interpret (stdI_T c T) e a ↔
      TrueV c vars.length σ p :=
  HoldsShape.trueDen_of (atomFacts_stdI h) (binderFacts_stdI h) (termDenAt_stdI h) p hok
    (by rw [← Cond.bound_eq_boundConf]; exact hbd) hP
    (reads_of_readsT h hr) hk hS a ((inhOf_srtOf_stdI h hS _ a).mpr ha)

/-- `holds_stdI` again, as (I2) with (I1): where the condition has a truth value, `TrueV` is it. -/
theorem holds_stdI_of_trueV {c : Semantics} (h : HypModelCore c) (T : GroundTerm → GroundTerm → Prop) (p : Cond)
    {vars : List Srt} {P : Nat → Prop} {σ : Subst} {tbl : KoreAML.VarTable} {e : Valuation Elem} {S : Srt}
    (hok : c.condOK vars p = true) (hbd : Cond.bound c vars.length p = true)
    (hP : ∀ i ∈ varOccsCond vars.length p, i < vars.length → P i) (hr : ReadsT c vars P σ tbl e)
    (hk : ∀ k ∈ KoreAML.varsOf (Cond.kore c (canonVars c vars) (srtOf c S) p), k ∈ tbl)
    (hS : S < nRegSorts + c.sortNames.length) (hd : ∃ b, Holds c vars.length σ p b)
    (a : Elem) (ha : InSort c S a) :
    (KoreAML.tr ⟨tbl, []⟩ (Cond.kore c (canonVars c vars) (srtOf c S) p)).interpret (stdI_T c T) e a ↔
      Holds c vars.length σ p true := by
  obtain ⟨b, hb⟩ := hd
  rw [trueV_stdI h T p hok hbd hP hr hk hS a ha, holds_trueV h.det hb]
  constructor
  · rintro rfl; exact hb
  · intro ht
    exact (holds_trueV h.det hb).mp ((holds_trueV h.det ht).mpr rfl)

end Faithful

end KCore
