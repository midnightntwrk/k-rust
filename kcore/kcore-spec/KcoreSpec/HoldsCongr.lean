/-
  KCore. A condition's truth value reads its substitution at the condition's variables only.

  `Holds.congr_NI`: where σ₁ and σ₂ agree on `varOccsCond n p`, a truth value p has under σ₁ it
  has under σ₂. An atom reads its terms (`EvalTerm.congr`); a connective its operands. A binder
  over the variables n, …, n + k - 1 reads the extensions of σ: each extension σ₁' of σ₁ has the
  extension of σ₂ that is σ₂ below n and σ₁' from n on (`mixSubst`), and conversely, and the two
  agree at the body's variables (those below n by the hypothesis, the others by construction). The
  truth value of the body at an extension of σ₂ is then taken from the extensions of σ₁ it is
  paired with: for `∃`, true where one of them gives true; for `∀`, true where all of them do.
  Each extension of σ₂ is paired with at least one extension of σ₁, so no determinism of `Holds`
  is read.
-/
import KcoreSpec.RightHeldExtend
import KcoreSpec.EvalSound

set_option autoImplicit false

namespace KCore

/-! ## Mixing two substitutions at a bound -/

/-- `σ` below n, `τ` from n on. -/
def mixSubst (n : Nat) (σ τ : Subst) : Subst :=
  σ.filter (fun q => decide (q.1 < n)) ++ τ.filter (fun q => decide (n ≤ q.1))

theorem lookup_filter_fst (P : Nat → Prop) [DecidablePred P] (a : Nat) :
    ∀ l : Subst, (l.filter (fun q => decide (P q.1))).lookup a = if P a then l.lookup a else none
  | [] => by simp
  | (k, v) :: l => by
    have ih := lookup_filter_fst P a l
    by_cases hk : P k
    · rw [List.filter_cons_of_pos (by simpa using hk)]
      simp only [List.lookup_cons]
      by_cases hak : a = k
      · subst hak; simp [hk]
      · have : (a == k) = false := by simpa using hak
        simp only [this]; exact ih
    · rw [List.filter_cons_of_neg (by simpa using hk), ih]
      simp only [List.lookup_cons]
      by_cases hak : a = k
      · subst hak; simp [hk]
      · have : (a == k) = false := by simpa using hak
        simp only [this]

theorem lookup_append_or : ∀ (l l' : Subst) (a : Nat), (l ++ l').lookup a = (l.lookup a).or (l'.lookup a)
  | [], _, _ => by simp
  | (k, v) :: l, l', a => by
    simp only [List.cons_append, List.lookup_cons]
    cases a == k
    · exact lookup_append_or l l' a
    · rfl

theorem mixSubst_lookup (n : Nat) (σ τ : Subst) (a : Nat) :
    (mixSubst n σ τ).lookup a = if a < n then σ.lookup a else τ.lookup a := by
  unfold mixSubst
  rw [lookup_append_or, lookup_filter_fst (· < n), lookup_filter_fst (n ≤ ·)]
  by_cases h : a < n
  · simp only [h, ite_true, show ¬ n ≤ a from Nat.not_le.mpr h, ite_false]
    cases σ.lookup a <;> rfl
  · simp [h, Nat.le_of_not_lt h]

theorem extends_mix {c : Semantics} {n : Nat} {ys : List Srt} {σ σ' τ : Subst}
    (h : Extends c n ys σ' τ) : Extends c n ys σ (mixSubst n σ τ) := by
  refine ⟨fun i hi => by rw [mixSubst_lookup, if_pos hi], fun j s hs => ?_⟩
  obtain ⟨v, hv, hsv⟩ := h.2 j s hs
  exact ⟨v, by rw [mixSubst_lookup, if_neg (by omega), hv], hsv⟩

/-! ## The congruence -/

/-- `Holds.congr_NI` with the second substitution explicit, by structural recursion on the
derivation: in a binder case the body's derivations `hb σ₁' …` are arguments of the constructor, so
the recursive calls on them are structural. The second substitution is explicit because a match
alternative of the statement with `∀ {σ₂}` after the derivation has it introduced and nameless. -/
theorem Holds.congr_NI_aux {c : Semantics} : ∀ {n : Nat} {σ₁ : Subst} {p : Cond} {b : Bool},
    Holds c n σ₁ p b → ∀ (σ₂ : Subst), (∀ j ∈ varOccsCond n p, σ₁.lookup j = σ₂.lookup j) →
    Holds c n σ₂ p b
  | _, _, _, _, .top => fun _ _ => .top
  | _, _, _, _, .bot => fun _ _ => .bot
  | _, _, _, _, .not h => fun _ ha => .not (Holds.congr_NI_aux h _ fun j hj => ha j (by simpa [varOccsCond] using hj))
  | _, _, _, _, .and h h' => fun _ ha =>
    .and (Holds.congr_NI_aux h _ fun j hj => ha j (by simp [varOccsCond, hj]))
      (Holds.congr_NI_aux h' _ fun j hj => ha j (by simp [varOccsCond, hj]))
  | _, _, _, _, .or h h' => fun _ ha =>
    .or (Holds.congr_NI_aux h _ fun j hj => ha j (by simp [varOccsCond, hj]))
      (Holds.congr_NI_aux h' _ fun j hj => ha j (by simp [varOccsCond, hj]))
  | _, _, _, _, .implies h h' => fun _ ha =>
    .implies (Holds.congr_NI_aux h _ fun j hj => ha j (by simp [varOccsCond, hj]))
      (Holds.congr_NI_aux h' _ fun j hj => ha j (by simp [varOccsCond, hj]))
  | _, _, _, _, .ceil he => fun _ ha =>
    .ceil (Exec.EvalTerm.congr he fun j hj => ha j (by simpa [varOccsCond] using hj))
  | _, _, _, _, .equals he he' => fun _ ha =>
    .equals (Exec.EvalTerm.congr he fun j hj => ha j (by simp [varOccsCond, hj]))
      (Exec.EvalTerm.congr he' fun j hj => ha j (by simp [varOccsCond, hj]))
  | _, _, _, _, .mem he he' => fun _ ha =>
    .mem (Exec.EvalTerm.congr he fun j hj => ha j (by simp [varOccsCond, hj]))
      (Exec.EvalTerm.congr he' fun j hj => ha j (by simp [varOccsCond, hj]))
  | _, _, _, _, .exNone he => fun _ ha =>
    .exNone (Exec.EvalTerm.congr he fun j hj => ha j (by simp [varOccsCond, hj]))
  | _, _, _, _, @Holds.exSome _ n σ₁ ys s p t body v b g he hb hr => fun σ₂ ha => by
    have ih : ∀ σ₁' (_ : Extends c n ys σ₁ σ₁') (_ : PatVal c σ₁' p v) {σ₂' : Subst},
        (∀ j ∈ varOccsCond (n + ys.length) body, σ₁'.lookup j = σ₂'.lookup j) →
        Holds c (n + ys.length) σ₂' body (g σ₁') := fun σ₁' hx hm => Holds.congr_NI_aux (hb σ₁' hx hm) _
    -- the extensions paired: an extension of σ₁, one of σ₂, agreeing at p's and the body's variables
    let R : Subst → Subst → Prop := fun σ₁' σ₂' => Extends c n ys σ₁ σ₁' ∧
      ∀ j ∈ varOccs p ++ varOccsCond (n + ys.length) body, σ₁'.lookup j = σ₂'.lookup j
    have hagr : ∀ σ₁' σ₂', Extends c n ys σ₁ σ₁' → Extends c n ys σ₂ σ₂' →
        (∀ j, n ≤ j → σ₁'.lookup j = σ₂'.lookup j) →
        ∀ j ∈ varOccs p ++ varOccsCond (n + ys.length) body, σ₁'.lookup j = σ₂'.lookup j := by
      intro σ₁' σ₂' h1 h2 hge j hj
      by_cases hjn : j < n
      · rw [h1.1 j hjn, h2.1 j hjn]
        exact ha j (by rw [varOccsCond, List.mem_append, List.mem_filter]; exact Or.inr ⟨hj, decide_eq_true hjn⟩)
      · exact hge j (Nat.le_of_not_lt hjn)
    have hR₁ : ∀ σ₂', Extends c n ys σ₂ σ₂' → R (mixSubst n σ₁ σ₂') σ₂' := fun σ₂' h2 =>
      ⟨extends_mix h2, hagr _ _ (extends_mix h2) h2 fun j hj => by
        rw [mixSubst_lookup, if_neg (Nat.not_lt.mpr hj)]⟩
    have hR₂ : ∀ σ₁', Extends c n ys σ₁ σ₁' → R σ₁' (mixSubst n σ₂ σ₁') := fun σ₁' h1 =>
      ⟨h1, hagr _ _ h1 (extends_mix h1) fun j hj => by
        rw [mixSubst_lookup, if_neg (Nat.not_lt.mpr hj)]⟩
    have hpv : ∀ σ₁' σ₂', R σ₁' σ₂' → (PatVal c σ₁' p v ↔ PatVal c σ₂' p v) := fun σ₁' σ₂' hr' =>
      ⟨fun hm => PatVal.congr_varsRH hm fun j hj => (hr'.2 j (List.mem_append_left _ hj)).symm,
       fun hm => PatVal.congr_varsRH hm fun j hj => hr'.2 j (List.mem_append_left _ hj)⟩
    have hbod : ∀ σ₁' σ₂', R σ₁' σ₂' → PatVal c σ₁' p v → Holds c (n + ys.length) σ₂' body (g σ₁') :=
      fun σ₁' σ₂' hr' hm => ih σ₁' hr'.1 hm fun j hj => hr'.2 j (List.mem_append_right _ hj)
    classical
    let g₂ : Subst → Bool := fun σ₂' => decide (∃ σ₁', R σ₁' σ₂' ∧ PatVal c σ₁' p v ∧ g σ₁' = true)
    refine .exSome g₂ (Exec.EvalTerm.congr he fun j hj => ha j (by rw [varOccsCond, List.mem_append]; exact Or.inl hj))
      (fun σ₂' h2 hm => ?_) ?_
    · by_cases hx : ∃ σ₁', R σ₁' σ₂' ∧ PatVal c σ₁' p v ∧ g σ₁' = true
      · obtain ⟨σ₁', hr', hm', hg⟩ := hx
        have := hbod σ₁' σ₂' hr' hm'
        rw [hg] at this
        have hd : g₂ σ₂' = true := decide_eq_true ⟨σ₁', hr', hm', hg⟩
        rw [hd]; exact this
      · have hr' := hR₁ σ₂' h2
        have hm' := (hpv _ _ hr').mpr hm
        have hg : g (mixSubst n σ₁ σ₂') = false := by
          cases hgv : g (mixSubst n σ₁ σ₂')
          · rfl
          · exact absurd ⟨_, hr', hm', hgv⟩ hx
        have := hbod _ σ₂' hr' hm'
        rw [hg] at this
        have hd : g₂ σ₂' = false := decide_eq_false hx
        rw [hd]; exact this
    · rw [hr]
      constructor
      · rintro ⟨σ₁', h1, hm, hg⟩
        have hr' := hR₂ σ₁' h1
        exact ⟨mixSubst n σ₂ σ₁', extends_mix h1, (hpv _ _ hr').mp hm, by simp only [g₂, decide_eq_true_eq]; exact ⟨σ₁', hr', hm, hg⟩⟩
      · rintro ⟨σ₂', -, -, hg⟩
        simp only [g₂, decide_eq_true_eq] at hg
        obtain ⟨σ₁', hr', hm, hg⟩ := hg
        exact ⟨σ₁', hr'.1, hm, hg⟩
  | _, _, _, _, @Holds.ex _ n σ₁ s body b g hb hr => fun σ₂ ha => by
    have ih : ∀ σ₁' (_ : Extends c n [s] σ₁ σ₁') {σ₂' : Subst},
        (∀ j ∈ varOccsCond (n + 1) body, σ₁'.lookup j = σ₂'.lookup j) →
        Holds c (n + 1) σ₂' body (g σ₁') := fun σ₁' hx => Holds.congr_NI_aux (hb σ₁' hx) _
    let R : Subst → Subst → Prop := fun σ₁' σ₂' => Extends c n [s] σ₁ σ₁' ∧
      ∀ j ∈ varOccsCond (n + 1) body, σ₁'.lookup j = σ₂'.lookup j
    have hagr : ∀ σ₁' σ₂', Extends c n [s] σ₁ σ₁' → Extends c n [s] σ₂ σ₂' →
        (∀ j, n ≤ j → σ₁'.lookup j = σ₂'.lookup j) →
        ∀ j ∈ varOccsCond (n + 1) body, σ₁'.lookup j = σ₂'.lookup j := by
      intro σ₁' σ₂' h1 h2 hge j hj
      by_cases hjn : j < n
      · rw [h1.1 j hjn, h2.1 j hjn]
        exact ha j (by rw [varOccsCond, List.mem_filter]; exact ⟨hj, decide_eq_true hjn⟩)
      · exact hge j (Nat.le_of_not_lt hjn)
    have hR₁ : ∀ σ₂', Extends c n [s] σ₂ σ₂' → R (mixSubst n σ₁ σ₂') σ₂' := fun σ₂' h2 =>
      ⟨extends_mix h2, hagr _ _ (extends_mix h2) h2 fun j hj => by
        rw [mixSubst_lookup, if_neg (Nat.not_lt.mpr hj)]⟩
    have hR₂ : ∀ σ₁', Extends c n [s] σ₁ σ₁' → R σ₁' (mixSubst n σ₂ σ₁') := fun σ₁' h1 =>
      ⟨h1, hagr _ _ h1 (extends_mix h1) fun j hj => by
        rw [mixSubst_lookup, if_neg (Nat.not_lt.mpr hj)]⟩
    have hbod : ∀ σ₁' σ₂', R σ₁' σ₂' → Holds c (n + 1) σ₂' body (g σ₁') :=
      fun σ₁' σ₂' hr' => ih σ₁' hr'.1 hr'.2
    classical
    let g₂ : Subst → Bool := fun σ₂' => decide (∃ σ₁', R σ₁' σ₂' ∧ g σ₁' = true)
    refine .ex g₂ (fun σ₂' h2 => ?_) ?_
    · by_cases hx : ∃ σ₁', R σ₁' σ₂' ∧ g σ₁' = true
      · obtain ⟨σ₁', hr', hg⟩ := hx
        have := hbod σ₁' σ₂' hr'
        rw [hg] at this
        have hd : g₂ σ₂' = true := decide_eq_true ⟨σ₁', hr', hg⟩
        rw [hd]; exact this
      · have hr' := hR₁ σ₂' h2
        have hg : g (mixSubst n σ₁ σ₂') = false := by
          cases hgv : g (mixSubst n σ₁ σ₂')
          · rfl
          · exact absurd ⟨_, hr', hgv⟩ hx
        have := hbod _ σ₂' hr'
        rw [hg] at this
        have hd : g₂ σ₂' = false := decide_eq_false hx
        rw [hd]; exact this
    · rw [hr]
      constructor
      · rintro ⟨σ₁', h1, hg⟩
        exact ⟨_, extends_mix h1, by simp only [g₂, decide_eq_true_eq]; exact ⟨σ₁', hR₂ σ₁' h1, hg⟩⟩
      · rintro ⟨σ₂', -, hg⟩
        simp only [g₂, decide_eq_true_eq] at hg
        obtain ⟨σ₁', hr', hg⟩ := hg
        exact ⟨σ₁', hr'.1, hg⟩
  | _, _, _, _, @Holds.all _ n σ₁ s body b g hb hr => fun σ₂ ha => by
    have ih : ∀ σ₁' (_ : Extends c n [s] σ₁ σ₁') {σ₂' : Subst},
        (∀ j ∈ varOccsCond (n + 1) body, σ₁'.lookup j = σ₂'.lookup j) →
        Holds c (n + 1) σ₂' body (g σ₁') := fun σ₁' hx => Holds.congr_NI_aux (hb σ₁' hx) _
    let R : Subst → Subst → Prop := fun σ₁' σ₂' => Extends c n [s] σ₁ σ₁' ∧
      ∀ j ∈ varOccsCond (n + 1) body, σ₁'.lookup j = σ₂'.lookup j
    have hagr : ∀ σ₁' σ₂', Extends c n [s] σ₁ σ₁' → Extends c n [s] σ₂ σ₂' →
        (∀ j, n ≤ j → σ₁'.lookup j = σ₂'.lookup j) →
        ∀ j ∈ varOccsCond (n + 1) body, σ₁'.lookup j = σ₂'.lookup j := by
      intro σ₁' σ₂' h1 h2 hge j hj
      by_cases hjn : j < n
      · rw [h1.1 j hjn, h2.1 j hjn]
        exact ha j (by rw [varOccsCond, List.mem_filter]; exact ⟨hj, decide_eq_true hjn⟩)
      · exact hge j (Nat.le_of_not_lt hjn)
    have hR₁ : ∀ σ₂', Extends c n [s] σ₂ σ₂' → R (mixSubst n σ₁ σ₂') σ₂' := fun σ₂' h2 =>
      ⟨extends_mix h2, hagr _ _ (extends_mix h2) h2 fun j hj => by
        rw [mixSubst_lookup, if_neg (Nat.not_lt.mpr hj)]⟩
    have hR₂ : ∀ σ₁', Extends c n [s] σ₁ σ₁' → R σ₁' (mixSubst n σ₂ σ₁') := fun σ₁' h1 =>
      ⟨h1, hagr _ _ h1 (extends_mix h1) fun j hj => by
        rw [mixSubst_lookup, if_neg (Nat.not_lt.mpr hj)]⟩
    have hbod : ∀ σ₁' σ₂', R σ₁' σ₂' → Holds c (n + 1) σ₂' body (g σ₁') :=
      fun σ₁' σ₂' hr' => ih σ₁' hr'.1 hr'.2
    classical
    let g₂ : Subst → Bool := fun σ₂' => decide (∀ σ₁', R σ₁' σ₂' → g σ₁' = true)
    refine .all g₂ (fun σ₂' h2 => ?_) ?_
    · by_cases hx : ∀ σ₁', R σ₁' σ₂' → g σ₁' = true
      · have hr' := hR₁ σ₂' h2
        have := hbod _ σ₂' hr'
        rw [hx _ hr'] at this
        have hd : g₂ σ₂' = true := decide_eq_true hx
        rw [hd]; exact this
      · have hx' : ¬ ∀ σ₁', R σ₁' σ₂' → g σ₁' = true := hx
        obtain ⟨σ₁', hr', hg⟩ : ∃ σ₁', R σ₁' σ₂' ∧ g σ₁' = false := by
          obtain ⟨σ₁', hσ⟩ := Classical.not_forall.mp hx
          obtain ⟨hr', hg⟩ := Classical.not_imp.mp hσ
          exact ⟨σ₁', hr', by simpa using hg⟩
        have := hbod σ₁' σ₂' hr'
        rw [hg] at this
        have hd : g₂ σ₂' = false := decide_eq_false hx'
        rw [hd]; exact this
    · rw [hr]
      constructor
      · intro hall σ₂' _
        simp only [g₂, decide_eq_true_eq]
        exact fun σ₁' hr' => hall σ₁' hr'.1
      · intro hall σ₁' h1
        have := hall _ (extends_mix h1)
        simp only [g₂, decide_eq_true_eq] at this
        exact this σ₁' (hR₂ σ₁' h1)

/-- **A condition's truth value reads the substitution at the condition's variables only.** -/
theorem Holds.congr_NI {c : Semantics} {n : Nat} {σ₁ : Subst} {p : Cond} {b : Bool}
    (h : Holds c n σ₁ p b) : ∀ {σ₂ : Subst}, (∀ j ∈ varOccsCond n p, σ₁.lookup j = σ₂.lookup j) →
    Holds c n σ₂ p b :=
  fun ha => Holds.congr_NI_aux h _ ha

/-! ## A clause under an extension of a match on its left variables -/

/-- The variables of a clause's predicate are among those of its patterns and conditions. -/
theorem Clause.pre_leftVarsRH {cl : Clause} : ∀ i ∈ varOccsCond cl.vars.length cl.pre, i ∈ cl.leftVars :=
  fun _ hi => List.mem_append_right _ (List.mem_append_right _ hi)

/-- **A clause that matches with its `requires` true and its predicate true under a substitution
well sorted on its patterns and conditions applies under an extension of it**, where each other
variable is of a sort with a value: the extension is well sorted on every variable and agrees on
`leftVars`, which hold the variables of the patterns, of the `requires` and of the predicate. -/
theorem Clause.appliesAt_extendRH {c : Semantics} {cl : Clause} (hh : c.HeldAt cl.vars cl.leftVars) {σ : Subst}
    {vs : List GroundTerm} (hσ : c.WellSortedAt cl.vars cl.leftVars σ) (hm : PatVals c σ cl.pats vs)
    (hreq : ∀ t, cl.req = some t → EvalTerm c σ t (some (bool true)))
    (hpre : Holds c cl.vars.length σ cl.pre true) :
    ∃ σ', cl.AppliesAt c σ' vs ∧ ∀ i ∈ cl.leftVars, σ'.lookup i = σ.lookup i := by
  obtain ⟨σ', hws, hag⟩ := Semantics.extendHeld hh hσ
  refine ⟨σ', ⟨hws.at _, PatVals.congr_varsRH hm fun j hj => hag j (List.mem_append_left _ hj), fun t ht => ?_,
    Holds.congr_NI hpre fun j hj => (hag j (Clause.pre_leftVarsRH j hj)).symm⟩, hag⟩
  exact Exec.EvalTerm.congr (hreq t ht) fun i hi => (hag i (Clause.req_leftVarsRH ht i hi)).symm

/-- **A clause that applies under no substitution fails**, where each variable outside its
patterns and conditions is of a sort with a value and, at each match well sorted on every variable,
its `requires` has a result and its predicate a truth value: a match well sorted on `leftVars`
extends to one well sorted on every variable (`Semantics.extendHeld`), under which the `requires`
has a result other than `true` or the predicate is false, the same under the match (both read
`leftVars` only). -/
theorem Clause.fails_of_not_appliesRH {c : Semantics} {cl : Clause} (hh : c.HeldAt cl.vars cl.leftVars)
    {vs : List GroundTerm}
    (hreq : ∀ σ, c.WellSorted cl.vars σ → PatVals c σ cl.pats vs →
      (∀ t, cl.req = some t → ∃ r, EvalTerm c σ t r) ∧ ∃ b, Holds c cl.vars.length σ cl.pre b)
    (hna : ¬ ∃ σ, cl.AppliesAt c σ vs) : Fails c vs cl := by
  refine Fails.intro fun σ hσ hm => ?_
  obtain ⟨σ', hws, hag⟩ := Semantics.extendHeld hh hσ
  have hm' : PatVals c σ' cl.pats vs := PatVals.congr_varsRH hm fun j hj => hag j (List.mem_append_left _ hj)
  obtain ⟨hq, b, hb⟩ := hreq σ' hws hm'
  by_cases hall : ∀ t, cl.req = some t → EvalTerm c σ' t (some (bool true))
  · cases b with
    | true => exact absurd ⟨σ', hws.at _, hm', hall, hb⟩ hna
    | false => exact ReqFails.pre (Holds.congr_NI hb fun j hj => hag j (Clause.pre_leftVarsRH j hj))
  · obtain ⟨t, hne⟩ := Classical.not_forall.mp hall
    obtain ⟨ht, hne⟩ := Classical.not_imp.mp hne
    obtain ⟨r, he⟩ := hq t ht
    exact ReqFails.intro ht (Exec.EvalTerm.congr he fun i hi => hag i (Clause.req_leftVarsRH ht i hi))
      fun h => hne (h ▸ he)

/-! ## A result of a clause where it decides is a result of its function -/

/-- **A result of a clause at a match where it decides is a result of its function**
(`Eval.clause`, `Eval.ensFails`, `Eval.clauseEx`, `Eval.exNone`, the `Decides` premise as their
`hprio`). For a clause with existential variables that gives a value, the instance that gives it
is the match of the derivation: it is the given match on the patterns, the `requires` and the
predicate, which hold no existential variable an instance varies. -/
theorem Clause.Res.eval {c : Semantics} {f : Sym} {fn : Fn} {cl : Clause} {σ : Subst} {vs : List GroundTerm}
    {r : Option GroundTerm} (hr : cl.Res c σ r) (hfn : c.lookupFn f = some fn) (hmem : cl ∈ fn.clauses)
    (hd : cl.Decides c fn σ vs) : Eval c f vs r := by
  obtain ⟨⟨hσ, hm, hq, hpre⟩, hp⟩ := hd
  rcases hr with ⟨hex, (⟨he, hpost, hrhs⟩ | ⟨t, w, ht, he, hw, rfl⟩)⟩ |
    ⟨hne, (⟨σ₁, v, ha, hσ₁, ⟨grhs, gens, gpost⟩, hall, rfl⟩ | ⟨rfl, hsome, hall⟩)⟩
  · exact .clause hfn hmem ((wellSortedAt_univ hex).mp hσ) hm hq hpre hp hex hrhs he hpost
  · exact .ensFails hfn hmem ((wellSortedAt_univ hex).mp hσ) hm hq hpre hp hex ht he hw
  · have hl : ∀ i ∈ cl.leftVars, σ₁.lookup i = σ.lookup i := fun i hi =>
      ha i (by simp [Clause.exsFree, hi])
    exact .clauseEx hfn hmem hσ₁
      (PatVals.congr_varsRH hm fun j hj => hl j (List.mem_append_left _ hj))
      (fun t ht => Exec.EvalTerm.congr (hq t ht) fun i hi => (hl i (Clause.req_leftVarsRH ht i hi)).symm)
      (Holds.congr_NI hpre fun j hj => (hl j (Clause.pre_leftVarsRH j hj)).symm) hp hne grhs gens gpost
      (fun σ'' ha'' hs'' => hall σ'' (ha.trans ha'') hs'')
  · exact .exNone hfn hmem hne hσ hm hq hpre hp hsome hall

/-- One result at each argument list gives the coherence of every two clauses: each clause's
result at its match is an `Eval` result (`Clause.Res.eval`), and `FnDet` equates the two. -/
theorem Coherent.of_fnDet {c : Semantics} (hd : FnDet c) (cl cl' : Clause) : Coherent c cl cl' := by
  intro vs σ σ' _ _ _ _ _ _ ⟨f, fn, hfn, hmem, hmem', hdec, hdec'⟩
  exact .inr fun r r' h1 h2 => hd _ _ _ _ (h1.eval hfn hmem hdec) (h2.eval hfn hmem' hdec')

end KCore
