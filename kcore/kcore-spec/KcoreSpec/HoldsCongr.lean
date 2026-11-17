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

end KCore
