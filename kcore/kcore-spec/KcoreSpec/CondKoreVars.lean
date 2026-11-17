/-
  KCore. The variables of a condition's pattern.

  A variable in scope that a condition holds is free in its pattern and one of the pattern's
  variables (`condKore_keys`); a free variable of a well-sorted condition's pattern is a variable
  of the condition in scope (`freeOf_condKore`). Both are read where a clause's or a rule's
  premise carries its predicate.
-/
import KcoreSpec.CondTwoTables

set_option autoImplicit false

namespace KCore

namespace Faithful

namespace Model

open ML

variable {c : Semantics}

/-- Under the binders of `existsAll`, the bound variables are the binders', innermost first, and
the outer ones. -/
theorem freeOf_existsAll_eqEx {S : Kore.KSort} {body : Kore.Pattern} :
    ∀ (bs : List Kore.EVar) (bound : List KoreAML.VarKey),
    KoreAML.freeOf bound (KoreAML.existsAll S bs body) =
      KoreAML.freeOf ((bs.map KoreAML.evarKey).reverse ++ bound) body
  | [], bound => rfl
  | b :: bs, bound => by
    show KoreAML.freeOf bound (.exist S b (KoreAML.existsAll S bs body)) = _
    rw [KoreAML.freeOf, freeOf_existsAll_eqEx bs]
    simp [List.reverse_cons, List.append_assoc]

theorem varsOf_existsAll_bodyEx {S : Kore.KSort} {body : Kore.Pattern} {k : KoreAML.VarKey}
    (hk : k ∈ KoreAML.varsOf body) : ∀ (bs : List Kore.EVar), k ∈ KoreAML.varsOf (KoreAML.existsAll S bs body)
  | [] => hk
  | b :: bs => by
    show k ∈ KoreAML.varsOf (.exist S b (KoreAML.existsAll S bs body))
    rw [KoreAML.varsOf]
    exact List.mem_append_right _ (varsOf_existsAll_bodyEx hk bs)

mutual
  /-- A variable of a term that a list of bound keys does not hold is free in its pattern. -/
  theorem kore_freeOfBEx (c : Semantics) (vs : List KoreAML.Var) {bound : List KoreAML.VarKey} :
      ∀ (t : Term) {i : Nat}, i ∈ varOccs t → bound.contains (KoreAML.evarKey (vs.getD i default).kore) = false →
      KoreAML.evarKey (vs.getD i default).kore ∈ KoreAML.freeOf bound (Term.kore c vs t)
    | .var j, i, h, hb => by
      rw [varOccs] at h
      have hij := mem_one h
      subst hij
      rw [Term.kore]; unfold KoreAML.varAt; rw [KoreAML.freeOf]
      simp only [hb]
      simp
    | .app f ts, i, h, hb => by
      rw [varOccs] at h
      rw [kore_app]
      obtain ⟨hd, ss, he, _⟩ := symApp_cases c f (Term.koreList c vs ts)
      rw [he, KoreAML.freeOf]
      exact kore_freeOfListBEx c vs ts h hb
    | .inj a b t, i, h, hb => by
      rw [varOccs] at h
      rw [Term.kore]; unfold KoreAML.injP; rw [KoreAML.freeOf, KoreAML.freeOfList, KoreAML.freeOfList]
      simp only [List.append_nil]
      exact kore_freeOfBEx c vs t h hb
    | .as t j, i, h, hb => by
      rw [varOccs] at h
      rw [Term.kore, KoreAML.freeOf, KoreAML.freeOfList, KoreAML.freeOfList, KoreAML.freeOfList]
      simp only [List.append_nil, List.mem_append]
      rcases List.mem_append.mp h with h | h
      · exact Or.inl (kore_freeOfBEx c vs t h hb)
      · right
        have hij := mem_one h
        subst hij
        unfold KoreAML.varAt; rw [KoreAML.freeOf]
        simp only [hb]
        simp
    | .dv s lit, i, h, _ => by rw [varOccs] at h; cases h
  theorem kore_freeOfListBEx (c : Semantics) (vs : List KoreAML.Var) {bound : List KoreAML.VarKey} :
      ∀ (ts : List Term) {i : Nat}, i ∈ varOccsList ts →
      bound.contains (KoreAML.evarKey (vs.getD i default).kore) = false →
      KoreAML.evarKey (vs.getD i default).kore ∈ KoreAML.freeOfList bound (Term.koreList c vs ts)
    | [], i, h, _ => by rw [varOccsList] at h; cases h
    | t :: ts, i, h, hb => by
      rw [varOccsList] at h
      rw [Term.koreList, KoreAML.freeOfList]
      rcases List.mem_append.mp h with h | h
      · exact List.mem_append_left _ (kore_freeOfBEx c vs t h hb)
      · exact List.mem_append_right _ (kore_freeOfListBEx c vs ts h hb)
end

/-! ## The variables of a condition's pattern -/

theorem canonKey_eqKore (vars : List Srt) (i : Nat) :
    canonKey c vars i = KoreAML.evarKey ((canonVars c vars).getD i default).kore := rfl

/-- The keys of the binders of a match are the canonical keys past the variables in scope. -/
theorem matchBinder_keys (vars ys : List Srt) {k : KoreAML.VarKey}
    (hk : k ∈ (((((List.range ys.length).zip ys).map
      (fun (j, y) => Cond.binder c ((canonVars c vars).length + j) y)).map KoreAML.Var.kore).map
        KoreAML.evarKey)) :
    ∃ j, vars.length ≤ j ∧ j < (vars ++ ys).length ∧ k = canonKey c (vars ++ ys) j := by
  rw [binders_eqStdI, List.map_map, List.mem_map] at hk
  obtain ⟨j, hj, rfl⟩ := hk
  rw [List.mem_range'_1] at hj
  exact ⟨j, hj.1, by simp; omega, rfl⟩

/-- A free variable of a member of a conjunction is one of the conjunction, under any bound keys. -/
theorem freeOf_and_memB {S : Kore.KSort} {bound : List KoreAML.VarKey} {p : Kore.Pattern} {k : KoreAML.VarKey}
    (hk : k ∈ KoreAML.freeOf bound p) : ∀ {ps : List Kore.Pattern}, p ∈ ps → k ∈ KoreAML.freeOf bound (.and S ps)
  | q :: qs, hp => by
    rw [KoreAML.freeOf, KoreAML.freeOfList]
    rcases List.mem_cons.mp hp with rfl | hp
    · exact List.mem_append_left _ hk
    · have := freeOf_and_memB (S := S) hk hp
      rw [KoreAML.freeOf] at this
      exact List.mem_append_right _ this

/-- **A variable in scope of a condition is free in its pattern** (where the bound keys do not hold
it) **and one of its variables.** -/
theorem condKore_keys (S : Kore.KSort) : ∀ (p : Cond) {vars : List Srt} {bound : List KoreAML.VarKey} {i : Nat},
    i < vars.length → i ∈ varOccsCond vars.length p → bound.contains (canonKey c vars i) = false →
    canonKey c vars i ∈ KoreAML.freeOf bound (Cond.kore c (canonVars c vars) S p) ∧
      canonKey c vars i ∈ KoreAML.varsOf (Cond.kore c (canonVars c vars) S p)
  | .top, _, _, _, _, h, _ => by simp [varOccsCond] at h
  | .bot, _, _, _, _, h, _ => by simp [varOccsCond] at h
  | .not p, vars, bound, i, hi, h, hb => by
    rw [varOccsCond] at h
    obtain ⟨k1, k2⟩ := condKore_keys S p hi h hb
    simp only [Cond.kore, KoreAML.freeOf, KoreAML.varsOf]
    exact ⟨k1, List.mem_append_right _ k2⟩
  | .and p q, vars, bound, i, hi, h, hb => by
    rw [varOccsCond] at h
    simp only [Cond.kore, KoreAML.freeOf, KoreAML.freeOfList, KoreAML.varsOf, KoreAML.varsOfList,
      List.append_nil, List.mem_append]
    rcases List.mem_append.mp h with h | h
    · obtain ⟨k1, k2⟩ := condKore_keys S p hi h hb; exact ⟨Or.inl k1, Or.inr (Or.inl k2)⟩
    · obtain ⟨k1, k2⟩ := condKore_keys S q hi h hb; exact ⟨Or.inr k1, Or.inr (Or.inr k2)⟩
  | .or p q, vars, bound, i, hi, h, hb => by
    rw [varOccsCond] at h
    simp only [Cond.kore, KoreAML.freeOf, KoreAML.freeOfList, KoreAML.varsOf, KoreAML.varsOfList,
      List.append_nil, List.mem_append]
    rcases List.mem_append.mp h with h | h
    · obtain ⟨k1, k2⟩ := condKore_keys S p hi h hb; exact ⟨Or.inl k1, Or.inr (Or.inl k2)⟩
    · obtain ⟨k1, k2⟩ := condKore_keys S q hi h hb; exact ⟨Or.inr k1, Or.inr (Or.inr k2)⟩
  | .implies p q, vars, bound, i, hi, h, hb => by
    rw [varOccsCond] at h
    simp only [Cond.kore, KoreAML.freeOf, KoreAML.varsOf, List.mem_append]
    rcases List.mem_append.mp h with h | h
    · obtain ⟨k1, k2⟩ := condKore_keys S p hi h hb; exact ⟨Or.inl k1, Or.inl (Or.inr k2)⟩
    · obtain ⟨k1, k2⟩ := condKore_keys S q hi h hb; exact ⟨Or.inr k1, Or.inr k2⟩
  | .ceil s t, vars, bound, i, hi, h, hb => by
    rw [varOccsCond] at h
    rw [canonKey_eqKore] at hb ⊢
    have k1 := kore_freeOfBEx c (canonVars c vars) t h hb
    have k2 := varsOf_kore c (canonVars c vars) t h
    simp only [Cond.kore, KoreAML.freeOf, KoreAML.varsOf, List.mem_append]
    exact ⟨k1, Or.inr k2⟩
  | .equals s t u, vars, bound, i, hi, h, hb => by
    rw [varOccsCond] at h
    rw [canonKey_eqKore] at hb ⊢
    simp only [Cond.kore, KoreAML.freeOf, KoreAML.varsOf, List.mem_append]
    rcases List.mem_append.mp h with h | h
    · exact ⟨Or.inl (kore_freeOfBEx c (canonVars c vars) t h hb),
        Or.inl (Or.inr (varsOf_kore c (canonVars c vars) t h))⟩
    · exact ⟨Or.inr (kore_freeOfBEx c (canonVars c vars) u h hb), Or.inr (varsOf_kore c (canonVars c vars) u h)⟩
  | .mem s t u, vars, bound, i, hi, h, hb => by
    rw [varOccsCond] at h
    rw [canonKey_eqKore] at hb ⊢
    simp only [Cond.kore, KoreAML.freeOf, KoreAML.varsOf, List.mem_append]
    rcases List.mem_append.mp h with h | h
    · exact ⟨Or.inl (kore_freeOfBEx c (canonVars c vars) t h hb),
        Or.inl (Or.inr (varsOf_kore c (canonVars c vars) t h))⟩
    · exact ⟨Or.inr (kore_freeOfBEx c (canonVars c vars) u h hb), Or.inr (varsOf_kore c (canonVars c vars) u h)⟩
  | .ex s body, vars, bound, i, hi, h, hb => by
    rw [varOccsCond] at h
    have h' := (List.mem_filter.mp h).1
    have hi' : i < (vars ++ [s]).length := by simp; omega
    have hocc : i ∈ varOccsCond (vars ++ [s]).length body := by simpa using h'
    have hne : canonKey c (vars ++ [s]) i ≠ canonKey c (vars ++ [s]) vars.length := fun he => by
      have := canonKey_inj hi' (by simp) he; omega
    have hb' : (canonKey c (vars ++ [s]) vars.length :: bound).contains (canonKey c (vars ++ [s]) i) = false := by
      rw [canonKey_appendStdI hi]
      rw [canonKey_appendStdI hi] at hne
      have hb2 : ¬ canonKey c vars i ∈ bound := by simpa [List.contains_iff_mem] using hb
      simp [hne, hb2]
    obtain ⟨k1, k2⟩ := condKore_keys S body hi' hocc hb'
    rw [canonKey_appendStdI hi] at k1 k2
    simp only [Cond.kore]
    rw [KoreAML.freeOf, KoreAML.varsOf, binder_keyStdI, canonVars_snocStdI]
    exact ⟨k1, List.mem_append_right _ k2⟩
  | .all s body, vars, bound, i, hi, h, hb => by
    rw [varOccsCond] at h
    have h' := (List.mem_filter.mp h).1
    have hi' : i < (vars ++ [s]).length := by simp; omega
    have hocc : i ∈ varOccsCond (vars ++ [s]).length body := by simpa using h'
    have hne : canonKey c (vars ++ [s]) i ≠ canonKey c (vars ++ [s]) vars.length := fun he => by
      have := canonKey_inj hi' (by simp) he; omega
    have hb' : (canonKey c (vars ++ [s]) vars.length :: bound).contains (canonKey c (vars ++ [s]) i) = false := by
      rw [canonKey_appendStdI hi]
      rw [canonKey_appendStdI hi] at hne
      have hb2 : ¬ canonKey c vars i ∈ bound := by simpa [List.contains_iff_mem] using hb
      simp [hne, hb2]
    obtain ⟨k1, k2⟩ := condKore_keys S body hi' hocc hb'
    rw [canonKey_appendStdI hi] at k1 k2
    simp only [Cond.kore]
    rw [KoreAML.freeOf, KoreAML.varsOf, binder_keyStdI, canonVars_snocStdI]
    exact ⟨k1, List.mem_append_right _ k2⟩
  | .exMatch ys s p t body, vars, bound, i, hi, h, hb => by
    rw [varOccsCond] at h
    have hi' : i < (vars ++ ys).length := by simp; omega
    let bs := ((List.range ys.length).zip ys).map
      (fun (j, y) => Cond.binder c ((canonVars c vars).length + j) y)
    have hbs : canonVars c vars ++ bs = canonVars c (vars ++ ys) := canonVars_appendStdI c vars ys
    have hb' : (((bs.map KoreAML.Var.kore).map KoreAML.evarKey).reverse ++ bound).contains
        (canonKey c vars i) = false := by
      rw [List.contains_append, hb, Bool.or_false]
      apply Bool.eq_false_iff.mpr
      intro hc
      rw [List.contains_iff_mem, List.mem_reverse] at hc
      obtain ⟨j, hj, hj', he⟩ := matchBinder_keys vars ys hc
      rw [← canonKey_appendStdI (ys := ys) hi] at he
      have := canonKey_inj hi' hj' he
      omega
    have hbK : (((bs.map KoreAML.Var.kore).map KoreAML.evarKey).reverse ++ bound).contains
        (canonKey c (vars ++ ys) i) = false := by rw [canonKey_appendStdI hi]; exact hb'
    show canonKey c vars i ∈ KoreAML.freeOf bound (KoreAML.existsAll S (bs.map KoreAML.Var.kore)
        (.and S [.in (srtOf c s) S (Term.kore c (canonVars c vars) t) (Term.kore c (canonVars c vars ++ bs) p),
          Cond.kore c (canonVars c vars ++ bs) S body])) ∧
      canonKey c vars i ∈ KoreAML.varsOf (KoreAML.existsAll S (bs.map KoreAML.Var.kore)
        (.and S [.in (srtOf c s) S (Term.kore c (canonVars c vars) t) (Term.kore c (canonVars c vars ++ bs) p),
          Cond.kore c (canonVars c vars ++ bs) S body]))
    rw [freeOf_existsAll_eqEx, hbs]
    have hin : ∀ {φ : Kore.Pattern},
        φ ∈ [Kore.Pattern.in (srtOf c s) S (Term.kore c (canonVars c vars) t) (Term.kore c (canonVars c (vars ++ ys)) p),
          Cond.kore c (canonVars c (vars ++ ys)) S body] →
        canonKey c vars i ∈ KoreAML.freeOf (((bs.map KoreAML.Var.kore).map KoreAML.evarKey).reverse ++ bound) φ →
        canonKey c vars i ∈ KoreAML.varsOf φ →
        canonKey c vars i ∈ KoreAML.freeOf (((bs.map KoreAML.Var.kore).map KoreAML.evarKey).reverse ++ bound)
          (.and S [.in (srtOf c s) S (Term.kore c (canonVars c vars) t) (Term.kore c (canonVars c (vars ++ ys)) p),
            Cond.kore c (canonVars c (vars ++ ys)) S body]) ∧
        canonKey c vars i ∈ KoreAML.varsOf (KoreAML.existsAll S (bs.map KoreAML.Var.kore)
          (.and S [.in (srtOf c s) S (Term.kore c (canonVars c vars) t) (Term.kore c (canonVars c (vars ++ ys)) p),
            Cond.kore c (canonVars c (vars ++ ys)) S body])) := fun hφ k1 k2 =>
      ⟨freeOf_and_memB k1 hφ, varsOf_existsAll_bodyEx (varsOf_and_mem hφ k2) _⟩
    rcases List.mem_append.mp h with h | h
    · rw [canonKey_eqKore] at hb' ⊢
      refine hin (List.mem_cons_self ..) ?_ ?_
      · rw [KoreAML.freeOf]; exact List.mem_append_left _ (kore_freeOfBEx c (canonVars c vars) t h hb')
      · rw [KoreAML.varsOf]
        exact List.mem_append_left _ (List.mem_append_right _ (varsOf_kore c (canonVars c vars) t h))
    · obtain ⟨h, -⟩ := List.mem_filter.mp h
      rw [← canonKey_appendStdI (ys := ys) hi] at hin ⊢
      rcases List.mem_append.mp h with h | h
      · rw [canonKey_eqKore] at hbK ⊢
        refine hin (List.mem_cons_self ..) ?_ ?_
        · rw [KoreAML.freeOf]
          exact List.mem_append_right _ (kore_freeOfBEx c (canonVars c (vars ++ ys)) p h hbK)
        · rw [KoreAML.varsOf]; exact List.mem_append_right _ (varsOf_kore c (canonVars c (vars ++ ys)) p h)
      · have hocc : i ∈ varOccsCond (vars ++ ys).length body := by simpa using h
        obtain ⟨k1, k2⟩ := condKore_keys S body hi' hocc hbK
        exact hin (List.mem_cons_of_mem _ (List.mem_cons_self ..)) k1 k2

/-- A free variable of a conjunction is free in one of its members. -/
theorem mem_freeOf_and {S : Kore.KSort} {bound : List KoreAML.VarKey} {k : KoreAML.VarKey} :
    ∀ {ps : List Kore.Pattern}, k ∈ KoreAML.freeOf bound (.and S ps) → ∃ p ∈ ps, k ∈ KoreAML.freeOf bound p
  | [], h => by simp [KoreAML.freeOf, KoreAML.freeOfList] at h
  | q :: qs, h => by
    rw [KoreAML.freeOf, KoreAML.freeOfList] at h
    rcases List.mem_append.mp h with h | h
    · exact ⟨q, List.mem_cons_self .., h⟩
    · obtain ⟨p, hp, h'⟩ := mem_freeOf_and (S := S) (ps := qs) (by rw [KoreAML.freeOf]; exact h)
      exact ⟨p, List.mem_cons_of_mem _ hp, h'⟩

/-- **A free variable of a well-sorted condition's pattern is a variable of the condition in
scope**, and the bound keys do not hold it. -/
theorem freeOf_condKore (S : Kore.KSort) : ∀ (p : Cond) {vars : List Srt} {bound : List KoreAML.VarKey}
    {k : KoreAML.VarKey}, c.condOK vars p = true →
    k ∈ KoreAML.freeOf bound (Cond.kore c (canonVars c vars) S p) →
    bound.contains k = false ∧ ∃ i ∈ varOccsCond vars.length p, k = canonKey c vars i
  | .top, _, _, _, _, h => by simp [Cond.kore, KoreAML.freeOf] at h
  | .bot, _, _, _, _, h => by simp [Cond.kore, KoreAML.freeOf] at h
  | .not p, vars, bound, k, hok, h => by
    rw [Semantics.condOK] at hok
    simp only [Cond.kore, KoreAML.freeOf] at h
    rw [varOccsCond]
    exact freeOf_condKore S p hok h
  | .and p q, vars, bound, k, hok, h | .or p q, vars, bound, k, hok, h => by
    rw [Semantics.condOK, Bool.and_eq_true] at hok
    simp only [Cond.kore, KoreAML.freeOf, KoreAML.freeOfList, List.append_nil, List.mem_append] at h
    rw [varOccsCond]
    rcases h with h | h
    · obtain ⟨hb, i, hi, rfl⟩ := freeOf_condKore S p hok.1 h
      exact ⟨hb, i, List.mem_append_left _ hi, rfl⟩
    · obtain ⟨hb, i, hi, rfl⟩ := freeOf_condKore S q hok.2 h
      exact ⟨hb, i, List.mem_append_right _ hi, rfl⟩
  | .implies p q, vars, bound, k, hok, h => by
    rw [Semantics.condOK, Bool.and_eq_true] at hok
    simp only [Cond.kore, KoreAML.freeOf, List.mem_append] at h
    rw [varOccsCond]
    rcases h with h | h
    · obtain ⟨hb, i, hi, rfl⟩ := freeOf_condKore S p hok.1 h
      exact ⟨hb, i, List.mem_append_left _ hi, rfl⟩
    · obtain ⟨hb, i, hi, rfl⟩ := freeOf_condKore S q hok.2 h
      exact ⟨hb, i, List.mem_append_right _ hi, rfl⟩
  | .ceil s t, vars, bound, k, _, h => by
    simp only [Cond.kore, KoreAML.freeOf] at h
    obtain ⟨hb, i, hi, rfl⟩ := freeOf_kore_bound c _ t h
    rw [varOccsCond]
    exact ⟨hb, i, hi, rfl⟩
  | .equals s t u, vars, bound, k, _, h | .mem s t u, vars, bound, k, _, h => by
    simp only [Cond.kore, KoreAML.freeOf, List.mem_append] at h
    rw [varOccsCond]
    rcases h with h | h
    · obtain ⟨hb, i, hi, rfl⟩ := freeOf_kore_bound c _ t h
      exact ⟨hb, i, List.mem_append_left _ hi, rfl⟩
    · obtain ⟨hb, i, hi, rfl⟩ := freeOf_kore_bound c _ u h
      exact ⟨hb, i, List.mem_append_right _ hi, rfl⟩
  | .ex s body, vars, bound, k, hok, h | .all s body, vars, bound, k, hok, h => by
    rw [Semantics.condOK] at hok
    simp only [Cond.kore] at h
    rw [KoreAML.freeOf, binder_keyStdI, canonVars_snocStdI] at h
    obtain ⟨hb, i, hi, rfl⟩ := freeOf_condKore S body hok h
    have hlt : i < vars.length + 1 := by
      have := varOccsCond_lt_twoT body hok i hi; simpa using this
    have hne : i ≠ vars.length := fun he => by
      subst he; simp at hb
    have hi' : i < vars.length := by omega
    rw [canonKey_appendStdI hi']
    rw [canonKey_appendStdI hi'] at hb
    refine ⟨by simp only [List.contains_cons, Bool.or_eq_false_iff] at hb; exact hb.2, i, ?_, rfl⟩
    rw [varOccsCond]
    exact List.mem_filter.mpr ⟨by simpa using hi, by simpa using hi'⟩
  | .exMatch ys s p t body, vars, bound, k, hok, h => by
    rw [Semantics.condOK] at hok
    simp only [Bool.and_eq_true, beq_iff_eq] at hok
    obtain ⟨⟨⟨hpS, -⟩, hbody⟩, -⟩ := hok
    let bs := ((List.range ys.length).zip ys).map
      (fun (j, y) => Cond.binder c ((canonVars c vars).length + j) y)
    have hbs : canonVars c vars ++ bs = canonVars c (vars ++ ys) := canonVars_appendStdI c vars ys
    change k ∈ KoreAML.freeOf bound (KoreAML.existsAll S (bs.map KoreAML.Var.kore)
        (.and S [.in (srtOf c s) S (Term.kore c (canonVars c vars) t) (Term.kore c (canonVars c vars ++ bs) p),
          Cond.kore c (canonVars c vars ++ bs) S body])) at h
    rw [freeOf_existsAll_eqEx, hbs] at h
    -- the binders' keys are the canonical keys past the variables in scope
    have hB : ∀ j, vars.length ≤ j → j < (vars ++ ys).length →
        (((bs.map KoreAML.Var.kore).map KoreAML.evarKey).reverse ++ bound).contains
          (canonKey c (vars ++ ys) j) = true := fun j hj hj' => by
      rw [List.contains_append, Bool.or_eq_true]
      left
      apply List.contains_iff_mem.mpr
      rw [List.mem_reverse, binders_eqStdI, List.map_map]
      exact List.mem_map.mpr ⟨j, List.mem_range'_1.mpr ⟨hj, by simp at hj'; omega⟩, rfl⟩
    have hbound : ∀ {k}, (((bs.map KoreAML.Var.kore).map KoreAML.evarKey).reverse ++ bound).contains k = false →
        bound.contains k = false := fun hb => by
      rw [List.contains_append, Bool.or_eq_false_iff] at hb; exact hb.2
    -- a variable under the binders that they do not hold is in scope
    have hin : ∀ i, i < (vars ++ ys).length →
        (((bs.map KoreAML.Var.kore).map KoreAML.evarKey).reverse ++ bound).contains
          (canonKey c (vars ++ ys) i) = false → i < vars.length := fun i hi hb =>
      Classical.byContradiction fun hn => by
        rw [hB i (by omega) hi] at hb; cases hb
    rcases mem_freeOf_and h with ⟨φ, hφ, hk⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hφ
    rw [varOccsCond]
    rcases hφ with rfl | rfl
    · rw [KoreAML.freeOf, List.mem_append] at hk
      rcases hk with hk | hk
      · obtain ⟨hb, i, hi, rfl⟩ := freeOf_kore_bound c _ t hk
        exact ⟨hbound hb, i, List.mem_append_left _ hi, rfl⟩
      · obtain ⟨hb, i, hi, rfl⟩ := freeOf_kore_bound c _ p hk
        have hlt := varOccs_lt p hpS i hi
        have hi' := hin i hlt hb
        refine ⟨hbound hb, i, List.mem_append_right _ (List.mem_filter.mpr
          ⟨List.mem_append_left _ hi, by simpa using hi'⟩), ?_⟩
        exact canonKey_appendStdI hi'
    · obtain ⟨hb, i, hi, rfl⟩ := freeOf_condKore S body hbody hk
      have hlt := varOccsCond_lt_twoT body hbody i hi
      have hi' := hin i hlt hb
      refine ⟨hbound hb, i, List.mem_append_right _ (List.mem_filter.mpr
        ⟨List.mem_append_right _ (by simpa using hi), by simpa using hi'⟩), ?_⟩
      exact canonKey_appendStdI hi'


end Model

end Faithful

end KCore
