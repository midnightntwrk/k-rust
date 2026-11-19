/-
  KCore. On a definition with `coreOK`, `Semantics.hasValue` accepts every sort `Semantics.valued`
  accepts (`Semantics.hasValue_of_valued`).

  `valued` accepts Int and Bool, which have a probe literal (`hasLit`); the result sort of a
  constructor of `ctorSigs` without arguments; and a sort of which the search of Exhibit.lean
  holds a value. Each sort the search holds a value of is a seed's, which has a probe literal or
  an empty collection (`hasEmpty`), or is added by a round from a constructor of `ctorSigs` whose
  argument sorts the search holds, or from a subsort pair whose lower sort it holds. `hasValue` is
  closed under both (`Semantics.hasValue_ctor`, `Semantics.hasValue_sub`): the result sort of a
  constructor and the upper sort of a subsort pair are constructor sorts (`genWf`), which are in
  the universe of `witnessed`, and as many rounds as the universe has sorts reach a list a round
  adds nothing to. The search's own checks of its values (`sortOfT`, `rawFree`) are read at the
  seeds only.

  `coreOK` is read for `genWf` alone. Outside the review cone: `hasValue` does not read `valued`.
-/
import KcoreSpec.HasValueValue
import KcoreSpec.RightHeld

set_option autoImplicit false

namespace KCore

open Faithful

/-! ## The rounds of `witnessed` reach a closed list -/

private theorem hvo_countP_lt {α : Type} (p q : α → Bool) : ∀ (l : List α),
    (∀ x ∈ l, p x = true → q x = true) → (∃ x ∈ l, q x = true ∧ p x = false) →
    l.countP p < l.countP q
  | [], _, ⟨_, hx, _⟩ => by cases hx
  | a :: l, hpq, ⟨x, hx, hqx, hpx⟩ => by
    have hle : l.countP p ≤ l.countP q :=
      List.countP_mono_left fun y hy => hpq y (List.mem_cons_of_mem _ hy)
    rw [List.countP_cons, List.countP_cons]
    rcases List.mem_cons.mp hx with rfl | hx'
    · simp [hqx, hpx]; omega
    · have ih := hvo_countP_lt p q l (fun y hy => hpq y (List.mem_cons_of_mem _ hy)) ⟨x, hx', hqx, hpx⟩
      have ha := hpq a (List.mem_cons_self ..)
      cases hpa : p a
      · simp; omega
      · simp [ha hpa]; omega

/-- As many rounds as the universe has sorts, each adding the sorts of the universe a test accepts
at the list so far, reach a list the test adds nothing to. -/
private theorem hvo_rounds_closed (univ : List Srt) (cond : List Srt → Srt → Bool) (init : List Srt) :
    ∀ N ∈ univ, cond (Nat.repeat (fun inh => inh ++ univ.filter fun N => !inh.contains N && cond inh N)
        univ.length init) N = true →
      N ∈ Nat.repeat (fun inh => inh ++ univ.filter fun N => !inh.contains N && cond inh N) univ.length init := by
  generalize hstep : (fun inh => inh ++ univ.filter fun N => !inh.contains N && cond inh N) = step
  have hstepEq : ∀ inh, step inh = inh ++ univ.filter fun N => !inh.contains N && cond inh N := by
    intro inh; rw [← hstep]
  let m := fun (inh : List Srt) => univ.countP fun N => !inh.contains N
  let closed := fun (inh : List Srt) => ∀ N ∈ univ, cond inh N = true → N ∈ inh
  have fix : ∀ inh, closed inh → step inh = inh := by
    intro inh hc
    rw [hstepEq]
    have : (univ.filter fun N => !inh.contains N && cond inh N) = [] := by
      rw [List.filter_eq_nil_iff]
      intro N hN h
      rw [Bool.and_eq_true, Bool.not_eq_true', ← Bool.not_eq_true, List.contains_iff_mem] at h
      exact h.1 (hc N hN h.2)
    rw [this, List.append_nil]
  have dec : ∀ inh, ¬ closed inh → m (step inh) < m inh := by
    intro inh hc
    obtain ⟨N, hN, hcN, hNi⟩ : ∃ N, N ∈ univ ∧ cond inh N = true ∧ N ∉ inh := by
      apply Classical.byContradiction
      intro hne
      exact hc fun N hN hcN => Classical.byContradiction fun hNi => hne ⟨N, hN, hcN, hNi⟩
    have hsub : ∀ x, x ∈ inh → x ∈ step inh := fun x hx => by rw [hstepEq]; exact List.mem_append_left _ hx
    have hNs : N ∈ step inh := by
      rw [hstepEq]
      refine List.mem_append_right _ (List.mem_filter.mpr ⟨hN, ?_⟩)
      rw [Bool.and_eq_true, Bool.not_eq_true', ← Bool.not_eq_true, List.contains_iff_mem]
      exact ⟨hNi, hcN⟩
    refine hvo_countP_lt _ _ univ (fun x _ hx => ?_) ⟨N, hN, ?_, ?_⟩
    · rw [Bool.not_eq_true', ← Bool.not_eq_true, List.contains_iff_mem] at hx ⊢
      exact fun h => hx (hsub x h)
    · rw [Bool.not_eq_true', ← Bool.not_eq_true, List.contains_iff_mem]; exact hNi
    · rw [Bool.not_eq_false', List.contains_iff_mem]; exact hNs
  have main : ∀ j, closed (Nat.repeat step j init) ∨ m (Nat.repeat step j init) + j ≤ univ.length := by
    intro j
    induction j with
    | zero => exact Or.inr (List.countP_le_length (p := fun N => !init.contains N) (l := univ))
    | succ j ih =>
      have hr : Nat.repeat step (j + 1) init = step (Nat.repeat step j init) := rfl
      rw [hr]
      by_cases hc : closed (Nat.repeat step j init)
      · rw [fix _ hc]; exact Or.inl hc
      · rcases ih with ih | ih
        · exact absurd ih hc
        · have := dec _ hc
          exact Or.inr (by omega)
  intro N hN hcN
  rcases main univ.length with h | h
  · exact h N hN hcN
  · have h0 : m (Nat.repeat step univ.length init) = 0 := by omega
    have := List.countP_eq_zero.mp h0 N hN
    rw [Bool.not_eq_true, Bool.not_eq_false', List.contains_iff_mem] at this
    exact this

/-! ## The sorts of constructors and injections are in the universe of `witnessed` -/

private theorem hvo_univ {c : Semantics} {s : Srt} (h : s ∈ consSorts c) :
    s ∈ [Srt.k, Srt.kitem] ++ c.lib.sortsBelowKItem ++ c.userSorts := by
  have h1 := (List.mem_filter.mp h).1
  rcases List.mem_append.mp h1 with h2 | h2
  · exact List.mem_append_left _ (List.mem_append_left _ h2)
  · rcases List.mem_append.mp ((mem_sortBy _ _ _).mp h2) with h3 | h3
    · exact List.mem_append_right _ h3
    · exact List.mem_append_left _ (List.mem_append_right _ (List.mem_filter.mp h3).1)

/-- `witnessed` holds each sort of its universe a constructor of `ctorSigs` or an injection
generates from sorts it holds, or with a probe literal or an empty collection. -/
private theorem hvo_witnessed_closed (c : Semantics) {N : Srt}
    (hN : N ∈ [Srt.k, Srt.kitem] ++ c.lib.sortsBelowKItem ++ c.userSorts)
    (h : ((c.ctorSigs.any fun k => k.result == N &&
        k.args.all fun a => c.witnessed.contains a || c.hasLit a || c.hasEmpty a) ||
      (c.subsorts.any fun p => p.2 == N && (c.witnessed.contains p.1 || c.hasLit p.1 || c.hasEmpty p.1))) = true) :
    N ∈ c.witnessed :=
  hvo_rounds_closed ([Srt.k, Srt.kitem] ++ c.lib.sortsBelowKItem ++ c.userSorts)
    (fun inh N => (c.ctorSigs.any fun k => k.result == N &&
        k.args.all fun a => inh.contains a || c.hasLit a || c.hasEmpty a) ||
      (c.subsorts.any fun p => p.2 == N && (inh.contains p.1 || c.hasLit p.1 || c.hasEmpty p.1)))
    _ N hN h

private theorem hvo_ok {c : Semantics} {a : Srt} (h : c.hasValue a = true) :
    (c.witnessed.contains a || c.hasLit a || c.hasEmpty a) = true := by
  simp only [Semantics.hasValue, Bool.or_eq_true] at h ⊢
  rcases h with (h | h) | h
  · exact Or.inl (Or.inr h)
  · exact Or.inr h
  · exact Or.inl (Or.inl h)

/-- **The result sort of a constructor of `ctorSigs` whose argument sorts `hasValue` accepts,
`hasValue` accepts**, where the constructors' result sorts are constructor sorts (`genWf`). -/
theorem Semantics.hasValue_ctor {c : Semantics} (hg : genWf c = true) {k : CtorSig} (hk : k ∈ c.ctorSigs)
    (hargs : ∀ a ∈ k.args, c.hasValue a = true) : c.hasValue k.result = true := by
  have hw : k.result ∈ c.witnessed := by
    refine hvo_witnessed_closed c (hvo_univ (genWf_ctor hg hk)) ?_
    rw [Bool.or_eq_true]
    refine Or.inl (List.any_eq_true.mpr ⟨k, hk, ?_⟩)
    rw [Bool.and_eq_true, beq_iff_eq, List.all_eq_true]
    exact ⟨rfl, fun a ha => hvo_ok (hargs a ha)⟩
  simp only [Semantics.hasValue, Bool.or_eq_true]
  exact Or.inr (List.contains_iff_mem.mpr hw)

/-- **The upper sort of a subsort pair whose lower sort `hasValue` accepts, `hasValue` accepts**,
where the upper sorts are constructor sorts (`genWf`). -/
theorem Semantics.hasValue_sub {c : Semantics} (hg : genWf c = true) {a b : Srt} (hab : (a, b) ∈ c.subsorts)
    (ha : c.hasValue a = true) : c.hasValue b = true := by
  have hw : b ∈ c.witnessed := by
    refine hvo_witnessed_closed c (hvo_univ (genWf_sub hg hab).1) ?_
    rw [Bool.or_eq_true]
    refine Or.inr (List.any_eq_true.mpr ⟨(a, b), hab, ?_⟩)
    rw [Bool.and_eq_true, beq_iff_eq]
    exact ⟨rfl, hvo_ok ha⟩
  simp only [Semantics.hasValue, Bool.or_eq_true]
  exact Or.inr (List.contains_iff_mem.mpr hw)

/-! ## Each sort the search holds a value of, `hasValue` accepts -/

private theorem hvo_firstPerSort_sub {l : List (Srt × GroundTerm)} {x : Srt × GroundTerm}
    (h : x ∈ Parse.firstPerSort l) : x ∈ l := by
  have key : ∀ (l acc : List (Srt × GroundTerm)),
      x ∈ l.foldl (fun acc (p : Srt × GroundTerm) => if acc.any (·.1 == p.1) then acc else acc ++ [p]) acc →
      x ∈ acc ∨ x ∈ l := by
    intro l
    induction l with
    | nil => exact fun acc h => Or.inl h
    | cons p l ih =>
      intro acc h
      rw [List.foldl_cons] at h
      rcases ih _ h with h1 | h1
      · split at h1
        · exact Or.inl h1
        · rcases List.mem_append.mp h1 with h2 | h2
          · exact Or.inl h2
          · exact Or.inr (List.mem_cons.mpr (Or.inl (List.mem_singleton.mp h2)))
      · exact Or.inr (List.mem_cons_of_mem _ h1)
  rcases key l [] h with h | h
  · cases h
  · exact h

private theorem hvo_lookup_mem {acc : List (Srt × GroundTerm)} {a : Srt} {w : GroundTerm}
    (h : acc.lookup a = some w) : (a, w) ∈ acc := by
  induction acc with
  | nil => cases h
  | cons p acc ih =>
    obtain ⟨b, v⟩ := p
    rw [List.lookup_cons] at h
    split at h
    · rename_i hab
      cases h
      rw [beq_iff_eq] at hab
      subst hab
      exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (ih h)

private theorem hvo_mapM_some {f : Srt → Option GroundTerm} : ∀ {l : List Srt} {ws : List GroundTerm},
    l.mapM f = some ws → ∀ a ∈ l, ∃ w, f a = some w
  | [], _, _, a, ha => by cases ha
  | b :: l, ws, h, a, ha => by
    rw [List.mapM_cons] at h
    cases hb : f b with
    | none => rw [hb] at h; cases h
    | some w =>
      cases hl : l.mapM f with
      | none => rw [hb, hl] at h; cases h
      | some ws' =>
        rcases List.mem_cons.mp ha with rfl | ha'
        · exact ⟨w, hb⟩
        · exact hvo_mapM_some hl a ha'

/-- A seed of the search is of a sort with a probe literal or an empty collection. -/
private theorem hvo_seeds {c : Semantics} {p : Srt × GroundTerm} (h : p ∈ Parse.exhibitSeeds c (tables c)) :
    c.hasValue p.1 = true := by
  have h1 := List.mem_filter.mp (hvo_firstPerSort_sub h)
  obtain ⟨s, v⟩ := p
  have hsort : sortOfT (tables c) c.lib v = some s := by simpa using h1.2
  simp only [Semantics.hasValue, Bool.or_eq_true]
  rcases List.mem_append.mp h1.1 with hl | hc
  · obtain ⟨s', -, hv⟩ := List.mem_flatMap.mp hl
    refine Or.inl (Or.inl ?_)
    simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hv
    have lit : ∀ lit, v = .dv s lit → dvOK c.lib s lit = true := by
      intro lit hv'
      subst hv'
      rw [sortOfT] at hsort
      split at hsort
      · assumption
      · cases hsort
    rcases hv with ⟨rfl, hv⟩ | ⟨rfl, hv⟩ | ⟨rfl, hv⟩
    · exact List.any_eq_true.mpr ⟨.int 0, by simp, lit _ hv⟩
    · exact List.any_eq_true.mpr ⟨.bool true, by simp, lit (.bool false) hv⟩
    · exact List.any_eq_true.mpr ⟨.tok "", by simp, lit _ hv⟩
  · obtain ⟨k, -, hv⟩ := List.mem_flatMap.mp hc
    refine Or.inl (Or.inr ?_)
    simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hv
    rcases hv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [sortOfT, collOf_tables] at hsort
      unfold Semantics.hasEmpty
      cases hk : c.collOf k.sort with
      | none => simp [hk] at hsort
      | some k' =>
        cases hval : k'.val with
        | none => simp [hk, hval] at hsort
        | some vs =>
          cases hkind : k'.kind <;> simp [hk, hval, hkind] at hsort ⊢
    · rw [sortOfT, collOf_tables] at hsort
      unfold Semantics.hasEmpty
      cases hk : c.collOf k.sort with
      | none => simp [hk] at hsort
      | some k' => cases hkind : k'.kind <;> simp [hk, hkind, sortsOfT] at hsort ⊢
    · rw [sortOfT, collOf_tables] at hsort
      unfold Semantics.hasEmpty
      cases hk : c.collOf k.sort with
      | none => simp [hk] at hsort
      | some k' => cases hkind : k'.kind <;> simp [hk, hkind, sortsOfT] at hsort ⊢

/-- A round keeps "each sort the list holds a value of, `hasValue` accepts". -/
private theorem hvo_round {c : Semantics} (hg : genWf c = true) (T : Tables) {acc : List (Srt × GroundTerm)}
    (hacc : ∀ p ∈ acc, c.hasValue p.1 = true) :
    ∀ p ∈ Parse.exhibitRound c T acc, c.hasValue p.1 = true := by
  intro p hp
  have hlk : ∀ a w, acc.lookup a = some w → c.hasValue a = true := fun a w h => hacc _ (hvo_lookup_mem h)
  rcases List.mem_append.mp (hvo_firstPerSort_sub hp) with h | h
  · obtain ⟨k, hk, hkp⟩ := List.mem_filterMap.mp h
    split at hkp
    · cases hkp
    · cases hm : k.args.mapM fun a => acc.lookup a with
      | none => simp [hm] at hkp
      | some args =>
        have hres : p.1 = k.result := by
          simp only [hm] at hkp
          simp only [Option.bind_eq_bind, Option.bind_some] at hkp
          split at hkp
          · cases hkp; rfl
          · cases hkp
        rw [hres]
        refine Semantics.hasValue_ctor hg hk fun a ha => ?_
        obtain ⟨w, hw⟩ := hvo_mapM_some hm a ha
        exact hlk a w hw
  · obtain ⟨⟨a, b⟩, hab, hkp⟩ := List.mem_filterMap.mp h
    simp only at hkp
    split at hkp
    · cases hkp
    · cases hw : acc.lookup a with
      | none => simp [hw] at hkp
      | some w =>
        have hres : p.1 = b := by
          simp only [hw] at hkp
          simp only [Option.bind_eq_bind, Option.bind_some] at hkp
          split at hkp <;> split at hkp <;> first | (cases hkp; rfl) | cases hkp
        rw [hres]
        exact Semantics.hasValue_sub hg hab (hlk a w hw)

private theorem hvo_rounds {c : Semantics} (hg : genWf c = true) (T : Tables) :
    ∀ (n : Nat) (acc : List (Srt × GroundTerm)), (∀ p ∈ acc, c.hasValue p.1 = true) →
      ∀ p ∈ Parse.exhibitN c T n acc, c.hasValue p.1 = true
  | 0, acc, hacc => by rw [Parse.exhibitN]; exact hacc
  | n + 1, acc, hacc => by
    rw [Parse.exhibitN]
    split
    · exact hacc
    · refine hvo_rounds hg T n _ fun p hp => ?_
      rcases List.mem_append.mp hp with hp | hp
      · exact hacc p hp
      · exact hvo_round hg T hacc p hp

/-- **A sort `valued` accepts, `hasValue` accepts**, where the result sorts of the constructors and
the upper sorts of the subsort pairs are constructor sorts (`genWf`). -/
theorem Semantics.hasValue_of_valued_of {c : Semantics} (hg : genWf c = true) {s : Srt}
    (h : c.valued s = true) : c.hasValue s = true := by
  simp only [Semantics.valued, Bool.or_eq_true, beq_iff_eq, List.any_eq_true, Option.any_eq_true,
    Bool.and_eq_true, List.isEmpty_iff] at h
  rcases h with ((rfl | rfl) | ⟨k, -, k', hk', ha, rfl⟩) | hx
  · simp only [Semantics.hasValue, Bool.or_eq_true]
    exact Or.inl (Or.inl (List.any_eq_true.mpr ⟨.int 0, by simp, rfl⟩))
  · simp only [Semantics.hasValue, Bool.or_eq_true]
    exact Or.inl (Or.inl (List.any_eq_true.mpr ⟨.bool true, by simp, rfl⟩))
  · exact Semantics.hasValue_ctor hg (lookupSig_spec hk').1 fun a ha' => by rw [ha] at ha'; cases ha'
  · obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hx
    unfold Parse.exhibit? at hv
    obtain ⟨hl, -⟩ := Option.filter_eq_some_iff.mp hv
    exact hvo_rounds hg (tables c) _ _ (fun p hp => hvo_seeds hp) (s, v) (hvo_lookup_mem hl)

/-- **`hasValue_of_valued`.** On a definition with `coreOK`, a sort `valued` accepts, `hasValue`
accepts. -/
theorem Semantics.hasValue_of_valued {c : Semantics} (h : c.coreOK = true) {s : Srt}
    (hs : c.valued s = true) : c.hasValue s = true :=
  Semantics.hasValue_of_valued_of (faithCoreOK_parts (Semantics.coreOK_parts h).2.1).2.1 hs

end KCore

