/-
  kore.k's `leq` on an embedded subsort table: its value at `K₀ sig`.

  `above(A, B, T, All, F)` evaluates, at every two Ints and every three tables, to the mirror
  `aboveF a b T All F` (KKMatchF.lean): by induction on the fuel `F` and then on the table `T`,
  the equation that applies is `above-nil` at `T = .Subs`, `above-dry` at the fuel `.Subs`, and
  else `above-hit` where the entry starts at `A` (its calls at the shorter fuel, and at the same
  fuel and the shorter table) or `above-miss` where it does not (the shorter table). So
  `leq(A, B, S)` evaluates to `leqF a b S` at every table (`leq_eval_leqF`), with no hypothesis:
  `leq-refl` where the two Ints are one, else `leq-up`, whose right side is `above(A, B, S, S, S)`.

  On a transitive table `leqF a b S` is `a == b || S.contains (a, b)` (`leqF_subsF`), and the table
  `encDef d` writes is `d`'s subsorts (`encDef_subs`), transitive by C7 (`subsortsOK`). So at
  `encDef d = some E`, `leq` on `embS E.subs` is the same sort or a stated subsort (`leq_eval`).
-/
import User.Sig

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.KK

open _root_.KK.Prio

/-- Symbols 446 and 482 are kore.k's `above` and `leq`. -/
theorem leq_names_kleq :
    RefKk.defn.sem.symName 446 =
      "Lblabove'LParUndsCommUndsCommUndsCommUndsCommUndsRParUnds'KORE'Unds'Bool'Unds'Int'Unds'Int'Unds'Subs'Unds'Subs'Unds'Subs" ∧
    RefKk.defn.sem.symName 482 =
      "Lblleq'LParUndsCommUndsCommUndsRParUnds'KORE'Unds'Bool'Unds'Int'Unds'Int'Unds'Subs" := by
  decide +kernel

theorem beq_int_kleq (y b : Int) : (y == b) = decide (y = b) := by
  by_cases h : y = b <;> simp [h]

/-- **`above` on embedded tables is `aboveF`**, by induction on the fuel and then on the table. -/
theorem above_eval_kleq (a b : Int) : ∀ (T All F : List (Int × Int)),
    Eval _root_.KK.c₀ 446 [int a, int b, embS T, embS All, embS F] (some (bool (aboveF a b T All F)))
  | [], All, F => by
    rw [aboveF]
    refine eval_of_clause lookup_above (cl := aboveNil) mem_nil (above_prio _ mem_nil)
      rfl rfl rfl rfl (σ := [(0, int a), (1, int b), (2, embS All), (3, embS F)]) ?_
      (.cons (.var rfl) (.cons (.var rfl) (.cons (.ctor (by decide +kernel) .nil) (.cons (.var rfl) (.cons (.var rfl) .nil)))))
      (fun _ h => by cases h) .dv
    intro i s hs
    match i, hs with
    | 0, hs => cases hs; exact ⟨_, rfl, sort_int a⟩
    | 1, hs => cases hs; exact ⟨_, rfl, sort_int b⟩
    | 2, hs => cases hs; exact ⟨_, rfl, embS_sorted_c₀ All⟩
    | 3, hs => cases hs; exact ⟨_, rfl, embS_sorted_c₀ F⟩
    | _ + 4, hs => simp [aboveNil] at hs
  | (x, y) :: rest, All, [] => by
    rw [aboveF]
    refine eval_of_clause lookup_above (cl := aboveDry) mem_dry (above_prio _ mem_dry)
      rfl rfl rfl rfl (σ := [(0, int a), (1, int b), (2, int x), (3, int y), (4, embS rest), (5, embS All)]) ?_
      (.cons (.var rfl) (.cons (.var rfl) (.cons (.ctor (by decide +kernel) (.cons (.var rfl) (.cons (.var rfl) (.cons (.var rfl) .nil))))
        (.cons (.var rfl) (.cons (.ctor (by decide +kernel) .nil) .nil)))))
      (fun _ h => by cases h) .dv
    intro i s hs
    match i, hs with
    | 0, hs => cases hs; exact ⟨_, rfl, sort_int a⟩
    | 1, hs => cases hs; exact ⟨_, rfl, sort_int b⟩
    | 2, hs => cases hs; exact ⟨_, rfl, sort_int x⟩
    | 3, hs => cases hs; exact ⟨_, rfl, sort_int y⟩
    | 4, hs => cases hs; exact ⟨_, rfl, embS_sorted_c₀ rest⟩
    | 5, hs => cases hs; exact ⟨_, rfl, embS_sorted_c₀ All⟩
    | _ + 6, hs => simp [aboveDry] at hs
  | (x, y) :: rest, All, (p, q) :: f => by
    have hu := above_eval_kleq y b All All f
    have hw := above_eval_kleq a b rest All ((p, q) :: f)
    let σ : Subst := [(0, int a), (1, int b), (2, int x), (3, int y), (4, embS rest), (5, embS All), (6, int p),
      (7, int q), (8, embS f), (9, embS ((p, q) :: f))]
    have hσ : _root_.KK.c₀.WellSorted aboveHit.vars σ := by
      intro i s hs
      match i, hs with
      | 0, hs => cases hs; exact ⟨_, rfl, sort_int a⟩
      | 1, hs => cases hs; exact ⟨_, rfl, sort_int b⟩
      | 2, hs => cases hs; exact ⟨_, rfl, sort_int x⟩
      | 3, hs => cases hs; exact ⟨_, rfl, sort_int y⟩
      | 4, hs => cases hs; exact ⟨_, rfl, embS_sorted_c₀ rest⟩
      | 5, hs => cases hs; exact ⟨_, rfl, embS_sorted_c₀ All⟩
      | 6, hs => cases hs; exact ⟨_, rfl, sort_int p⟩
      | 7, hs => cases hs; exact ⟨_, rfl, sort_int q⟩
      | 8, hs => cases hs; exact ⟨_, rfl, embS_sorted_c₀ f⟩
      | 9, hs => cases hs; exact ⟨_, rfl, embS_sorted_c₀ ((p, q) :: f)⟩
      | _ + 10, hs => simp [aboveHit] at hs
    have hm : PatVals _root_.KK.c₀ σ aboveHit.pats
        [int a, int b, embS ((x, y) :: rest), embS All, embS ((p, q) :: f)] :=
      .cons (.var rfl) (.cons (.var rfl) (.cons (.ctor (by decide +kernel) (.cons (.var rfl) (.cons (.var rfl) (.cons (.var rfl) .nil))))
        (.cons (.var rfl) (.cons (.as (.ctor (by decide +kernel) (.cons (.var rfl) (.cons (.var rfl) (.cons (.var rfl) .nil)))) rfl) .nil))))
    rw [aboveF]
    by_cases hxa : x = a
    · -- `above-hit`
      subst hxa
      rw [ite_eq_left_of_eq_true _ _ (eq_self _), beq_int_kleq]
      refine eval_of_clause lookup_above (cl := aboveHit) mem_hit (above_prio _ mem_hit) rfl rfl rfl rfl
        (σ := σ) hσ hm ?_ ?_
      · intro t ht; cases ht
        have := evalHook (σ := σ) (f := intEq) (ts := [.var 2, .var 0]) (vs := [int x, int x])
          (.cons (evalVar rfl) (.cons (evalVar rfl) .nil)) (hook_intEq_int x x)
        simpa using this
      · exact evalHook (vs := [bool (decide (y = b) || aboveF y b All All f), bool (aboveF x b rest All ((p, q) :: f))])
          (.cons (evalHook (vs := [bool (decide (y = b)), bool (aboveF y b All All f)])
              (.cons (evalHook (vs := [int y, int b]) (.cons (evalVar rfl) (.cons (evalVar rfl) .nil)) (hook_intEq_int y b))
                (.cons (evalCall (vs := [int y, int b, embS All, embS All, embS f])
                  (.cons (evalVar rfl) (.cons (evalVar rfl) (.cons (evalVar rfl) (.cons (evalVar rfl) (.cons (evalVar rfl) .nil))))) hu) .nil))
              (hook_boolOr_bool _ _))
            (.cons (evalCall (vs := [int x, int b, embS rest, embS All, embS ((p, q) :: f)])
              (.cons (evalVar rfl) (.cons (evalVar rfl) (.cons (evalVar rfl) (.cons (evalVar rfl) (.cons (evalVar rfl) .nil))))) hw) .nil))
          (hook_boolOr_bool _ _)
    · -- `above-miss`
      rw [ite_eq_right_of_eq_false _ _ (eq_false hxa)]
      refine eval_of_clause lookup_above (cl := aboveMiss) mem_miss (above_prio _ mem_miss) rfl rfl rfl rfl
        (σ := σ) hσ hm ?_ ?_
      · intro t ht; cases ht
        have := evalHook (σ := σ) (f := intNe) (ts := [.var 2, .var 0]) (vs := [int x, int a])
          (.cons (evalVar rfl) (.cons (evalVar rfl) .nil)) (hook_intNe_int x a)
        simpa [hxa] using this
      · exact evalCall (vs := [int a, int b, embS rest, embS All, embS ((p, q) :: f)])
          (.cons (evalVar rfl) (.cons (evalVar rfl) (.cons (evalVar rfl) (.cons (evalVar rfl) (.cons (evalVar rfl) .nil))))) hw
  termination_by T _ F => (F.length, T.length)

/-- **`leq` on an embedded table is `leqF`**, at every two Ints and every table. -/
theorem leq_eval_leqF (a b : Int) (S : List (Int × Int)) :
    Eval (K₀ sig) 482 [int a, int b, embS S] (some (bool (leqF a b S))) := by
  show Eval _root_.KK.c₀ 482 [int a, int b, embS S] (some (bool (leqF a b S)))
  have hw : _root_.KK.c₀.WellSorted [3, 3, 32] [(0, int a), (1, int b), (2, embS S)] := by
    intro i s' hs'
    match i, hs' with
    | 0, hs' => cases hs'; exact ⟨_, rfl, sort_int a⟩
    | 1, hs' => cases hs'; exact ⟨_, rfl, sort_int b⟩
    | 2, hs' => cases hs'; exact ⟨_, rfl, embS_sorted_c₀ S⟩
    | _ + 3, hs' => simp at hs'
  have hm : PatVals _root_.KK.c₀ [(0, int a), (1, int b), (2, embS S)] [.var 0, .var 1, .var 2]
      [int a, int b, embS S] :=
    .cons (.var rfl) (.cons (.var rfl) (.cons (.var rfl) .nil))
  unfold leqF
  by_cases hab : a = b
  · subst hab
    rw [ite_eq_left_of_eq_true _ _ (eq_self _)]
    refine eval_of_clause lookup_leq (cl := leqRefl) mem_refl (leq_prio _ mem_refl)
      rfl rfl rfl rfl hw hm ?_ .dv
    intro t ht; cases ht
    have := evalHook (σ := [(0, int a), (1, int a), (2, embS S)]) (f := intEq) (ts := [.var 0, .var 1])
      (vs := [int a, int a]) (.cons (evalVar rfl) (.cons (evalVar rfl) .nil)) (hook_intEq_int a a)
    simpa using this
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hab)]
    refine eval_of_clause lookup_leq (cl := leqUp) mem_up (leq_prio _ mem_up)
      rfl rfl rfl rfl hw hm ?_ ?_
    · intro t ht; cases ht
      have := evalHook (σ := [(0, int a), (1, int b), (2, embS S)]) (f := intNe) (ts := [.var 0, .var 1])
        (vs := [int a, int b]) (.cons (evalVar rfl) (.cons (evalVar rfl) .nil)) (hook_intNe_int a b)
      simpa [hab] using this
    · exact evalCall (vs := [int a, int b, embS S, embS S, embS S])
        (.cons (evalVar rfl) (.cons (evalVar rfl) (.cons (evalVar rfl) (.cons (evalVar rfl) (.cons (evalVar rfl) .nil)))))
        (above_eval_kleq a b S S S)

/-- C7 gives a transitive subsort table. -/
theorem subsorts_trans_kleq {d : Semantics} (h : subsortsOK d = true) :
    ∀ a b e, (a, b) ∈ d.subsorts → (b, e) ∈ d.subsorts → (a, e) ∈ d.subsorts := by
  intro a b e hab hbe
  unfold subsortsOK at h
  simp only [Bool.and_eq_true, List.all_eq_true] at h
  have := h.2 (a, b) hab (b, e) hbe
  simpa using this

theorem subsortsOK_of_encDef_kleq {d : Semantics} {E : D} (hE : encDef d = some E) : subsortsOK d = true := by
  have h : encodable d = true := by rw [← encDef_isSome, hE]; rfl
  unfold encodable at h
  simp only [Bool.and_eq_true] at h
  exact h.1.1.1.1.1.2

/-- **`leq` on the subsort table `encDef d` writes**: at two sorts `a`, `b` of `d`, the same sort or
a stated subsort. -/
theorem leq_eval {d : Semantics} {E : D} (hE : encDef d = some E) (a b : Srt) :
    Eval (K₀ sig) 482 [int a, int b, embS E.subs] (some (bool (a == b || d.subsorts.contains (a, b)))) := by
  rw [encDef_subs hE, ← leqF_subsF (subsorts_trans_kleq (subsortsOK_of_encDef_kleq hE))]
  exact leq_eval_leqF a b (subsF d)

/-! ## Checks -/

#check @leq_names_kleq
#check @above_eval_kleq
#check @leq_eval_leqF
#check @leq_eval
#print axioms leq_eval

end KCore.KK
