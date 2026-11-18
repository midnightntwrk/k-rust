/-
  `Γ`'s items for the clauses `Parse.frClauses` writes: the shapes `TieFR.Readings` reads them in.

  For a function f and clauses `frClauses s vars pats req prio aside (frAltsOf xs)` (all of them
  of the priority `prio`, with the variables `vars`, the patterns `pats` and the `requires` req),
  `fnEquationsK` writes each clause's equation `prioEquation c f cl`. Its premise is, before the
  clause's predicate `pre`, the same for all of them (`frameFG`): the clauses of f that apply
  before priority `prio` (`lowerAtFG`) depend only on the priority, so either none competes with
  any of them and the premise is `⌈req = true⌉ ∧ X̄ ∈ p̄` (`premFG`), or the same competitors do
  with each and it is `¬ ⋁ competitors ∧ ⌈req = true⌉ ∧ X̄ ∈ p̄`.

  ## One table for all the clauses (`clause_patFG`)

  An axiom's table lists its variables in order of first occurrence, its guards its free variables
  so. Each clause's axiom is `frame ∧ pre → f(X̄) = rhs ∧ ens`, and the frame comes first. Where
  every variable of `pre`, of `f(X̄)`, of `rhs` and of `ens` is one of the frame's, the table and the
  guards are the frame's (`tableOf_frameFG`, `guards_frameFG`): `X̄` is the frame's where there is a
  pattern for each argument, and a variable of the clause is the frame's where it occurs in the
  patterns (`key_mem_premFG`). The clauses `frClauses` writes have only such variables where each
  alternative's term and conditions have no variable outside the patterns (the hypothesis `hocc`
  of `gamma_shapeFG`): `pre` is `⌈aₖ⌉ ∧ ⋀ Bₖⱼ = true` or the conjunction of their negations, the
  right side an alternative's term, `ens` none or `false`.

  ## The shapes (`gamma_shapeFG`)

  With that table, each alternative's item is `eqnPat ws r Q S F (aₖ ∧ ⊤)` with `Q` the premise
  `clauseQ` of TieFRRead.lean, the last item `eqnPat ws r QN S F (a₁ ∧ (false = true))` with
  `QN = lastQ`; where competitors apply, `Q` and `QN` stand under their negation `n`, as
  `readings_compete` reads them (`withCompFG`, `readings_withCompFG`). Where f has other clauses
  around them, its items are theirs and these (`fnEquationsK_splitFG`).
-/
import KcoreSpec.TieFRRead

set_option autoImplicit false

namespace KCore

namespace TieFRGamma

open ML Faithful KoreAML KoreAML.TieFR TieFRRead

/-! ## Erasing duplicates -/

/-- A suffix whose elements are in the prefix adds nothing. -/
theorem eraseDups_append_subFG {α : Type} [BEq α] [LawfulBEq α] {as bs : List α} (h : ∀ b ∈ bs, b ∈ as) :
    (as ++ bs).eraseDups = as.eraseDups := by
  rw [List.eraseDups_append]
  have : bs.removeAll as = [] := by
    rw [List.removeAll, List.filter_eq_nil_iff]
    intro b hb
    simp [h b hb]
  rw [this, List.eraseDups_nil, List.append_nil]

/-- An element after its first occurrence adds nothing. -/
theorem eraseDups_mid_memFG {α : Type} [BEq α] [LawfulBEq α] {as bs : List α} {a : α} (h : a ∈ as) :
    (as ++ a :: bs).eraseDups = (as ++ bs).eraseDups := by
  rw [List.eraseDups_append, List.eraseDups_append]
  have : (a :: bs).removeAll as = bs.removeAll as := by
    simp [List.removeAll, h]
  rw [this]

theorem eraseDups_cons_dupFG {α : Type} [BEq α] [LawfulBEq α] (a : α) (l : List α) :
    (a :: a :: l).eraseDups = (a :: l).eraseDups :=
  eraseDups_mid_memFG (as := [a]) (List.mem_singleton_self a)

/-- A list `a :: l` followed by elements of l erases as `a :: l`; so does `a :: n ++ l` with
another `a` before l. -/
theorem eraseDups_frame_nilFG {α : Type} [BEq α] [LawfulBEq α] (a : α) (l x : List α) (h : ∀ b ∈ x, b ∈ l) :
    (a :: (l ++ x)).eraseDups = (a :: l).eraseDups := by
  rw [← List.cons_append]
  exact eraseDups_append_subFG fun b hb => List.mem_cons_of_mem _ (h b hb)

theorem eraseDups_frame_consFG {α : Type} [BEq α] [LawfulBEq α] (a : α) (n l x : List α) (h : ∀ b ∈ x, b ∈ l) :
    (a :: (n ++ a :: (l ++ x))).eraseDups = (a :: (n ++ l)).eraseDups := by
  rw [← List.cons_append, eraseDups_mid_memFG (List.mem_cons_self ..), ← List.append_assoc]
  exact eraseDups_append_subFG fun b hb => List.mem_append_right _ (h b hb)

/-! ## The variables of a term's pattern -/

theorem sortVarsOfList_constsFG : ∀ {ss : List Kore.KSort}, (∀ s ∈ ss, ∃ C, s = .ctor C []) →
    KoreAML.sortVarsOfList ss = []
  | [], _ => rfl
  | s :: ss, h => by
    obtain ⟨C, rfl⟩ := h s (List.mem_cons_self ..)
    rw [KoreAML.sortVarsOfList, sortVarsOfList_constsFG fun s' hs' => h s' (List.mem_cons_of_mem _ hs')]
    rfl

theorem varsOf_varAtFG (vs : List KoreAML.Var) (i : Nat) :
    KoreAML.varsOf (KoreAML.varAt vs i) = [KoreAML.evarKey (vs.getD i default).kore] := rfl

mutual
  /-- **A variable of a term's pattern is a variable of the term.** -/
  theorem varsOf_kore_invFG (c : Semantics) (vs : List KoreAML.Var) : ∀ (t : Term) {k : VarKey},
      k ∈ KoreAML.varsOf (Term.kore c vs t) → ∃ i ∈ varOccs t, k = KoreAML.evarKey (vs.getD i default).kore
    | .var i, k, h => by
      rw [Term.kore, varsOf_varAtFG] at h
      exact ⟨i, by simp [varOccs], mem_one h⟩
    | .app f ts, k, h => by
      rw [kore_app] at h
      obtain ⟨hd, ss, he, hss⟩ := symApp_cases c f (Term.koreList c vs ts)
      rw [he, KoreAML.varsOf, sortVarsOfList_constsFG hss, List.nil_append] at h
      obtain ⟨i, hi, rfl⟩ := varsOf_koreList_invFG c vs ts h
      exact ⟨i, by rw [varOccs]; exact hi, rfl⟩
    | .inj a b t, k, h => by
      rw [Term.kore] at h; unfold KoreAML.injP at h
      rw [KoreAML.varsOf, KoreAML.varsOfList, KoreAML.varsOfList] at h
      simp only [KoreAML.srt, KoreAML.sortVarsOfList, KoreAML.sortVarsOf, List.nil_append, List.append_nil] at h
      obtain ⟨i, hi, rfl⟩ := varsOf_kore_invFG c vs t h
      exact ⟨i, by rw [varOccs]; exact hi, rfl⟩
    | .as t j, k, h => by
      rw [Term.kore, KoreAML.varsOf, KoreAML.varsOfList, KoreAML.varsOfList, KoreAML.varsOfList,
        varsOf_varAtFG] at h
      simp only [KoreAML.srt, KoreAML.sortVarsOfList, KoreAML.sortVarsOf, List.nil_append, List.append_nil,
        List.mem_append] at h
      rcases h with h | h
      · obtain ⟨i, hi, rfl⟩ := varsOf_kore_invFG c vs t h
        exact ⟨i, by rw [varOccs]; exact List.mem_append_left _ hi, rfl⟩
      · exact ⟨j, by rw [varOccs]; exact List.mem_append_right _ (List.mem_singleton_self _), mem_one h⟩
    | .dv s lit, k, h => by
      rw [Term.kore, KoreAML.varsOf, sortVarsOf_srtOf] at h; cases h
  theorem varsOf_koreList_invFG (c : Semantics) (vs : List KoreAML.Var) : ∀ (ts : List Term) {k : VarKey},
      k ∈ KoreAML.varsOfList (Term.koreList c vs ts) →
        ∃ i ∈ varOccsList ts, k = KoreAML.evarKey (vs.getD i default).kore
    | [], k, h => by rw [Term.koreList, KoreAML.varsOfList] at h; cases h
    | t :: ts, k, h => by
      rw [Term.koreList, KoreAML.varsOfList] at h
      rcases List.mem_append.mp h with h | h
      · obtain ⟨i, hi, rfl⟩ := varsOf_kore_invFG c vs t h
        exact ⟨i, by rw [varOccsList]; exact List.mem_append_left _ hi, rfl⟩
      · obtain ⟨i, hi, rfl⟩ := varsOf_koreList_invFG c vs ts h
        exact ⟨i, by rw [varOccsList]; exact List.mem_append_right _ hi, rfl⟩
end

theorem mem_varOccsList_ofFG {i : Nat} {t : Term} : ∀ {ts : List Term}, t ∈ ts → i ∈ varOccs t → i ∈ varOccsList ts
  | _ :: ts, ht, hi => by
    rw [varOccsList]
    rcases List.mem_cons.mp ht with rfl | ht
    · exact List.mem_append_left _ hi
    · exact List.mem_append_right _ (mem_varOccsList_ofFG ht hi)


/-! ## The variables of the clauses' predicates -/

section
variable (c : Semantics) (vs : List KoreAML.Var) (S : Kore.KSort)

theorem varsOf_conjCFG : ∀ (ps : List Cond) {k : VarKey}, k ∈ KoreAML.varsOf (Cond.kore c vs S (Parse.conjC ps)) →
    k ∈ KoreAML.sortVarsOf S ∨ ∃ p ∈ ps, k ∈ KoreAML.varsOf (Cond.kore c vs S p)
  | [], k, h => by
    rw [Parse.conjC, Cond.kore, KoreAML.varsOf] at h; exact Or.inl h
  | [p], k, h => by
    rw [Parse.conjC] at h; exact Or.inr ⟨p, List.mem_singleton_self _, h⟩
  | p :: q :: ps, k, h => by
    rw [show Parse.conjC (p :: q :: ps) = .and p (Parse.conjC (q :: ps)) from rfl, Cond.kore, KoreAML.varsOf,
      KoreAML.varsOfList, KoreAML.varsOfList, KoreAML.varsOfList] at h
    simp only [List.append_nil, List.mem_append] at h
    rcases h with h | h | h
    · exact Or.inl h
    · exact Or.inr ⟨p, List.mem_cons_self .., h⟩
    · rcases varsOf_conjCFG (q :: ps) h with h | ⟨p', hp', h⟩
      · exact Or.inl h
      · exact Or.inr ⟨p', List.mem_cons_of_mem _ hp', h⟩

theorem freeOf_conjCFG : ∀ (ps : List Cond) {bound : List VarKey} {k : VarKey},
    k ∈ KoreAML.freeOf bound (Cond.kore c vs S (Parse.conjC ps)) →
    ∃ p ∈ ps, k ∈ KoreAML.freeOf bound (Cond.kore c vs S p)
  | [], _, k, h => by
    rw [Parse.conjC, Cond.kore, KoreAML.freeOf] at h; cases h
  | [p], _, k, h => by
    rw [Parse.conjC] at h; exact ⟨p, List.mem_singleton_self _, h⟩
  | p :: q :: ps, _, k, h => by
    rw [show Parse.conjC (p :: q :: ps) = .and p (Parse.conjC (q :: ps)) from rfl, Cond.kore, KoreAML.freeOf,
      KoreAML.freeOfList, KoreAML.freeOfList, KoreAML.freeOfList] at h
    simp only [List.append_nil, List.mem_append] at h
    rcases h with h | h
    · exact ⟨p, List.mem_cons_self .., h⟩
    · obtain ⟨p', hp', h⟩ := freeOf_conjCFG (q :: ps) h
      exact ⟨p', List.mem_cons_of_mem _ hp', h⟩

/-- The variables of `preOf s x`: the sort's, and those of the alternative's term and conditions. -/
theorem varsOf_preOfFG (s : Srt) (x : Term × List Term) {k : VarKey}
    (h : k ∈ KoreAML.varsOf (Cond.kore c vs S (preOf s x))) :
    k ∈ KoreAML.sortVarsOf S ∨ ∃ i ∈ varOccsList (x.1 :: x.2), k = KoreAML.evarKey (vs.getD i default).kore := by
  unfold preOf at h
  rcases varsOf_conjCFG c vs S _ h with h | ⟨p, hp, h⟩
  · exact Or.inl h
  rcases List.mem_cons.mp hp with rfl | hp
  · rw [Cond.kore, KoreAML.varsOf, sortVarsOf_srtOf, List.nil_append, List.mem_append] at h
    rcases h with h | h
    · exact Or.inl h
    · obtain ⟨i, hi, rfl⟩ := varsOf_kore_invFG c vs _ h
      exact Or.inr ⟨i, by rw [varOccsList]; exact List.mem_append_left _ hi, rfl⟩
  · obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hp
    rw [Parse.isTrueC, Cond.kore, KoreAML.varsOf, sortVarsOf_srtOf, List.nil_append] at h
    simp only [Parse.boolT, Term.kore, KoreAML.varsOf, sortVarsOf_srtOf, List.append_nil, List.mem_append] at h
    rcases h with h | h
    · exact Or.inl h
    · obtain ⟨i, hi, rfl⟩ := varsOf_kore_invFG c vs _ h
      exact Or.inr ⟨i, by rw [varOccsList]; exact List.mem_append_right _ (mem_varOccsList_ofFG hb hi), rfl⟩

theorem freeOf_preOfFG (s : Srt) (x : Term × List Term) {bound : List VarKey} {k : VarKey}
    (h : k ∈ KoreAML.freeOf bound (Cond.kore c vs S (preOf s x))) :
    ∃ i ∈ varOccsList (x.1 :: x.2), k = KoreAML.evarKey (vs.getD i default).kore := by
  unfold preOf at h
  obtain ⟨p, hp, h⟩ := freeOf_conjCFG c vs S _ h
  rcases List.mem_cons.mp hp with rfl | hp
  · rw [Cond.kore, KoreAML.freeOf] at h
    obtain ⟨i, hi, rfl⟩ := freeOf_kore c vs _ h
    exact ⟨i, by rw [varOccsList]; exact List.mem_append_left _ hi, rfl⟩
  · obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hp
    rw [Parse.isTrueC, Cond.kore, KoreAML.freeOf] at h
    simp only [Parse.boolT, Term.kore, KoreAML.freeOf, List.append_nil] at h
    obtain ⟨i, hi, rfl⟩ := freeOf_kore c vs _ h
    exact ⟨i, by rw [varOccsList]; exact List.mem_append_right _ (mem_varOccsList_ofFG hb hi), rfl⟩

/-- The variables of `preN s xs`: the sort's, and those of the alternatives' terms and conditions. -/
theorem varsOf_preNFG (s : Srt) (xs : List (Term × List Term)) {k : VarKey}
    (h : k ∈ KoreAML.varsOf (Cond.kore c vs S (preN s xs))) :
    k ∈ KoreAML.sortVarsOf S ∨
      ∃ x ∈ xs, ∃ i ∈ varOccsList (x.1 :: x.2), k = KoreAML.evarKey (vs.getD i default).kore := by
  unfold preN at h
  rcases varsOf_conjCFG c vs S _ h with h | ⟨p, hp, h⟩
  · exact Or.inl h
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hq
  rw [Cond.kore, KoreAML.varsOf, List.mem_append] at h
  rcases h with h | h
  · exact Or.inl h
  · rcases varsOf_preOfFG c vs S s x h with h | ⟨i, hi, he⟩
    · exact Or.inl h
    · exact Or.inr ⟨x, hx, i, hi, he⟩

theorem freeOf_preNFG (s : Srt) (xs : List (Term × List Term)) {bound : List VarKey} {k : VarKey}
    (h : k ∈ KoreAML.freeOf bound (Cond.kore c vs S (preN s xs))) :
    ∃ x ∈ xs, ∃ i ∈ varOccsList (x.1 :: x.2), k = KoreAML.evarKey (vs.getD i default).kore := by
  unfold preN at h
  obtain ⟨p, hp, h⟩ := freeOf_conjCFG c vs S _ h
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hq
  rw [Cond.kore, KoreAML.freeOf] at h
  obtain ⟨i, hi, he⟩ := freeOf_preOfFG c vs S s x h
  exact ⟨x, hx, i, hi, he⟩

end

/-! ## The variables of the premise -/

theorem sX_eqFG (n : Nat) : (s!"X{n}" : String) = "X" ++ toString n := by simp; rfl

theorem argsConj_varsFG : ∀ (n : Nat) (args : List String) (ps : List Kore.Pattern), ps.length ≤ args.length →
    ∀ k ∈ KoreAML.varsOfList ps, k ∈ KoreAML.varsOf (KoreAML.argsConj n (args.zip ps))
  | _, _, [], _, k, hk => by rw [KoreAML.varsOfList] at hk; cases hk
  | _, [], _ :: _, h, _, _ => by simp at h
  | n, a :: args, p :: ps, h, k, hk => by
    rw [List.zip_cons_cons, KoreAML.argsConj, KoreAML.varsOf, KoreAML.varsOfList, KoreAML.varsOfList,
      KoreAML.varsOfList, KoreAML.varsOf]
    rw [KoreAML.varsOfList, List.mem_append] at hk
    simp only [List.mem_append]
    rcases hk with hk | hk
    · exact Or.inr (Or.inl (Or.inr hk))
    · exact Or.inr (Or.inr (Or.inl (argsConj_varsFG (n + 1) args ps (by simpa using h) k hk)))

theorem argsConj_freeFG : ∀ (n : Nat) (args : List String) (ps : List Kore.Pattern), ps.length ≤ args.length →
    ∀ k ∈ KoreAML.freeOfList [] ps, k ∈ KoreAML.freeOf [] (KoreAML.argsConj n (args.zip ps))
  | _, _, [], _, k, hk => by rw [KoreAML.freeOfList] at hk; cases hk
  | _, [], _ :: _, h, _, _ => by simp at h
  | n, a :: args, p :: ps, h, k, hk => by
    rw [List.zip_cons_cons, KoreAML.argsConj, KoreAML.freeOf, KoreAML.freeOfList, KoreAML.freeOfList,
      KoreAML.freeOfList, KoreAML.freeOf]
    rw [KoreAML.freeOfList, List.mem_append] at hk
    simp only [List.mem_append]
    rcases hk with hk | hk
    · exact Or.inl (Or.inr hk)
    · exact Or.inr (Or.inl (argsConj_freeFG (n + 1) args ps (by simpa using h) k hk))

theorem argsConj_XvarsFG : ∀ (n : Nat) (args : List String) (ps : List Kore.Pattern), args.length ≤ ps.length →
    ∀ k ∈ KoreAML.varsOfList (KoreAML.vars (KoreAML.numbered "X" n args)),
      k ∈ KoreAML.varsOf (KoreAML.argsConj n (args.zip ps))
  | _, [], _, _, k, hk => by simp [KoreAML.numbered, KoreAML.vars, KoreAML.varsOfList] at hk
  | _, _ :: _, [], h, _, _ => by simp at h
  | n, a :: args, p :: ps, h, k, hk => by
    rw [List.zip_cons_cons, KoreAML.argsConj, KoreAML.varsOf, KoreAML.varsOfList, KoreAML.varsOfList,
      KoreAML.varsOfList, KoreAML.varsOf]
    rw [KoreAML.numbered, KoreAML.vars, List.map_cons, KoreAML.varsOfList, List.mem_append] at hk
    simp only [List.mem_append]
    rcases hk with hk | hk
    · refine Or.inr (Or.inl (Or.inl (Or.inr ?_)))
      rw [sX_eqFG]; simpa [KoreAML.ev, KoreAML.evar, KoreAML.varsOf] using hk
    · exact Or.inr (Or.inr (Or.inl (argsConj_XvarsFG (n + 1) args ps (by simpa using h) k hk)))

theorem argsConj_XfreeFG : ∀ (n : Nat) (args : List String) (ps : List Kore.Pattern), args.length ≤ ps.length →
    ∀ k ∈ KoreAML.freeOfList [] (KoreAML.vars (KoreAML.numbered "X" n args)),
      k ∈ KoreAML.freeOf [] (KoreAML.argsConj n (args.zip ps))
  | _, [], _, _, k, hk => by simp [KoreAML.numbered, KoreAML.vars, KoreAML.freeOfList] at hk
  | _, _ :: _, [], h, _, _ => by simp at h
  | n, a :: args, p :: ps, h, k, hk => by
    rw [List.zip_cons_cons, KoreAML.argsConj, KoreAML.freeOf, KoreAML.freeOfList, KoreAML.freeOfList,
      KoreAML.freeOfList, KoreAML.freeOf]
    rw [KoreAML.numbered, KoreAML.vars, List.map_cons, KoreAML.freeOfList, List.mem_append] at hk
    simp only [List.mem_append]
    rcases hk with hk | hk
    · refine Or.inl (Or.inl ?_)
      rw [sX_eqFG]; simpa [KoreAML.ev, KoreAML.evar, KoreAML.freeOf] using hk
    · exact Or.inr (Or.inl (argsConj_XfreeFG (n + 1) args ps (by simpa using h) k hk))

/-! ## The frame: one table and one guard list -/

/-- **One table for an equation and its frame.** The axiom `frame ∧ pre → C`, the frame `P0` or
`N ∧ P0`, has the frame's table where every variable of `pre` and `C` is one of `P0`'s. -/
theorem tableOf_frameFG {N P0 pre C : Kore.Pattern} (b : Bool)
    (hV : ∀ k ∈ KoreAML.varsOf pre ++ KoreAML.varsOf C, k ∈ KoreAML.varsOf P0) :
    tableOf [Rv] (.implies R (if b then .and R [P0, pre] else .and R [N, .and R [P0, pre]]) C) =
      tableOf [Rv] (if b then P0 else .and R [N, P0]) := by
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte, KoreAML.tableOf, KoreAML.varsOf, KoreAML.varsOfList, List.map_cons,
      List.map_nil, KoreAML.R, KoreAML.sortVarsOf, List.append_assoc, List.cons_append, List.nil_append,
      List.append_nil]
    rw [eraseDups_cons_dupFG, eraseDups_cons_dupFG, eraseDups_cons_dupFG]
    exact eraseDups_frame_consFG _ _ _ _ hV
  · simp only [↓reduceIte, KoreAML.tableOf, KoreAML.varsOf, KoreAML.varsOfList, List.map_cons,
      List.map_nil, KoreAML.R, KoreAML.sortVarsOf, List.append_assoc, List.cons_append, List.nil_append,
      List.append_nil]
    rw [eraseDups_cons_dupFG, eraseDups_cons_dupFG]
    exact eraseDups_frame_nilFG _ _ _ hV

/-- **One guard list for an equation and its frame**, where every free variable of `pre` and `C` is
one of `P0`'s. -/
theorem guards_frameFG {N P0 pre C : Kore.Pattern} (b : Bool)
    (hF : ∀ k ∈ KoreAML.freeOf [] pre ++ KoreAML.freeOf [] C, k ∈ KoreAML.freeOf [] P0) :
    ([Rv].map sortVarKey ++
        KoreAML.freeOf [] (.implies R (if b then .and R [P0, pre] else .and R [N, .and R [P0, pre]]) C)).eraseDups =
      ([Rv].map sortVarKey ++ KoreAML.freeOf [] (if b then P0 else .and R [N, P0])).eraseDups := by
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte, KoreAML.freeOf, KoreAML.freeOfList, List.map_cons,
      List.map_nil, List.append_assoc, List.cons_append, List.nil_append, List.append_nil]
    rw [← List.append_assoc (KoreAML.freeOf [] N)]
    exact eraseDups_frame_nilFG _ _ _ fun b hb => List.mem_append_right _ (hF b hb)
  · simp only [↓reduceIte, KoreAML.freeOf, KoreAML.freeOfList, List.map_cons,
      List.map_nil, List.append_assoc, List.cons_append, List.nil_append, List.append_nil]
    exact eraseDups_frame_nilFG _ _ _ hF

/-! ## The frame of the clauses' equations -/

/-- The clauses of f that apply before a clause of priority `prio`: those of a smaller priority
that are not `aside` (`lowerClauses` of a clause of that priority). -/
def lowerAtFG (f : Fn) (prio : Nat) : List Clause :=
  f.clauses.filter fun cl' => !cl'.aside && cl'.prio < prio

theorem lowerClauses_eqFG (f : Fn) (cl : Clause) : lowerClauses f cl = lowerAtFG f cl.prio := rfl

/-- The negation of the competitors `L`, `¬ ⋁ exclusions` (`competingEquation`). -/
def compNotFG (c : Semantics) (f : Fn) (L : List Clause) : Kore.Pattern :=
  .not R (KoreAML.anyOf (L.map fun cl' => exclusion c f cl' (canonClausePres cl')))

/-- `⌈req = true⌉ ∧ X̄ ∈ p̄` over the clauses' variables `vars`. -/
def premFG (c : Semantics) (f : Fn) (vars : List Srt) (pats : List Term) (req : Option Term) : Kore.Pattern :=
  KCore.premise (f.args.map c.sortName) (req.map (Term.kore c (canonVars c vars)))
    (Term.koreList c (canonVars c vars) pats)

/-- **The frame**: a clause's premise before its predicate, `premFG`, under the competitors'
negation where `L`, the competitors, is not empty. -/
def frameFG (c : Semantics) (f : Fn) (L : List Clause) (vars : List Srt) (pats : List Term) (req : Option Term) :
    Kore.Pattern :=
  if L.isEmpty then premFG c f vars pats req else .and R [compNotFG c f L, premFG c f vars pats req]

/-- The frame's table: its sort variable `R`, then its variables in order of first occurrence. -/
def tblFG (c : Semantics) (f : Fn) (L : List Clause) (vars : List Srt) (pats : List Term) (req : Option Term) :
    VarTable :=
  tableOf [Rv] (frameFG c f L vars pats req)

/-- The frame's guards: of `R` and of its free variables, over its table. -/
def wsFG (c : Semantics) (f : Fn) (L : List Clause) (vars : List Srt) (pats : List Term) (req : Option Term) :
    List P :=
  ([Rv].map sortVarKey ++ freeOf [] (frameFG c f L vars pats req)).eraseDups.map
    (guardOf (tblFG c f L vars pats req))

/-- A premise `q`, under the competitors' negation `n` where `L` is not empty. -/
def withCompFG (L : List Clause) (n q : P) : P := if L.isEmpty then q else sAnd n q

/-- The equations' left side `f(X0, …)`. -/
def headFG (c : Semantics) (f : Fn) : Kore.Pattern :=
  ap (c.symName f.label) (KoreAML.vars (numbered "X" 0 (f.args.map c.sortName)))

/-- The axiom of a clause's equation, as `prioEquation` writes it. -/
def prioAxFG (c : Semantics) (f : Fn) (cl : Clause) : Kore.Axiom :=
  { sortVars := [Rv]
    pattern := .implies R
      (if (lowerClauses f cl).isEmpty then withPre c (canonVars c cl.vars) cl (premFG c f cl.vars cl.pats cl.req)
       else .and R [compNotFG c f (lowerClauses f cl),
         withPre c (canonVars c cl.vars) cl (premFG c f cl.vars cl.pats cl.req)])
      (.equals (srtOf c f.result) R (headFG c f)
        (.and (srtOf c f.result) [(clauseRhs c f cl).1, (clauseRhs c f cl).2]))
    attributes := [] }

theorem prioEquation_axFG (c : Semantics) (f : Fn) (cl : Clause) : prioEquation c f cl = .axiom (prioAxFG c f cl) := by
  unfold prioEquation prioAxFG
  split <;> rfl

theorem kernelItems_mapFG (c : Semantics) (f : Fn) : ∀ cls : List Clause,
    kernelItems (cls.map (prioEquation c f)) = cls.map fun cl => trAxiom [] [] ⟨0, "kernel", prioAxFG c f cl⟩
  | [] => rfl
  | cl :: cls => by
    rw [List.map_cons, List.map_cons, ← kernelItems_mapFG c f cls]
    unfold kernelItems
    rw [List.filterMap_cons, prioEquation_axFG]

/-! ## The frame holds the clauses' variables -/

section
variable (c : Semantics) (f : Fn) (vars : List Srt) (pats : List Term) (req : Option Term)

theorem R_mem_premFG : sortVarKey Rv ∈ KoreAML.varsOf (premFG c f vars pats req) := by
  unfold premFG KCore.premise
  rw [KoreAML.varsOf]
  exact List.mem_append_left _ (List.mem_singleton_self _)

/-- A variable of the patterns is a variable, and a free one, of the frame's premise. -/
theorem key_mem_premFG (hlen : pats.length = f.args.length) {i : Nat} (hi : i ∈ varOccsList pats) :
    KoreAML.evarKey ((canonVars c vars).getD i default).kore ∈ KoreAML.varsOf (premFG c f vars pats req) ∧
      KoreAML.evarKey ((canonVars c vars).getD i default).kore ∈ KoreAML.freeOf [] (premFG c f vars pats req) := by
  have hl : (Term.koreList c (canonVars c vars) pats).length ≤ (f.args.map c.sortName).length := by
    rw [koreList_length, List.length_map, hlen]; exact Nat.le_refl _
  unfold premFG KCore.premise
  rw [KoreAML.varsOf, KoreAML.varsOfList, KoreAML.varsOfList, KoreAML.varsOfList, KoreAML.freeOf,
    KoreAML.freeOfList, KoreAML.freeOfList, KoreAML.freeOfList]
  refine ⟨List.mem_append_right _ (List.mem_append_right _ (List.mem_append_left _ ?_)),
    List.mem_append_right _ (List.mem_append_left _ ?_)⟩
  · exact argsConj_varsFG 0 _ _ hl _ (varsOf_koreList c _ pats hi)
  · exact argsConj_freeFG 0 _ _ hl _ (Model.kore_freeOfList c _ pats hi)

/-- The arguments `X̄` of the left side are variables, and free ones, of the frame's premise. -/
theorem head_sub_premFG (hlen : pats.length = f.args.length) :
    (∀ k ∈ KoreAML.varsOf (headFG c f), k ∈ KoreAML.varsOf (premFG c f vars pats req)) ∧
      ∀ k ∈ KoreAML.freeOf [] (headFG c f), k ∈ KoreAML.freeOf [] (premFG c f vars pats req) := by
  have hl : (f.args.map c.sortName).length ≤ (Term.koreList c (canonVars c vars) pats).length := by
    rw [koreList_length, List.length_map, hlen]; exact Nat.le_refl _
  unfold headFG premFG KCore.premise
  simp only [KoreAML.ap, KoreAML.varsOf, KoreAML.freeOf, KoreAML.sortVarsOfList, List.nil_append,
    KoreAML.varsOfList, KoreAML.freeOfList, List.append_nil, List.mem_append]
  exact ⟨fun k hk => Or.inr (Or.inr (argsConj_XvarsFG 0 _ _ hl k hk)),
    fun k hk => Or.inr (argsConj_XfreeFG 0 _ _ hl k hk)⟩

/-- The left side, the right side and the `ensures` part hold only variables of the frame's
premise, where those of the right side and the `ensures` part occur in the patterns. -/
theorem concl_subFG (hlen : pats.length = f.args.length) {rhs : Term} {ens : Option Term}
    (hrhs : ∀ i ∈ varOccs rhs, i ∈ varOccsList pats) (hens : ∀ t ∈ ens, ∀ i ∈ varOccs t, i ∈ varOccsList pats) :
    let C : Kore.Pattern := .equals (srtOf c f.result) R (headFG c f)
      (.and (srtOf c f.result) [Term.kore c (canonVars c vars) rhs,
        reqPat (srtOf c f.result) (ens.map (Term.kore c (canonVars c vars)))])
    (∀ k ∈ KoreAML.varsOf C, k ∈ KoreAML.varsOf (premFG c f vars pats req)) ∧
      ∀ k ∈ KoreAML.freeOf [] C, k ∈ KoreAML.freeOf [] (premFG c f vars pats req) := by
  intro C
  have hT : ∀ t : Term, (∀ i ∈ varOccs t, i ∈ varOccsList pats) →
      (∀ k ∈ KoreAML.varsOf (Term.kore c (canonVars c vars) t), k ∈ KoreAML.varsOf (premFG c f vars pats req)) ∧
        ∀ k ∈ KoreAML.freeOf [] (Term.kore c (canonVars c vars) t), k ∈ KoreAML.freeOf [] (premFG c f vars pats req) :=
    fun t ht => ⟨fun k hk => by
        obtain ⟨i, hi, rfl⟩ := varsOf_kore_invFG c _ t hk
        exact (key_mem_premFG c f vars pats req hlen (ht i hi)).1,
      fun k hk => by
        obtain ⟨i, hi, rfl⟩ := freeOf_kore c _ t hk
        exact (key_mem_premFG c f vars pats req hlen (ht i hi)).2⟩
  have hE : (∀ k ∈ KoreAML.varsOf (reqPat (srtOf c f.result) (ens.map (Term.kore c (canonVars c vars)))),
        k ∈ KoreAML.varsOf (premFG c f vars pats req)) ∧
      ∀ k ∈ KoreAML.freeOf [] (reqPat (srtOf c f.result) (ens.map (Term.kore c (canonVars c vars)))),
        k ∈ KoreAML.freeOf [] (premFG c f vars pats req) := by
    cases ens with
    | none => exact ⟨fun k hk => by simp [reqPat, KoreAML.varsOf, sortVarsOf_srtOf] at hk,
        fun k hk => by simp [reqPat, KoreAML.freeOf] at hk⟩
    | some t =>
      have h := hT t (hens t rfl)
      refine ⟨fun k hk => ?_, fun k hk => ?_⟩
      · simp only [Option.map_some, reqPat, KoreAML.varsOf, sortVarsOf_srtOf, KoreAML.srt, KoreAML.sortVarsOf,
          KoreAML.sortVarsOfList, List.nil_append, List.append_nil] at hk
        exact h.1 k hk
      · simp only [Option.map_some, reqPat, KoreAML.freeOf, List.append_nil] at hk
        exact h.2 k hk
  have hH := head_sub_premFG c f vars pats req hlen
  have hRr := hT rhs hrhs
  refine ⟨fun k hk => ?_, fun k hk => ?_⟩
  · simp only [C, KoreAML.varsOf, KoreAML.varsOfList, sortVarsOf_srtOf, List.nil_append, List.append_nil,
      List.mem_append] at hk
    rcases hk with (hk | hk) | hk | hk
    · simp only [R, KoreAML.sortVarsOf, List.mem_singleton] at hk
      rw [hk]; exact R_mem_premFG c f vars pats req
    · exact hH.1 k hk
    · exact hRr.1 k hk
    · exact hE.1 k hk
  · simp only [C, KoreAML.freeOf, KoreAML.freeOfList, List.append_nil, List.mem_append] at hk
    rcases hk with hk | hk | hk
    · exact hH.2 k hk
    · exact hRr.2 k hk
    · exact hE.2 k hk

end

/-! ## A clause's item -/

theorem withPre_notTopFG {c : Semantics} {vs : List KoreAML.Var} {cl : Clause} {prem : Kore.Pattern}
    (h : cl.pre.isTop = false) : withPre c vs cl prem = .and R [prem, Cond.kore c vs R cl.pre] := by
  unfold withPre; rw [h]; rfl

/-- **A clause's item over the frame's table and guards.** For a clause of the priority `prio`
with the variables `vars`, the patterns `pats` and the `requires` req, no existential variable and
a predicate other than `\top`: where its predicate, its right side and its `ensures` part hold only
variables of the frame's premise, its item is `ws → (Q → f(X̄) = rhs ∧ ens)` over the frame's
table, `Q` the frame's premise with the predicate, under the competitors' negation where there are
competitors. -/
theorem clause_patFG (c : Semantics) (f : Fn) {cl : Clause} {vars : List Srt} {pats : List Term}
    {req : Option Term} {prio : Nat}
    (hv : cl.vars = vars) (hp : cl.pats = pats) (hr : cl.req = req) (hpr : cl.prio = prio) (hexs : cl.exs = [])
    (hpre : cl.pre.isTop = false) (hlen : pats.length = f.args.length)
    (hrhs : ∀ i ∈ varOccs cl.rhs, i ∈ varOccsList pats)
    (hens : ∀ t ∈ cl.ens, ∀ i ∈ varOccs t, i ∈ varOccsList pats)
    (hpV : ∀ k ∈ KoreAML.varsOf (Cond.kore c (canonVars c vars) R cl.pre), k ∈ KoreAML.varsOf (premFG c f vars pats req))
    (hpF : ∀ k ∈ KoreAML.freeOf [] (Cond.kore c (canonVars c vars) R cl.pre),
      k ∈ KoreAML.freeOf [] (premFG c f vars pats req)) :
    (trAxiom [] [] ⟨0, "kernel", prioAxFG c f cl⟩).pat =
      eqnPat (wsFG c f (lowerAtFG f prio) vars pats req)
        ((tblFG c f (lowerAtFG f prio) vars pats req).ev (sortVarKey Rv))
        (withCompFG (lowerAtFG f prio)
          (tr ⟨tblFG c f (lowerAtFG f prio) vars pats req, []⟩ (compNotFG c f (lowerAtFG f prio)))
          (sAnd (tr ⟨tblFG c f (lowerAtFG f prio) vars pats req, []⟩ (premFG c f vars pats req))
            (tr ⟨tblFG c f (lowerAtFG f prio) vars pats req, []⟩ (Cond.kore c (canonVars c vars) R cl.pre))))
        (trSort (tblFG c f (lowerAtFG f prio) vars pats req) (srtOf c f.result))
        (tr ⟨tblFG c f (lowerAtFG f prio) vars pats req, []⟩ (headFG c f))
        (sAnd (tr ⟨tblFG c f (lowerAtFG f prio) vars pats req, []⟩ (Term.kore c (canonVars c vars) cl.rhs))
          (tr ⟨tblFG c f (lowerAtFG f prio) vars pats req, []⟩
            (reqPat (srtOf c f.result) (cl.ens.map (Term.kore c (canonVars c vars)))))) := by
  subst hv hp hr hpr
  have hC := concl_subFG c f cl.vars cl.pats cl.req hlen hrhs hens
  have hpat : (prioAxFG c f cl).pattern = .implies R
      (if (lowerAtFG f cl.prio).isEmpty then .and R [premFG c f cl.vars cl.pats cl.req,
          Cond.kore c (canonVars c cl.vars) R cl.pre]
        else .and R [compNotFG c f (lowerAtFG f cl.prio), .and R [premFG c f cl.vars cl.pats cl.req,
          Cond.kore c (canonVars c cl.vars) R cl.pre]])
      (.equals (srtOf c f.result) R (headFG c f) (.and (srtOf c f.result) [Term.kore c (canonVars c cl.vars) cl.rhs,
        reqPat (srtOf c f.result) (cl.ens.map (Term.kore c (canonVars c cl.vars)))])) := by
    unfold prioAxFG
    rw [withPre_notTopFG hpre, clauseRhs_nil hexs, lowerClauses_eqFG]
  have htbl : tableOf (prioAxFG c f cl).sortVars (prioAxFG c f cl).pattern =
      tblFG c f (lowerAtFG f cl.prio) cl.vars cl.pats cl.req := by
    rw [hpat, show (prioAxFG c f cl).sortVars = [Rv] from rfl, tableOf_frameFG _
      (fun k hk => (List.mem_append.mp hk).elim (hpV k) (hC.1 k))]
    unfold tblFG frameFG
    cases (lowerAtFG f cl.prio).isEmpty <;> rfl
  have hgd : guardsOf (prioAxFG c f cl) = wsFG c f (lowerAtFG f cl.prio) cl.vars cl.pats cl.req := by
    unfold guardsOf wsFG
    rw [htbl, hpat, show (prioAxFG c f cl).sortVars = [Rv] from rfl, guards_frameFG _
      (fun k hk => (List.mem_append.mp hk).elim (hpF k) (hC.2 k))]
    unfold frameFG
    cases (lowerAtFG f cl.prio).isEmpty <;> rfl
  rw [trAxiom_eqnPat [] [] 0 "kernel" (prioAxFG c f cl) rfl hpat, htbl, hgd]
  unfold withCompFG
  cases (lowerAtFG f cl.prio).isEmpty
  · simp only [Bool.false_eq_true, ↓reduceIte, Faithful.tr_and2]
  · simp only [↓reduceIte, Faithful.tr_and2]

/-! ## The items of the clauses `frClauses` writes -/

/-- **`Γ`'s items for the clauses `frClauses` writes** (`fnEquationsK`), over the frame's table
`tblFG` and guards `wsFG`: for each alternative x the premise `clauseQ` and the right side
`x.1 ∧ ⊤`, for the last clause the premise `lastQ` and the right side `a₁ ∧ (false = true)`; each
premise under the competitors' negation where clauses of f of a smaller priority than `prio`, not
`aside`, compete (`withCompFG`, the premises `readings_compete` reads). What it takes of the
clauses: an alternative at least (`preN` is not `\top` then), a pattern for each argument, and no
variable of an alternative's term or conditions outside the patterns. -/
theorem gamma_shapeFG (c : Semantics) (f : Fn) {s : Srt} {vars : List Srt} {pats : List Term}
    {req : Option Term} {prio : Nat} {aside : Bool} {xs : List (Term × List Term)}
    (hxs : xs ≠ []) (hlen : pats.length = f.args.length)
    (hocc : ∀ x ∈ xs, ∀ i ∈ varOccsList (x.1 :: x.2), i ∈ varOccsList pats) :
    (kernelItems ((Parse.frClauses s vars pats req prio aside (frAltsOf xs)).map (prioEquation c f))).map (·.pat) =
      xs.map (fun x => eqnPat (wsFG c f (lowerAtFG f prio) vars pats req)
          ((tblFG c f (lowerAtFG f prio) vars pats req).ev (sortVarKey Rv))
          (withCompFG (lowerAtFG f prio)
            (tr ⟨tblFG c f (lowerAtFG f prio) vars pats req, []⟩ (compNotFG c f (lowerAtFG f prio)))
            (clauseQ c (tblFG c f (lowerAtFG f prio) vars pats req) (canonVars c vars) s
              (tr ⟨tblFG c f (lowerAtFG f prio) vars pats req, []⟩ (premFG c f vars pats req)) x))
          (trSort (tblFG c f (lowerAtFG f prio) vars pats req) (srtOf c f.result))
          (tr ⟨tblFG c f (lowerAtFG f prio) vars pats req, []⟩ (headFG c f))
          (sAnd (altP c (tblFG c f (lowerAtFG f prio) vars pats req) (canonVars c vars) x)
            (sTop (trSort (tblFG c f (lowerAtFG f prio) vars pats req) (srtOf c f.result))))) ++
        [eqnPat (wsFG c f (lowerAtFG f prio) vars pats req)
          ((tblFG c f (lowerAtFG f prio) vars pats req).ev (sortVarKey Rv))
          (withCompFG (lowerAtFG f prio)
            (tr ⟨tblFG c f (lowerAtFG f prio) vars pats req, []⟩ (compNotFG c f (lowerAtFG f prio)))
            (lastQ c (tblFG c f (lowerAtFG f prio) vars pats req) (canonVars c vars) s
              (tr ⟨tblFG c f (lowerAtFG f prio) vars pats req, []⟩ (premFG c f vars pats req)) xs))
          (trSort (tblFG c f (lowerAtFG f prio) vars pats req) (srtOf c f.result))
          (tr ⟨tblFG c f (lowerAtFG f prio) vars pats req, []⟩ (headFG c f))
          (sAnd (altP c (tblFG c f (lowerAtFG f prio) vars pats req) (canonVars c vars) (xs.headD (Parse.boolT false, [])))
            (tr ⟨tblFG c f (lowerAtFG f prio) vars pats req, []⟩
              (reqPat (srtOf c f.result) (some (Term.kore c (canonVars c vars) (Parse.boolT false))))))] := by
  have hkey : ∀ {k : VarKey}, (k ∈ KoreAML.sortVarsOf R ∨
      ∃ i ∈ varOccsList pats, k = KoreAML.evarKey ((canonVars c vars).getD i default).kore) →
      k ∈ KoreAML.varsOf (premFG c f vars pats req) := by
    intro k h
    rcases h with h | ⟨i, hi, rfl⟩
    · simp only [R, KoreAML.sortVarsOf, List.mem_singleton] at h
      rw [h]; exact R_mem_premFG c f vars pats req
    · exact (key_mem_premFG c f vars pats req hlen hi).1
  rw [kernelItems_mapFG, frClauses_eq, List.map_append, List.map_append, List.map_map, List.map_map]
  congr 1
  · refine List.map_congr_left fun x hx => ?_
    exact clause_patFG c f rfl rfl rfl rfl rfl (preOf_isTop s x) hlen
      (fun i hi => hocc x hx i (by rw [varOccsList]; exact List.mem_append_left _ hi))
      (fun t ht => by cases ht)
      (fun k hk => hkey ((varsOf_preOfFG c _ R s x hk).imp_right fun ⟨i, hi, he⟩ => ⟨i, hocc x hx i hi, he⟩))
      (fun k hk => by
        obtain ⟨i, hi, rfl⟩ := freeOf_preOfFG c _ R s x hk
        exact (key_mem_premFG c f vars pats req hlen (hocc x hx i hi)).2)
  · obtain ⟨x₁, xs', rfl⟩ := List.exists_cons_of_ne_nil hxs
    simp only [List.map_cons, List.map_nil]
    congr 1
    exact clause_patFG c f rfl rfl rfl rfl rfl (preN_isTop s hxs) hlen
      (fun i hi => hocc x₁ (List.mem_cons_self ..) i (by rw [varOccsList]; exact List.mem_append_left _ hi))
      (fun t ht i hi => by cases ht; simp [Parse.boolT, varOccs] at hi)
      (fun k hk => hkey ((varsOf_preNFG c _ R s _ hk).imp_right fun ⟨x, hx, i, hi, he⟩ => ⟨i, hocc x hx i hi, he⟩))
      (fun k hk => by
        obtain ⟨x, hx, i, hi, rfl⟩ := freeOf_preNFG c _ R s _ hk
        exact (key_mem_premFG c f vars pats req hlen (hocc x hx i hi)).2)

/-- **`Γ`'s items for f** where f's clauses are `before ++ frClauses … ++ after`: those of
`before` and `after`, and between them the shapes of `gamma_shapeFG`. -/
theorem fnEquationsK_splitFG (c : Semantics) (f : Fn) {before cls after : List Clause}
    (h : f.clauses = before ++ cls ++ after) :
    (kernelItems (fnEquationsK c f)).map (·.pat) =
      (kernelItems (before.map (prioEquation c f))).map (·.pat) ++
        (kernelItems (cls.map (prioEquation c f))).map (·.pat) ++
          (kernelItems (after.map (prioEquation c f))).map (·.pat) := by
  unfold fnEquationsK
  rw [h, kernelItems_mapFG, kernelItems_mapFG, kernelItems_mapFG, kernelItems_mapFG]
  simp only [List.map_append]

theorem withCompFG_nil (n q : P) : withCompFG [] n q = q := rfl

theorem withCompFG_ne {L : List Clause} (h : L ≠ []) (n q : P) : withCompFG L n q = sAnd n q := by
  cases L with
  | nil => exact absurd rfl h
  | cons => rfl

/-- **The readings under the competitors' negation**: where competitors apply (`L` not empty) the
premises of `gamma_shapeFG` stand under their negation n, and the readings hold of `n ∧ prem`
(`readings_compete`); where none does they are the readings of `prem`. -/
theorem readings_withCompFG {M : Type} {I : Interpretation KoreAML.Sym M} (L : List Clause) (n : P)
    {ws : List P} {r : EVar} {σ : M} {prem rhs : P} {α : Type} {alts : List α} {A : α → P}
    {G : α → Valuation M → Prop} {Q : α → P} {QN : P}
    (R : Readings I ws r σ prem rhs alts A G Q QN) :
    Readings I ws r σ (withCompFG L n prem) rhs alts A G (fun x => withCompFG L n (Q x)) (withCompFG L n QN) := by
  unfold withCompFG
  cases L.isEmpty
  · exact readings_compete R
  · exact R

end TieFRGamma

end KCore
