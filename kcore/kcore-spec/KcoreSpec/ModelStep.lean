/-
  KCore. Parts of the reading of the step's closure axiom (`SatStepGoal`, proved in
  OpenConsistent.lean by `satStepGoal_open`): its disjuncts and their free variables.

  The axiom is `∀y. •y ⊆ ⋁_r ∃x̄_r. (L_r ∧ y ∈ R_r)`, one disjunct per rule, each read through its
  rule's table placed after the tables of the rules before it. In the model `•y` is the
  configurations of which `y` is a `StepM` successor (ModelCarrier.lean), and a step is made by a
  rule: its left-hand side matches the configuration under a well-sorted σ, its `requires` evaluates
  to `true`, no rule of a smaller priority applies (`RuleApplies`), and its right-hand side evaluates
  to `y`. Giving
  the rule's variables the elements of their values in σ, the configuration is in `L_r`
  (`tr_pat`, `reqPat_iff`, `applies_iff_open`, `tr_term`) and `y` in `R_r`.
-/
import KcoreSpec.ModelRules

set_option autoImplicit false

namespace KCore

namespace Faithful

namespace Model

open ML

variable {c : Semantics}

/-! ## The disjuncts of the closure -/

/-- One step of the fold that builds the closure's disjuncts (`stepClosureItem`). -/
def stepF (y : EVar) (acc : List String × List KoreAML.P × Nat) (p : Kore.Pattern) :
    List String × List KoreAML.P × Nat :=
  let (ns, φ) := KoreAML.closureDisjunct [] acc.2.2 y p
  (acc.1 ++ ns, acc.2.1 ++ [φ], acc.2.2 + ns.length)

/-- The number of variables of the tables of `pats`, from `n`. -/
def tablesLen (pats : List Kore.Pattern) (n : Nat) : Nat :=
  pats.foldl (fun n p => n + (KoreAML.tableOf [] p).length) n

theorem closureDisjunct_names_length (off : Nat) (y : EVar) (p : Kore.Pattern) :
    (KoreAML.closureDisjunct [] off y p).1.length = (KoreAML.tableOf [] p).length := by
  unfold KoreAML.closureDisjunct; simp

theorem stepF_off (y : EVar) : ∀ (pats : List Kore.Pattern) (acc : List String × List KoreAML.P × Nat),
    (pats.foldl (stepF y) acc).2.2 = tablesLen pats acc.2.2
  | [], _ => rfl
  | p :: pats, acc => by
    rw [List.foldl_cons, stepF_off y pats]
    unfold tablesLen
    rw [List.foldl_cons]
    congr 1
    show acc.2.2 + (KoreAML.closureDisjunct [] acc.2.2 y p).1.length = _
    rw [closureDisjunct_names_length]

theorem tablesLen_ge (pats : List Kore.Pattern) : ∀ n, n ≤ tablesLen pats n := by
  induction pats with
  | nil => intro n; exact Nat.le_refl _
  | cons p pats ih =>
    intro n
    unfold tablesLen at ih ⊢
    rw [List.foldl_cons]
    exact Nat.le_trans (Nat.le_add_right _ _) (ih _)

theorem stepF_keep (y : EVar) {φ : KoreAML.P} : ∀ (pats : List Kore.Pattern) (acc : List String × List KoreAML.P × Nat),
    φ ∈ acc.2.1 → φ ∈ (pats.foldl (stepF y) acc).2.1
  | [], _, h => h
  | p :: pats, acc, h => by
    rw [List.foldl_cons]
    refine stepF_keep y pats _ ?_
    show φ ∈ acc.2.1 ++ [(KoreAML.closureDisjunct [] acc.2.2 y p).2]
    exact List.mem_append_left _ h

/-- Each pattern's disjunct is among the closure's, read through its table placed at an offset
that leaves its variables below the total. -/
theorem stepF_mem (y : EVar) : ∀ (pats : List Kore.Pattern) (acc : List String × List KoreAML.P × Nat),
    ∀ p ∈ pats, ∃ off, off + (KoreAML.tableOf [] p).length ≤ tablesLen pats acc.2.2 ∧
      (KoreAML.closureDisjunct [] off y p).2 ∈ (pats.foldl (stepF y) acc).2.1
  | [], _, p, hp => absurd hp List.not_mem_nil
  | q :: pats, acc, p, hp => by
    rcases List.mem_cons.mp hp with rfl | hp
    · refine ⟨acc.2.2, ?_, ?_⟩
      · unfold tablesLen
        rw [List.foldl_cons]
        exact tablesLen_ge pats _
      · rw [List.foldl_cons]
        refine stepF_keep y pats _ ?_
        show _ ∈ acc.2.1 ++ [(KoreAML.closureDisjunct [] acc.2.2 y p).2]
        exact List.mem_append_right _ (List.mem_singleton_self _)
    · obtain ⟨off, hoff, hm⟩ := stepF_mem y pats (stepF y acc q) p hp
      refine ⟨off, ?_, ?_⟩
      · have : (stepF y acc q).2.2 = acc.2.2 + (KoreAML.tableOf [] q).length := by
          show acc.2.2 + (KoreAML.closureDisjunct [] acc.2.2 y q).1.length = _
          rw [closureDisjunct_names_length]
        rw [this] at hoff
        unfold tablesLen
        rw [List.foldl_cons]
        exact hoff
      · rw [List.foldl_cons]; exact hm

theorem stepClosure_pat (c : Semantics) :
    (stepClosureItem c).pat =
      let pats := c.rules.map (prioRuleK c)
      let y : EVar := ⟨tablesLen pats 0 + 1⟩
      ∀∀ y (KoreAML.sNext (.evar y) ⊆⊆ KoreAML.disjList (pats.foldl (stepF y) ([], [], 0)).2.1) := rfl

/-! ## Existentials over a disjunct's free variables -/

theorem sExists_foldr_intro {tbl : KoreAML.VarTable} {body : KoreAML.P} :
    ∀ (free : List (KoreAML.VarKey × Kore.KSort)) (e e' : Valuation Elem) (m : Elem),
    (∀ x, (∀ ks ∈ free, x ≠ tbl.ev ks.1) → e'.evalEvar x = e.evalEvar x) →
    e'.evalSvar = e.evalSvar →
    (∀ ks ∈ free, ∃ n, ks.2 = KoreAML.srt n ∧ InS (stdI c) n (e'.evalEvar (tbl.ev ks.1))) →
    body.interpret (stdI c) e' m →
    (free.foldr (fun (k, s) φ => KoreAML.sExists (tbl.ev k) (KoreAML.trSort tbl s) φ) body).interpret (stdI c) e m
  | [], e, e', m, hoff, hsv, _, hb => by
    have : e' = e := by
      cases e; cases e'
      simp only at hsv
      subst hsv
      congr 1
      funext x
      exact hoff x (fun _ h => absurd h List.not_mem_nil)
    subst this
    exact hb
  | (k, s) :: free, e, e', m, hoff, hsv, hg, hb => by
    show (KoreAML.sExists (tbl.ev k) (KoreAML.trSort tbl s)
      (free.foldr (fun (k, s) φ => KoreAML.sExists (tbl.ev k) (KoreAML.trSort tbl s) φ) body)).interpret (stdI c) e m
    rw [KoreAML.interp_sExists]
    refine ⟨e'.evalEvar (tbl.ev k), ?_, ?_⟩
    · rw [KoreAML.interp_member defOK_std]
      simp only [Function.update_same]
      obtain ⟨n, hn, hin⟩ := hg (k, s) (List.mem_cons_self ..)
      simp only at hn
      rw [hn, trSort_srt]
      exact (inS_iff _).mpr hin
    · refine sExists_foldr_intro free _ e' m (fun x hx => ?_) hsv
        (fun ks hks => hg ks (List.mem_cons_of_mem _ hks)) hb
      show e'.evalEvar x = Function.update e.evalEvar (tbl.ev k) (e'.evalEvar (tbl.ev k)) x
      by_cases hxk : x = tbl.ev k
      · subst hxk; simp only [Function.update_same]
      · rw [Function.update_noteq hxk]
        exact hoff x (fun ks hks => by
          rcases List.mem_cons.mp hks with rfl | hks
          · exact hxk
          · exact hx ks hks)

/-- The element variables of a list of keys, with their sorts (`closureDisjunct`'s binders). -/
def evarsOf (l : List KoreAML.VarKey) : List (KoreAML.VarKey × Kore.KSort) :=
  l.filterMap fun
    | k@(.evar _ s) => some (k, s)
    | _ => none

/-- The keys an evar filter keeps are among the list's. -/
theorem mem_filterMap_evar {l : List KoreAML.VarKey} {ks : KoreAML.VarKey × Kore.KSort}
    (h : ks ∈ evarsOf l) : ks.1 ∈ l ∧ ∃ n, ks.1 = .evar n ks.2 := by
  obtain ⟨k, hk, he⟩ := List.mem_filterMap.mp h
  cases k with
  | evar n s => simp only [Option.some.injEq] at he; subst he; exact ⟨hk, n, rfl⟩
  | sortVar n => cases he
  | svar n s => cases he

theorem evar_mem_filterMap {l : List KoreAML.VarKey} {n : String} {s : Kore.KSort} (h : .evar n s ∈ l) :
    (KoreAML.VarKey.evar n s, s) ∈ evarsOf l :=
  List.mem_filterMap.mpr ⟨_, h, rfl⟩

/-! ## The closure -/

/-- The free variables of a rule's axiom are its own, for a semantics whose clauses and rules are
well sorted. -/
theorem freeOf_prio_of_sorted (hok : c.sortedOK = true) (hb : ∀ r ∈ c.rules, binds r.vars.length (varOccs r.lhs) = true) {r : Rule} (hr : r ∈ c.rules) {k : KoreAML.VarKey}
    (hk : k ∈ KoreAML.freeOf [] (prioRuleK c r)) : ∃ i < r.vars.length, k = canonKey c r.vars i := by
  obtain ⟨-, hreqs, -⟩ := rule_ctx hok hr
  obtain ⟨hex₀, hpre₀, hpost₀⟩ := Semantics.sortedOK_rule hok hr
  rw [prioRuleK_top hex₀ hpre₀ hpost₀] at hk
  dsimp only at hk
  split at hk
  · rw [KoreAML.freeOf] at hk
    simp only [KoreAML.freeOf, KoreAML.freeOfList, List.append_nil, List.mem_append, List.not_mem_nil,
      or_false] at hk
    rcases hk with (hk | hk | hk) | hk
    · exact freeOf_rule_parts hok hr (Or.inl hk)
    · exact freeOf_rule_parts hok hr (Or.inr (Or.inl hk))
    · exact freeOf_rule_parts hok hr (Or.inr (Or.inr hk))
    · exact freeOf_rule_parts hok hr (Or.inr (Or.inr hk))
  · rw [KoreAML.freeOf] at hk
    simp only [KoreAML.freeOf, KoreAML.freeOfList, List.append_nil, List.mem_append, List.not_mem_nil,
      or_false] at hk
    rcases hk with (hk | hk | hk | hk) | hk
    · exact freeOf_rule_parts hok hr (Or.inl hk)
    · exact freeOf_rule_parts hok hr (Or.inr (Or.inl hk))
    · exfalso
      obtain ⟨φ, hφ, hk⟩ := mem_freeOf_anyOfC hk
      obtain ⟨r', hr', rfl⟩ := List.mem_map.mp hφ
      have hr'm := (List.mem_filter.mp hr').1
      obtain ⟨hlhs', hreqs', -⟩ := rule_ctx hok hr'm
      exact freeOf_applies hlhs' (fun t ht i hi => varOccs_lt t (hreqs' t ht) i hi)
        (Semantics.sortedOK_rule hok hr'm).2.1 (hb _ hr'm) hk
    · exact freeOf_rule_parts hok hr (Or.inr (Or.inr hk))
    · exact freeOf_rule_parts hok hr (Or.inr (Or.inr hk))

theorem top_free (tbl : KoreAML.VarTable) :
    (KoreAML.trSort tbl (srtOf c topCellSort)).isFreeEvar KoreAML.topVar = false := by
  unfold srtOf; rw [trSort_srt]; rfl

theorem index_le {tbl : KoreAML.VarTable} {k : KoreAML.VarKey} (hk : k ∈ tbl) : (tbl.ev k).val ≤ tbl.length := by
  show tbl.idxOf k + 1 ≤ tbl.length
  exact List.idxOf_lt_length_of_mem hk

end Model

end Faithful

end KCore
