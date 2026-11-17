/-
  KCore. Completeness at a configuration for rules with a `pre` and a `post`.

  In a model of `Γc ∪ Γstep`, an element after x's is in the right side of a rule of the definition,
  at a valuation where x's element is in the rule's left side, `⌈req = true⌉`, `pre`'s patterns and
  no competitor's `applies` (`step_successor_axiomPP`, from the closure axiom and `rule_parts_pp`).
  Where the step at x is decided (`StepDecided`), that element is the element of a successor of a
  step by the rule, or is in the open family of an unblocked match (`successor_split_pp`):
  - each predicate has a truth value at the match (`StepDecided`), and in a model of `Γc` its
    patterns hold at an element of the configuration sort exactly where that value is `true`
    (`conj_iff_holdsPP`), so `Holds … pre true` and `Holds … post true`;
  - a competitor does not apply at values (`applies_of_values_pp`,
    `notApplies_of_not_applies_pp`);
  - in the open case `pre`'s patterns, known at x's element, are read at the successor's: a
    condition's pattern is a predicate (`cond_pred_transfer_top`), its free variables valued in
    their sorts and its keys in `famOpen`'s table (`famOpen_keysPP`).
  `complete_at_pp` is `complete_at`'s statement from the per-rule facts `ruleSorted` and
  `rulePlainPP`. No `FnTerminates` is read, and no hypothesis that a competitor's conditions are
  decided beyond `StepDecided`.

  `famOpenPatPP`, `famOpen_eqPP`, `famOpen_keysPP` (the pattern `famOpen` reads and its table) and
  `readsConfined_of_pre` are public, for the values of an open family.
-/
import KcoreSpec.CondPred
import KcoreSpec.CompetePP
import KcoreSpec.ExComplete
import KcoreSpec.ModelChoicePP
import KcoreSpec.FamExPost
import KcoreSpec.CondTwoTables
import KcoreSpec.SatRulePP

set_option autoImplicit false

namespace KCore

namespace Faithful

open ML
open KoreAML (VarTable)
open HoldsShape (hasBinder Reads reads_of_agrees)

/-! ## A rule of the definition with a binder in a predicate -/

section
variable {c : Semantics}

/-- A rule of the definition whose `pre` has a binder makes the definition read a confined sort. -/
theorem readsConfined_of_pre {r : Rule} (hr : r ∈ c.rules) (hb : hasBinder r.pre = true) :
    c.readsConfined = true := by
  simp only [Semantics.readsConfined, Bool.or_eq_true, List.any_eq_true]
  exact Or.inl ⟨r, hr, by simp [hb]⟩

end

/-! ## The pattern `famOpen` reads, for a rule with predicates -/

section
variable {c : Semantics}

/-- `famOpen`'s pattern: the variables other than the existential ones bound, those of the left
side fixed to their values under σ, the `requires`, `pre`, and the right side
`∃ē. (rhs ∧ ens ∧ post)`. -/
def famOpenPatPP (c : Semantics) (r : Rule) (σ : Subst) : Kore.Pattern :=
  KoreAML.existsAll (srtOf c topCellSort)
    (((List.range r.vars.length).filter fun i => !r.exs.contains i).map
      fun i => ((canonVars c r.vars).getD i default).kore)
    (.and (srtOf c topCellSort) (fixK c r σ (varOccs r.lhs) ++
      [reqPat (srtOf c topCellSort) (r.req.map (Term.kore c (canonVars c r.vars)))] ++
      Cond.conj c (canonVars c r.vars) (srtOf c topCellSort) r.pre ++
      [KoreAML.existsAll (srtOf c topCellSort) (Model.ruleExBinders c r) (Model.ruleRightBodyPP c r)]))

theorem famOpen_eqPP {r : Rule} (hlt : ∀ i ∈ r.exs, i < r.vars.length) (σ : Subst) :
    famOpen c r σ = KoreAML.denB (famOpenPatPP c r σ) := by
  unfold famOpen famOpenPatPP
  dsimp only
  rw [Model.ruleRight_eqPP hlt, filterMap_getElem?_of_lt _ _ (fun i hi => by
    rw [canonVars_length]; exact List.mem_range.mp (List.mem_filter.mp hi).1), List.map_map]
  rfl

/-- Every variable of a rule, and every key of its predicates' patterns, is in the table of
`famOpen`'s pattern. -/
theorem famOpen_keysPP {r : Rule} {σ : Subst} :
    (∀ i < r.vars.length, canonKey c r.vars i ∈ KoreAML.tableOf [] (famOpenPatPP c r σ)) ∧
    (∀ k ∈ KoreAML.varsOf (Cond.kore c (canonVars c r.vars) (srtOf c topCellSort) r.pre),
      k ∈ KoreAML.tableOf [] (famOpenPatPP c r σ)) ∧
    (∀ k ∈ KoreAML.varsOf (Cond.kore c (canonVars c r.vars) (srtOf c topCellSort) r.post),
      k ∈ KoreAML.tableOf [] (famOpenPatPP c r σ)) := by
  have hT : ∀ {k}, k ∈ KoreAML.varsOf (famOpenPatPP c r σ) → k ∈ KoreAML.tableOf [] (famOpenPatPP c r σ) :=
    fun hk => by unfold KoreAML.tableOf; exact List.mem_eraseDups.mpr (List.mem_append_right _ hk)
  refine ⟨fun i hi => hT ?_, fun k hk => hT ?_, fun k hk => hT ?_⟩
  · unfold famOpenPatPP
    by_cases hx : i ∈ r.exs
    · refine Model.varsOf_existsAll_bodyEx ?_ _
      refine Model.varsOf_and_mem (List.mem_append_right _ (List.mem_singleton_self _)) ?_
      exact varsOf_existsAll_binder _ (List.mem_map_of_mem (f := fun i => ((canonVars c r.vars).getD i default).kore) hx)
    · exact varsOf_existsAll_binder _ (List.mem_map_of_mem (f := fun i => ((canonVars c r.vars).getD i default).kore)
        (List.mem_filter.mpr ⟨List.mem_range.mpr hi, by simpa using hx⟩))
  · unfold famOpenPatPP
    exact Model.varsOf_existsAll_bodyEx
      (Model.varsOf_condConj (fun φ hφ => List.mem_append_left _ (List.mem_append_right _ hφ)) hk) _
  · unfold famOpenPatPP
    refine Model.varsOf_existsAll_bodyEx (Model.varsOf_and_mem (List.mem_append_right _ (List.mem_singleton_self _)) ?_) _
    unfold Model.ruleRightBodyPP
    exact Model.varsOf_existsAll_bodyEx (Model.varsOf_condConj (fun φ hφ => List.mem_append_right _ hφ) hk) _

end

/-! ## The axiom of a well-sorted rule, in any model -/

section
variable {c : Semantics} {M : Type} {I : Interpretation KoreAML.Sym M}

/-- The conjuncts a predicate adds to a sentence read two valuations under two tables alike where
they give each of its free variables one element. -/
theorem conj_twoTPP (hD : KoreAML.DefOK I) {vars : List Srt} {p : Cond} (hok : c.condOK vars p = true)
    {tbl tbl' : VarTable} {e e' : Valuation M}
    (hk : ∀ k ∈ KoreAML.varsOf (Cond.kore c (canonVars c vars) (srtOf c topCellSort) p), k ∈ tbl ∧ k ∈ tbl')
    (hag : ∀ i ∈ varOccsCond vars.length p, canonKey c vars i ∈ tbl ∧ canonKey c vars i ∈ tbl' ∧
      e.evalEvar (tbl.ev (canonKey c vars i)) = e'.evalEvar (tbl'.ev (canonKey c vars i))) {a : M}
    (hm : ∀ φ ∈ Cond.conj c (canonVars c vars) (srtOf c topCellSort) p, (KoreAML.tr ⟨tbl, []⟩ φ).interpret I e a) :
    ∀ φ ∈ Cond.conj c (canonVars c vars) (srtOf c topCellSort) p, (KoreAML.tr ⟨tbl', []⟩ φ).interpret I e' a := by
  intro φ hφ
  by_cases hT : p.isTop = true
  · simp [Cond.conj, hT] at hφ
  · obtain rfl : φ = Cond.kore c (canonVars c vars) (srtOf c topCellSort) p := by simpa [Cond.conj, hT] using hφ
    exact (tr_condKore_twoT hD p hok hk hag a).mp (hm _ (by simp [Cond.conj, hT]))

/-- **A rule's axiom `\rewrites(L, ∃ē. (rhs ∧ ens ∧ post))`, its left part `L` read**, for a rule
with `ruleSorted` (not asked to be one of the definition's), whatever its predicates: every variable of the rule and every key of `pre`'s pattern is a variable
of `L`, those other than ē occur free in it, the canonical variables of the left sides and
conditions of its competitors and the keys of their `pre`'s patterns are among `L`'s, and an element
of `L` is in the left side, in `⌈req = true⌉` and `pre`, and in no competitor's `applies`. -/
theorem rule_parts_pp {r : Rule} (hs : c.ruleSorted r = true) :
    ∃ L, prioRuleK c r = .rewrites (srtOf c topCellSort) L (ruleRight c r) ∧
      (∀ i < r.vars.length, canonKey c r.vars i ∈ KoreAML.varsOf L) ∧
      (∀ i < r.vars.length, i ∉ r.exs → canonKey c r.vars i ∈ KoreAML.freeOf [] L) ∧
      (∀ k ∈ KoreAML.varsOf (Cond.kore c (canonVars c r.vars) (srtOf c topCellSort) r.pre),
        k ∈ KoreAML.varsOf L) ∧
      (∀ r' ∈ c.rules, r'.prio < r.prio →
        (∀ i < r'.vars.length, i ∈ r'.leftVars → canonKey c r'.vars i ∈ KoreAML.varsOf L) ∧
        ∀ k ∈ KoreAML.varsOf (Cond.kore c (canonVars c r'.vars) (srtOf c topCellSort) r'.pre),
          k ∈ KoreAML.varsOf L) ∧
      ∀ (tbl : VarTable) (e : Valuation M) (a : M), (KoreAML.tr ⟨tbl, []⟩ L).interpret I e a →
        (KoreAML.tr ⟨tbl, []⟩ (Term.kore c (canonVars c r.vars) r.lhs)).interpret I e a ∧
        (KoreAML.tr ⟨tbl, []⟩ (reqPat (srtOf c topCellSort) (r.req.map (Term.kore c (canonVars c r.vars))))).interpret
          I e a ∧
        (∀ φ ∈ Cond.conj c (canonVars c r.vars) (srtOf c topCellSort) r.pre,
          (KoreAML.tr ⟨tbl, []⟩ φ).interpret I e a) ∧
        ∀ r' ∈ c.rules, r'.prio < r.prio →
          ¬ (KoreAML.tr ⟨tbl, []⟩ (applies c r' (canonRulePres r'))).interpret I e a := by
  obtain ⟨-, hocc, -⟩ := Model.ruleSorted_partsPP hs
  obtain ⟨hRf, hRv⟩ := Model.ruleRight_keysPP hs
  let C := srtOf c topCellSort
  let vs := canonVars c r.vars
  let n := r.vars.length
  let comps := (c.rules.filter (·.prio < r.prio)).map fun r' => applies c r' (canonRulePres r')
  have hcomp : ∀ r' ∈ c.rules, r'.prio < r.prio → applies c r' (canonRulePres r') ∈ comps := fun r' hr' hlt =>
    List.mem_map.mpr ⟨r', List.mem_filter.mpr ⟨hr', by simpa using hlt⟩, rfl⟩
  let left : List Kore.Pattern := [Term.kore c vs r.lhs, reqPat C (r.req.map (Term.kore c vs))] ++
    Cond.conj c vs C r.pre
  have hreqK : ∀ {k : KoreAML.VarKey} {p : Kore.Pattern}, k ∈ KoreAML.freeOf [] p → k ∈ KoreAML.varsOf p →
      k ∈ KoreAML.freeOf [] (reqPat C (some p)) ∧ k ∈ KoreAML.varsOf (reqPat C (some p)) := fun hf hv => by
    simp only [reqPat]
    rw [KoreAML.freeOf, KoreAML.varsOf]
    exact ⟨List.mem_append_left _ hf, List.mem_append_left _ (List.mem_append_right _ hv)⟩
  have hceilK : ∀ {k : KoreAML.VarKey}, (k ∈ KoreAML.freeOf [] (ruleRight c r) →
      k ∈ KoreAML.freeOf [] (.ceil C C (ruleRight c r))) ∧
      (k ∈ KoreAML.varsOf (ruleRight c r) → k ∈ KoreAML.varsOf (.ceil C C (ruleRight c r))) :=
    ⟨fun hk => by rw [KoreAML.freeOf]; exact hk,
     fun hk => by rw [KoreAML.varsOf]; exact List.mem_append_right _ hk⟩
  have hkeys : ∀ {ps : List Kore.Pattern}, (∀ q ∈ left, q ∈ ps) → .ceil C C (ruleRight c r) ∈ ps →
      (∀ i < n, canonKey c r.vars i ∈ KoreAML.varsOf (.and C ps)) ∧
      (∀ i < n, i ∉ r.exs → canonKey c r.vars i ∈ KoreAML.freeOf [] (.and C ps)) ∧
      (∀ k ∈ KoreAML.varsOf (Cond.kore c vs C r.pre), k ∈ KoreAML.varsOf (.and C ps)) := by
    intro ps hsub h3
    have h1 : Term.kore c vs r.lhs ∈ ps := hsub _ (by simp [left])
    have h2 : reqPat C (r.req.map (Term.kore c vs)) ∈ ps := hsub _ (by simp [left])
    have hP : ∀ φ ∈ Cond.conj c vs C r.pre, φ ∈ ps := fun φ hφ => hsub _ (List.mem_append_right _ hφ)
    have hpart : ∀ i < n, (i ∉ r.exs → canonKey c r.vars i ∈ KoreAML.freeOf [] (.and C ps)) ∧
        canonKey c r.vars i ∈ KoreAML.varsOf (.and C ps) := by
      intro i hi
      by_cases hx : i ∈ r.exs
      · exact ⟨fun h' => absurd hx h', Model.varsOf_and_mem h3 (hceilK.2 (hRv i hi (Or.inl hx)))⟩
      rcases hocc i hi with hL | ⟨t, ht, hit⟩ | hPr | hR | ⟨t, ht, hit⟩ | hPo
      · exact ⟨fun _ => Model.freeOf_and_memOpen h1 (Model.kore_freeOf c vs r.lhs hL),
          Model.varsOf_and_mem h1 (varsOf_kore c vs r.lhs hL)⟩
      · rw [ht] at h2
        obtain ⟨hf, hv⟩ := hreqK (Model.kore_freeOf c vs t hit) (varsOf_kore c vs t hit)
        exact ⟨fun _ => Model.freeOf_and_memOpen h2 hf, Model.varsOf_and_mem h2 hv⟩
      · have hT : r.pre.isTop = false := by
          cases hq : r.pre.isTop
          · rfl
          · rw [Cond.eq_top_of_isTop hq] at hPr; simp [varOccsCond] at hPr
        have hmem : Cond.kore c vs C r.pre ∈ ps := hP _ (by simp [Cond.conj, hT])
        obtain ⟨k1, k2⟩ := Model.condKore_keys C r.pre (bound := []) hi hPr (by simp)
        exact ⟨fun _ => Model.freeOf_and_memOpen hmem k1, Model.varsOf_and_mem hmem k2⟩
      · exact ⟨fun _ => Model.freeOf_and_memOpen h3 (hceilK.1 (hRf i hi hx (Or.inl hR))),
          Model.varsOf_and_mem h3 (hceilK.2 (hRv i hi (Or.inr (Or.inl hR))))⟩
      · exact ⟨fun _ => Model.freeOf_and_memOpen h3 (hceilK.1 (hRf i hi hx (Or.inr (Or.inl ⟨t, ht, hit⟩)))),
          Model.varsOf_and_mem h3 (hceilK.2 (hRv i hi (Or.inr (Or.inr (Or.inl ⟨t, ht, hit⟩)))))⟩
      · exact ⟨fun _ => Model.freeOf_and_memOpen h3 (hceilK.1 (hRf i hi hx (Or.inr (Or.inr hPo)))),
          Model.varsOf_and_mem h3 (hceilK.2 (hRv i hi (Or.inr (Or.inr (Or.inr hPo)))))⟩
    exact ⟨fun i hi => (hpart i hi).2, fun i hi hx => (hpart i hi).1 hx, fun k hk => Model.varsOf_condConj hP hk⟩
  have hread : ∀ {ps : List Kore.Pattern}, (∀ q ∈ left, q ∈ ps) → ∀ (tbl : VarTable) (e : Valuation M) (a : M),
      (KoreAML.tr ⟨tbl, []⟩ (.and C ps)).interpret I e a →
      (KoreAML.tr ⟨tbl, []⟩ (Term.kore c vs r.lhs)).interpret I e a ∧
      (KoreAML.tr ⟨tbl, []⟩ (reqPat C (r.req.map (Term.kore c vs)))).interpret I e a ∧
      (∀ φ ∈ Cond.conj c vs C r.pre, (KoreAML.tr ⟨tbl, []⟩ φ).interpret I e a) := by
    intro ps hsub tbl e a h
    have h1 : Term.kore c vs r.lhs ∈ ps := hsub _ (by simp [left])
    rw [interp_and (List.ne_nil_of_mem h1)] at h
    exact ⟨h _ h1, h _ (hsub _ (by simp [left])), fun φ hφ => h _ (hsub _ (List.mem_append_right _ hφ))⟩
  by_cases hce : comps.isEmpty
  · have hnone : ∀ r' ∈ c.rules, ¬ r'.prio < r.prio := fun r' hr' hlt => by
      have := hcomp r' hr' hlt
      rw [List.isEmpty_iff.mp hce] at this
      exact absurd this List.not_mem_nil
    obtain ⟨hk1, hk2, hk3⟩ := hkeys (ps := left ++ [.ceil C C (ruleRight c r)])
      (fun q hq => List.mem_append_left _ hq) (by simp)
    refine ⟨_, by unfold prioRuleK; dsimp only; rw [if_pos hce], hk1, hk2, hk3,
      fun r' hr' hlt => absurd hlt (hnone r' hr'), fun tbl e a h => ?_⟩
    obtain ⟨h1, h2, h3⟩ := hread (fun q hq => List.mem_append_left _ hq) tbl e a h
    exact ⟨h1, h2, h3, fun r' hr' hlt => absurd hlt (hnone r' hr')⟩
  · have hnot : Kore.Pattern.not C (anyOfC C comps) ∈ left ++ [.not C (anyOfC C comps), .ceil C C (ruleRight c r)] := by
      simp
    obtain ⟨hk1, hk2, hk3⟩ := hkeys (ps := left ++ [.not C (anyOfC C comps), .ceil C C (ruleRight c r)])
      (fun q hq => List.mem_append_left _ hq) (by simp)
    have hvC : ∀ r' ∈ c.rules, r'.prio < r.prio → ∀ {k}, k ∈ KoreAML.varsOf (applies c r' (canonRulePres r')) →
        k ∈ KoreAML.varsOf (.and C (left ++ [.not C (anyOfC C comps), .ceil C C (ruleRight c r)])) :=
      fun r' hr' hlt k hk => Model.varsOf_and_mem hnot (by
        simp only [KoreAML.varsOf]
        exact List.mem_append_right _ (mem_varsOf_anyOfC (hcomp r' hr' hlt) hk))
    refine ⟨_, by unfold prioRuleK; dsimp only; rw [if_neg hce], hk1, hk2, hk3,
      fun r' hr' hlt => ⟨fun i hi hil => hvC r' hr' hlt ((Model.varsOf_applies_pp r').1 i hi hil),
        fun k hk => hvC r' hr' hlt ((Model.varsOf_applies_pp r').2 k hk)⟩, fun tbl e a h => ?_⟩
    obtain ⟨h1, h2, h3⟩ := hread (fun q hq => List.mem_append_left _ hq) tbl e a h
    rw [interp_and (List.ne_nil_of_mem hnot)] at h
    have h4 := h _ hnot
    rw [KoreAML.tr, KoreAML.interp_sNot] at h4
    exact ⟨h1, h2, h3, fun r' hr' hlt happ => h4.1 (anyOfC_of_mem h4.2 (hcomp r' hr' hlt) happ)⟩

end

/-! ## The successor a disjunct of the step's closure gives -/

section
variable {c : Semantics} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}

/-- **The successor a rule's axiom gives, in two cases, for a rule with predicates.** For a rule r
with `ruleSorted` (not asked to be one of the definition's) in a definition whose rules have it, in
a model of `Γc`, at a valuation of r's variables other than the existential ones in their sorts
where x's element is in r's left side, in `⌈req = true⌉`, in `pre` and in no competitor's
`applies`, and b is in r's right side `∃ē. (rhs ∧ ens ∧ post)`, where the step at x is decided
(`StepDecided`): there is an unblocked match σ of r at x, and
- where r's left side binds every variable, b is the element of a configuration y with every premise
  of `StepBy c r σ x y` but the rule's membership, `Holds … pre true` and `Holds … post true`
  included: each predicate has a truth value at σ (`StepDecided`), and in a model of `Γc` it holds
  at an element exactly where that value is `true` (`conj_iff_holdsPP`);
- otherwise b is in `famOpen c r σ`.
No rule of a smaller priority applies at values (`applies_of_values_pp`), so none applies where its
`requires` has a result and its `pre` a truth value at each match (`notApplies_of_not_applies_pp`). -/
theorem successor_split_pp (h : c.coreOK = true) (hrules : ∀ r ∈ c.rules, c.ruleSorted r = true)
    (x : Config c) (hd : StepDecided c x.val) (hI : I ⊧ᴵP Γc c)
    (hcw : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, cl.needsWitness c = true → cl.CondDecided c) {r : Rule}
    (hs : c.ruleSorted r = true)
    (hrcP : hasBinder r.pre = true → c.readsConfined = true) (hrcQ : hasBinder r.post = true → c.readsConfined = true)
    (hdr : (∀ r' ∈ c.rules, r'.prio < r.prio → ¬ RuleApplies c r' x.val) →
      (∀ σ, c.WellSortedAt r.vars r.leftVars σ → PatVal c σ r.lhs x.val →
        (∀ t, r.req = some t → ∃ v, EvalTerm c σ t v) ∧ ∃ b, Holds c r.vars.length σ r.pre b) ∧
      (∀ σ, c.WellSorted r.vars σ → PatVal c σ r.lhs x.val →
        (∀ t, r.req = some t → EvalTerm c σ t (some (bool true))) → Holds c r.vars.length σ r.pre true →
          (∃ v, EvalTerm c σ r.rhs v) ∧ (∀ e, r.ens = some e → ∃ w, EvalTerm c σ e w) ∧
          ∃ b, Holds c r.vars.length σ r.post b))
    {tbl : VarTable} (hkeys : ∀ i < r.vars.length, canonKey c r.vars i ∈ tbl)
    (hkP : ∀ k ∈ KoreAML.varsOf (Cond.kore c (canonVars c r.vars) (srtOf c topCellSort) r.pre), k ∈ tbl)
    (hkQ : ∀ k ∈ KoreAML.varsOf (Cond.kore c (canonVars c r.vars) (srtOf c topCellSort) r.post), k ∈ tbl)
    (hkeysC : ∀ r' ∈ c.rules, r'.prio < r.prio →
      (∀ i < r'.vars.length, i ∈ r'.leftVars → canonKey c r'.vars i ∈ tbl) ∧
      ∀ k ∈ KoreAML.varsOf (Cond.kore c (canonVars c r'.vars) (srtOf c topCellSort) r'.pre), k ∈ tbl)
    {e : Valuation M}
    (hin : ∀ i < r.vars.length, i ∉ r.exs → InS I (c.sortName (r.vars.getD i 0))
      (e.evalEvar (tbl.ev (keyAt (canonVars c r.vars) i))))
    (hl : (KoreAML.tr ⟨tbl, []⟩ (Term.kore c (canonVars c r.vars) r.lhs)).interpret I e (elemOf c I x.val))
    (hreqm : (KoreAML.tr ⟨tbl, []⟩ (reqPat (srtOf c topCellSort)
      (r.req.map (Term.kore c (canonVars c r.vars))))).interpret I e (elemOf c I x.val))
    (hprem : ∀ φ ∈ Cond.conj c (canonVars c r.vars) (srtOf c topCellSort) r.pre,
      (KoreAML.tr ⟨tbl, []⟩ φ).interpret I e (elemOf c I x.val))
    (hcomp : ∀ r' ∈ c.rules, r'.prio < r.prio →
      ¬ (KoreAML.tr ⟨tbl, []⟩ (applies c r' (canonRulePres r'))).interpret I e (elemOf c I x.val))
    {b : M} (hy : (KoreAML.tr ⟨tbl, []⟩ (ruleRight c r)).interpret I e b) :
    (r.opens = [] ∧ ∃ (y : Config c) (σ : Subst), (r ∈ c.rules → StepBy c r σ x y) ∧ b = elemOf c I y.val) ∨
    (r.opens ≠ [] ∧ ∃ σ, Unblocked c r σ x.val ∧ ∀ e', (famOpen c r σ).interpret I e' b) := by
  have hIΓ : I ⊧ᴵP Γ c := fun φ hφ => hI φ (Or.inl hφ)
  have hs0 := hypSound_of_core h
  obtain ⟨hok, hsr, hnn, hg, hph, hcso, hcs, hph', hno⟩ := id hs0
  haveI : OvlOK c := hno
  have hsc := sortCtx_of_all hok hsr (OvlOK.ovlCase hno)
  have hD := defOK hIΓ
  have hneg := (neg_of_coreCl hI (Semantics.sortedOKCl_of_sortedOK hok) hsr (Semantics.coreOK_parts h).2.1 hph hcw (HoldsShape.preReadAll_of_core h hI))
  obtain ⟨hlhs, -, hreqs, hensS, hrhss, hexnd, hexs, hokP, hokQ, hbdP, hbdQ⟩ := Model.ruleSorted_partsPP hs
  have hlt : ∀ i ∈ r.exs, i < r.vars.length := fun i hi => (hexs i hi).1
  let vs := canonVars c r.vars
  have hnxL : ∀ i ∈ varOccs r.lhs, i < r.vars.length ∧ i ∉ r.exs := fun i hi =>
    ⟨varOccs_lt r.lhs hlhs i hi, fun hx => (hexs i hx).2.1 hi⟩
  have hnxQ : ∀ t, r.req = some t → ∀ i ∈ varOccs t, i < r.vars.length ∧ i ∉ r.exs := fun t ht i hi =>
    ⟨varOccs_lt t (hreqs t ht) i hi, fun hx => (hexs i hx).2.2 (List.mem_append_left _ (by rw [ht]; exact hi))⟩
  have hnxP : ∀ i ∈ varOccsCond r.vars.length r.pre, i < r.vars.length ∧ i ∉ r.exs := fun i hi =>
    ⟨varOccsCond_lt_twoT r.pre hokP i hi, fun hx => (hexs i hx).2.2 (List.mem_append_right _ hi)⟩
  -- inside `∃ē`: a valuation that agrees with e off ē and gives ē elements of their sorts
  rw [Model.ruleRight_eqPP hlt] at hy
  obtain ⟨eR, hoff, hguard, hbody⟩ := existsAll_elim hD (Model.ruleExBinders c r) e _
    (binders_nodupEx hkeys hlt hexnd) (binders_sortEx hlt) hy
  unfold Model.ruleRightBodyPP at hbody
  rw [interp_and (by simp)] at hbody
  have hyR := hbody (Term.kore c vs r.rhs) (List.mem_append_left _ (List.mem_cons_self ..))
  have hensR := hbody (reqPat (srtOf c topCellSort) (r.ens.map (Term.kore c vs)))
    (List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
  have hpostR : ∀ φ ∈ Cond.conj c vs (srtOf c topCellSort) r.post, (KoreAML.tr ⟨tbl, []⟩ φ).interpret I eR b :=
    fun φ hφ => hbody φ (List.mem_append_right _ hφ)
  have hoffE : ∀ i < r.vars.length, i ∉ r.exs →
      eR.evalEvar (tbl.ev (canonKey c r.vars i)) = e.evalEvar (tbl.ev (canonKey c r.vars i)) := by
    intro i hi hx
    refine hoff _ fun b hb he => ?_
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hb
    exact hx ((canonKey_inj hi (hlt j hj) (ev_inj (hkeys i hi) (hkeys j (hlt j hj)) he)) ▸ hj)
  have hinR : ∀ i < r.vars.length,
      InS I (c.sortName (r.vars.getD i 0)) (eR.evalEvar (tbl.ev (keyAt vs i))) := by
    intro i hi
    by_cases hx : i ∈ r.exs
    · exact hguard _ (List.mem_map_of_mem (f := fun i => ((canonVars c r.vars).getD i default).kore) hx) _
        (by rw [canonVars_getD c hi]; rfl)
    · show InS I _ (eR.evalEvar (tbl.ev (canonKey c r.vars i)))
      rw [hoffE i hi hx]; exact hin i hi hx
  have hlR : (KoreAML.tr ⟨tbl, []⟩ (Term.kore c vs r.lhs)).interpret I eR (elemOf c I x.val) :=
    (tr_kore_congr r.lhs (fun i hi => (hoffE i (hnxL i hi).1 (hnxL i hi).2).symm) _).mp hl
  have hreqR : (KoreAML.tr ⟨tbl, []⟩ (reqPat (srtOf c topCellSort)
      (r.req.map (Term.kore c vs)))).interpret I eR (elemOf c I x.val) :=
    reqPat_transferSplit hIΓ (fun t ht i hi => (hoffE i (hnxQ t ht i hi).1 (hnxQ t ht i hi).2).symm) hreqm
      (reqPat_inhSplit hIΓ hreqm tbl eR)
  have hpreR : ∀ φ ∈ Cond.conj c vs (srtOf c topCellSort) r.pre,
      (KoreAML.tr ⟨tbl, []⟩ φ).interpret I eR (elemOf c I x.val) :=
    conj_congrPP hD hokP hkP (fun i hi => hkeys i (hnxP i hi).1)
      (fun i hi => (hoffE i (hnxP i hi).1 (hnxP i hi).2).symm) hprem
  let σ := substOf c I tbl vs r.vars eR
  -- the left side binds the variables it holds at values
  obtain ⟨hmatch, hwitL⟩ := patVal_backC hIΓ hph hcs hcso hg hsc.trans hnn.1 (canonVars_length c r.vars) hinR
    (collPat_of_sorted hph' hlhs) hlhs x.property hlR
  -- no rule of a smaller priority applies at values: it would apply in the model
  have hnoapp : ∀ r' ∈ c.rules, r'.prio < r.prio → ¬ RuleApplies c r' x.val :=
    fun r' hr' hlt' ⟨σ', hσ', hpv', hreq', hpre'⟩ => hcomp r' hr' hlt'
      (applies_of_values_pp h hI hcw (hrules r' hr') (readsConfined_of_pre hr') hσ' hpv' hreq' hpre'
        (hkeysC r' hr' hlt').1 (hkeysC r' hr' hlt').2 e)
  -- so none applies, at values, where its `requires` has a result and its `pre` a truth value
  have hprio : ∀ r' ∈ c.rules, r'.prio < r.prio → NotApplies c r' x.val := by
    intro r' hr' hlt'
    have hun : ∀ r'' ∈ c.rules, r''.prio < r'.prio → ¬ RuleApplies c r'' x.val :=
      fun r'' hr'' hlt'' => hnoapp r'' hr'' (Nat.lt_trans hlt'' hlt')
    exact notApplies_of_not_applies_pp h hI hcw (hrules r' hr') (readsConfined_of_pre hr') (hd r' hr' hun).1
      (hkeysC r' hr' hlt').1 (hkeysC r' hr' hlt').2 e (hcomp r' hr' hlt')
  by_cases hop : r.opens = []
  · -- every variable is held by the left side: the step of `StepDecided`
    left
    refine ⟨hop, ?_⟩
    have hbinds := Rule.lhs_of_opens_nilSplit hop
    obtain ⟨hσ, hag⟩ := substOf_ok hIΓ hg hsc.trans (canonVars_length c r.vars) (fun i hi => hwitL i (hbinds i hi))
    have hdr' := hdr hnoapp
    obtain ⟨σC, hσC1, hσC2⟩ := sortSing hIΓ (top_numbered (c := c))
    have hSC : ∀ a, (KoreAML.trSort tbl (srtOf c topCellSort)).interpret I eR a ↔ a = σC := fun a => by
      unfold srtOf; rw [trSort_srt]; exact hσC1 a
    -- a condition the element satisfies evaluates to `true`, where it has a result
    have htrue : ∀ (q : Option Term) (m : M), (∀ t, q = some t →
        sortOfTerm (c.rhsCtx (c.fns.map Fn.sig)) r.vars t = some Srt.bool) →
        (∀ t, q = some t → ∃ v, EvalTerm c σ t v) →
        (KoreAML.tr ⟨tbl, []⟩ (reqPat (srtOf c topCellSort) (q.map (Term.kore c vs)))).interpret I eR m →
        ∀ t, q = some t → EvalTerm c σ t (some (bool true)) := by
      intro q m hqs hqv hqm t ht
      obtain ⟨v, hv⟩ := hqv t ht
      by_cases hvt : v = some (bool true)
      · rw [hvt] at hv; exact hv
      · exfalso
        rw [ht] at hqm
        exact reqFalse_empty hIΓ hSC hσC2 hvt (fun u hu => EvalTerm.sorted hsc hv fns_headsOK hσ (hqs t ht) hu)
          (evalTerm_den4ClPre hIΓ hnn hsc hph (clauseOpenFactsP_of_sortedOKCl (Semantics.sortedOKCl_of_sortedOK hok))
            hneg (HoldsShape.preReadAll_of_core h hI) hv fns_headsOK hσ (canonVars_length c r.vars) hag (hqs t ht)) _ hqm
    have hreqT := htrue r.req _ hreqs (hdr'.1 σ (hσ.at _) hmatch).1 hreqR
    -- `pre` has a truth value at σ, and x's element is in `pre`: it is `true`
    have hpreT : Holds c r.vars.length σ r.pre true := by
      obtain ⟨bp, hbp⟩ := (hdr'.1 σ (hσ.at _) hmatch).2
      have hbt := (conj_iff_holdsPP h hI hcw hokP hbdP hrcP
        (reads_of_agrees hσ hag fun i hi => ⟨(hnxP i hi).1, hkeys i (hnxP i hi).1⟩)
        hkP (inh_top_PP hIΓ x tbl eR) hbp).mp hpreR
      rw [hbt] at hbp; exact hbp
    have hrest := hdr'.2 σ hσ hmatch hreqT hpreT
    have hensT := htrue r.ens _ hensS hrest.2.1 hensR
    obtain ⟨v, hv⟩ := hrest.1
    have hbR := (evalTerm_den4ClPre hIΓ hnn hsc hph (clauseOpenFactsP_of_sortedOKCl (Semantics.sortedOKCl_of_sortedOK hok))
      hneg (HoldsShape.preReadAll_of_core h hI) hv fns_headsOK hσ (canonVars_length c r.vars) hag hrhss b).mp hyR
    cases v with
    | none => exact hbR.elim
    | some yv =>
      have hyv := EvalTerm.sorted hsc hv fns_headsOK hσ hrhss rfl
      have hbe : b = elemOf c I yv := ((elemOf_spec hIΓ hyv eR).1 b).mp (((den_closed c yv).interp eR eR b).mp hbR)
      -- `post` has a truth value at σ, and b is in `post`: it is `true`
      have hpostT : Holds c r.vars.length σ r.post true := by
        obtain ⟨bq, hbq⟩ := hrest.2.2
        have hbt := (conj_iff_holdsPP h hI hcw hokQ hbdQ hrcQ
          (reads_of_agrees hσ hag fun i hi =>
            ⟨varOccsCond_lt_twoT r.post hokQ i hi, hkeys i (varOccsCond_lt_twoT r.post hokQ i hi)⟩)
          hkQ (by rw [hbe]; exact inh_top_PP hIΓ ⟨yv, hyv⟩ tbl eR) hbq).mp hpostR
        rw [hbt] at hbq; exact hbq
      exact ⟨⟨yv, hyv⟩, σ, fun hmem => ⟨hmem, hσ, hmatch, hreqT, hpreT, hv, hensT, hpostT, hprio⟩, hbe⟩
  -- an open variable: the valuation, moved to `famOpen`'s variables, satisfies its body at b
  right
  refine ⟨hop, σ, ⟨fun i hi s hsi => ?_, hmatch, hprio⟩, fun e' => ?_⟩
  · have hlti : i < r.vars.length := (List.getElem?_eq_some_iff.mp hsi).1
    obtain ⟨h1, -⟩ := pick_spec (hwitL i hi)
    refine ⟨_, substOf_lookup hlti, ?_⟩
    rw [h1, List.getD_eq_getElem?_getD, hsi, Option.getD_some]
  rw [famOpen_eqPP hlt]
  unfold KoreAML.denB
  obtain ⟨hkf, hkfP, hkfQ⟩ := famOpen_keysPP (c := c) (r := r) (σ := σ)
  generalize KoreAML.tableOf [] (famOpenPatPP c r σ) = tf at hkf hkfP hkfQ ⊢
  unfold famOpenPatPP
  let outer := (List.range r.vars.length).filter fun i => !r.exs.contains i
  have houter : ∀ i, i ∈ outer ↔ i < r.vars.length ∧ i ∉ r.exs := fun i => by simp [outer]
  have hol : ∀ i ∈ outer, i < r.vars.length := fun i hi => ((houter i).mp hi).1
  have hsortB : ∀ i < r.vars.length,
      ((canonVars c r.vars).getD i default).kore.sort = KoreAML.srt (c.sortName (r.vars.getD i 0)) := fun i hi => by
    rw [canonVars_getD c hi]; rfl
  let e₁ := copyVEx c tbl tf r.vars outer eR e'
  let e₂ := copyVSplit c tbl tf r.vars eR e₁
  have hat₁ : ∀ i < r.vars.length, i ∉ r.exs →
      e₁.evalEvar (tf.ev (keyAt vs i)) = eR.evalEvar (tbl.ev (keyAt vs i)) :=
    fun i hi hx => copyVEx_at hkf hi ((houter i).mpr ⟨hi, hx⟩)
  have hat₂ : ∀ i < r.vars.length, e₂.evalEvar (tf.ev (keyAt vs i)) = eR.evalEvar (tbl.ev (keyAt vs i)) :=
    fun i hi => copyVSplit_at hkf hi
  have hinC : (KoreAML.inhOf (KoreAML.trSort tf (srtOf c topCellSort))).interpret I e₁ b :=
    reqPat_inhSplit hIΓ hensR tf e₁
  have hne : ∀ (l : List Kore.Pattern) (p : Kore.Pattern), l ++ [p] ≠ [] := fun l p => by simp
  refine existsAll_intro_at hD _ e' e₁ b (binders_nodupEx hkf hol (List.nodup_range.filter _)) (binders_sortEx hol)
    (fun z hz => copyVEx_off fun i hi his he => hz _ (List.mem_map_of_mem his) he) rfl
    (fun b' hb' n hn => ?_) ?_
  · obtain ⟨i, hio, rfl⟩ := List.mem_map.mp hb'
    have hi := hol i hio
    rw [hsortB i hi] at hn
    rw [← srt_inj hn]
    show InS I _ (e₁.evalEvar (tf.ev (canonKey c r.vars i)))
    rw [copyVEx_at hkf hi hio]
    exact hinR i hi
  rw [interp_and (hne _ _)]
  intro p hp'
  rcases List.mem_append.mp hp' with hp' | hp'
  rcases List.mem_append.mp hp' with hp' | hp'
  rcases List.mem_append.mp hp' with hp' | hp'
  · -- the left side's variables, fixed to their values under σ
    unfold fixK at hp'
    obtain ⟨i, hiL, hpi⟩ := List.mem_filterMap.mp hp'
    split at hpi
    · rename_i v s g hv hsi hg'
      cases hpi
      have hi : i < r.vars.length := (List.getElem?_eq_some_iff.mp hsi).1
      obtain ⟨hgs, hge⟩ := pick_spec (hwitL i hiL)
      rw [substOf_lookup hi] at hg'
      cases hg'
      have hgs' : c.sortOf (pick c I (r.vars.getD i 0) (eR.evalEvar (tbl.ev (keyAt vs i)))) = some s := by
        rw [hgs, List.getD_eq_getElem?_getD, hsi, Option.getD_some]
      refine (fixEq_iff hIΓ (sortOf_numbered_of hs0 (sortsNumbered_of_core h) (Semantics.coreOK_ovls h) hgs') hgs'
        b).mpr ⟨hinC, ?_⟩
      have hvk : KoreAML.evarKey v.kore = canonKey c r.vars i := by
        unfold canonKey
        rw [List.getD_eq_getElem?_getD, hv, Option.getD_some]
      rw [hvk]
      exact (hat₁ i hi (hnxL i hiL).2).trans hge.symm
    · cases hpi
  · -- the `requires`, from x's element
    rw [List.mem_singleton.mp hp']
    exact reqPat_transferSplit hIΓ (fun t ht i hi => (hat₁ i (hnxQ t ht i hi).1 (hnxQ t ht i hi).2).symm) hreqR hinC
  · -- `pre`, from x's element: its free variables are not existential
    exact cond_pred_transfer_top h hIΓ hokP tf e₁ _ b (fun k hk => hkfP k hk)
      (fun i hi => ⟨hkf i (hnxP i hi).1, by
        show InS I _ (e₁.evalEvar (tf.ev (keyAt vs i)))
        rw [hat₁ i (hnxP i hi).1 (hnxP i hi).2]; exact hinR i (hnxP i hi).1⟩)
      (inh_top_PP hIΓ x tf e₁) hinC (conj_twoTPP hD hokP (fun k hk => ⟨hkP k hk, hkfP k hk⟩)
      (fun i hi => ⟨hkeys i (hnxP i hi).1, hkf i (hnxP i hi).1, (hat₁ i (hnxP i hi).1 (hnxP i hi).2).symm⟩)
      hpreR) p hp'
  · -- inside `∃ē`, the existential variables at their elements under the binders
    rw [List.mem_singleton.mp hp']
    refine existsAll_intro_at hD _ e₁ e₂ b (binders_nodupEx hkf hlt hexnd) (binders_sortEx hlt) (fun z hz => ?_) rfl
      (fun b' hb' n hn => ?_) ?_
    · by_cases hk : ∃ i < r.vars.length, z = tf.ev (canonKey c r.vars i)
      · obtain ⟨i, hi, rfl⟩ := hk
        have hx : i ∉ r.exs := fun hx => hz _ (List.mem_map_of_mem hx) rfl
        exact (hat₂ i hi).trans (hat₁ i hi hx).symm
      · exact copyVSplit_off fun i hi he => hk ⟨i, hi, he⟩
    · obtain ⟨i, hix, rfl⟩ := List.mem_map.mp hb'
      have hi := hlt i hix
      rw [hsortB i hi] at hn
      rw [← srt_inj hn]
      show InS I _ (e₂.evalEvar (tf.ev (keyAt vs i)))
      rw [hat₂ i hi]
      exact hinR i hi
    · unfold Model.ruleRightBodyPP
      rw [interp_and (by simp)]
      intro q hq
      rcases List.mem_append.mp hq with hq | hq
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl
        · exact (tr_kore_congr r.rhs (fun i hi => (hat₂ i (varOccs_lt r.rhs hrhss i hi)).symm) b).mp hyR
        · exact reqPat_transferSplit hIΓ (fun t ht i hi => (hat₂ i (varOccs_lt t (hensS t ht) i hi)).symm) hensR
            (reqPat_inhSplit hIΓ hensR tf e₂)
      · exact conj_twoTPP hD hokQ (fun k hk => ⟨hkQ k hk, hkfQ k hk⟩)
          (fun i hi => ⟨hkeys i (varOccsCond_lt_twoT r.post hokQ i hi), hkf i (varOccsCond_lt_twoT r.post hokQ i hi),
            (hat₂ i (varOccsCond_lt_twoT r.post hokQ i hi)).symm⟩) hpostR q hq


/-- **The rule a successor comes from**, in a model of `Γc ∪ Γstep`, for rules with predicates:
an element after x's that is in ψ is in the right side `∃ē. (rhs ∧ ens ∧ post)` of a rule of the
definition, at a valuation of the rule's variables other than ē in their sorts where x's element is
in the rule's left side, in `⌈req = true⌉`, in `pre`'s patterns and in no competitor's `applies`;
the table holds the rule's variables, the keys of its `pre`'s and `post`'s patterns, and for each
competitor the variables of its left side and conditions and the keys of its `pre`'s pattern. -/
theorem step_successor_axiomPP
    (hrules : ∀ r ∈ c.rules, c.ruleSorted r = true)
    (x : Config c) (hI : I ⊧ᴵP (Γc c ∪ Γstep c))
    (e : Valuation M) (ψ : KoreAML.P)
    (hs : (KoreAML.sNext ψ).interpret I e (elemOf c I x.val)) :
    ∃ b, ψ.interpret I e b ∧ ∃ r ∈ c.rules, ∃ (tbl : VarTable) (e2 : Valuation M),
      (∀ i < r.vars.length, canonKey c r.vars i ∈ tbl) ∧
      (∀ k ∈ KoreAML.varsOf (Cond.kore c (canonVars c r.vars) (srtOf c topCellSort) r.pre), k ∈ tbl) ∧
      (∀ k ∈ KoreAML.varsOf (Cond.kore c (canonVars c r.vars) (srtOf c topCellSort) r.post), k ∈ tbl) ∧
      (∀ r' ∈ c.rules, r'.prio < r.prio →
        (∀ i < r'.vars.length, i ∈ r'.leftVars → canonKey c r'.vars i ∈ tbl) ∧
        ∀ k ∈ KoreAML.varsOf (Cond.kore c (canonVars c r'.vars) (srtOf c topCellSort) r'.pre), k ∈ tbl) ∧
      (∀ i < r.vars.length, i ∉ r.exs → InS I (c.sortName (r.vars.getD i 0))
        (e2.evalEvar (tbl.ev (keyAt (canonVars c r.vars) i)))) ∧
      (KoreAML.tr ⟨tbl, []⟩ (Term.kore c (canonVars c r.vars) r.lhs)).interpret I e2 (elemOf c I x.val) ∧
      (KoreAML.tr ⟨tbl, []⟩ (reqPat (srtOf c topCellSort)
        (r.req.map (Term.kore c (canonVars c r.vars))))).interpret I e2 (elemOf c I x.val) ∧
      (∀ φ ∈ Cond.conj c (canonVars c r.vars) (srtOf c topCellSort) r.pre,
        (KoreAML.tr ⟨tbl, []⟩ φ).interpret I e2 (elemOf c I x.val)) ∧
      (∀ r' ∈ c.rules, r'.prio < r.prio →
        ¬ (KoreAML.tr ⟨tbl, []⟩ (applies c r' (canonRulePres r'))).interpret I e2 (elemOf c I x.val)) ∧
      (KoreAML.tr ⟨tbl, []⟩ (ruleRight c r)).interpret I e2 b := by
  have hIΓ : I ⊧ᴵP Γ c := fun φ hφ => hI φ (Or.inl (Or.inl hφ))
  have hD := defOK hIΓ
  have hnext := hs
  unfold KoreAML.sNext at hnext
  rw [KoreAML.interp_app] at hnext
  obtain ⟨n0, b, hn0, hb, happ⟩ := hnext
  refine ⟨b, hb, ?_⟩
  -- the closure axiom, at `y := b`
  have hcl := hI _ (Or.inr rfl) e (elemOf c I x.val)
  rw [Model.stepClosure_pat] at hcl
  dsimp only at hcl
  generalize hy : (⟨Model.tablesLen (c.rules.map (prioRuleK c)) 0 + 1⟩ : EVar) = y at hcl
  let e1 : Valuation M := ⟨Function.update e.evalEvar y b, e.evalSvar⟩
  have hψ : (KoreAML.sNext (.evar y) ⊆⊆
      KoreAML.disjList ((c.rules.map (prioRuleK c)).foldl (Model.stepF y) ([], [], 0)).2.1).interpret I e1
        (elemOf c I x.val) := by
    unfold Pattern.universal at hcl
    rw [interpret_neg, interpret_exists] at hcl
    exact Classical.byContradiction fun hc => hcl ⟨b, by rw [interpret_neg]; exact hc⟩
  rw [KoreAML.interp_included hD] at hψ
  have hdisj := hψ (elemOf c I x.val) (by
    unfold KoreAML.sNext
    rw [KoreAML.interp_app]
    exact ⟨n0, b, hn0, by show b = Function.update e.evalEvar y b y; simp, happ⟩)
  obtain ⟨φ, hφ, hφm⟩ := disjList_mem hdisj
  rcases stepF_cases y _ _ φ hφ with hφ | ⟨p, hp, off, hoff, rfl⟩
  · exact absurd hφ List.not_mem_nil
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hp
  have hsr := hrules r hr
  obtain ⟨L, hPL, hLv, hLf, hLP, hLcomp, hLread⟩ := rule_parts_pp (I := I) hsr
  let C := srtOf c topCellSort
  let R : Kore.Pattern := ruleRight c r
  have hfreeP : ∀ k ∈ KoreAML.freeOf [] (.rewrites C L R), ∃ i < r.vars.length, i ∉ r.exs ∧ k = canonKey c r.vars i :=
    fun k hk => Model.freeOf_prio_pp hrules hsr (by rw [hPL]; exact hk)
  rw [hPL] at hφm hoff
  rw [closureDisjunct_rewrites] at hφm
  -- the table of the disjunct
  let tbl : VarTable := List.replicate off (.sortVar "#pad") ++ KoreAML.tableOf [] (.rewrites C L R)
  have hin_tbl : ∀ k ∈ KoreAML.varsOf L, k ∈ tbl := fun k hk =>
    List.mem_append_right _ (List.mem_eraseDups.mpr (List.mem_append_right _ (by
      simp only [KoreAML.varsOf]
      exact List.mem_append_left _ (List.mem_append_right _ hk))))
  have hkeys : ∀ i < r.vars.length, canonKey c r.vars i ∈ tbl := fun i hi => hin_tbl _ (hLv i hi)
  have hy_ne : ∀ k ∈ tbl, y ≠ tbl.ev k := by
    intro k hk he
    have h1 := Model.index_le hk
    have hoff' : off + (KoreAML.tableOf [] (.rewrites C L R)).length ≤ Model.tablesLen (c.rules.map (prioRuleK c)) 0 :=
      hoff
    rw [← he, ← hy] at h1
    have h2 : tbl.length = off + (KoreAML.tableOf [] (.rewrites C L R)).length := by simp [tbl]
    simp only at h1
    omega
  -- the binders of the disjunct are the rule's variables other than the existential ones
  let free := Model.evarsOf (KoreAML.freeOf [] (.rewrites C L R)).eraseDups
  have hfree : ∀ ks ∈ free, ∃ i < r.vars.length, ks.1 = canonKey c r.vars i ∧
      ks.2 = KoreAML.srt (c.sortName (r.vars.getD i 0)) := by
    intro ks hks
    obtain ⟨hk1, n, hn⟩ := Model.mem_filterMap_evar hks
    obtain ⟨i, hi, -, he⟩ := hfreeP _ (List.mem_eraseDups.mp hk1)
    refine ⟨i, hi, he, ?_⟩
    rw [he, canonKey_eq c hi] at hn
    injection hn with _ h2
    exact h2.symm
  obtain ⟨e2, he2, hguard, hbody⟩ := sExists_foldr_elim hD free e1 _
    (fun ks hks ks' hks' heq => by
      obtain ⟨i, hi, h1, h2⟩ := hfree ks hks
      obtain ⟨j, hj, h1', h2'⟩ := hfree ks' hks'
      have hij := canonKey_inj hi hj (by rw [← h1, ← h1']; exact ev_inj (h1 ▸ hkeys i hi) (h1' ▸ hkeys j hj) heq)
      subst hij
      rw [h2, h2'])
    (fun ks hks => by obtain ⟨i, -, -, h2⟩ := hfree ks hks; exact ⟨_, h2⟩) hφm
  have he2y : e2.evalEvar y = b := by
    rw [he2 y (fun ks hks => by
      obtain ⟨i, hi, h1, -⟩ := hfree ks hks
      rw [h1]; exact hy_ne _ (hkeys i hi))]
    show Function.update e.evalEvar y b y = b
    simp
  rw [interpret_conj] at hbody
  obtain ⟨hL, hRm⟩ := hbody
  rw [KoreAML.interp_member hD, he2y] at hRm
  change (KoreAML.tr ⟨tbl, []⟩ (ruleRight c r)).interpret I e2 b at hRm
  obtain ⟨hl, hreq, hprem, hcomp⟩ := hLread tbl e2 _ hL
  -- the valuation gives each of the rule's variables but the existential ones an element of its sort
  have hin : ∀ i < r.vars.length, i ∉ r.exs →
      InS I (c.sortName (r.vars.getD i 0)) (e2.evalEvar (tbl.ev (keyAt (canonVars c r.vars) i))) := by
    intro i hi hx
    have hk : canonKey c r.vars i ∈ KoreAML.freeOf [] (.rewrites C L R) := by
      rw [KoreAML.freeOf]; exact List.mem_append_left _ (hLf i hi hx)
    have hks := Model.evar_mem_filterMap (List.mem_eraseDups.mpr (by rw [canonKey_eq c hi] at hk; exact hk))
    have := hguard _ hks _ rfl
    show InS I _ (e2.evalEvar (tbl.ev (canonKey c r.vars i)))
    rw [canonKey_eq c hi]
    exact this
  have hkQ : ∀ k ∈ KoreAML.varsOf (Cond.kore c (canonVars c r.vars) (srtOf c topCellSort) r.post), k ∈ tbl :=
    fun k hk => List.mem_append_right _ (List.mem_eraseDups.mpr (List.mem_append_right _ (by
      simp only [KoreAML.varsOf]
      exact List.mem_append_right _ (Model.varsOf_post_ruleRight hsr hk))))
  exact ⟨r, hr, tbl, e2, hkeys, fun k hk => hin_tbl _ (hLP k hk), hkQ,
    fun r' hr' hlt => ⟨fun i hi hil => hin_tbl _ ((hLcomp r' hr' hlt).1 i hi hil),
      fun k hk => hin_tbl _ ((hLcomp r' hr' hlt).2 k hk)⟩, hin, hl, hreq, hprem, hcomp, hRm⟩

/-- **A successor is a step's or an open family's**, for rules with predicates:
`step_successor_axiomPP` then `successor_split_pp`, a binder in a predicate of a rule of the
definition giving `readsConfined`. -/
theorem step_successor_pp (h : c.coreOK = true)
    (hrules : ∀ r ∈ c.rules, c.ruleSorted r = true)
    (x : Config c) (hd : StepDecided c x.val) (hI : I ⊧ᴵP (Γc c ∪ Γstep c))
    (hcw : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, cl.needsWitness c = true → cl.CondDecided c)
    (e : Valuation M) (ψ : KoreAML.P)
    (hs : (KoreAML.sNext ψ).interpret I e (elemOf c I x.val)) :
    ∃ b, ψ.interpret I e b ∧
      ((∃ (y : Config c) (r : Rule) (σ : Subst), r.opens = [] ∧ StepBy c r σ x y ∧ b = elemOf c I y.val) ∨
       (∃ r ∈ c.rules, r.opens ≠ [] ∧ ∃ σ, Unblocked c r σ x.val ∧ (famOpen c r σ).interpret I e b)) := by
  obtain ⟨b, hb, r, hr, tbl, e2, hkeys, hkP, hkQ, hkeysC, hin, hl, hreq, hprem, hcomp, hy⟩ :=
    step_successor_axiomPP hrules x hI e ψ hs
  refine ⟨b, hb, ?_⟩
  rcases successor_split_pp h hrules x hd (fun φ hφ => hI φ (Or.inl hφ)) hcw (hrules r hr)
      (readsConfined_of_pre hr) (readsConfined_of_post hr) (hd r hr) hkeys hkP hkQ hkeysC hin hl
      hreq hprem hcomp hy with
    ⟨hop, y', σ, hst, hbe⟩ | ⟨hop, σ, hu, hfam⟩
  · exact Or.inl ⟨y', r, σ, hop, hst hr, hbe⟩
  · exact Or.inr ⟨r, hr, hop, σ, hu, hfam e⟩


end

end Faithful

open ML Faithful

/-- **Completeness at a configuration, for rules with a `pre` and a `post`**: `complete_at`'s
statement from the per-rule facts `ruleSorted` and `rulePlainPP` (`rulePlainPP` is carried, not
read). -/
theorem complete_at_pp (c : Semantics) (h : c.coreOK = true)
    (hrules : ∀ r ∈ c.rules, c.ruleSorted r = true ∧ c.rulePlainPP r = true)
    (x : Config c) (hd : StepDecided c x.val) (os : List Outcome)
    (hval : ∀ (y : Config c) (r : Rule) (σ : Subst), r.opens = [] → StepBy c r σ x y → .val y.val ∈ os)
    (hfam : ∀ r ∈ c.rules, r.opens ≠ [] → ∀ σ, Unblocked c r σ x.val →
      ∃ σ', (∀ i ∈ varOccs r.lhs, σ'.lookup i = σ.lookup i) ∧ .fam r σ' ∈ os)
    (hcw : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, cl.needsWitness c = true → cl.CondDecided c) :
    (Γc c ∪ Γstep c) ⊧ (den c x.val ⇒ KoreAML.allNext (KoreAML.disjList (os.map (Outcome.pat c)))) := by
  intro M _ I hI e m
  have hIΓ : I ⊧ᴵP Γ c := fun φ hφ => hI φ (Or.inl (Or.inl hφ))
  rw [interpret_impl]
  intro hmx
  have hmx' : m = elemOf c I x.val := ((elemOf_spec hIΓ x.property e).1 m).mp hmx
  subst hmx'
  unfold KoreAML.allNext
  rw [interpret_neg]
  intro hnext
  obtain ⟨b, hb, hcase⟩ := step_successor_pp h (fun r hr => (hrules r hr).1) x hd hI hcw e _ hnext
  rw [interpret_neg] at hb
  rcases hcase with ⟨y, r, σ, hop, hs, rfl⟩ | ⟨r, hr, hop, σ, hu, hfo⟩
  · exact hb (disjList_of_mem (List.mem_map_of_mem (hval y r σ hop hs))
      (((elemOf_spec hIΓ y.property e).1 _).mpr rfl))
  · obtain ⟨σ', hag, hmem⟩ := hfam r hr hop σ hu
    refine hb (disjList_of_mem (List.mem_map_of_mem hmem) ?_)
    show (famOpen c r σ').interpret I e b
    rw [famOpen_congrOpen c r hag]
    exact hfo

end KCore
