/-
  KCore. Completeness at a configuration for rules with a `pre` and a `post`: the lemmas that read
  no clause.

  In a model of `Γc ∪ Γstep`, an element after x's is in the right side of a rule of the definition,
  at a valuation where x's element is in the rule's left side, `⌈req = true⌉`, `pre`'s patterns and
  no competitor's `applies` (`step_successor_axiomPP`, from the closure axiom and `rule_parts_pp`).
  The two cases of that successor (`successor_split_ppCEx`) are CompleteCEx.lean's.

  `famOpenPatPP`, `famOpen_eqPP`, `famOpen_keysPP` (the pattern `famOpen` reads and its table),
  `conj_twoTPP` (the conjuncts of a predicate under two tables) and `readsConfined_of_pre` are
  public, for the values of an open family.
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

end

end Faithful

open ML Faithful

end KCore
