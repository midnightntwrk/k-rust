/-
  KCore. Completeness at a configuration, for a definition whose rules may have existential
  variables, in any model of `Γc` with the step's closure: the lemmas that read no clause.

  The step's closure gives a successor b of x a disjunct, the axiom of a rule r of the definition
  at a valuation of r's variables other than the existential ones, each in its sort
  (`step_successor_axiomEx`, from `rule_partsEx`): x's element is in the left side, in
  `⌈req = true⌉` and in no competitor's `applies`; b is in r's right side `∃ē. (rhs ∧ ens)`. A
  competitor that does not apply is read with its existential variables as ordinary ones
  (`ruleDropExs`, `notApplies_ofDropExs`: its `applies` and its `NotApplies` are the same).
  `famOpenPatEx`, `famOpen_eqEx` and `famOpen_keysEx` are the pattern `famOpen` reads and its
  table; `copyVEx_at` and `copyVEx_off` move a valuation to another table;
  `stepDecided_of_rules_ex` is `StepDecided` from the rules' facts.
-/
import KcoreSpec.ExSound
import KcoreSpec.OpenComplete

set_option autoImplicit false

namespace KCore

namespace Faithful

open ML
open KoreAML (VarTable)

/-! ## A rule with its existential variables read as ordinary ones does not apply where it does not -/

section
variable {c : Semantics}

/-- `NotApplies` reads the left side and the conditions only: read with its existential variables
as ordinary ones, a rule does not apply exactly where it does not. -/
theorem notApplies_ofDropExs {r : Rule} {x : GroundTerm} (hna : NotApplies c (ruleDropExs r) x) :
    NotApplies c r x := fun σ hσ hm => by
  cases hna σ hσ hm with
  | intro ht he hv => exact .intro ht he hv
  | pre hb => exact .pre hb

end

/-! ## The pattern `famOpen` reads, for a rule with `rulePlainEx` -/

section
variable {c : Semantics}

/-- `famOpen`'s pattern for a rule with `\top` predicates: the variables other than the existential
ones bound, those of the left side fixed to their values under σ, the `requires`, and the right side
`∃ē. (rhs ∧ ens)`. -/
def famOpenPatEx (c : Semantics) (r : Rule) (σ : Subst) : Kore.Pattern :=
  KoreAML.existsAll (srtOf c topCellSort)
    (((List.range r.vars.length).filter fun i => !r.exs.contains i).map
      fun i => ((canonVars c r.vars).getD i default).kore)
    (.and (srtOf c topCellSort) (fixK c r σ (varOccs r.lhs) ++
      [reqPat (srtOf c topCellSort) (r.req.map (Term.kore c (canonVars c r.vars)))] ++
      [KoreAML.existsAll (srtOf c topCellSort) (Model.ruleExBinders c r) (Model.ruleRightBody c r)]))

/-- The pattern `famOpen` reads, for a rule whose predicates are `\top` (not asked to be one of the
definition's). -/
theorem famOpen_eqEx {r : Rule} (hpre : r.pre = .top) (hpost : r.post = .top)
    (hlt : ∀ i ∈ r.exs, i < r.vars.length) (σ : Subst) :
    famOpen c r σ = KoreAML.denB (famOpenPatEx c r σ) := by
  unfold famOpen famOpenPatEx
  dsimp only
  rw [Model.ruleRight_eqEx hpost hlt, filterMap_getElem?_of_lt _ _ (fun i hi => by
    rw [canonVars_length]; exact List.mem_range.mp (List.mem_filter.mp hi).1), List.map_map]
  simp only [hpre, Cond.conj, Cond.isTop, ite_true, List.append_nil]
  rfl

/-- Every variable of a rule has its key in the table of `famOpen`'s pattern. -/
theorem famOpen_keysEx {r : Rule} {σ : Subst} :
    ∀ i < r.vars.length, canonKey c r.vars i ∈ KoreAML.tableOf [] (famOpenPatEx c r σ) := by
  intro i hi
  unfold KoreAML.tableOf famOpenPatEx
  refine List.mem_eraseDups.mpr (List.mem_append_right _ ?_)
  by_cases hx : i ∈ r.exs
  · refine Model.varsOf_existsAll_bodyEx ?_ _
    refine Model.varsOf_and_mem (List.mem_append_right _ (List.mem_singleton_self _)) ?_
    exact varsOf_existsAll_binder _ (List.mem_map_of_mem (f := fun i => ((canonVars c r.vars).getD i default).kore) hx)
  · exact varsOf_existsAll_binder _ (List.mem_map_of_mem (f := fun i => ((canonVars c r.vars).getD i default).kore)
      (List.mem_filter.mpr ⟨List.mem_range.mpr hi, by simpa using hx⟩))

end

/-! ## A valuation moved to another table at listed variables -/

section
variable {c : Semantics} {M : Type} {I : Interpretation KoreAML.Sym M}

open Classical in
/-- The valuation that gives the canonical variables of `vars` listed in `is`, through `tbl'`, the
elements `src` gives them through `tbl`, and agrees with `base` elsewhere. -/
noncomputable def copyVEx (c : Semantics) (tbl tbl' : VarTable) (vars : List Srt) (is : List Nat)
    (src base : Valuation M) : Valuation M :=
  ⟨fun x => if h : ∃ i < vars.length, i ∈ is ∧ x = tbl'.ev (canonKey c vars i)
    then src.evalEvar (tbl.ev (canonKey c vars (Classical.choose h))) else base.evalEvar x, base.evalSvar⟩

theorem copyVEx_at {tbl tbl' : VarTable} {vars : List Srt} {is : List Nat} {src base : Valuation M}
    (hkeys : ∀ i < vars.length, canonKey c vars i ∈ tbl') {i : Nat} (hi : i < vars.length) (his : i ∈ is) :
    (copyVEx c tbl tbl' vars is src base).evalEvar (tbl'.ev (canonKey c vars i)) =
      src.evalEvar (tbl.ev (canonKey c vars i)) := by
  have hex : ∃ j < vars.length, j ∈ is ∧ tbl'.ev (canonKey c vars i) = tbl'.ev (canonKey c vars j) :=
    ⟨i, hi, his, rfl⟩
  show (if h : _ then _ else _) = _
  rw [dif_pos hex]
  obtain ⟨hj, -, hje⟩ := Classical.choose_spec hex
  rw [(canonKey_inj hi hj (ev_inj (hkeys i hi) (hkeys _ hj) hje)).symm]

theorem copyVEx_off {tbl tbl' : VarTable} {vars : List Srt} {is : List Nat} {src base : Valuation M} {x : EVar}
    (hx : ∀ i < vars.length, i ∈ is → x ≠ tbl'.ev (canonKey c vars i)) :
    (copyVEx c tbl tbl' vars is src base).evalEvar x = base.evalEvar x := by
  show (if h : _ then _ else _) = _
  rw [dif_neg (fun ⟨i, hi, his, he⟩ => hx i hi his he)]

end

/-! ## The axiom of a rule with `rulePlainEx`, in any model -/

section
variable {c : Semantics}

/-- **A rule's axiom `\rewrites(L, ∃ē. (rhs ∧ ens))`, its left part `L` read**, for a rule with
`ruleSorted` and `rulePlainEx` (not asked to be one of the definition's) in a definition whose rules
have both: every variable of the rule is a variable of `L`, those other than ē occur free in it, the
canonical variables of the left sides and conditions of its competitors are among `L`'s, and an
element of `L` is in the left side and in `⌈req = true⌉`, and in no competitor's `applies`. -/
theorem rule_partsEx {M : Type} {I : Interpretation KoreAML.Sym M}
    (hrules : ∀ r ∈ c.rules, c.ruleSorted r = true ∧ c.rulePlainEx r = true) {r : Rule}
    (hs : c.ruleSorted r = true) (hp : c.rulePlainEx r = true) :
    ∃ L, prioRuleK c r = .rewrites (srtOf c topCellSort) L (ruleRight c r) ∧
      (∀ i < r.vars.length, canonKey c r.vars i ∈ KoreAML.varsOf L) ∧
      (∀ i < r.vars.length, i ∉ r.exs → canonKey c r.vars i ∈ KoreAML.freeOf [] L) ∧
      (∀ r' ∈ c.rules, r'.prio < r.prio → ∀ i < r'.vars.length, i ∈ r'.leftVars →
        canonKey c r'.vars i ∈ KoreAML.varsOf L) ∧
      ∀ (tbl : VarTable) (e : Valuation M) (a : M), (KoreAML.tr ⟨tbl, []⟩ L).interpret I e a →
        (KoreAML.tr ⟨tbl, []⟩ (Term.kore c (canonVars c r.vars) r.lhs)).interpret I e a ∧
        (KoreAML.tr ⟨tbl, []⟩ (reqPat (srtOf c topCellSort) (r.req.map (Term.kore c (canonVars c r.vars))))).interpret
          I e a ∧
        ∀ r' ∈ c.rules, r'.prio < r.prio →
          ¬ (KoreAML.tr ⟨tbl, []⟩ (applies c r' (canonRulePres r'))).interpret I e a := by
  obtain ⟨-, hocc, -, -, -, -, -⟩ := Model.ruleSorted_partsEx hs hp
  obtain ⟨hpre₀, -⟩ := Semantics.rulePlainEx_top hp
  obtain ⟨hRf, hRv⟩ := Model.ruleRight_keysEx hs hp
  let C := srtOf c topCellSort
  let vs := canonVars c r.vars
  let n := r.vars.length
  let comps := (c.rules.filter (·.prio < r.prio)).map fun r' => applies c r' (canonRulePres r')
  have hcomp : ∀ r' ∈ c.rules, r'.prio < r.prio → applies c r' (canonRulePres r') ∈ comps := fun r' hr' hlt =>
    List.mem_map.mpr ⟨r', List.mem_filter.mpr ⟨hr', by simpa using hlt⟩, rfl⟩
  -- the keys of the parts
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
  have hkeys : ∀ {ps : List Kore.Pattern},
      Term.kore c vs r.lhs ∈ ps → reqPat C (r.req.map (Term.kore c vs)) ∈ ps → .ceil C C (ruleRight c r) ∈ ps →
      (∀ i < n, canonKey c r.vars i ∈ KoreAML.varsOf (.and C ps)) ∧
      (∀ i < n, i ∉ r.exs → canonKey c r.vars i ∈ KoreAML.freeOf [] (.and C ps)) := by
    intro ps h1 h2 h3
    have hpart : ∀ i < n, (i ∉ r.exs → canonKey c r.vars i ∈ KoreAML.freeOf [] (.and C ps)) ∧
        canonKey c r.vars i ∈ KoreAML.varsOf (.and C ps) := by
      intro i hi
      by_cases hx : i ∈ r.exs
      · exact ⟨fun h' => absurd hx h', Model.varsOf_and_mem h3 (hceilK.2 (hRv i hi (Or.inl hx)))⟩
      rcases hocc i hi with hL | ⟨t, ht, hit⟩ | hR | ⟨t, ht, hit⟩
      · exact ⟨fun _ => Model.freeOf_and_memOpen h1 (Model.kore_freeOf c vs r.lhs hL),
          Model.varsOf_and_mem h1 (varsOf_kore c vs r.lhs hL)⟩
      · rw [ht] at h2
        obtain ⟨hf, hv⟩ := hreqK (Model.kore_freeOf c vs t hit) (varsOf_kore c vs t hit)
        exact ⟨fun _ => Model.freeOf_and_memOpen h2 hf, Model.varsOf_and_mem h2 hv⟩
      · exact ⟨fun _ => Model.freeOf_and_memOpen h3 (hceilK.1 (hRf i hi hx (Or.inl hR))),
          Model.varsOf_and_mem h3 (hceilK.2 (hRv i hi (Or.inr (Or.inl hR))))⟩
      · exact ⟨fun _ => Model.freeOf_and_memOpen h3 (hceilK.1 (hRf i hi hx (Or.inr ⟨t, ht, hit⟩))),
          Model.varsOf_and_mem h3 (hceilK.2 (hRv i hi (Or.inr (Or.inr ⟨t, ht, hit⟩))))⟩
    exact ⟨fun i hi => (hpart i hi).2, fun i hi hx => (hpart i hi).1 hx⟩
  by_cases hce : comps.isEmpty
  · have hnone : ∀ r' ∈ c.rules, ¬ r'.prio < r.prio := fun r' hr' hlt => by
      have := hcomp r' hr' hlt
      rw [List.isEmpty_iff.mp hce] at this
      exact absurd this List.not_mem_nil
    obtain ⟨hk1, hk2⟩ := hkeys (ps := [Term.kore c vs r.lhs, reqPat C (r.req.map (Term.kore c vs)),
      .ceil C C (ruleRight c r)]) (List.mem_cons_self ..) (List.mem_cons_of_mem _ (List.mem_cons_self ..))
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
    refine ⟨_, by rw [Model.prioRuleK_preTop hpre₀]; dsimp only; rw [if_pos hce], hk1, hk2,
      fun r' hr' hlt => absurd hlt (hnone r' hr'), fun tbl e a h => ?_⟩
    rw [tr_and3, KoreAML.interp_sAnd, KoreAML.interp_sAnd] at h
    exact ⟨h.1, h.2.1, fun r' hr' hlt => absurd hlt (hnone r' hr')⟩
  · obtain ⟨hk1, hk2⟩ := hkeys (ps := [Term.kore c vs r.lhs, reqPat C (r.req.map (Term.kore c vs)),
      .not C (anyOfC C comps), .ceil C C (ruleRight c r)]) (List.mem_cons_self ..)
      (List.mem_cons_of_mem _ (List.mem_cons_self ..))
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))
    refine ⟨_, by rw [Model.prioRuleK_preTop hpre₀]; dsimp only; rw [if_neg hce], hk1, hk2,
      fun r' hr' hlt i hi hil => ?_, fun tbl e a h => ?_⟩
    · refine Model.varsOf_and_mem (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))) ?_
      simp only [KoreAML.varsOf]
      exact List.mem_append_right _ (mem_varsOf_anyOfC (hcomp r' hr' hlt)
        (Model.varsOf_appliesOpen (Semantics.rulePlainEx_top (hrules r' hr').2).1 hi hil))
    · rw [tr_and4, KoreAML.interp_sAnd, KoreAML.interp_sAnd, KoreAML.interp_sAnd] at h
      obtain ⟨h1, h2, h3, -⟩ := h
      rw [KoreAML.tr, KoreAML.interp_sNot] at h3
      exact ⟨h1, h2, fun r' hr' hlt happ => h3.1 (anyOfC_of_mem h3.2 (hcomp r' hr' hlt) happ)⟩

end

/-! ## The successor a disjunct of the step's closure gives -/

section
variable {c : Semantics} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}

open Classical in
/-- **A successor of a configuration, at the axiom of a rule that may have existential variables**:
with the step's closure, in every model of `Γc c`, for a definition whose rules have `ruleSorted` and
`rulePlainEx`, a successor b of x's element that lies in a pattern ψ is given by the axiom of a rule r
of the definition at a valuation of r's variables other than the existential ones in their sorts,
under a table holding r's variables and the variables of the left sides of r's competitors: x's
element is in r's left side, in `⌈req = true⌉` and in no competitor's `applies`, and b is in r's
right side `∃ē. (rhs ∧ ens)`. -/
theorem step_successor_axiomEx
    (hrules : ∀ r ∈ c.rules, c.ruleSorted r = true ∧ c.rulePlainEx r = true)
    (x : Config c) (hI : I ⊧ᴵP (Γc c ∪ Γstep c))
    (e : Valuation M) (ψ : KoreAML.P)
    (hs : (KoreAML.sNext ψ).interpret I e (elemOf c I x.val)) :
    ∃ b, ψ.interpret I e b ∧ ∃ r ∈ c.rules, ∃ (tbl : VarTable) (e2 : Valuation M),
      (∀ i < r.vars.length, canonKey c r.vars i ∈ tbl) ∧
      (∀ r' ∈ c.rules, r'.prio < r.prio → ∀ i < r'.vars.length, i ∈ r'.leftVars →
        canonKey c r'.vars i ∈ tbl) ∧
      (∀ i < r.vars.length, i ∉ r.exs → InS I (c.sortName (r.vars.getD i 0))
        (e2.evalEvar (tbl.ev (keyAt (canonVars c r.vars) i)))) ∧
      (KoreAML.tr ⟨tbl, []⟩ (Term.kore c (canonVars c r.vars) r.lhs)).interpret I e2 (elemOf c I x.val) ∧
      (KoreAML.tr ⟨tbl, []⟩ (reqPat (srtOf c topCellSort)
        (r.req.map (Term.kore c (canonVars c r.vars))))).interpret I e2 (elemOf c I x.val) ∧
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
  obtain ⟨hsr, hpr⟩ := hrules r hr
  obtain ⟨L, hPL, hLv, hLf, hLcomp, hLread⟩ := rule_partsEx (I := I) hrules hsr hpr
  let C := srtOf c topCellSort
  let R : Kore.Pattern := ruleRight c r
  have hfreeP : ∀ k ∈ KoreAML.freeOf [] (.rewrites C L R), ∃ i < r.vars.length, i ∉ r.exs ∧ k = canonKey c r.vars i :=
    fun k hk => Model.freeOf_prio_T hrules hsr hpr (by rw [hPL]; exact hk)
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
  obtain ⟨hl, hreq, hcomp⟩ := hLread tbl e2 _ hL
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
  exact ⟨r, hr, tbl, e2, hkeys, fun r' hr' hlt i hi hil => hin_tbl _ (hLcomp r' hr' hlt i hi hil), hin, hl, hreq,
    hcomp, hRm⟩

end

end Faithful

open ML Faithful

/-- Every configuration is `StepDecided` where every function has a result at arguments of its
sorts and every rule is well sorted with `rulePlainEx`. -/
theorem stepDecided_of_rules_ex {c : Semantics} (h : HypSoundCore c) (hft : FnTerminates c)
    (hr : ∀ r ∈ c.rules, c.ruleSorted r = true ∧ c.rulePlainEx r = true) (x : GroundTerm) :
    StepDecided c x :=
  stepDecided_pp h hft (fun r hmem => (hr r hmem).1) x

end KCore
