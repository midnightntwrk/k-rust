/-
  KCore. The instances of a step by a rule without existential variables are its successor, for a
  rule whose `post` need not be `\top`.

  `famEx c r σ` with `r.exs = []` is `∃v̄. (v̄ = ⟦σ⟧ ∧ rhs ∧ ⌈ens = true⌉ ∧ post)`, every variable
  fixed (`famEx_eqPP`). In a model of `Γc`, an element in it is in `rhs` at σ's values, so it is
  y's element (the soundness of `EvalTerm`). Conversely y's element is in `rhs` and `⌈ens = true⌉`
  at the valuation that gives each variable the element of its value, and in `post` there: `post`
  is `condOK` and `Cond.bound` (`ruleSorted`), `Holds … post true` at σ, and in a model of `Γc` a
  condition holds at an element exactly where its truth value is `true` (`holds_entails`), its
  free variables read at σ's values (`overV_agrees`) (`famEx_denPP`). `pre` is not read: `famEx`
  does not hold it.

  `famEx_closed_post` is `famEx_closed`'s statement, proved from `ruleSorted` alone of what `coreOK`
  says of the rule: not from `rulePlainEx` and so not from `\top` predicates. A condition with a
  binder is not `\top`, so a rule of `c` with one makes `c.readsConfined` true, which the binder
  cases of `holds_entails` ask.
-/
import KcoreSpec.OpenSound
import KcoreSpec.SatRulePP
import KcoreSpec.ClausePreCore
import KcoreSpec.CondTwoTables

set_option autoImplicit false

namespace KCore

namespace Faithful

open ML
open KoreAML (VarTable)
open HoldsShape (hasBinder reads_of_agrees)

section
variable {c : Semantics}

/-- The pattern `famEx` reads, for a rule without existential variables, whatever its `post`:
every variable is fixed to its value under σ. -/
theorem famEx_eqPP {r : Rule} (hex : r.exs = []) (σ : Subst) :
    famEx c r σ = KoreAML.denB (KoreAML.existsAll (srtOf c topCellSort)
      ((canonVars c r.vars).map KoreAML.Var.kore)
      (.and (srtOf c topCellSort) (fixK c r σ (List.range r.vars.length) ++
        [.and (srtOf c topCellSort) ([Term.kore c (canonVars c r.vars) r.rhs,
          reqPat (srtOf c topCellSort) (r.ens.map (Term.kore c (canonVars c r.vars)))] ++
          Cond.conj c (canonVars c r.vars) (srtOf c topCellSort) r.post)]))) := by
  have hv := filterMap_range_getElem? (canonVars c r.vars)
  rw [canonVars_length] at hv
  have hf : (List.range r.vars.length).filter (fun _ => true) = List.range r.vars.length :=
    List.filter_eq_self.mpr (fun _ _ => rfl)
  simp only [famEx, ruleRight, hex, List.contains_nil, Bool.not_false, List.filterMap_nil, List.foldr_nil]
  rw [hf, hv]

/-- A condition with a binder is not `\top`. -/
theorem not_isTop_of_hasBinder {p : Cond} (h : hasBinder p = true) : p.isTop = false := by
  cases p with
  | top => exact absurd h (by simp [hasBinder])
  | _ => rfl

/-- A rule of `c` whose `post` has a binder makes `c.readsConfined` true. -/
theorem readsConfined_of_post {r : Rule} (hr : r ∈ c.rules) (hb : hasBinder r.post = true) :
    c.readsConfined = true := by
  simp only [Semantics.readsConfined, Bool.or_eq_true, List.any_eq_true]
  exact Or.inl ⟨r, hr, by simp [hb]⟩

variable {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}

/-- **The instances of a step are its successor**, in every model of `Γc`, for a rule with
`ruleSorted` and no existential variable (not asked to be one of the definition's; its `post` need
not be `\top`), at a σ that gives every variable a value, under which the right side evaluates to
y, the `ensures` to `true` and `post` holds; a `post` with a binder asks `readsConfined`. -/
theorem famEx_denPP (h : c.coreOK = true) {r : Rule} (hs : c.ruleSorted r = true) (hex : r.exs = [])
    (hrc : hasBinder r.post = true → c.readsConfined = true)
    {σ : Subst} (hσ : c.WellSorted r.vars σ) {y : Config c}
    (heval : EvalTerm c σ r.rhs (some y.val)) (hens : ∀ t, r.ens = some t → EvalTerm c σ t (some (bool true)))
    (hpost : Holds c r.vars.length σ r.post true)
    (hIc : I ⊧ᴵP Γc c)
    (hcw : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, cl.needsWitness c = true → cl.CondDecided c) (e : Valuation M) (m : M) :
    (famEx c r σ).interpret I e m ↔ (den c y.val).interpret I e m := by
  have hI : I ⊧ᴵP Γ c := fun φ hφ => hIc φ (Or.inl hφ)
  have hs0 := hypSound_of_core h
  obtain ⟨hok, hsr, hnn, hg, hph, hcso, hcs, hph', hno⟩ := id hs0
  haveI : OvlOK c := hno
  have hsc := sortCtx_of_all hok hsr (OvlOK.ovlCase hno)
  have hD := defOK hI
  have hneg := (neg_of_coreCl hIc (Semantics.sortedOKCl_of_sortedOK hok) hsr (Semantics.coreOK_parts h).2.1 hph hcw (HoldsShape.preReadAll_of_core h hIc))
  obtain ⟨-, -, -, hensS, hrhss, -, -, -, hokQ, -, hbdQ⟩ := Model.ruleSorted_partsPP hs
  have hsorts := sortsNumbered_of_core h
  have hov := Semantics.coreOK_ovls h
  rw [famEx_eqPP hex]
  unfold KoreAML.denB
  generalize htbl : KoreAML.tableOf [] _ = tbl
  have hkeys : ∀ i < r.vars.length, canonKey c r.vars i ∈ tbl := fun i hi => by
    rw [← htbl]; exact canonKey_mem_existsAll hi
  have hkQ : ∀ k ∈ KoreAML.varsOf (Cond.kore c (canonVars c r.vars) (srtOf c topCellSort) r.post), k ∈ tbl :=
    fun k hk => by
      rw [← htbl]
      unfold KoreAML.tableOf
      refine List.mem_eraseDups.mpr (List.mem_append_right _ (Model.varsOf_existsAll_bodyEx ?_ _))
      exact Model.varsOf_and_mem (List.mem_append_right _ (List.mem_singleton_self _))
        (Model.varsOf_condConj (fun φ hφ => List.mem_append_right _ hφ) hk)
  obtain ⟨hnd, hsrt⟩ := canon_binders hkeys
  have hne : ∀ (l : List Kore.Pattern) (p : Kore.Pattern), l ++ [p] ≠ [] := fun l p => by simp
  have hne2 : ∀ (l : List Kore.Pattern) (p q : Kore.Pattern), [p, q] ++ l ≠ [] := fun l p q => by simp
  constructor
  · intro hm
    obtain ⟨e', -, -, hb⟩ := existsAll_elim hD _ e m hnd hsrt hm
    rw [interp_and (hne _ _)] at hb
    have hag := agrees_of_fixK hI hs0 hsorts hov hσ (is := List.range r.vars.length)
      (fun i hi => List.mem_range.mpr hi) (fun p hp => hb p (List.mem_append_left _ hp))
    have hRm := hb _ (List.mem_append_right _ (List.mem_singleton_self _))
    rw [interp_and (hne2 _ _ _)] at hRm
    have := (evalTerm_den4ClPre hI hnn hsc hph (clauseOpenFactsP_of_sortedOKCl (Semantics.sortedOKCl_of_sortedOK hok)) hneg (HoldsShape.preReadAll_of_core h hIc) heval fns_headsOK hσ (canonVars_length c r.vars) hag
      hrhss m).mp (hRm _ (by simp))
    exact ((den_closed c y.val).interp e' e m).mp this
  · intro hm
    have hmy : m = elemOf c I y.val := ((elemOf_spec hI y.property e).1 m).mp hm
    have hag := overV_agrees hI hkeys hσ (e := e)
    refine existsAll_intro_at hD _ e (overV c I tbl r.vars σ e) m hnd hsrt (fun z hz => ?_) rfl
      (fun b hb n hn => ?_) ?_
    · refine overV_off fun i hi he => hz _ ?_ he
      have hlt : i < (canonVars c r.vars).length := by rw [canonVars_length]; exact hi
      show ((canonVars c r.vars).getD i default).kore ∈ (canonVars c r.vars).map KoreAML.Var.kore
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]
      exact List.mem_map_of_mem (List.getElem_mem hlt)
    · obtain ⟨i, hi, rfl⟩ := canonVars_kore_mem hb
      have hs' : ((canonVars c r.vars).getD i default).kore.sort = KoreAML.srt (c.sortName (r.vars.getD i 0)) := by
        rw [canonVars_getD c hi]; rfl
      rw [hs'] at hn
      rw [← srt_inj hn]
      show InS I _ ((overV c I tbl r.vars σ e).evalEvar (tbl.ev (canonKey c r.vars i)))
      rw [overV_at hkeys hi]
      obtain ⟨w, hw, hsw⟩ := hσ i (r.vars.getD i 0)
        (by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; rfl)
      rw [hw]
      exact (inS_iff e).mp (elemOf_spec hI hsw e).2
    · have hinC : (KoreAML.inhOf (KoreAML.trSort tbl (srtOf c topCellSort))).interpret I
          (overV c I tbl r.vars σ e) m := by
        rw [hmy]
        have := (elemOf_spec hI y.property (overV c I tbl r.vars σ e)).2
        unfold srtOf; rw [trSort_srt]; exact this
      rw [interp_and (hne _ _)]
      intro p hp
      rcases List.mem_append.mp hp with hp | hp
      · unfold fixK at hp
        obtain ⟨i, -, hpi⟩ := List.mem_filterMap.mp hp
        split at hpi
        · rename_i v s g hv hsi hg'
          cases hpi
          have hi : i < r.vars.length := (List.getElem?_eq_some_iff.mp hsi).1
          obtain ⟨w, hw, hsw⟩ := hσ i s hsi
          rw [hg'] at hw; cases hw
          refine (fixEq_iff hI (sortOf_numbered_of hs0 hsorts hov hsw) hsw m).mpr ⟨hinC, ?_⟩
          have hvk : KoreAML.evarKey v.kore = canonKey c r.vars i := by
            unfold canonKey
            rw [List.getD_eq_getElem?_getD, hv, Option.getD_some]
          rw [hvk, overV_at hkeys hi, hg', Option.getD_some]
        · cases hpi
      · rw [List.mem_singleton.mp hp, interp_and (hne2 _ _ _)]
        intro q hq
        simp only [List.cons_append, List.nil_append, List.mem_cons] at hq
        rcases hq with rfl | rfl | hq
        · exact (evalTerm_den4ClPre hI hnn hsc hph (clauseOpenFactsP_of_sortedOKCl (Semantics.sortedOKCl_of_sortedOK hok)) hneg (HoldsShape.preReadAll_of_core h hIc) heval fns_headsOK hσ (canonVars_length c r.vars) hag
            hrhss m).mpr (((den_closed c y.val).interp e _ m).mp hm)
        · exact reqPat_holds hI (fun t ht b =>
            evalTerm_den4ClPre hI hnn hsc hph (clauseOpenFactsP_of_sortedOKCl (Semantics.sortedOKCl_of_sortedOK hok)) hneg (HoldsShape.preReadAll_of_core h hIc) (hens t ht) fns_headsOK hσ (canonVars_length c r.vars) hag
              (hensS t ht) b) hinC
        · have hT : r.post.isTop = false := by
            cases hT : r.post.isTop
            · rfl
            · simp [Cond.conj, hT] at hq
          have hq' : q = Cond.kore c (canonVars c r.vars) (srtOf c topCellSort) r.post := by
            simpa [Cond.conj, hT] using hq
          subst hq'
          have hr := reads_of_agrees hσ hag (P := fun i => i ∈ varOccsCond r.vars.length r.post)
            fun i hi => ⟨varOccsCond_lt_twoT r.post hokQ i hi, hkeys i (varOccsCond_lt_twoT r.post hokQ i hi)⟩
          exact (HoldsShape.holds_entails h hIc hcw r.post hrc hokQ hbdQ (fun i hi _ => hi) hr hkQ top_numbered
            hpost m hinC).mpr rfl

end

end Faithful

open Faithful

/-- **A step by a rule without existential variables has one instance**, whatever the rule's
`post` (`famEx_closed`'s statement): of what `coreOK` says of the rule, only `ruleSorted` is read
(`famEx_denPP`), and `readsConfined` where `post` has a binder comes from the rule being one of
`c`'s. -/
theorem famEx_closed_post (c : Semantics) (h : c.coreOK = true) {x y : Config c} {r : Rule} {σ : Subst}
    (hs : StepBy c r σ x y) (hex : r.exs = [])
    (hc : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, cl.needsWitness c = true → cl.CondDecided c) :
    Γc c ⊧ (famEx c r σ ≡ den c y.val) := by
  intro M _ I hI e m
  rw [KoreAML.interp_equal (defOK fun φ hφ => hI φ (Or.inl hφ))]
  exact fun a => famEx_denPP h (Semantics.ruleFactsHO1_of_core h r hs.mem).1 hex
    (readsConfined_of_post hs.mem) hs.hσ hs.heval hs.hens hs.hpost hI hc e a

end KCore
