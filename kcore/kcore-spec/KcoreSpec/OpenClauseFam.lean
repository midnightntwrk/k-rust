/-
  KCore. The instances of a step are its successor (`famEx_den_exNil`), and a step by a rule without
  existential variables has one instance (`famEx_closed`), for a semantics whose clauses are asked
  CN-4's bodies (`Semantics.sortedOKCl`), with no hypothesis on the sorts of the variables the
  patterns and conditions do not hold.

  Of the clauses, the proof reads what the evaluation lemmas read (`eval_den4_coreCl`'s hypotheses:
  `evalTerm_den4Cl` with each negated clause's exclusion empty, `neg_of_coreCl`); of the rule, its
  sorts and shape (`rule_ctxCl`, `rule_ctx_ensCl`, and its `post` is `\top`). The sorts of the
  values are numbered from `genWf` and `OvlOK` (`sortOf_numbered_ofCl`), and the valuation that
  satisfies the equations `fixK` writes agrees with σ (`agrees_of_fixKCl`).
-/
import KcoreSpec.FaithfulFamilies
import KcoreSpec.OpenClauseFn

set_option autoImplicit false

namespace KCore

namespace Faithful

open ML
open KoreAML (DefOK Inh IsSort Closed VarKey VarTable)

section
variable {c : Semantics}

/-- `sortOf_numbered_of` from what it reads: the values generated (`genWf`) and `OvlOK`. -/
theorem sortOf_numbered_ofCl (hg : genWf c = true) [OvlOK c] (hsorts : Model.sortsNumbered c = true) (hov : c.overloadsOK = true)
    {v : GroundTerm} {s : Srt} (hv : c.sortOf v = some s) : s < nRegSorts + c.sortNames.length := by
  have hn := hsorts
  simp only [Model.sortsNumbered, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hn
  have hsym : ∀ {k : CtorSig}, k ∈ kernelSyms c → ∀ s ∈ k.result :: k.args, s < nRegSorts + c.sortNames.length :=
    fun hk => hn.1.1.1 _ hk
  have hcoll : ∀ {k : CollSig}, k ∈ c.allColls → k.sort < nRegSorts + c.sortNames.length :=
    fun hk => (hn.2 _ hk).1.1
  cases v with
  | ctor f ts =>
    rcases sortOf_ctor_cases hg hv with ⟨k, hk, -, rfl⟩ | ⟨o, hlo, -, -, -, rfl, -⟩ | ⟨kp, hko, -, -, -, -, rfl, -⟩
    rotate_right
    · exact hsym (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (List.mem_map_of_mem (f := (·.sig)) (c.lookupOpen_spec hko).1)))) _ (List.mem_cons_self ..)
    · exact hsym (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
        (List.mem_append_left _ (lookupSig_spec hk).1)))) _ (List.mem_cons_self ..)
    · exact hsym (List.mem_append_right _ (List.mem_map_of_mem (OvlLaws.ovl_parts hov hlo).1)) _
        (List.mem_cons_self ..)
  | inj a b t =>
    obtain ⟨hab, -, -, rfl⟩ := sortOf_inj.mp hv
    exact (hn.1.1.2 _ hab).2
  | dv s0 lit =>
    obtain ⟨hd, rfl⟩ := sortOf_dv.mp hv
    by_cases hcar : c.lib.carriers.all (·.1 != s) = false
    · have : ∃ p ∈ c.lib.carriers, p.1 = s := by
        refine Classical.byContradiction fun hne => ?_
        have : c.lib.carriers.all (·.1 != s) = true := List.all_eq_true.mpr fun p hp => by
          have : p.1 ≠ s := fun he => hne ⟨p, hp, he⟩
          simpa using this
        rw [this] at hcar; cases hcar
      obtain ⟨p, hp, rfl⟩ := this
      exact hn.1.2 _ (List.mem_append_right _ (List.mem_map.mpr ⟨p, hp, rfl⟩))
    have hcs := Lib.carrier_of_not _ (by rw [Bool.not_eq_false] at hcar; exact hcar)
    cases lit with
    | int _ => simp only [dvOK, hcs] at hd; rw [beq_iff_eq.mp hd]; exact Nat.lt_of_lt_of_le (by decide) (Nat.le_add_right _ _)
    | bool _ => simp only [dvOK, hcs] at hd; rw [beq_iff_eq.mp hd]; exact Nat.lt_of_lt_of_le (by decide) (Nat.le_add_right _ _)
    | tok t =>
      simp only [dvOK, hcs, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true] at hd
      rcases hd with ((hd | hd) | hd) | ⟨hd | hd, -⟩
      · rw [hd]; exact Nat.lt_of_lt_of_le (by decide) (Nat.le_add_right _ _)
      · rw [hd]; exact Nat.lt_of_lt_of_le (by decide) (Nat.le_add_right _ _)
      · exact hn.1.2 _ (List.mem_append_left _ (List.mem_append_left _ (List.contains_iff_mem.mp hd)))
      · rw [hd]; exact Nat.lt_of_lt_of_le (by decide) (Nat.le_add_right _ _)
      · exact hn.1.2 _ (List.mem_append_left _ (List.mem_append_right _ (List.contains_iff_mem.mp hd)))
    | float _ _ _ =>
      simp only [dvOK, hcs, Bool.and_eq_true, beq_iff_eq] at hd
      rw [hd.1]; exact Nat.lt_of_lt_of_le (by decide) (Nat.le_add_right _ _)
  | map s0 es =>
    obtain ⟨k, -, hco, -, -, -, -, rfl⟩ := sortOf_mapS_fwd hv
    obtain ⟨hk, rfl⟩ := Model.collOf_spec hco
    exact hcoll hk
  | set s0 es =>
    obtain ⟨k, hco, -, -, -, rfl⟩ := sortOf_setS.mp hv
    obtain ⟨hk, rfl⟩ := Model.collOf_spec hco
    exact hcoll hk
  | list s0 es =>
    obtain ⟨k, hco, -, -, rfl⟩ := sortOf_listS.mp hv
    obtain ⟨hk, rfl⟩ := Model.collOf_spec hco
    exact hcoll hk

end

section
variable {c : Semantics} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hI : I ⊧ᴵP Γ c) [OvlOK c]
include hI

/-- `agrees_of_fixK` from what it reads: the values generated (`genWf`). -/
theorem agrees_of_fixKCl (hg : genWf c = true) (hsorts : Model.sortsNumbered c = true) (hov : c.overloadsOK = true)
    {r : Rule} {σ : Subst} (hσ : c.WellSorted r.vars σ) {is : List Nat} (his : ∀ i < r.vars.length, i ∈ is)
    {tbl : VarTable} {e : Valuation M} {m : M}
    (hb : ∀ p ∈ fixK c r σ is, (KoreAML.tr ⟨tbl, []⟩ p).interpret I e m) :
    Agrees c I tbl (canonVars c r.vars) σ e := by
  intro i v hi hv a
  rw [canonVars_length] at hi
  obtain ⟨w, hw, hws⟩ := hσ i (r.vars[i]) (List.getElem?_eq_getElem hi)
  rw [hv] at hw; cases hw
  have hvi : (canonVars c r.vars)[i]? = some ((canonVars c r.vars)[i]'(by rw [canonVars_length]; exact hi)) :=
    List.getElem?_eq_getElem _
  have hmem : Kore.Pattern.equals (srtOf c r.vars[i]) (srtOf c topCellSort)
      (.var (.evar ((canonVars c r.vars)[i]'(by rw [canonVars_length]; exact hi)).kore)) (v.kore c) ∈
      fixK c r σ is := by
    unfold fixK
    refine List.mem_filterMap.mpr ⟨i, his i hi, ?_⟩
    simp only [hvi, List.getElem?_eq_getElem hi, hv]
  have hx := ((fixEq_iff hI (sortOf_numbered_ofCl hg hsorts hov hws) hws m).mp (hb _ hmem)).2
  rw [List.getD_eq_getElem?_getD, hvi, Option.getD_some, hx]
  exact ((elemOf_spec hI hws e).1 a).symm

end

section
variable {c : Semantics}

/-- `famEx_eq_exNil` from `sortedOKCl`. -/
theorem famEx_eqCl_exNil (hok : c.sortedOKCl = true) {r : Rule} (hr : r ∈ c.rules) (hex : r.exs = []) (hpost : r.post = .top) (σ : Subst) :
    famEx c r σ = KoreAML.denB (KoreAML.existsAll (srtOf c topCellSort)
      ((canonVars c r.vars).map KoreAML.Var.kore)
      (.and (srtOf c topCellSort) (fixK c r σ (List.range r.vars.length) ++
        [.and (srtOf c topCellSort) [Term.kore c (canonVars c r.vars) r.rhs,
          reqPat (srtOf c topCellSort) (r.ens.map (Term.kore c (canonVars c r.vars)))]]))) := by
  have hv := filterMap_range_getElem? (canonVars c r.vars)
  rw [canonVars_length] at hv
  have hf : (List.range r.vars.length).filter (fun _ => true) = List.range r.vars.length :=
    List.filter_eq_self.mpr (fun _ _ => rfl)
  simp only [famEx, ruleRight, hex, hpost, List.contains_nil, Bool.not_false, Cond.conj, Cond.isTop, ite_true,
    List.filterMap_nil, List.foldr_nil, List.append_nil]
  rw [hf, hv]

variable {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}

/-- **The instances of a step are its successor**, in every model of `Γc`, for a semantics whose
clauses are asked CN-4's bodies (`sortedOKCl`) with `srReady`, `OvlOK`, `faithCoreOK`,
`patHooksApart` and `overloadsOK`, and whose clauses' conditions are decided where `needsWitness`
holds (`neg_of_coreCl`'s hypotheses). `famEx_den_exNil` with no fact on the clauses' variables beyond
each occurring in its clause; a rule without existential variables. -/
theorem famEx_denCl_exNil (hIc : I ⊧ᴵP Γc c) (hok : c.sortedOKCl = true) (hsr : c.srReady = true) [hno : OvlOK c]
    (hfa : c.faithCoreOK = true) (hph : patHooksApart c = true) (hov : c.overloadsOK = true)
    (hc : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, cl.needsWitness c = true → cl.CondDecided c)
    {x y : Config c} {r : Rule} {σ : Subst} (hs : StepBy c r σ x y) (hexs : r.exs = []) (hpost : r.post = .top) (e : Valuation M)
    (m : M) : (famEx c r σ).interpret I e m ↔ (den c y.val).interpret I e m := by
  have hI : I ⊧ᴵP Γ c := fun φ hφ => hIc φ (Or.inl hφ)
  obtain ⟨hnn, hg, -, -, -, -, -⟩ := faithCoreOK_parts hfa
  have hnn := namesNumbered_spec hnn
  have hsorts : Model.sortsNumbered c = true := (faithCoreOK_parts hfa).2.2.2.2.2.2.2.1
  have hsc := sortCtx_of_allCl hok hsr (OvlOK.ovlCase hno)
  have hD := defOK hI
  have hcls := clauseOpenFactsP_of_sortedOKCl hok
  have hneg := neg_of_coreCl hIc hok hsr hfa hph hc (preRead_of_allTop (clauseOpenFacts_of_sortedOKCl hok))
  obtain ⟨-, -, hrhss⟩ := rule_ctxCl hok hs.mem
  have hensS := rule_ctx_ensCl hok hs.mem
  rw [famEx_eqCl_exNil hok hs.mem hexs hpost]
  unfold KoreAML.denB
  generalize htbl : KoreAML.tableOf [] _ = tbl
  have hkeys : ∀ i < r.vars.length, canonKey c r.vars i ∈ tbl := fun i hi => by
    rw [← htbl]; exact canonKey_mem_existsAll hi
  obtain ⟨hnd, hsrt⟩ := canon_binders hkeys
  have hne : ∀ (l : List Kore.Pattern) (p : Kore.Pattern), l ++ [p] ≠ [] := fun l p => by simp
  constructor
  · intro hm
    obtain ⟨e', -, -, hb⟩ := existsAll_elim hD _ e m hnd hsrt hm
    rw [interp_and (hne _ _)] at hb
    have hag := agrees_of_fixKCl hI hg hsorts hov hs.hσ (is := List.range r.vars.length)
      (fun i hi => List.mem_range.mpr hi) (fun p hp => hb p (List.mem_append_left _ hp))
    have hRm := hb _ (List.mem_append_right _ (List.mem_singleton_self _))
    rw [tr_and2, KoreAML.interp_sAnd] at hRm
    have := (evalTerm_den4ClPre hI hnn hsc hph hcls hneg (preRead_of_allTop (clauseOpenFacts_of_sortedOKCl hok)) hs.heval fns_headsOK hs.hσ (canonVars_length c r.vars) hag
      hrhss m).mp hRm.1
    exact ((den_closed c y.val).interp e' e m).mp this
  · intro hm
    have hmy : m = elemOf c I y.val := ((elemOf_spec hI y.property e).1 m).mp hm
    have hag := overV_agrees hI hkeys hs.hσ (e := e)
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
      obtain ⟨w, hw, hsw⟩ := hs.hσ i (r.vars.getD i 0)
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
          obtain ⟨w, hw, hsw⟩ := hs.hσ i s hsi
          rw [hg'] at hw; cases hw
          refine (fixEq_iff hI (sortOf_numbered_ofCl hg hsorts hov hsw) hsw m).mpr ⟨hinC, ?_⟩
          have hvk : KoreAML.evarKey v.kore = canonKey c r.vars i := by
            unfold canonKey
            rw [List.getD_eq_getElem?_getD, hv, Option.getD_some]
          rw [hvk, overV_at hkeys hi, hg', Option.getD_some]
        · cases hpi
      · rw [List.mem_singleton.mp hp, tr_and2, KoreAML.interp_sAnd]
        refine ⟨(evalTerm_den4ClPre hI hnn hsc hph hcls hneg (preRead_of_allTop (clauseOpenFacts_of_sortedOKCl hok)) hs.heval fns_headsOK hs.hσ (canonVars_length c r.vars) hag
          hrhss m).mpr (((den_closed c y.val).interp e _ m).mp hm), reqPat_holds hI (fun t ht b =>
            evalTerm_den4ClPre hI hnn hsc hph hcls hneg (preRead_of_allTop (clauseOpenFacts_of_sortedOKCl hok)) (hs.hens t ht) fns_headsOK hs.hσ (canonVars_length c r.vars) hag
              (hensS t ht) b) hinC⟩


/-- **A step by a rule without existential variables has one instance**, for a semantics whose
clauses are asked CN-4's bodies: `famEx_closed`'s conclusion with `sortedOKCl` and the conjuncts of
`coreOK` the proof reads in place of `coreOK` (`famEx_denCl_exNil`). No hypothesis on the sorts of
the variables the patterns and conditions do not hold. -/
theorem famEx_closedCl (c : Semantics) (hok : c.sortedOKCl = true) (hsr : c.srReady = true) [OvlOK c]
    (hfa : c.faithCoreOK = true) (hph : patHooksApart c = true) (hov : c.overloadsOK = true)
    {x y : Config c} {r : Rule} {σ : Subst} (hs : StepBy c r σ x y) (_hex : r.exs = []) (hpost : r.post = .top)
    (hc : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, cl.needsWitness c = true → cl.CondDecided c) :
    Γc c ⊧ (famEx c r σ ≡ den c y.val) := by
  intro M _ I hI e m
  rw [KoreAML.interp_equal (defOK fun φ hφ => hI φ (Or.inl hφ))]
  exact famEx_denCl_exNil hI hok hsr hfa hph hov hc hs _hex hpost e

end

end Faithful

end KCore
