/-
  KCore. The families of an application of a rule in a model (`famEx`, `famOpen`, Faithful.lean),
  for a rule of the shapes `coreOK` admits (no existential variable, `\top` predicates, a left side
  that binds every variable): the instances of a step are its successor (`famEx_den_exNil`, a rule without existential variables), and the
  outcomes of an unblocked match are among the successors of its steps (`famOpen_step`). And, in
  every model of `Γ` with the step's closure, a configuration x has a successor in the element of
  a value y exactly where `Step c x y` (`step_iff_model`).
-/
import KcoreSpec.FaithfulCompleteAt

set_option autoImplicit false

namespace KCore

namespace Faithful

open ML
open KoreAML (DefOK Inh IsSort Closed VarKey VarTable)

/-! ## Patterns of the encoding -/

section
variable {c : Semantics}

theorem tr_app_nil (t : VarTable) (h : Kore.SymbolIdent) (ps : List Kore.Pattern) :
    KoreAML.tr ⟨t, []⟩ (.app h [] ps) = KoreAML.trArgs ⟨t, []⟩ (KoreAML.sym (.symbol h.ident.name)) ps := by
  rw [KoreAML.tr]; simp [KoreAML.trSortApp]

theorem trArgs_two (ctx : KoreAML.Ctx) (acc : KoreAML.P) (p q : Kore.Pattern) :
    KoreAML.trArgs ctx acc [p, q] = acc ⬝ KoreAML.tr ctx p ⬝ KoreAML.tr ctx q := by
  simp [KoreAML.trArgs]

theorem trArgs_one (ctx : KoreAML.Ctx) (acc : KoreAML.P) (p : Kore.Pattern) :
    KoreAML.trArgs ctx acc [p] = acc ⬝ KoreAML.tr ctx p := by
  simp [KoreAML.trArgs]

mutual
  /-- A value's KORE has no variable: its translation does not read the variable table. -/
  theorem tr_groundKore (c : Semantics) (t : VarTable) : ∀ g : GroundTerm,
      KoreAML.tr ⟨t, []⟩ (g.kore c) = KoreAML.tr ⟨[], []⟩ (g.kore c)
    | .ctor f ts => by
      simp only [GroundTerm.kore]
      rw [tr_app_nil, tr_app_nil, trArgs_groundKore c t ts]
    | .inj a b w => by
      simp only [GroundTerm.kore, KoreAML.injP]
      rw [KoreAML.tr, KoreAML.tr]
      simp only [List.contains_nil, Bool.false_eq_true, ite_false, KoreAML.trSortApp, trSort_srt, trArgs_one]
      rw [tr_groundKore c t w]
    | .dv s lit => by
      simp only [GroundTerm.kore]
      rw [KoreAML.tr_dv, KoreAML.tr_dv]
    | .map s es => tr_groundEntries c t _ es
    | .set s es => tr_groundElems c t _ es
    | .list s es => tr_groundElems c t _ es
    termination_by structural g => g
  theorem trArgs_groundKore (c : Semantics) (t : VarTable) : ∀ (ts : List GroundTerm) (acc : KoreAML.P),
      KoreAML.trArgs ⟨t, []⟩ acc (GroundTerm.koreList c ts) = KoreAML.trArgs ⟨[], []⟩ acc (GroundTerm.koreList c ts)
    | [], _ => by simp [GroundTerm.koreList, KoreAML.trArgs]
    | g :: ts, acc => by
      simp only [GroundTerm.koreList, KoreAML.trArgs]
      rw [tr_groundKore c t g, trArgs_groundKore c t ts]
    termination_by structural ts => ts
  theorem tr_groundEntries (c : Semantics) (t : VarTable) (k : CollSig) :
      ∀ es : List (GroundTerm × GroundTerm),
      KoreAML.tr ⟨t, []⟩ (GroundTerm.koreEntries c k es) = KoreAML.tr ⟨[], []⟩ (GroundTerm.koreEntries c k es)
    | [] => by simp only [GroundTerm.koreEntries, KoreAML.ap]; rw [tr_app_nil, tr_app_nil]; rfl
    | [e] => by simp only [GroundTerm.koreEntries]; exact tr_groundEntry c t k e
    | e :: e' :: es => by
      simp only [GroundTerm.koreEntries, KoreAML.ap]
      rw [tr_app_nil, tr_app_nil, trArgs_two, trArgs_two, tr_groundEntry c t k e]
      rw [tr_groundEntries c t k (e' :: es)]
    termination_by structural es => es
  theorem tr_groundEntry (c : Semantics) (t : VarTable) (k : CollSig) : ∀ e : GroundTerm × GroundTerm,
      KoreAML.tr ⟨t, []⟩ (GroundTerm.koreEntry c k e) = KoreAML.tr ⟨[], []⟩ (GroundTerm.koreEntry c k e)
    | (x, v) => by
      simp only [GroundTerm.koreEntry, KoreAML.ap]
      rw [tr_app_nil, tr_app_nil, trArgs_two, trArgs_two, tr_groundKore c t x, tr_groundKore c t v]
    termination_by structural e => e
  theorem tr_groundElems (c : Semantics) (t : VarTable) (k : CollSig) : ∀ es : List GroundTerm,
      KoreAML.tr ⟨t, []⟩ (GroundTerm.koreElems c k es) = KoreAML.tr ⟨[], []⟩ (GroundTerm.koreElems c k es)
    | [] => by simp only [GroundTerm.koreElems, KoreAML.ap]; rw [tr_app_nil, tr_app_nil]; rfl
    | [e] => by
      simp only [GroundTerm.koreElems, KoreAML.ap]
      rw [tr_app_nil, tr_app_nil, trArgs_one, trArgs_one, tr_groundKore c t e]
    | e :: e' :: es => by
      simp only [GroundTerm.koreElems, KoreAML.ap]
      rw [tr_app_nil, tr_app_nil, trArgs_two, trArgs_two, tr_app_nil, tr_app_nil, trArgs_one, trArgs_one,
        tr_groundKore c t e]
      rw [tr_groundElems c t k (e' :: es)]
    termination_by structural es => es
end

/-- The translation of a value's KORE under any table is the value's pattern. -/
theorem tr_ground_den (t : VarTable) (g : GroundTerm) : KoreAML.tr ⟨t, []⟩ (g.kore c) = den c g := by
  rw [tr_groundKore c t g]; rfl

variable {M : Type} {I : Interpretation KoreAML.Sym M}

/-- `\and{S}(φ₁,…,φₙ)` with at least one operand: each operand holds. -/
theorem interp_trAndList {ctx : KoreAML.Ctx} {S : KoreAML.P} {e : Valuation M} {m : M} :
    ∀ {ps : List Kore.Pattern}, ps ≠ [] →
      ((KoreAML.trAndList ctx S ps).interpret I e m ↔ ∀ p ∈ ps, (KoreAML.tr ctx p).interpret I e m)
  | [], h => absurd rfl h
  | [p], _ => by simp [KoreAML.trAndList]
  | p :: q :: ps, _ => by
    rw [KoreAML.trAndList]
    rw [KoreAML.interp_sAnd, interp_trAndList (List.cons_ne_nil _ _)]
    simp only [List.mem_cons, forall_eq_or_imp]

theorem interp_and {ctx : KoreAML.Ctx} {S : Kore.KSort} {e : Valuation M} {m : M} {ps : List Kore.Pattern}
    (h : ps ≠ []) :
    (KoreAML.tr ctx (.and S ps)).interpret I e m ↔ ∀ p ∈ ps, (KoreAML.tr ctx p).interpret I e m := by
  rw [KoreAML.tr]; exact interp_trAndList h

theorem varsOf_existsAll {S : Kore.KSort} {body : Kore.Pattern} : ∀ {bs : List Kore.EVar} {b : Kore.EVar}, b ∈ bs →
    KoreAML.evarKey b ∈ KoreAML.varsOf (KoreAML.existsAll S bs body)
  | b' :: bs, b, hb => by
    show KoreAML.evarKey b ∈ KoreAML.varsOf (.exist S b' (KoreAML.existsAll S bs body))
    rw [KoreAML.varsOf]
    rcases List.mem_cons.mp hb with rfl | hb
    · simp
    · exact List.mem_append_right _ (varsOf_existsAll hb)

end

/-! ## Sorts of values -/

section
variable {c : Semantics}

/-- `coreOK`'s numbering of sorts. -/
theorem sortsNumbered_of_core (h : c.coreOK = true) : Model.sortsNumbered c = true :=
  (faithCoreOK_parts (Semantics.coreOK_parts h).2.1).2.2.2.2.2.2.2.1

/-- The sort of a value is numbered, under the conditions `coreOK` gives. -/
theorem sortOf_numbered_of (hs : HypSoundCore c) (hsorts : Model.sortsNumbered c = true) (hov : c.overloadsOK = true)
    {v : GroundTerm} {s : Srt} (hv : c.sortOf v = some s) : s < nRegSorts + c.sortNames.length := by
  have hn := hsorts
  simp only [Model.sortsNumbered, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hn
  have hsym : ∀ {k : CtorSig}, k ∈ kernelSyms c → ∀ s ∈ k.result :: k.args, s < nRegSorts + c.sortNames.length :=
    fun hk => hn.1.1.1 _ hk
  have hcoll : ∀ {k : CollSig}, k ∈ c.allColls → k.sort < nRegSorts + c.sortNames.length :=
    fun hk => (hn.2 _ hk).1.1
  cases v with
  | ctor f ts =>
    haveI : OvlOK c := hs.2.2.2.2.2.2.2.2
    rcases sortOf_ctor_cases hs.2.2.2.1 hv with ⟨k, hk, -, rfl⟩ | ⟨o, hlo, -, -, -, rfl, -⟩ | ⟨kp, hko, -, -, -, -, rfl, -⟩
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

/-! ## The equations `fixK` writes, in a model -/

section
variable {c : Semantics} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hI : I ⊧ᴵP Γ c) [OvlOK c]
include hI

/-- `\equals{s, C}(X, ⟦g⟧)` for a value g of the numbered sort s: the elements of C where the
variable X is the element of g. -/
theorem fixEq_iff {s : Srt} (hnum : s < nRegSorts + c.sortNames.length) {tbl : VarTable} {e : Valuation M}
    {x : Kore.EVar} {g : GroundTerm} (hg : c.sortOf g = some s) (m : M) :
    (KoreAML.tr ⟨tbl, []⟩ (.equals (srtOf c s) (srtOf c topCellSort) (.var (.evar x)) (g.kore c))).interpret I e m ↔
      (KoreAML.inhOf (KoreAML.trSort tbl (srtOf c topCellSort))).interpret I e m ∧
        e.evalEvar (tbl.ev (KoreAML.evarKey x)) = elemOf c I g := by
  have hD := defOK hI
  have hc := sat_sigItem hI (sig_ceilDef (c := c))
  obtain ⟨σC, hσC1, hσC2⟩ := sortSing hI (top_numbered (c := c))
  obtain ⟨σs, hσs1, hσs2⟩ := sortSing hI hnum
  have hSC : ∀ b, (KoreAML.trSort tbl (srtOf c topCellSort)).interpret I e b ↔ b = σC := by
    unfold srtOf; rw [trSort_srt]; exact hσC1
  have hSs : ∀ b, (KoreAML.trSort tbl (srtOf c s)).interpret I e b ↔ b = σs := by
    unfold srtOf; rw [trSort_srt]; exact hσs1
  have hgs := elemOf_spec hI hg e
  have hgin : Inh I σs (elemOf c I g) := (KoreAML.interp_inhOf_of (S := KoreAML.sym _) hσs1).mp hgs.2
  rw [KoreAML.tr, KoreAML.interp_sEquals hD hc hSs hSC hσs2 hσC2, KoreAML.interp_inhOf_of hSC, tr_ground_den]
  constructor
  · rintro ⟨hm, hall⟩
    refine ⟨hm, ?_⟩
    have := (hall _ hgin).mpr ((hgs.1 _).mpr rfl)
    rw [KoreAML.tr] at this
    exact this.symm
  · rintro ⟨hm, hx⟩
    refine ⟨hm, fun a _ => ?_⟩
    rw [KoreAML.tr, hgs.1 a]
    show a = e.evalEvar (tbl.ev (KoreAML.evarKey x)) ↔ _
    rw [hx]

/-- Where the equations `fixK` writes for the listed variables hold, and every variable is
listed, the valuation agrees with σ. -/
theorem agrees_of_fixK (hs : HypSoundCore c) (hsorts : Model.sortsNumbered c = true) (hov : c.overloadsOK = true)
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
  have hx := ((fixEq_iff hI (sortOf_numbered_of hs hsorts hov hws) hws m).mp (hb _ hmem)).2
  rw [List.getD_eq_getElem?_getD, hvi, Option.getD_some, hx]
  exact ((elemOf_spec hI hws e).1 a).symm

end

/-! ## The instances of a step -/

section
variable {c : Semantics}

/-- The pattern `famEx` reads, for a rule of the shapes `coreOK` admits without existential
variables. -/
theorem famEx_eq_exNil (hok : c.sortedOK = true) {r : Rule} (hr : r ∈ c.rules) (hex : r.exs = []) (hpost : r.post = .top) (σ : Subst) :
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

theorem canonKey_mem_existsAll {vars : List Srt} {S : Kore.KSort} {body : Kore.Pattern} {i : Nat}
    (hi : i < vars.length) :
    canonKey c vars i ∈ KoreAML.tableOf [] (KoreAML.existsAll S ((canonVars c vars).map KoreAML.Var.kore) body) := by
  unfold KoreAML.tableOf canonKey
  refine List.mem_eraseDups.mpr (List.mem_append_right _ (varsOf_existsAll (List.mem_map_of_mem ?_)))
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [canonVars_length]; exact hi)]
  exact List.getElem_mem _

variable {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}

/-- **The instances of a step are its successor**, in every model of `Γ`, for a rule of the shapes
`coreOK` admits: every variable is fixed to its value, and the right side is the successor. -/
theorem famEx_den_exNil (hpreTop : c.clausesPreTop = true) (h : HypSoundCore c) (hbc : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, binds cl.vars.length (varOccsList cl.pats) = true) (hsorts : Model.sortsNumbered c = true) (hov : c.overloadsOK = true)
    {x y : Config c} {r : Rule} {σ : Subst} (hs : StepBy c r σ x y) (hexs : r.exs = []) (hpost : r.post = .top)
    (hI : I ⊧ᴵP Γ c) (e : Valuation M) (m : M) :
    (famEx c r σ).interpret I e m ↔ (den c y.val).interpret I e m := by
  obtain ⟨hok, hsr, hnn, hg, hph, hcso, hcs, hph', hno⟩ := h
  haveI : OvlOK c := hno
  have hsc := sortCtx_of_all hok hsr (OvlOK.ovlCase hno)
  have hD := defOK hI
  have hex : ∀ fn ∈ c.allFns, ∀ cl ∈ fn.clauses, ExclEmpty c I fn cl := fun fn hfn cl hcl => by
    obtain ⟨hp', hb', -⟩ := clause_ctx hok hbc hfn hcl
    exact fun hws _ hkeys hXkeys hRkey _ hX _ hR hσR hfail m =>
      exclusion_emptyC hI hph hcs hcso hg hsc.trans hnn.1 (clause_preTop (hpreTop := hpreTop) hok hfn hcl) hp' hb' (collPats_of_sorted hph' hp') hws hkeys hXkeys
        hRkey hX hR hσR hfail m
  have hneg : ∀ fn ∈ c.allFns, ∀ cl ∈ fn.clauses, ClauseNeg c fn cl → ExclEmpty c I fn cl :=
    fun fn hfn cl hcl _ => hex fn hfn cl hcl
  have hs0 : HypSoundCore c := ⟨hok, hsr, hnn, hg, hph, hcso, hcs, hph', hno⟩
  obtain ⟨-, -, hrhss⟩ := rule_ctx hok hs.mem
  have hensS := rule_ctx_ens hok hs.mem
  rw [famEx_eq_exNil hok hs.mem hexs hpost]
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
    have hag := agrees_of_fixK hI hs0 hsorts hov hs.hσ (is := List.range r.vars.length)
      (fun i hi => List.mem_range.mpr hi) (fun p hp => hb p (List.mem_append_left _ hp))
    have hRm := hb _ (List.mem_append_right _ (List.mem_singleton_self _))
    rw [tr_and2, KoreAML.interp_sAnd] at hRm
    have := (evalTerm_den4 (hpreTop := hpreTop) hI hnn hsc hok hbc hph hneg hs.heval fns_headsOK hs.hσ (canonVars_length c r.vars) hag
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
          refine (fixEq_iff hI (sortOf_numbered_of hs0 hsorts hov hsw) hsw m).mpr ⟨hinC, ?_⟩
          have hvk : KoreAML.evarKey v.kore = canonKey c r.vars i := by
            unfold canonKey
            rw [List.getD_eq_getElem?_getD, hv, Option.getD_some]
          rw [hvk, overV_at hkeys hi, hg', Option.getD_some]
        · cases hpi
      · rw [List.mem_singleton.mp hp, tr_and2, KoreAML.interp_sAnd]
        refine ⟨(evalTerm_den4 (hpreTop := hpreTop) hI hnn hsc hok hbc hph hneg hs.heval fns_headsOK hs.hσ (canonVars_length c r.vars) hag
          hrhss m).mpr (((den_closed c y.val).interp e _ m).mp hm), reqPat_holds hI (fun t ht b =>
            evalTerm_den4 (hpreTop := hpreTop) hI hnn hsc hok hbc hph hneg (hs.hens t ht) fns_headsOK hs.hσ (canonVars_length c r.vars) hag
              (hensS t ht) b) hinC⟩

end

/-! ## The outcomes of a match -/

section
variable {c : Semantics}

/-- The pattern `famOpen` reads, for a rule of the shapes `coreOK` admits without existential
variables. -/
theorem famOpen_eq_exNil (hok : c.sortedOK = true) {r : Rule} (hr : r ∈ c.rules) (hex : r.exs = []) (hpre : r.pre = .top) (hpost : r.post = .top) (σ : Subst) :
    famOpen c r σ = KoreAML.denB (KoreAML.existsAll (srtOf c topCellSort)
      ((canonVars c r.vars).map KoreAML.Var.kore)
      (.and (srtOf c topCellSort) (fixK c r σ (varOccs r.lhs) ++
        [reqPat (srtOf c topCellSort) (r.req.map (Term.kore c (canonVars c r.vars)))] ++
        [.and (srtOf c topCellSort) [Term.kore c (canonVars c r.vars) r.rhs,
          reqPat (srtOf c topCellSort) (r.ens.map (Term.kore c (canonVars c r.vars)))]]))) := by
  have hv := filterMap_range_getElem? (canonVars c r.vars)
  rw [canonVars_length] at hv
  have hf : (List.range r.vars.length).filter (fun _ => true) = List.range r.vars.length :=
    List.filter_eq_self.mpr (fun _ _ => rfl)
  simp only [famOpen, ruleRight, hex, hpre, hpost, List.contains_nil, Bool.not_false, Cond.conj, Cond.isTop,
    ite_true, List.filterMap_nil, List.foldr_nil, List.append_nil]
  rw [hf, hv]

variable {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}

/-- **The outcomes of an unblocked match are successors of its steps**, in every model of `Γ`, for a
rule of the shapes `coreOK` admits, where every function has a result at arguments of its sorts:
an element of `famOpen` is the element of a configuration y with `StepBy c r σ x y`. -/
theorem famOpen_step (hpreTop : c.clausesPreTop = true) (h : HypSoundCore c) (hb : ∀ r ∈ c.rules, binds r.vars.length (varOccs r.lhs) = true) (htop : ∀ r ∈ c.rules, r.pre = .top ∧ r.post = .top)
    (hbc : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, binds cl.vars.length (varOccsList cl.pats) = true) (hsorts : Model.sortsNumbered c = true) (hov : c.overloadsOK = true)
    (hft : FnTerminates c) {x : Config c} {r : Rule} (hr : r ∈ c.rules) {σ : Subst}
    (hu : Unblocked c r σ x.val) (hI : I ⊧ᴵP Γ c) (e : Valuation M) (m : M)
    (hm : (famOpen c r σ).interpret I e m) :
    ∃ y : Config c, StepBy c r σ x y ∧ (den c y.val).interpret I e m := by
  have hs0 := h
  obtain ⟨hok, hsr, hnn, hg, hph, hcso, hcs, hph', hno⟩ := h
  haveI : OvlOK c := hno
  have hsc := sortCtx_of_all hok hsr (OvlOK.ovlCase hno)
  have hD := defOK hI
  have hex : ∀ fn ∈ c.allFns, ∀ cl ∈ fn.clauses, ExclEmpty c I fn cl := fun fn hfn cl hcl => by
    obtain ⟨hp', hb', -⟩ := clause_ctx hok hbc hfn hcl
    exact fun hws _ hkeys hXkeys hRkey _ hX _ hR hσR hfail m =>
      exclusion_emptyC hI hph hcs hcso hg hsc.trans hnn.1 (clause_preTop (hpreTop := hpreTop) hok hfn hcl) hp' hb' (collPats_of_sorted hph' hp') hws hkeys hXkeys
        hRkey hX hR hσR hfail m
  have hneg : ∀ fn ∈ c.allFns, ∀ cl ∈ fn.clauses, ClauseNeg c fn cl → ExclEmpty c I fn cl :=
    fun fn hfn cl hcl _ => hex fn hfn cl hcl
  obtain ⟨-, hreqs, hrhss⟩ := rule_ctx hok hr
  have hbinds := Exec.binds_all (hb _ hr)
  obtain ⟨hpre, hpost⟩ := htop _ hr
  have hensS := rule_ctx_ens hok hr
  obtain ⟨hσat, hmatch, hprio⟩ := hu
  have hσ : c.WellSorted r.vars σ := fun i s hs =>
    hσat i (hbinds i (List.getElem?_eq_some_iff.mp hs).1) s hs
  rw [famOpen_eq_exNil hok hr (Semantics.sortedOK_exsNil hok hr (hb r hr)) hpre hpost] at hm
  unfold KoreAML.denB at hm
  generalize htbl : KoreAML.tableOf [] _ = tbl at hm
  have hkeys : ∀ i < r.vars.length, canonKey c r.vars i ∈ tbl := fun i hi => by
    rw [← htbl]; exact canonKey_mem_existsAll hi
  obtain ⟨hnd, hsrt⟩ := canon_binders hkeys
  obtain ⟨e', -, -, hb⟩ := existsAll_elim hD _ e m hnd hsrt hm
  rw [interp_and (by simp)] at hb
  have hag := agrees_of_fixK hI hs0 hsorts hov hσ (is := varOccs r.lhs) hbinds
    (fun p hp => hb p (List.mem_append_left _ (List.mem_append_left _ hp)))
  have hreqm := hb _ (List.mem_append_left _ (List.mem_append_right _ (List.mem_singleton_self _)))
  have hRm := hb _ (List.mem_append_right _ (List.mem_singleton_self _))
  rw [tr_and2, KoreAML.interp_sAnd] at hRm
  obtain ⟨σC, hσC1, hσC2⟩ := sortSing hI (top_numbered (c := c))
  have hSC : ∀ a, (KoreAML.trSort tbl (srtOf c topCellSort)).interpret I e' a ↔ a = σC := by
    unfold srtOf; rw [trSort_srt]; exact hσC1
  -- a condition the element satisfies evaluates to `true`
  have htrue : ∀ (q : Option Term), (∀ t, q = some t →
      sortOfTerm (c.rhsCtx (c.fns.map Fn.sig)) r.vars t = some Srt.bool) →
      (KoreAML.tr ⟨tbl, []⟩ (reqPat (srtOf c topCellSort) (q.map (Term.kore c (canonVars c r.vars))))).interpret
        I e' m →
      ∀ t, q = some t → EvalTerm c σ t (some (bool true)) := by
    intro q hqs hqm t ht
    obtain ⟨v, hv⟩ := Model.evalTerm_total hs0 hft fns_headsOK hσ (hqs t ht)
    by_cases hvt : v = some (bool true)
    · rw [hvt] at hv; exact hv
    · exfalso
      rw [ht] at hqm
      exact reqFalse_empty hI hSC hσC2 hvt (fun u hu => EvalTerm.sorted hsc hv fns_headsOK hσ (hqs t ht) hu)
        (evalTerm_den4 (hpreTop := hpreTop) hI hnn hsc hok hbc hph hneg hv fns_headsOK hσ (canonVars_length c r.vars) hag (hqs t ht)) m hqm
  have hreqT := htrue r.req hreqs hreqm
  have hensT := htrue r.ens hensS hRm.2
  obtain ⟨v, hv⟩ := Model.evalTerm_total hs0 hft fns_headsOK hσ hrhss
  have hbR := (evalTerm_den4 (hpreTop := hpreTop) hI hnn hsc hok hbc hph hneg hv fns_headsOK hσ (canonVars_length c r.vars) hag hrhss m).mp
    hRm.1
  cases v with
  | none => exact hbR.elim
  | some yv =>
    exact ⟨⟨yv, rhs_sorted_core hok hsr (OvlOK.ovlCase inferInstance) hr hσ hv⟩,
      ⟨hr, hσ, hmatch, hreqT, hpre ▸ .top, hv, hensT, hpost ▸ .top, hprio⟩,
      ((den_closed c yv).interp e' e m).mp hbR⟩

end

/-! ## Steps and the successors of a model -/

section
variable {c : Semantics}

/-- **In every model of `Γ` with the step's closure, the steps at values are `Step`**: x has a
successor in the element of y exactly where `Step c x y`, where the evaluations the step at x reads
have results. -/
theorem step_iff_model (hpreTop : c.clausesPreTop = true) (h : HypSoundCore c) (hb : ∀ r ∈ c.rules, binds r.vars.length (varOccs r.lhs) = true) (htop : ∀ r ∈ c.rules, r.pre = .top ∧ r.post = .top)
    (hbc : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, binds cl.vars.length (varOccsList cl.pats) = true) (x y : Config c) (hd : StepDecided c x.val)
    {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hI : I ⊧ᴵP (Γ c ∪ Γstep c)) :
    Step c x y ↔ ¬ (I ⊧ᴵ (den c x.val ⇒ ∼ KoreAML.sNext (den c y.val))) := by
  have hIΓ : I ⊧ᴵP Γ c := fun φ hφ => hI φ (Or.inl hφ)
  constructor
  · intro hs hall
    have hsd := step_sound_core (hpreTop := hpreTop) c h hb htop hbc x y hs hIΓ KoreAML.val0 (elemOf c I x.val)
    have hx := ((elemOf_spec hIΓ x.property KoreAML.val0).1 _).mpr rfl
    have h1 := hall KoreAML.val0 (elemOf c I x.val)
    rw [interpret_impl] at hsd h1
    exact (interpret_neg.mp (h1 hx)) (hsd hx)
  · intro hn
    simp only [Interpretation.satisfies, Valuation.satifies] at hn
    obtain ⟨e, hn⟩ := Classical.not_forall.mp hn
    obtain ⟨m, hn⟩ := Classical.not_forall.mp hn
    rw [interpret_impl] at hn
    have h1 : (den c x.val).interpret I e m := Classical.byContradiction fun hc => hn fun h => absurd h hc
    have h2 : (KoreAML.sNext (den c y.val)).interpret I e m :=
      Classical.byContradiction fun hc => hn fun _ => interpret_neg.mpr hc
    have hmx : m = elemOf c I x.val := ((elemOf_spec hIΓ x.property e).1 m).mp h1
    rw [hmx] at h2
    obtain ⟨y', hy', hyy⟩ := step_successor_at (hpreTop := hpreTop) h hb htop hbc x hd hI e _ h2
    have he : elemOf c I y'.val = elemOf c I y.val := ((elemOf_spec hIΓ y.property e).1 _).mp hyy
    obtain ⟨hok, hsr, -, hg, -, -, -, -, hno⟩ := h
    haveI : OvlOK c := hno
    have hsc := sortCtx_of_all hok hsr (OvlOK.ovlCase hno)
    have := values_apart hIΓ hg hsc.trans (apartSort_of_sorted hg y.property) y'.property y.property he
    have hyy' : y' = y := Subtype.ext this
    rw [← hyy']
    exact hy'

end

end Faithful

end KCore
