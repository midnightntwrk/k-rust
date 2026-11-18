/-
  KCore. `famEx_values`'s and `famOpen_values`'s statements with `coreOKEx` for `coreOK`
  (`famEx_values_ce`, `famOpen_values_ce`): a function's clauses may bind variables by `\exists`.

  - `holdsTrue_of_memPPFv`, `holds_of_conjPPFv`: a predicate whose patterns hold at an element of
    the configuration sort holds, read by `HoldsShape.holds_entailsCEx` and decided by
    `holds_decidedCEx`.
  - `famEx_value_heldCEx`, `famEx_values_heldCEx`: a value in the instances of an application is a
    step, for rules with `rulePlainHeldH` under `HeldBackAll`; the right side is read by
    `HoldsShape.termSoundEx`, and the model of `Γc` is `Faithful.Model.consistent_of_coreEx`'s,
    whose hypotheses `FnHyp` gives (`fnModel_of_fnHypCEx`, `clausePreDecided_of_fnHypCEx`,
    `clausePostDecided_of_fnHypCEx`).
  - `famOpen_stepPPCEx`, `famOpen_values_ppCEx`: the outcomes of a match are among any values
    that hold its steps, for a rule with `ruleSorted`.
  - `famEx_values_ce`, `famOpen_values_ce`: the rules' facts and `HeldBackAll` read from
    `coreOKEx` (`Semantics.ruleFactsHeld_of_coreEx`, `heldBackAll_holdsCEx`,
    `Semantics.ruleFactsHO1_of_coreEx`).
-/
import KcoreSpec.FamExValuesHeld
import KcoreSpec.FamOpenValuesPP
import KcoreSpec.SoundCE
import KcoreSpec.FnModelCEx
import KcoreSpec.HypModelCoreEx
import KcoreSpec.StepExRuleSSx

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace KCore

namespace Faithful

open ML
open KoreAML (DefOK VarTable)
open HoldsShape (hasBinder Reads reads_of_agrees)

section
variable {c : Semantics} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}

variable {H : Sym → Bool}

/-- **A predicate that holds at an element is `true`**, in a model of `Γc` of a semantics
`coreOKEx` accepts, at a σ that gives its free variables values whose elements the valuation gives
them. -/
theorem holdsTrue_of_memPPFv (h : c.coreOKEx = true) (hft : FnTerminates c) (hI : I ⊧ᴵP Γc c)
    (hcw : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, cl.needsWitness c = true → cl.CondDecided c)
    {vars : List Srt} {p : Cond} (hok : c.condOK vars p = true) (hbd : Cond.bound c vars.length p = true)
    (hrc : hasBinder p = true → c.readsConfined = true) {σ : Subst}
    (hσ : c.WellSortedAt vars (varOccsCond vars.length p) σ) {tbl : VarTable} {e : Valuation M}
    (hr : Reads c I vars (fun i => i ∈ varOccsCond vars.length p) σ tbl e)
    (hk : ∀ k ∈ KoreAML.varsOf (Cond.kore c (canonVars c vars) (srtOf c topCellSort) p), k ∈ tbl)
    {a : M} (ha : (KoreAML.inhOf (KoreAML.trSort tbl (srtOf c topCellSort))).interpret I e a)
    (hm : (KoreAML.tr ⟨tbl, []⟩ (Cond.kore c (canonVars c vars) (srtOf c topCellSort) p)).interpret I e a) :
    Holds c vars.length σ p true := by
  obtain ⟨b, hb⟩ := holds_decidedCEx (hypSoundEx_of_coreEx h) hft p hok hσ
  have hiff := HoldsShape.holds_entailsCEx h hI hcw p hrc hok hbd (fun i hi _ => hi) hr hk top_numbered hb a ha
  rw [hiff.mp hm] at hb
  exact hb

/-- `holdsTrue_of_memPPFv` over the conjuncts a predicate adds to a sentence (none for `\top`), at a
σ well sorted on every variable that agrees with the valuation. -/
theorem holds_of_conjPPFv (h : c.coreOKEx = true) (hft : FnTerminates c) (hI : I ⊧ᴵP Γc c)
    (hcw : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, cl.needsWitness c = true → cl.CondDecided c)
    {vars : List Srt} {p : Cond} (hok : c.condOK vars p = true) (hbd : Cond.bound c vars.length p = true)
    (hrc : hasBinder p = true → c.readsConfined = true) {σ : Subst} (hσ : c.WellSorted vars σ)
    {tbl : VarTable} {e : Valuation M} (hag : Agrees c I tbl (canonVars c vars) σ e)
    (hkeys : ∀ i < vars.length, canonKey c vars i ∈ tbl)
    (hk : ∀ k ∈ KoreAML.varsOf (Cond.kore c (canonVars c vars) (srtOf c topCellSort) p), k ∈ tbl)
    {a : M} (ha : (KoreAML.inhOf (KoreAML.trSort tbl (srtOf c topCellSort))).interpret I e a)
    (hm : ∀ φ ∈ Cond.conj c (canonVars c vars) (srtOf c topCellSort) p, (KoreAML.tr ⟨tbl, []⟩ φ).interpret I e a) :
    Holds c vars.length σ p true := by
  by_cases hT : p.isTop = true
  · rw [Cond.eq_top_of_isTop hT]; exact .top
  · refine holdsTrue_of_memPPFv h hft hI hcw hok hbd hrc (hσ.at _)
      (reads_of_agrees hσ hag fun i hi => ⟨varOccsCond_lt_twoT p hok i hi, hkeys i (varOccsCond_lt_twoT p hok i hi)⟩)
      hk ha (hm _ ?_)
    simp [Cond.conj, hT]

/-- **An instance's value gives a substitution**, in a model of `Γc` of a semantics `coreOKEx`
accepts, for a rule with `rulePlainHeldH c H` where each symbol of H that is no constructor has
`HeldBack`: y's element in `famEx c r σ` gives a σ' that is σ off the existential variables, well
sorted, under which the right side evaluates to y, the `ensures` to `true` and `post` holds. An
existential variable the right side holds under H is a value's by `occsUnder_witnessed`, one of a
confined sort by `confined_valueCEx`; no existential variable is a condition variable. A `post`
with a binder asks `readsConfined`. -/
theorem famEx_value_heldCEx (h : c.coreOKEx = true) (hft : FnTerminates c) (hI : I ⊧ᴵP Γc c)
    (hback : ∀ f k, c.isCtor f = false → H f = true →
      lookupSig (c.rhsCtx (c.fns.map Fn.sig)).heads f = some k → HeldBack c I f k)
    (hcw : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, cl.needsWitness c = true → cl.CondDecided c) {r : Rule}
    (hs : c.ruleSorted r = true) (hp : c.rulePlainHeldH H r = true)
    (hrc : r.exs.any (fun i => (r.vars[i]?.map c.confined).getD false) = true → c.readsConfined = true)
    (hrcQ : hasBinder r.post = true → c.readsConfined = true)
    {σ : Subst} (hσ : c.WellSorted r.vars σ) (y : Config c)
    (e : Valuation M) (hm : (famEx c r σ).interpret I e (elemOf c I y.val)) :
    ∃ σ' : Subst, (∀ i, ¬ i ∈ r.exs → σ'.lookup i = σ.lookup i) ∧ c.WellSorted r.vars σ' ∧
      EvalTerm c σ' r.rhs (some y.val) ∧ (∀ t, r.ens = some t → EvalTerm c σ' t (some (bool true))) ∧
      Holds c r.vars.length σ' r.post true := by
  have hIΓ : I ⊧ᴵP Γ c := fun φ hφ => hI φ (Or.inl hφ)
  have hs0 := hypSoundEx_of_coreEx h
  obtain ⟨hok, hsr, hnn, hg, hph, hcso, hcs, hph', hno⟩ := id hs0
  haveI : OvlOK c := hno
  have hsc := sortCtx_of_allCEx hok hsr (OvlOK.ovlCase hno)
  have hD := defOK hIΓ
  obtain ⟨-, -, -, hensS, hrhss, hexnd, hexs, -, hokQ, -, hbdQ⟩ := Model.ruleSorted_partsPP hs
  have hlt : ∀ i ∈ r.exs, i < r.vars.length := fun i hi => (hexs i hi).1
  let vs := canonVars c r.vars
  have hfixed : ∀ i, i ∈ (List.range r.vars.length).filter (fun i => !r.exs.contains i) ↔
      i < r.vars.length ∧ i ∉ r.exs := fun i => by simp
  rw [famEx_eqPPx hlt] at hm
  unfold KoreAML.denB at hm
  generalize htbl : KoreAML.tableOf [] _ = tbl at hm
  -- every variable of the rule has its key in the table
  have hkeys : ∀ i < r.vars.length, canonKey c r.vars i ∈ tbl := by
    intro i hi
    rw [← htbl]
    unfold KoreAML.tableOf
    refine List.mem_eraseDups.mpr (List.mem_append_right _ ?_)
    by_cases hx : i ∈ r.exs
    · refine Model.varsOf_existsAll_bodyEx ?_ _
      refine Model.varsOf_and_mem (List.mem_append_right _ (List.mem_singleton_self _)) ?_
      exact varsOf_existsAll_binder _ (List.mem_map_of_mem (f := fun i => (vs.getD i default).kore) hx)
    · exact varsOf_existsAll_binder _
        (List.mem_map_of_mem (f := fun i => (vs.getD i default).kore) ((hfixed i).mpr ⟨hi, hx⟩))
  have hkQ : ∀ k ∈ KoreAML.varsOf (Cond.kore c (canonVars c r.vars) (srtOf c topCellSort) r.post), k ∈ tbl :=
    fun k hk => by
      rw [← htbl]
      unfold KoreAML.tableOf
      refine List.mem_eraseDups.mpr (List.mem_append_right _ (Model.varsOf_existsAll_bodyEx ?_ _))
      refine Model.varsOf_and_mem (List.mem_append_right _ (List.mem_singleton_self _)) ?_
      unfold Model.ruleRightBodyPP
      exact Model.varsOf_existsAll_bodyEx (Model.varsOf_condConj (fun φ hφ => List.mem_append_right _ hφ) hk) _
  have hsortB : ∀ i < r.vars.length,
      (vs.getD i default).kore.sort = KoreAML.srt (c.sortName (r.vars.getD i 0)) := fun i hi => by
    show ((canonVars c r.vars).getD i default).kore.sort = _
    rw [canonVars_getD c hi]; rfl
  have hinjB : ∀ {l : List Nat}, (∀ i ∈ l, i < r.vars.length) → l.Nodup →
      ((l.map fun i => (vs.getD i default).kore).map fun b => tbl.ev (KoreAML.evarKey b)).Nodup := by
    intro l hl hnd
    rw [List.map_map]
    refine List.pairwise_map.mpr (hnd.imp_of_mem fun {i j} hi hj hne he => hne ?_)
    exact canonKey_inj (hl i hi) (hl j hj) (ev_inj (hkeys i (hl i hi)) (hkeys j (hl j hj)) he)
  -- the binders of the variables other than the existential ones
  obtain ⟨e', -, hguard1, hb⟩ := existsAll_elim hD _ e _
    (hinjB (fun i hi => ((hfixed i).mp hi).1) (List.nodup_range.filter _))
    (fun b hb => by obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb; exact ⟨_, hsortB i ((hfixed i).mp hi).1⟩) hm
  rw [interp_and (by simp)] at hb
  have hinner := hb _ (List.mem_append_right _ (List.mem_singleton_self _))
  -- the binders of the existential variables
  obtain ⟨e'', hoff, hguard2, hbody⟩ := existsAll_elim hD (Model.ruleExBinders c r) e' _
    (hinjB hlt hexnd) (fun b hb => by obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb; exact ⟨_, hsortB i (hlt i hi)⟩)
    hinner
  unfold Model.ruleRightBodyPP at hbody
  rw [interp_and (by simp)] at hbody
  have hyR := hbody (Term.kore c vs r.rhs) (List.mem_append_left _ (List.mem_cons_self ..))
  have hensR := hbody (reqPat (srtOf c topCellSort) (r.ens.map (Term.kore c vs)))
    (List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
  have hpostR : ∀ φ ∈ Cond.conj c vs (srtOf c topCellSort) r.post,
      (KoreAML.tr ⟨tbl, []⟩ φ).interpret I e'' (elemOf c I y.val) :=
    fun φ hφ => hbody φ (List.mem_append_right _ hφ)
  -- off the existential variables, e'' is e'
  have hoffE : ∀ i < r.vars.length, i ∉ r.exs →
      e''.evalEvar (tbl.ev (keyAt vs i)) = e'.evalEvar (tbl.ev (keyAt vs i)) := by
    intro i hi hx
    refine hoff _ fun b hb he => ?_
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hb
    have := canonKey_inj hi (hlt j hj) (ev_inj (hkeys i hi) (hkeys j (hlt j hj)) he)
    exact hx (this ▸ hj)
  -- the variables other than the existential ones are the elements of their values under σ
  have hfix : ∀ i < r.vars.length, i ∉ r.exs → ∃ g, σ.lookup i = some g ∧ c.sortOf g = some (r.vars.getD i 0) ∧
      elemOf c I g = e''.evalEvar (tbl.ev (keyAt vs i)) := by
    intro i hi hx
    have hsi : r.vars[i]? = some (r.vars.getD i 0) := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; rfl
    obtain ⟨g, hg', hgs⟩ := hσ i _ hsi
    refine ⟨g, hg', hgs, ?_⟩
    have hvi : (canonVars c r.vars)[i]? = some ((canonVars c r.vars)[i]'(by rw [canonVars_length]; exact hi)) :=
      List.getElem?_eq_getElem _
    have hpm : Kore.Pattern.equals (srtOf c (r.vars.getD i 0)) (srtOf c topCellSort)
        (.var (.evar ((canonVars c r.vars)[i]'(by rw [canonVars_length]; exact hi)).kore)) (g.kore c) ∈
        fixK c r σ ((List.range r.vars.length).filter fun i => !r.exs.contains i) := by
      unfold fixK
      refine List.mem_filterMap.mpr ⟨i, (hfixed i).mpr ⟨hi, hx⟩, ?_⟩
      simp only [hvi, hsi, hg']
    have hx' := ((fixEq_iff hIΓ (sortOf_numbered_ofCEx hs0 (sortsNumbered_of_coreEx h) (Semantics.coreOKEx_ovls h) hgs)
      hgs _).mp (hb _ (List.mem_append_left _ hpm))).2
    rw [hoffE i hi hx]
    show elemOf c I g = e'.evalEvar (tbl.ev (KoreAML.evarKey ((canonVars c r.vars).getD i default).kore))
    rw [List.getD_eq_getElem?_getD, hvi, Option.getD_some, hx']
  -- every variable's element is in its sort
  have hin : ∀ i < r.vars.length, InS I (c.sortName (r.vars.getD i 0)) (e''.evalEvar (tbl.ev (keyAt vs i))) := by
    intro i hi
    by_cases hx : i ∈ r.exs
    · exact hguard2 _ (List.mem_map_of_mem (f := fun i => (vs.getD i default).kore) hx) _ (hsortB i hi)
    · rw [hoffE i hi hx]
      exact hguard1 _ (List.mem_map_of_mem (f := fun i => (vs.getD i default).kore) ((hfixed i).mpr ⟨hi, hx⟩)) _
        (hsortB i hi)
  -- every variable is the element of a value of its sort: an existential one by arm A or B
  have hopens : ∀ i ∈ r.opens, (occsUnder c H r.rhs).contains i = true ∨
      (r.vars[i]?.map c.confined).getD false = true ∨ r.condVars.contains i = true := by
    intro i hi
    rcases Semantics.rulePlainHeldH_opens hp i hi with (hA | hB | hM) | ⟨hC, -⟩
    · exact Or.inl hA
    · exact Or.inr (Or.inl hB)
    · exact Or.inr (Or.inr (List.contains_iff_mem.mpr
        (List.mem_append_right _ (memHeldH_condVar r.vars.length hM).2)))
    · exact Or.inr (Or.inr (List.contains_iff_mem.mpr hC))
  have hwit : ∀ i < r.vars.length, Witnessed c I tbl vs r.vars e'' i := by
    intro i hi
    by_cases hx : i ∈ r.exs
    · have hop : i ∈ r.opens := by
        simp only [Rule.opens, List.mem_filter, List.mem_range]
        exact ⟨hi, by simpa using (hexs i hx).2.1⟩
      rcases hopens i hop with hA | hB | hC
      · exact occsUnder_witnessed hIΓ hg hsc.trans hnn.1 (canonVars_length c r.vars) hin fns_headsOK hback hrhss
          y.property hyR i (List.contains_iff_mem.mp hA)
      · obtain ⟨s, hvs⟩ : ∃ s, r.vars[i]? = some s := ⟨_, List.getElem?_eq_getElem hi⟩
        rw [hvs] at hB
        have hcs' : c.confined s = true := hB
        have hrc' := hrc (List.any_eq_true.mpr ⟨i, hx, by rw [hvs]; exact hB⟩)
        have hin' := hin i hi
        rw [List.getD_eq_getElem?_getD, hvs, Option.getD_some] at hin'
        obtain ⟨v, hv, hden⟩ := confined_valueCEx h hrc' hI hcs' e'' _ ((inS_iff e'').mpr hin')
        have hel := ((elemOf_spec hIΓ hv e'').1 _).mpr rfl
        exact witnessed_of hvs hv ((hden _).mp hel)
      · exact absurd (List.contains_iff_mem.mp hC) (hexs i hx).2.2
    · obtain ⟨g, -, hgs, hge⟩ := hfix i hi hx
      exact ⟨g, hgs, hge⟩
  -- the substitution: the valuation's on the rule's variables, σ beyond them
  let σ₀ := substOf c I tbl vs r.vars e''
  obtain ⟨hσ₀, hag₀⟩ := substOf_ok hIΓ hg hsc.trans (canonVars_length c r.vars) hwit
  have hkeys₀ : ∀ i, i ∈ σ₀.map (·.1) ↔ i < r.vars.length := fun i => by simp [σ₀, substOf]
  let σ' := σ₀ ++ σ
  have hlk : ∀ i < r.vars.length, σ'.lookup i = σ₀.lookup i := fun i hi =>
    lookup_append_of_mem σ₀ σ ((hkeys₀ i).mpr hi)
  have hσ' : c.WellSorted r.vars σ' := fun i s hi => by
    rw [hlk i (List.getElem?_eq_some_iff.mp hi).1]; exact hσ₀ i s hi
  have hag' : Agrees c I tbl vs σ' e'' := fun i v hi hv => by
    rw [hlk i (by rw [canonVars_length] at hi; exact hi)] at hv
    exact hag₀ i v hi hv
  have hagree : ∀ i, ¬ i ∈ r.exs → σ'.lookup i = σ.lookup i := by
    intro i hx
    by_cases hi : i < r.vars.length
    · rw [hlk i hi]
      obtain ⟨g, hg', hgs, hge⟩ := hfix i hi hx
      rw [hg']
      exact substOf_var hIΓ hg hsc.trans hnn.1 (canonVars_length c r.vars) hin
        (List.getElem?_eq_getElem hi)
        (by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi] at hgs; exact hgs) hge
    · exact lookup_append_of_not_mem σ₀ σ (fun hm' => hi ((hkeys₀ i).mp hm'))
  -- the `ensures` holds, so it evaluates to `true`
  have hensT : ∀ t, r.ens = some t → EvalTerm c σ' t (some (bool true)) := by
    intro t ht
    have hq := hensR
    rw [ht] at hq
    exact evalTrue_of_modelSSx h hft hI hcw hσ' hag' (hensS t ht) hq
  -- the right side evaluates to a value whose element is y's: y
  obtain ⟨v, hv⟩ := Model.evalTerm_totalCl hsc hno hft fns_headsOK hσ' hrhss
  have hbR := (HoldsShape.termSoundEx h hI hcw hv hσ' (canonVars_length c r.vars) hag' hrhss _).mp hyR
  cases v with
  | none => exact hbR.elim
  | some yv =>
    have hyv := EvalTerm.sorted hsc hv fns_headsOK hσ' hrhss rfl
    have h1 : (den c yv).interpret I e (elemOf c I y.val) := ((den_closed c yv).interp e'' e _).mp hbR
    have h2 : elemOf c I y.val = elemOf c I yv := ((elemOf_spec hIΓ hyv e).1 _).mp h1
    have hyy : y.val = yv := values_apart hIΓ hg hsc.trans (apartSort_of_sorted hg y.property) y.property hyv h2
    rw [← hyy] at hv
    exact ⟨σ', hagree, hσ', hv, hensT,
      holds_of_conjPPFv h hft hI hcw hokQ hbdQ hrcQ hσ' hag' hkeys hkQ (elemOf_top hIΓ y tbl e'') hpostR⟩

/-- **An element of an open family is a successor's**, in a model of `Γc` of a semantics
`coreOKEx` accepts, for a rule with `ruleSorted` whose open variables are of confined sorts,
whatever its predicates: m in `famOpen c r σ` gives a configuration y whose pattern holds m and a σ'
that is σ on the left side, with every premise of `StepBy c r σ' x y` but the rule's membership and
the competitors, `Holds … pre true` and `Holds … post true` included. A binder in a predicate asks
`readsConfined`. -/
theorem famOpen_stepPPCEx (h : c.coreOKEx = true) (hft : FnTerminates c) (hI : I ⊧ᴵP Γc c)
    (hcw : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, cl.needsWitness c = true → cl.CondDecided c) {r : Rule}
    (hs : c.ruleSorted r = true)
    (hcf : ∀ i ∈ r.opens, (r.vars[i]?.map c.confined).getD false = true)
    (hrc : r.opens.any (fun i => (r.vars[i]?.map c.confined).getD false) = true → c.readsConfined = true)
    (hrcP : hasBinder r.pre = true → c.readsConfined = true)
    (hrcQ : hasBinder r.post = true → c.readsConfined = true)
    {x : Config c} {σ : Subst} (hσ : c.WellSortedAt r.vars (varOccs r.lhs) σ) (hmatch : PatVal c σ r.lhs x.val)
    (e : Valuation M) (m : M) (hm : (famOpen c r σ).interpret I e m) :
    ∃ (y : Config c) (σ' : Subst), (∀ i ∈ varOccs r.lhs, σ'.lookup i = σ.lookup i) ∧
      c.WellSorted r.vars σ' ∧ PatVal c σ' r.lhs x.val ∧ (∀ t, r.req = some t → EvalTerm c σ' t (some (bool true))) ∧
      Holds c r.vars.length σ' r.pre true ∧ EvalTerm c σ' r.rhs (some y.val) ∧
      (∀ t, r.ens = some t → EvalTerm c σ' t (some (bool true))) ∧ Holds c r.vars.length σ' r.post true ∧
      (den c y.val).interpret I e m := by
  have hIΓ : I ⊧ᴵP Γ c := fun φ hφ => hI φ (Or.inl hφ)
  have hs0 := hypSoundEx_of_coreEx h
  obtain ⟨hok, hsr, hnn, hg, hph, hcso, hcs, hph', hno⟩ := id hs0
  haveI : OvlOK c := hno
  have hsc := sortCtx_of_allCEx hok hsr (OvlOK.ovlCase hno)
  have hD := defOK hIΓ
  obtain ⟨hlhs, -, hreqs, hensS, hrhss, hexnd, hexs, hokP, hokQ, hbdP, hbdQ⟩ := Model.ruleSorted_partsPP hs
  have hlt : ∀ i ∈ r.exs, i < r.vars.length := fun i hi => (hexs i hi).1
  let vs := canonVars c r.vars
  have hfixed : ∀ i, i ∈ (List.range r.vars.length).filter (fun i => !r.exs.contains i) ↔
      i < r.vars.length ∧ i ∉ r.exs := fun i => by simp
  -- the left side's and the `requires`' variables are not existential
  have hnxL : ∀ i ∈ varOccs r.lhs, i < r.vars.length ∧ i ∉ r.exs := fun i hi =>
    ⟨varOccs_lt r.lhs hlhs i hi, fun hx => (hexs i hx).2.1 hi⟩
  have hnxQ : ∀ t, r.req = some t → ∀ i ∈ varOccs t, i < r.vars.length ∧ i ∉ r.exs := fun t ht i hi =>
    ⟨varOccs_lt t (hreqs t ht) i hi, fun hx => (hexs i hx).2.2 (List.mem_append_left _ (by rw [ht]; exact hi))⟩
  have hnxP : ∀ i ∈ varOccsCond r.vars.length r.pre, i < r.vars.length ∧ i ∉ r.exs := fun i hi =>
    ⟨varOccsCond_lt_twoT r.pre hokP i hi, fun hx => (hexs i hx).2.2 (List.mem_append_right _ hi)⟩
  rw [famOpen_eqPP hlt σ] at hm
  unfold KoreAML.denB at hm
  obtain ⟨hkeys, hkP, hkQ⟩ := famOpen_keysPP (c := c) (r := r) (σ := σ)
  generalize KoreAML.tableOf [] (famOpenPatPP c r σ) = tbl at hm hkeys hkP hkQ
  unfold famOpenPatPP at hm
  have hsortB : ∀ i < r.vars.length,
      (vs.getD i default).kore.sort = KoreAML.srt (c.sortName (r.vars.getD i 0)) := fun i hi => by
    show ((canonVars c r.vars).getD i default).kore.sort = _
    rw [canonVars_getD c hi]; rfl
  have hinjB : ∀ {l : List Nat}, (∀ i ∈ l, i < r.vars.length) → l.Nodup →
      ((l.map fun i => (vs.getD i default).kore).map fun b => tbl.ev (KoreAML.evarKey b)).Nodup := by
    intro l hl hnd
    rw [List.map_map]
    refine List.pairwise_map.mpr (hnd.imp_of_mem fun {i j} hi hj hne he => hne ?_)
    exact canonKey_inj (hl i hi) (hl j hj) (ev_inj (hkeys i (hl i hi)) (hkeys j (hl j hj)) he)
  -- the binders of the variables other than the existential ones
  obtain ⟨e', -, hguard1, hb⟩ := existsAll_elim hD _ e m
    (hinjB (fun i hi => ((hfixed i).mp hi).1) (List.nodup_range.filter _))
    (fun b hb => by obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb; exact ⟨_, hsortB i ((hfixed i).mp hi).1⟩) hm
  rw [interp_and (by simp)] at hb
  have hreqm := hb _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (List.mem_singleton_self _))))
  have hprem : ∀ φ ∈ Cond.conj c vs (srtOf c topCellSort) r.pre, (KoreAML.tr ⟨tbl, []⟩ φ).interpret I e' m :=
    fun φ hφ => hb φ (List.mem_append_left _ (List.mem_append_right _ hφ))
  have hinner := hb _ (List.mem_append_right _ (List.mem_singleton_self _))
  -- the binders of the existential variables
  obtain ⟨e'', hoff, hguard2, hbody⟩ := existsAll_elim hD (Model.ruleExBinders c r) e' m
    (hinjB hlt hexnd) (fun b hb => by obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb; exact ⟨_, hsortB i (hlt i hi)⟩)
    hinner
  unfold Model.ruleRightBodyPP at hbody
  rw [interp_and (by simp)] at hbody
  have hyR := hbody (Term.kore c vs r.rhs) (List.mem_append_left _ (List.mem_cons_self ..))
  have hensR := hbody (reqPat (srtOf c topCellSort) (r.ens.map (Term.kore c vs)))
    (List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
  have hpostR : ∀ φ ∈ Cond.conj c vs (srtOf c topCellSort) r.post, (KoreAML.tr ⟨tbl, []⟩ φ).interpret I e'' m :=
    fun φ hφ => hbody φ (List.mem_append_right _ hφ)
  -- off the existential variables, e'' is e'
  have hoffE : ∀ i < r.vars.length, i ∉ r.exs →
      e''.evalEvar (tbl.ev (keyAt vs i)) = e'.evalEvar (tbl.ev (keyAt vs i)) := by
    intro i hi hx
    refine hoff _ fun b hb he => ?_
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hb
    have := canonKey_inj hi (hlt j hj) (ev_inj (hkeys i hi) (hkeys j (hlt j hj)) he)
    exact hx (this ▸ hj)
  -- every variable's element is in its sort
  have hin : ∀ i < r.vars.length, InS I (c.sortName (r.vars.getD i 0)) (e''.evalEvar (tbl.ev (keyAt vs i))) := by
    intro i hi
    by_cases hx : i ∈ r.exs
    · exact hguard2 _ (List.mem_map_of_mem (f := fun i => (vs.getD i default).kore) hx) _ (hsortB i hi)
    · rw [hoffE i hi hx]
      exact hguard1 _ (List.mem_map_of_mem (f := fun i => (vs.getD i default).kore) ((hfixed i).mpr ⟨hi, hx⟩)) _
        (hsortB i hi)
  -- the left side's variables are the elements of their values under σ
  have hfix : ∀ i ∈ varOccs r.lhs, ∃ g, σ.lookup i = some g ∧ c.sortOf g = some (r.vars.getD i 0) ∧
      elemOf c I g = e''.evalEvar (tbl.ev (keyAt vs i)) := by
    intro i hiL
    obtain ⟨hi, hx⟩ := hnxL i hiL
    have hsi : r.vars[i]? = some (r.vars.getD i 0) := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; rfl
    obtain ⟨g, hg', hgs⟩ := hσ i hiL _ hsi
    refine ⟨g, hg', hgs, ?_⟩
    have hvi : (canonVars c r.vars)[i]? = some ((canonVars c r.vars)[i]'(by rw [canonVars_length]; exact hi)) :=
      List.getElem?_eq_getElem _
    have hpm : Kore.Pattern.equals (srtOf c (r.vars.getD i 0)) (srtOf c topCellSort)
        (.var (.evar ((canonVars c r.vars)[i]'(by rw [canonVars_length]; exact hi)).kore)) (g.kore c) ∈
        fixK c r σ (varOccs r.lhs) := by
      unfold fixK
      refine List.mem_filterMap.mpr ⟨i, hiL, ?_⟩
      simp only [hvi, hsi, hg']
    have hx' := ((fixEq_iff hIΓ (sortOf_numbered_ofCEx hs0 (sortsNumbered_of_coreEx h) (Semantics.coreOKEx_ovls h) hgs)
      hgs m).mp (hb _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hpm))))).2
    rw [hoffE i hi hx]
    show elemOf c I g = e'.evalEvar (tbl.ev (KoreAML.evarKey ((canonVars c r.vars).getD i default).kore))
    rw [List.getD_eq_getElem?_getD, hvi, Option.getD_some, hx']
  -- every variable is the element of a value of its sort: one outside the left side is open, so of
  -- a confined sort
  have hwit : ∀ i < r.vars.length, Witnessed c I tbl vs r.vars e'' i := by
    intro i hi
    by_cases hiL : i ∈ varOccs r.lhs
    · obtain ⟨g, -, hgs, hge⟩ := hfix i hiL
      exact ⟨g, hgs, hge⟩
    · have hop : i ∈ r.opens := by
        simp only [Rule.opens, List.mem_filter, List.mem_range]; exact ⟨hi, by simpa using hiL⟩
      obtain ⟨s, hvs⟩ : ∃ s, r.vars[i]? = some s := ⟨_, List.getElem?_eq_getElem hi⟩
      have hB := hcf i hop
      rw [hvs] at hB
      have hcs' : c.confined s = true := hB
      have hrc' := hrc (List.any_eq_true.mpr ⟨i, hop, by rw [hvs]; exact hB⟩)
      have hin' := hin i hi
      rw [List.getD_eq_getElem?_getD, hvs, Option.getD_some] at hin'
      obtain ⟨v, hv, hden⟩ := confined_valueCEx h hrc' hI hcs' e'' _ ((inS_iff e'').mpr hin')
      have hel := ((elemOf_spec hIΓ hv e'').1 _).mpr rfl
      exact witnessed_of hvs hv ((hden _).mp hel)
  let σ' := substOf c I tbl vs r.vars e''
  obtain ⟨hσ', hag⟩ := substOf_ok hIΓ hg hsc.trans (canonVars_length c r.vars) hwit
  -- σ' is σ on the left side's variables
  have hagL : ∀ i ∈ varOccs r.lhs, σ'.lookup i = σ.lookup i := by
    intro i hiL
    obtain ⟨g, hg', hgs, hge⟩ := hfix i hiL
    have hi := (hnxL i hiL).1
    rw [hg']
    exact substOf_var hIΓ hg hsc.trans hnn.1 (canonVars_length c r.vars) hin
      (List.getElem?_eq_getElem hi) (by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi] at hgs; exact hgs)
      hge
  have hmatch' : PatVal c σ' r.lhs x.val := PatVal.congr_lookup hmatch hagL
  -- the conditions hold, so they evaluate to `true`
  have hreqR : (KoreAML.tr ⟨tbl, []⟩ (reqPat (srtOf c topCellSort)
      (r.req.map (Term.kore c (canonVars c r.vars))))).interpret I e'' m :=
    reqPat_transferSplit hIΓ (fun t ht i hi => (hoffE i (hnxQ t ht i hi).1 (hnxQ t ht i hi).2).symm) hreqm
      (reqPat_inhSplit hIΓ hreqm tbl e'')
  have hreqT : ∀ t, r.req = some t → EvalTerm c σ' t (some (bool true)) := by
    intro t ht
    have hq := hreqR
    rw [ht] at hq
    exact evalTrue_of_modelSSx h hft hI hcw hσ' hag (hreqs t ht) hq
  have hensT : ∀ t, r.ens = some t → EvalTerm c σ' t (some (bool true)) := by
    intro t ht
    have hq := hensR
    rw [ht] at hq
    exact evalTrue_of_modelSSx h hft hI hcw hσ' hag (hensS t ht) hq
  -- `pre` and `post` hold at m, an element of the configuration sort: they hold at σ'
  have hinC : (KoreAML.inhOf (KoreAML.trSort tbl (srtOf c topCellSort))).interpret I e'' m :=
    reqPat_inhSplit hIΓ hreqm tbl e''
  have hpreR : ∀ φ ∈ Cond.conj c vs (srtOf c topCellSort) r.pre, (KoreAML.tr ⟨tbl, []⟩ φ).interpret I e'' m :=
    conj_congrPP hD hokP hkP (fun i hi => hkeys i (hnxP i hi).1)
      (fun i hi => (hoffE i (hnxP i hi).1 (hnxP i hi).2).symm) hprem
  have hpreT : Holds c r.vars.length σ' r.pre true :=
    holds_of_conjPPFv h hft hI hcw hokP hbdP hrcP hσ' hag hkeys hkP hinC hpreR
  have hpostT : Holds c r.vars.length σ' r.post true :=
    holds_of_conjPPFv h hft hI hcw hokQ hbdQ hrcQ hσ' hag hkeys hkQ hinC hpostR
  -- the right side evaluates to a value whose element is m
  obtain ⟨v, hv⟩ := Model.evalTerm_totalCl hsc hno hft fns_headsOK hσ' hrhss
  have hbR := (HoldsShape.termSoundEx h hI hcw hv hσ' (canonVars_length c r.vars) hag hrhss m).mp hyR
  cases v with
  | none => exact hbR.elim
  | some yv =>
    exact ⟨⟨yv, EvalTerm.sorted hsc hv fns_headsOK hσ' hrhss rfl⟩, σ', hagL, hσ', hmatch', hreqT, hpreT, hv,
      hensT, hpostT, ((den_closed c yv).interp e'' e m).mp hbR⟩

end

end Faithful

open ML Faithful Faithful.Model

/-- **A value in the instances of an application is a step by the rule**, for a semantics
`coreOKEx` accepts whose rules have `ruleSorted` and `rulePlainHeldH` (a `pre` and a `post`
allowed), under `HeldBackAll`: `famEx_values`'s conclusion in the model of
`Faithful.Model.consistent_of_coreEx`. -/
theorem famEx_values_heldCEx (c : Semantics) {H : Sym → Bool} (h : c.coreOKEx = true) (hf : FnHyp c)
    (hrules : ∀ r ∈ c.rules, c.ruleSorted r = true ∧ c.rulePlainHeldH H r = true) (hbk : HeldBackAll c H)
    (x y : Config c) (r : Rule) (σ : Subst) (hs : ∃ y₀, StepBy c r σ x y₀)
    (hy : Γc c ⊧ (den c y.val ⇒ famEx c r σ)) :
    ∃ σ', (∀ i, ¬ i ∈ r.exs → σ'.lookup i = σ.lookup i) ∧ StepBy c r σ' x y := by
  obtain ⟨y₀, hs₀⟩ := hs
  obtain ⟨M, hinh, I, hI⟩ := Faithful.Model.consistent_of_coreEx h (fnModel_of_fnHypCEx h hf).1
    (fnModel_of_fnHypCEx h hf).2 (clausePreDecided_of_fnHypCEx h hf) (clausePostDecided_of_fnHypCEx h hf) hf.2.2.2.2.2
  haveI := hinh
  have hIc : I ⊧ᴵP Γc c := fun φ hφ => hI φ (Or.inl hφ)
  have hIΓ : I ⊧ᴵP Γ c := fun φ hφ => hIc φ (Or.inl hφ)
  have h1 := hy hIc KoreAML.val0 (elemOf c I y.val)
  rw [interpret_impl] at h1
  have h2 := h1 (((elemOf_spec hIΓ y.property _).1 _).mpr rfl)
  obtain ⟨hsr, hpr⟩ := hrules r hs₀.mem
  obtain ⟨-, -, -, -, -, -, hexs, -, -, -, -⟩ := ruleSorted_partsPP hsr
  have hrc : r.exs.any (fun i => (r.vars[i]?.map c.confined).getD false) = true → c.readsConfined = true :=
      fun hany => by
    obtain ⟨i, hi, -⟩ := List.any_eq_true.mp hany
    have hop : i ∈ r.opens := by
      simp only [Rule.opens, List.mem_filter, List.mem_range]
      exact ⟨(hexs i hi).1, by simpa using (hexs i hi).2.1⟩
    simp only [Semantics.readsConfined, Bool.or_eq_true, List.any_eq_true]
    exact Or.inl ⟨r, hs₀.mem, by simp [List.ne_nil_of_mem hop]⟩
  obtain ⟨σ', hag, hσ', hev, hens, hpost⟩ :=
    famEx_value_heldCEx h hf.1 hIc (hbk I hIc) hf.2.2.2.2.1.2 hsr hpr hrc (readsConfined_of_post hs₀.mem) hs₀.hσ y _ h2
  refine ⟨σ', hag, hs₀.mem, hσ', PatVal.congr_lookup hs₀.hmatch fun j hj => hag j fun hx => (hexs j hx).2.1 hj,
    fun t ht => Exec.EvalTerm.congr (hs₀.hreq t ht) fun j hj => (hag j fun hx => (hexs j hx).2.2 ?_).symm,
    hs₀.hpre.congr_NI fun j hj => (hag j fun hx => (hexs j hx).2.2 (List.mem_append_right _ hj)).symm,
    hev, hens, hpost, hs₀.hprio⟩
  simp only [Rule.condVars, ht, Option.map_some, Option.getD_some, List.mem_append]
  exact Or.inl hj

/-- **The outcomes of a match are among any values that hold its steps**, for a semantics
`coreOKEx` accepts and a rule with `ruleSorted`: `famOpen_values`'s conclusion. -/
theorem famOpen_values_ppCEx (c : Semantics) (h : c.coreOKEx = true) (hf : FnHyp c)
    (x : Config c) (r : Rule) (hr : r ∈ c.rules) (hs : c.ruleSorted r = true)
    (σ : Subst) (hu : Unblocked c r σ x.val)
    (hcf : ∀ i ∈ r.opens, (r.vars[i]?.map c.confined).getD false = true)
    (ys : List GroundTerm)
    (hys : ∀ y : Config c, (∃ σ', (∀ i ∈ varOccs r.lhs, σ'.lookup i = σ.lookup i) ∧ StepBy c r σ' x y) →
      y.val ∈ ys) :
    Γc c ⊧ (famOpen c r σ ⇒ KoreAML.disjList (ys.map (den c))) := by
  have hrc : r.opens.any (fun i => (r.vars[i]?.map c.confined).getD false) = true → c.readsConfined = true :=
      fun hany => by
    obtain ⟨i, hi, -⟩ := List.any_eq_true.mp hany
    simp only [Semantics.readsConfined, Bool.or_eq_true, List.any_eq_true]
    exact Or.inl ⟨r, hr, by simp [List.ne_nil_of_mem hi]⟩
  intro M _ I hI e m
  rw [interpret_impl]
  intro hm
  obtain ⟨hσat, hmatch, hprio⟩ := hu
  obtain ⟨y, σ', hagL, hσ', hm', hrq, hpr, hev, hen, hpo, hy⟩ :=
    famOpen_stepPPCEx h hf.1 hI hf.2.2.2.2.1.2 hs hcf hrc (readsConfined_of_pre hr) (readsConfined_of_post hr)
      hσat hmatch e m hm
  exact disjList_of_mem (List.mem_map_of_mem (hys y ⟨σ', hagL, ⟨hr, hσ', hm', hrq, hpr, hev, hen, hpo, hprio⟩⟩)) hy

/-- **A value in the instances of an application is a step by it**: `famEx_values`'s statement with
`coreOKEx` for `coreOK`. -/
theorem famEx_values_ce (c : Semantics) (h : c.coreOKEx = true) (hf : FnHyp c) (x y : Config c)
    (r : Rule) (σ : Subst) (hs : ∃ y₀, StepBy c r σ x y₀)
    (hy : Γc c ⊧ (den c y.val ⇒ famEx c r σ)) :
    ∃ σ', (∀ i, ¬ i ∈ r.exs → σ'.lookup i = σ.lookup i) ∧ StepBy c r σ' x y :=
  famEx_values_heldCEx c h hf (Semantics.ruleFactsHeld_of_coreEx h) (heldBackAll_holdsCEx h) x y r σ hs hy

/-- **The outcomes of a match are, in every model, among any values that hold its steps**:
`famOpen_values`'s statement with `coreOKEx` for `coreOK`. -/
theorem famOpen_values_ce (c : Semantics) (h : c.coreOKEx = true) (hf : FnHyp c)
    (x : Config c) (r : Rule) (hr : r ∈ c.rules) (σ : Subst) (hu : Unblocked c r σ x.val)
    (hcf : ∀ i ∈ r.opens, (r.vars[i]?.map c.confined).getD false = true)
    (ys : List GroundTerm)
    (hys : ∀ y : Config c, (∃ σ', (∀ i ∈ varOccs r.lhs, σ'.lookup i = σ.lookup i) ∧ StepBy c r σ' x y) →
      y.val ∈ ys) :
    Γc c ⊧ (famOpen c r σ ⇒ KoreAML.disjList (ys.map (den c))) :=
  famOpen_values_ppCEx c h hf x r hr (Semantics.ruleFactsHO1_of_coreEx h r hr).1 σ hu hcf ys hys

end KCore
