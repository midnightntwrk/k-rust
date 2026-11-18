/-
  KCore. A successor's valuation at values, in any model of `Γc c`, for a rule whose left side need
  not bind every variable.

  At a valuation of a rule's variables in their sorts where the element of a configuration x lies in
  the rule's left side and the element of a configuration y in its right side, the valuation gives
  the element of a value of its sort to each variable that is
  - held by the left side (`patVal_backC`),
  - held by the right side under constructors and injections only (arm A, `ctorOccs_witnessed` at y),
  - or of a confined sort (arm B, `confined_value`: every element of a confined sort is a value's,
    in a model of `Γc` of a definition that reads a confined sort)
  (`rule_witnessed`). Where every open variable passes arm A or B, the valuation's substitution
  gives every variable a value, agrees with the valuation, and the left side denotes x under it
  (`rule_subst_AB`).

  A translated term reads the valuation at its own variables only, through any table
  (`tr_kore_congr`, `tr_reqPat_congr`). So, with x's element also in `⌈req = true⌉` and y's in
  `⌈ens = true⌉`, a σ of values has every premise of `Step.rule` but the rule's membership and
  `hprio` (`rule_step_values`, and `stepBy_of_values` for a rule of the definition under `FnHyp`):
  - arms A and B: the valuation's own substitution (`rule_step_AB`);
  - arm C, a variable held by closed conditions no variable of which the left side, the right side
    or the `ensures` holds: `needsWitness` holds, so the conditions are decided. `Refuted` fails at
    the valuation, which satisfies `∃ō. ⌈req = true⌉` (`cond_not_refuted`); `Witnessed` gives the
    conditions' variables values, which the valuation takes in place of its own without changing
    what the left side, the right side or the `ensures` denote (`rule_step_C`).
  This file holds the valuations at values (`rule_witnessed`, `rule_subst_AB`, `rule_witnessed_all`)
  and `cond_not_refuted`; the step lemmas read the functions' clauses through `neg_of_coreCl` and
  are in OpenRuleStepCl.lean.
-/
import KcoreSpec.Confined
import KcoreSpec.RhsValues
import KcoreSpec.OpenStep
import KcoreSpec.FaithfulCompleteAt

set_option autoImplicit false

namespace KCore

/-- Arm A or B of `rulePlainOpen` for the variable i: held by the right side under constructors,
or of a confined sort. -/
def Rule.armAB (c : Semantics) (r : Rule) (i : Nat) : Bool :=
  (ctorOccs c r.rhs).contains i || (r.vars[i]?.map c.confined).getD false

namespace Faithful

open ML
open KoreAML (DefOK Inh IsSort Closed VarKey VarTable)

section
variable {c : Semantics} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}

/-- **A successor's valuation at the variables of arms A and B.** In a model of `Γc c`, at a
valuation of the variables of a well-sorted rule in their sorts where the element of x lies in the
rule's left side and the element of y in its right side, the valuation gives the element of a value
of its sort to each variable held by the left side, held by the right side under constructors only,
or of a confined sort (the last where the definition reads a confined sort). -/
theorem rule_witnessed (h : c.coreOK = true) (hI : I ⊧ᴵP Γc c) {r : Rule} (hs : c.ruleSorted r = true)
    {tbl : VarTable} {e : Valuation M}
    (hin : ∀ i < r.vars.length, InS I (c.sortName (r.vars.getD i 0))
      (e.evalEvar (tbl.ev (keyAt (canonVars c r.vars) i))))
    (x y : Config c)
    (hl : (KoreAML.tr ⟨tbl, []⟩ (Term.kore c (canonVars c r.vars) r.lhs)).interpret I e (elemOf c I x.val))
    (hy : (KoreAML.tr ⟨tbl, []⟩ (Term.kore c (canonVars c r.vars) r.rhs)).interpret I e (elemOf c I y.val))
    (i : Nat) (hi : i < r.vars.length)
    (harm : (varOccs r.lhs).contains i = true ∨ r.armAB c i = true)
    (hrc : (r.vars[i]?.map c.confined).getD false = true → c.readsConfined = true) :
    Witnessed c I tbl (canonVars c r.vars) r.vars e i := by
  obtain ⟨hok, hsr, hnn, hg, hph, hcso, hcs, hph', hno⟩ := hypSound_of_core h
  haveI : OvlOK c := hno
  have hsc := sortCtx_of_all hok hsr (OvlOK.ovlCase hno)
  have hIΓ : I ⊧ᴵP Γ c := fun φ hφ => hI φ (Or.inl hφ)
  obtain ⟨hlhs, -, -, hrhs⟩ := Semantics.ruleSorted_parts c hs
  rcases harm with hL | hAB
  · obtain ⟨-, hwit⟩ := patVal_backC hIΓ hph hcs hcso hg hsc.trans hnn.1 (canonVars_length c r.vars) hin
      (collPat_of_sorted hph' hlhs) (Semantics.ruleSorted_lhs_nf c hs) x.property hl
    exact hwit i (List.contains_iff_mem.mp hL)
  simp only [Rule.armAB, Bool.or_eq_true] at hAB
  rcases hAB with hA | hB
  · exact ctorOccs_witnessed hIΓ hg hsc.trans hnn.1 (canonVars_length c r.vars) hin fns_headsOK hrhs y.property hy
      i (List.contains_iff_mem.mp hA)
  · obtain ⟨s, hvs⟩ : ∃ s, r.vars[i]? = some s := ⟨_, List.getElem?_eq_getElem hi⟩
    rw [hvs] at hB
    have hcs' : c.confined s = true := hB
    have hrc' := hrc (by rw [hvs]; exact hB)
    have hin' := hin i hi
    rw [List.getD_eq_getElem?_getD, hvs, Option.getD_some] at hin'
    obtain ⟨v, hv, hden⟩ := confined_value h hrc' hI hcs' e _ ((inS_iff e).mpr hin')
    have hel := ((elemOf_spec hIΓ hv e).1 _).mpr rfl
    exact witnessed_of hvs hv ((hden _).mp hel)

/-- **The valuation's substitution, where every open variable passes arm A or B**: it gives every
variable a value of its sort, agrees with the valuation, and the left side denotes x under it. -/
theorem rule_subst_AB (h : c.coreOK = true) (hI : I ⊧ᴵP Γc c) {r : Rule} (hs : c.ruleSorted r = true)
    (hAB : r.opens.all (r.armAB c) = true)
    (hrc : r.opens.any (fun i => (r.vars[i]?.map c.confined).getD false) = true → c.readsConfined = true)
    {tbl : VarTable} {e : Valuation M}
    (hin : ∀ i < r.vars.length, InS I (c.sortName (r.vars.getD i 0))
      (e.evalEvar (tbl.ev (keyAt (canonVars c r.vars) i))))
    (x y : Config c)
    (hl : (KoreAML.tr ⟨tbl, []⟩ (Term.kore c (canonVars c r.vars) r.lhs)).interpret I e (elemOf c I x.val))
    (hy : (KoreAML.tr ⟨tbl, []⟩ (Term.kore c (canonVars c r.vars) r.rhs)).interpret I e (elemOf c I y.val)) :
    let σ := substOf c I tbl (canonVars c r.vars) r.vars e
    c.WellSorted r.vars σ ∧ Agrees c I tbl (canonVars c r.vars) σ e ∧ PatVal c σ r.lhs x.val := by
  obtain ⟨hok, hsr, hnn, hg, hph, hcso, hcs, hph', hno⟩ := hypSound_of_core h
  haveI : OvlOK c := hno
  have hsc := sortCtx_of_all hok hsr (OvlOK.ovlCase hno)
  have hIΓ : I ⊧ᴵP Γ c := fun φ hφ => hI φ (Or.inl hφ)
  obtain ⟨hlhs, -, -, -⟩ := Semantics.ruleSorted_parts c hs
  obtain ⟨hmatch, hwitL⟩ := patVal_backC hIΓ hph hcs hcso hg hsc.trans hnn.1 (canonVars_length c r.vars) hin
    (collPat_of_sorted hph' hlhs) (Semantics.ruleSorted_lhs_nf c hs) x.property hl
  have hwit : ∀ i < r.vars.length, Witnessed c I tbl (canonVars c r.vars) r.vars e i := by
    intro i hi
    by_cases hL : (varOccs r.lhs).contains i = true
    · exact hwitL i (List.contains_iff_mem.mp hL)
    · have hop : i ∈ r.opens := by
        simp only [Rule.opens, List.mem_filter, List.mem_range]
        exact ⟨hi, by simpa using hL⟩
      exact rule_witnessed h hI hs hin x y hl hy i hi (Or.inr (List.all_eq_true.mp hAB i hop))
        (fun hc => hrc (List.any_eq_true.mpr ⟨i, hop, hc⟩))
  obtain ⟨hσ, hag⟩ := substOf_ok hIΓ hg hsc.trans (canonVars_length c r.vars) hwit
  exact ⟨hσ, hag, hmatch⟩

end


/-! ## A translated term reads the valuation at its own variables only -/

section
variable {c : Semantics} {M : Type} {I : Interpretation KoreAML.Sym M}

theorem kore_var_eq (vs : List KoreAML.Var) (i : Nat) : Term.kore c vs (.var i) = KoreAML.varAt vs i := by
  rw [Term.kore]

mutual
  /-- **A translated term, under two tables**: where two valuations give each variable the term
  holds one element, through the two tables, the translations denote one set. With one table, the
  translation does not read the valuation off the term's variables. -/
  theorem tr_kore_congr {vs : List KoreAML.Var} {tbl tbl' : VarTable} {e e' : Valuation M} :
      ∀ (t : Term), (∀ i ∈ varOccs t, e.evalEvar (tbl.ev (keyAt vs i)) = e'.evalEvar (tbl'.ev (keyAt vs i))) →
      ∀ m, (KoreAML.tr ⟨tbl, []⟩ (Term.kore c vs t)).interpret I e m ↔
        (KoreAML.tr ⟨tbl', []⟩ (Term.kore c vs t)).interpret I e' m
    | .var i, h, m => by
      rw [tr_var, tr_var]
      exact iff_of_eq (congrArg (m = ·) (h i (by simp [varOccs])))
    | .dv s lit, _, m => by
      rw [Term.kore]; unfold srtOf
      rw [KoreAML.tr_dv, KoreAML.tr_dv]
      exact ((Closed.sym _).app (Closed.sym _)).interp e e' m
    | .app f ts, h, m => by
      rw [kore_app, tr_symApp, tr_symApp]
      exact trArgs_kore_congr ts _ _ (fun m => (symHead_closed f).interp e e' m)
        (fun i hi => h i (by rw [varOccs]; exact hi)) m
    | .inj a b t, h, m => by
      rw [Term.kore, KoreAML.tr_injP, KoreAML.tr_injP]
      exact injApp_congr (tr_kore_congr t (fun i hi => h i (by rw [varOccs]; exact hi))) m
    | .as t i, h, m => by
      rw [Term.kore, tr_and2, tr_and2, KoreAML.interp_sAnd, KoreAML.interp_sAnd, ← kore_var_eq]
      exact and_congr (tr_kore_congr t (fun j hj => h j (by rw [varOccs]; exact List.mem_append_left _ hj)) m)
        (by rw [tr_var (c := c), tr_var (c := c)]; exact iff_of_eq (congrArg (m = ·) (h i (by simp [varOccs]))))
    termination_by structural t => t
  theorem trArgs_kore_congr {vs : List KoreAML.Var} {tbl tbl' : VarTable} {e e' : Valuation M} :
      ∀ (ts : List Term) (acc acc' : KoreAML.P), (∀ m, acc.interpret I e m ↔ acc'.interpret I e' m) →
      (∀ i ∈ varOccsList ts, e.evalEvar (tbl.ev (keyAt vs i)) = e'.evalEvar (tbl'.ev (keyAt vs i))) →
      ∀ m, (KoreAML.trArgs ⟨tbl, []⟩ acc (Term.koreList c vs ts)).interpret I e m ↔
        (KoreAML.trArgs ⟨tbl', []⟩ acc' (Term.koreList c vs ts)).interpret I e' m
    | [], acc, acc', hacc, _, m => by
      rw [Term.koreList, KoreAML.trArgs_nil, KoreAML.trArgs_nil]; exact hacc m
    | t :: ts, acc, acc', hacc, h, m => by
      rw [Term.koreList, KoreAML.trArgs_cons, KoreAML.trArgs_cons]
      exact trArgs_kore_congr ts _ _
        (KoreAML.interp_app_congr hacc (tr_kore_congr t (fun i hi => h i (by
          rw [varOccsList]; exact List.mem_append_left _ hi))))
        (fun i hi => h i (by rw [varOccsList]; exact List.mem_append_right _ hi)) m
    termination_by structural ts => ts
end

/-- **`⌈t = true⌉` under two tables**, likewise. -/
theorem tr_reqPat_congr [Inhabited M] (hI : I ⊧ᴵP Γ c) [OvlOK c] {vs : List KoreAML.Var} {tbl tbl' : VarTable}
    {e e' : Valuation M} {t : Term}
    (h : ∀ i ∈ varOccs t, e.evalEvar (tbl.ev (keyAt vs i)) = e'.evalEvar (tbl'.ev (keyAt vs i))) (m : M) :
    (KoreAML.tr ⟨tbl, []⟩ (reqPat (srtOf c topCellSort) (some (Term.kore c vs t)))).interpret I e m ↔
      (KoreAML.tr ⟨tbl', []⟩ (reqPat (srtOf c topCellSort) (some (Term.kore c vs t)))).interpret I e' m := by
  have hD := defOK hI
  have hc := sat_sigItem hI (sig_ceilDef (c := c))
  obtain ⟨σC, hσC1, hσC2⟩ := sortSing hI (top_numbered (c := c))
  obtain ⟨σB, hσB1, hσB2⟩ := sortSing hI (bool_numbered (c := c))
  rw [sortName_bool] at hσB1
  simp only [reqPat]
  rw [KoreAML.tr, KoreAML.tr,
    KoreAML.interp_sEquals hD hc (by rw [trSort_srt]; exact hσB1) (by unfold srtOf; rw [trSort_srt]; exact hσC1)
      hσB2 hσC2,
    KoreAML.interp_sEquals hD hc (by rw [trSort_srt]; exact hσB1) (by unfold srtOf; rw [trSort_srt]; exact hσC1)
      hσB2 hσC2]
  refine and_congr Iff.rfl (forall_congr' fun a => imp_congr_right fun _ => ?_)
  rw [KoreAML.tr_dv, KoreAML.tr_dv]
  exact iff_congr (tr_kore_congr t h a) (((Closed.sym _).app (Closed.sym _)).interp e e' a)

end


/-! ## A successor's step, from a valuation that gives every variable a value -/

section
variable {c : Semantics} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}

/-- Every clause's exclusion is empty where it fails, in a model of `Γ`. -/
theorem neg_of_core (h : c.coreOK = true) (hbc : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, binds cl.vars.length (varOccsList cl.pats) = true) (hIΓ : I ⊧ᴵP Γ c) :
    ∀ fn ∈ c.allFns, ∀ cl ∈ fn.clauses, ClauseNeg c fn cl → ExclEmpty c I fn cl := by
  obtain ⟨hok, hsr, hnn, hg, hph, hcso, hcs, hph', hno⟩ := hypSound_of_core h
  haveI : OvlOK c := hno
  have hsc := sortCtx_of_all hok hsr (OvlOK.ovlCase hno)
  intro fn hfn cl hcl _
  obtain ⟨hp', hb', -⟩ := clause_ctx hok hbc hfn hcl
  exact fun hws _ hkeys hXkeys hRkey _ hX _ hR hσR hfail m =>
    exclusion_emptyC hIΓ hph hcs hcso hg hsc.trans hnn.1 (clause_preTop hok hfn hcl)
        (Semantics.pats_nf (OvlOK.hyp inferInstance hsc.trans) hfn hcl hp') hb' (collPats_of_sorted hph' hp') hws hkeys hXkeys
      hRkey hX hR hσR hfail m

/-- Each variable is held by the left side or open: where each open variable is given the element
of a value of its sort, so is every variable. -/
theorem rule_witnessed_all (h : c.coreOK = true) (hIΓ : I ⊧ᴵP Γ c) {r : Rule} (hs : c.ruleSorted r = true)
    {tbl : VarTable} {e : Valuation M}
    (hin : ∀ i < r.vars.length, InS I (c.sortName (r.vars.getD i 0))
      (e.evalEvar (tbl.ev (keyAt (canonVars c r.vars) i))))
    (x : Config c)
    (hl : (KoreAML.tr ⟨tbl, []⟩ (Term.kore c (canonVars c r.vars) r.lhs)).interpret I e (elemOf c I x.val))
    (hop : ∀ i ∈ r.opens, Witnessed c I tbl (canonVars c r.vars) r.vars e i) :
    ∀ i < r.vars.length, Witnessed c I tbl (canonVars c r.vars) r.vars e i := by
  obtain ⟨hok, hsr, hnn, hg, hph, hcso, hcs, hph', hno⟩ := hypSound_of_core h
  haveI : OvlOK c := hno
  have hsc := sortCtx_of_all hok hsr (OvlOK.ovlCase hno)
  obtain ⟨hlhs, -, -, -⟩ := Semantics.ruleSorted_parts c hs
  obtain ⟨-, hwitL⟩ := patVal_backC hIΓ hph hcs hcso hg hsc.trans hnn.1 (canonVars_length c r.vars) hin
    (collPat_of_sorted hph' hlhs) (Semantics.ruleSorted_lhs_nf c hs) x.property hl
  intro i hi
  by_cases hL : (varOccs r.lhs).contains i = true
  · exact hwitL i (List.contains_iff_mem.mp hL)
  · exact hop i (by simp only [Rule.opens, List.mem_filter, List.mem_range]; exact ⟨hi, by simpa using hL⟩)

end


/-! ## Case C: an open variable held by closed conditions only -/

section
variable {c : Semantics} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}

theorem filterMap_getElem?_of_lt {α : Type} [Inhabited α] (vs : List α) :
    ∀ (l : List Nat), (∀ i ∈ l, i < vs.length) → l.filterMap (vs[·]?) = l.map (vs.getD · default)
  | [], _ => rfl
  | i :: l, h => by
    have hi := h i (List.mem_cons_self ..)
    rw [List.filterMap_cons, List.getElem?_eq_getElem hi, List.map_cons,
      filterMap_getElem?_of_lt vs l (fun j hj => h j (List.mem_cons_of_mem _ hj)),
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]

theorem mem_varsOf_existsAll {S : Kore.KSort} {body : Kore.Pattern} :
    ∀ {bs : List Kore.EVar} {b : Kore.EVar}, b ∈ bs → KoreAML.evarKey b ∈ KoreAML.varsOf (KoreAML.existsAll S bs body)
  | b' :: bs, b, hb => by
    show KoreAML.evarKey b ∈ KoreAML.varsOf (.exist S b' (KoreAML.existsAll S bs body))
    rw [KoreAML.varsOf]
    rcases List.mem_cons.mp hb with rfl | hb
    · simp
    · exact List.mem_append_right _ (mem_varsOf_existsAll hb)

open Classical in
/-- The valuation that gives the canonical variables of `vars` listed in `is`, through `tbl'`, the
elements `e` gives them through `tbl`, and agrees with `e` elsewhere. -/
noncomputable def moveV (c : Semantics) (tbl tbl' : VarTable) (vars : List Srt) (is : List Nat)
    (e : Valuation M) : Valuation M :=
  ⟨fun x => if h : ∃ i < vars.length, i ∈ is ∧ x = tbl'.ev (canonKey c vars i)
    then e.evalEvar (tbl.ev (canonKey c vars (Classical.choose h))) else e.evalEvar x, e.evalSvar⟩

omit [Inhabited M] in
theorem moveV_at {tbl tbl' : VarTable} {vars : List Srt} {is : List Nat} {e : Valuation M}
    (hkeys : ∀ i < vars.length, i ∈ is → canonKey c vars i ∈ tbl') {i : Nat} (hi : i < vars.length) (his : i ∈ is) :
    (moveV c tbl tbl' vars is e).evalEvar (tbl'.ev (canonKey c vars i)) = e.evalEvar (tbl.ev (canonKey c vars i)) := by
  have hex : ∃ j < vars.length, j ∈ is ∧ tbl'.ev (canonKey c vars i) = tbl'.ev (canonKey c vars j) :=
    ⟨i, hi, his, rfl⟩
  show (if h : _ then _ else _) = _
  rw [dif_pos hex]
  obtain ⟨hj, hjs, hje⟩ := Classical.choose_spec hex
  have e1 : Classical.choose hex = i :=
    (canonKey_inj hi hj (ev_inj (hkeys i hi his) (hkeys _ hj hjs) hje)).symm
  rw [e1]

/-- **A condition that holds is not refuted.** In a model of `Γc`, where `⌈req = true⌉` holds at
a valuation of the conditions' variables in their sorts, the rule's conditions `∃ō. ⌈req = true⌉`
(`Rule.condK`, the predicate `\top`) are satisfied, so `Rule.Refuted` fails. -/
theorem cond_not_refuted_at (h : c.coreOK = true) (hI : I ⊧ᴵP Γc c) {r : Rule} (hs : c.ruleSorted r = true)
    (hpre : r.pre = .top) {tbl : VarTable} {e : Valuation M}
    (hin : ∀ i < r.vars.length, i ∈ r.condVars → InS I (c.sortName (r.vars.getD i 0))
      (e.evalEvar (tbl.ev (keyAt (canonVars c r.vars) i))))
    {t : Term} (ht : r.req = some t) {m : M}
    (hm : (KoreAML.tr ⟨tbl, []⟩ (reqPat (srtOf c topCellSort) (some (Term.kore c (canonVars c r.vars) t)))).interpret
      I e m) :
    ¬ r.Refuted c := by
  intro href
  have hIΓ : I ⊧ᴵP Γ c := fun φ hφ => hI φ (Or.inl hφ)
  haveI : OvlOK c := (hypSound_of_core h).2.2.2.2.2.2.2.2
  have hD := defOK hIΓ
  obtain ⟨-, hreqK, -, -⟩ := Semantics.ruleSorted_parts c hs
  have htS : sortOfTerm (c.rhsCtx (c.fns.map Fn.sig)) r.vars t = some Srt.bool := by
    rw [ht] at hreqK; simpa [reqOK] using hreqK
  have hlt : ∀ i ∈ varOccs t, i < r.vars.length := Exec.sortOfTerm_vars htS
  have hcv : ∀ i ∈ varOccs t, i ∈ r.condVars := fun i hi => by
    simp only [Rule.condVars, ht, Option.map_some, Option.getD_some]; exact List.mem_append_left _ hi
  let C := srtOf c topCellSort
  let vs := canonVars c r.vars
  let l := (List.range r.vars.length).filter r.condVars.contains
  have hl : ∀ i ∈ l, i < r.vars.length := fun i hi => List.mem_range.mp (List.mem_filter.mp hi).1
  have hbs : l.filterMap (vs[·]?) = l.map (vs.getD · default) :=
    filterMap_getElem?_of_lt vs l (fun i hi => by rw [canonVars_length]; exact hl i hi)
  have hK : r.condK c = KoreAML.existsAll C ((l.map (vs.getD · default)).map KoreAML.Var.kore)
      (.and C [reqPat C (some (Term.kore c vs t))]) := by
    unfold Rule.condK
    rw [← hbs]
    simp [ht, hpre, Cond.conj, Cond.isTop, vs, l, C]
  unfold Rule.Refuted at href
  rw [hK] at href
  unfold KoreAML.denB at href
  generalize htbl : KoreAML.tableOf [] _ = tbl2 at href
  have hkeys2 : ∀ i < r.vars.length, i ∈ l → canonKey c r.vars i ∈ tbl2 := fun i _ hil => by
    rw [← htbl]; unfold KoreAML.tableOf canonKey
    exact List.mem_eraseDups.mpr (List.mem_append_right _
      (mem_varsOf_existsAll (List.mem_map_of_mem (List.mem_map_of_mem hil))))
  let e' := moveV c tbl tbl2 r.vars l e
  have hneg := href hI e' m
  rw [interpret_neg] at hneg
  apply hneg
  have hnd : (((l.map (vs.getD · default)).map KoreAML.Var.kore).map fun b => tbl2.ev (KoreAML.evarKey b)).Nodup := by
    rw [List.map_map, List.map_map]
    refine Model.nodup_map_of_injOn _ (fun i hi j hj he => ?_) (List.nodup_range.filter _)
    exact canonKey_inj (hl i hi) (hl j hj) (ev_inj (hkeys2 i (hl i hi) hi) (hkeys2 j (hl j hj) hj) he)
  have hsrt : ∀ b ∈ (l.map (vs.getD · default)).map KoreAML.Var.kore, ∃ n, b.sort = KoreAML.srt n := fun b hb => by
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hb
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hv
    show ∃ n, ((canonVars c r.vars).getD i default).kore.sort = KoreAML.srt n
    rw [canonVars_getD c (hl i hi)]; exact ⟨_, rfl⟩
  refine existsAll_intro_at hD _ e' e' m hnd hsrt (fun _ _ => rfl) rfl (fun b hb n hn => ?_) ?_
  · obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hb
    obtain ⟨i, hil, rfl⟩ := List.mem_map.mp hv
    have hs' : ((canonVars c r.vars).getD i default).kore.sort = KoreAML.srt (c.sortName (r.vars.getD i 0)) := by
      rw [canonVars_getD c (hl i hil)]; rfl
    change ((canonVars c r.vars).getD i default).kore.sort = KoreAML.srt n at hn
    rw [hs'] at hn
    rw [← srt_inj hn]
    show InS I _ (e'.evalEvar (tbl2.ev (canonKey c r.vars i)))
    rw [moveV_at hkeys2 (hl i hil) hil]
    exact hin i (hl i hil) (by simpa using (List.mem_filter.mp hil).2)
  · show (KoreAML.tr ⟨tbl2, []⟩ (.and C [reqPat C (some (Term.kore c vs t))])).interpret I e' m
    rw [KoreAML.tr]
    simp only [KoreAML.trAndList]
    exact (tr_reqPat_congr hIΓ (fun i hi => moveV_at hkeys2 (hlt i hi)
      (List.mem_filter.mpr ⟨List.mem_range.mpr (hlt i hi), by simpa using hcv i hi⟩)) m).mpr hm

/-- `cond_not_refuted_at` at a valuation of every variable in its sort. -/
theorem cond_not_refuted (h : c.coreOK = true) (hI : I ⊧ᴵP Γc c) {r : Rule} (hs : c.ruleSorted r = true)
    (hpre : r.pre = .top) {tbl : VarTable} {e : Valuation M}
    (hin : ∀ i < r.vars.length, InS I (c.sortName (r.vars.getD i 0))
      (e.evalEvar (tbl.ev (keyAt (canonVars c r.vars) i))))
    {t : Term} (ht : r.req = some t) {m : M}
    (hm : (KoreAML.tr ⟨tbl, []⟩ (reqPat (srtOf c topCellSort) (some (Term.kore c (canonVars c r.vars) t)))).interpret
      I e m) :
    ¬ r.Refuted c :=
  cond_not_refuted_at h hI hs hpre (fun i hi _ => hin i hi) ht hm

end



end Faithful

end KCore
