/-
  KCore. The equations of a function whose clauses' patterns need not bind every variable, read in a
  model.

  A clause's equation `∀x̄. premise → f(X̄) = rhs ∧ ens` is read at a valuation that gives each
  variable the element of its value under a well-sorted σ (`Eval.clause` gives one for every
  variable). Its table holds a key for each variable that occurs in the axiom, in the premise or in
  the conclusion (`eqn_atCl`), so a clause whose variables each occur in it (`clauseSortedOpen`)
  needs no variable bound by its patterns (`clause_keys_inAx`). This direction reads `Γ` only.

  The clauses of a smaller priority are read negatively, through their exclusions, which bind the
  variables of their patterns and conditions only (`freeOf_exclusionCl`, `varsOf_exclusionCl`);
  each exclusion is asked empty where its clause fails (`ExclEmptyCl`, given in a model of `Γc` by
  `exclEmptyCl_of`). A clause's premise carries its predicate at the sort variable `R` where it is
  not `\top` (`withPre`): the predicate is asked well sorted (so that its free variables are the
  clause's), and that it holds at `R` is asked as a reading of its own (`ihpre`). With that, a clause that decides gives its function its right side's result
  (`plain_eq4Cl`, `compete_eq4Cl`, `clause_den4Cl`): `clause_den4` and `clause_den3` for clauses
  whose patterns need not bind every variable.
-/
import KcoreSpec.OpenClause

set_option autoImplicit false

namespace KCore

namespace Faithful

open ML
open KoreAML (DefOK Inh IsSort Closed KGround VarKey VarTable)

section
variable {c : Semantics} {M : Type} {I : Interpretation KoreAML.Sym M}

/-- **An equation of a function, read in a model**, whose variables occur in its axiom (`hVin`, in
the premise or in the conclusion) rather than in its premise. `eqn_at` with `hVin` so weakened. -/

theorem eqn_atCl [Inhabited M] (hI : I ⊧ᴵP Γ c) [OvlOK c] (hnn : NamesNumbered c)
    {f : Sym} {fn : Fn} (hfn : c.lookupFn f = some fn) {cl : Clause} {prem : Kore.Pattern}
    (hmem : KoreAML.trAxiom [] [] ⟨0, "kernel",
      { sortVars := [KoreAML.Rv], pattern := .implies KoreAML.R prem (clauseConcl c fn cl), attributes := [] }⟩ ∈ fnItems c)
    {ws : List GroundTerm} (hws : c.sortsOf ws = some fn.args)
    {σ' : Subst} (hσ' : c.WellSorted cl.vars σ')
    (hXin : ∀ (j : Nat) s, (fn.args.map c.sortName)[j]? = some s →
      VarKey.evar ("X" ++ toString j) (KoreAML.srt s) ∈ KoreAML.varsOf prem)
    (hVin : ∀ i < cl.vars.length,
      canonKey c cl.vars i ∈ KoreAML.varsOf (.implies KoreAML.R prem (clauseConcl c fn cl)))
    (hfree : ∀ k ∈ KoreAML.freeOf [] prem,
      (∃ (j : Nat) (s : String), (fn.args.map c.sortName)[j]? = some s ∧ k = .evar ("X" ++ toString j) (KoreAML.srt s)) ∨
        ∃ i < cl.vars.length, k = canonKey c cl.vars i)
    (hrhsv : ∀ i ∈ varOccs cl.rhs, i < cl.vars.length)
    (hensv : ∀ t, cl.ens = some t → ∀ i ∈ varOccs t, i < cl.vars.length)
    {r : Option GroundTerm} (hr : ∀ v, r = some v → c.sortOf v = some fn.result)
    (hprem : ∀ (tbl : VarTable) (e : Valuation M) (σr m0 : M), (∀ k ∈ KoreAML.varsOf prem, k ∈ tbl) →
      Agrees c I tbl (canonVars c cl.vars) σ' e →
      (∀ (j : Nat) w s, ws[j]? = some w → (fn.args.map c.sortName)[j]? = some s →
        e.evalEvar (tbl.ev (.evar ("X" ++ toString j) (KoreAML.srt s))) = elemOf c I w) →
      (∀ a, (KoreAML.trSort tbl KoreAML.R).interpret I e a ↔ a = σr) → IsSort I σr → Inh I σr m0 →
      (KoreAML.tr ⟨tbl, []⟩ prem).interpret I e m0)
    (ihrhs : ∀ (tbl : VarTable) (e : Valuation M), Agrees c I tbl (canonVars c cl.vars) σ' e →
      ∀ m, (KoreAML.tr ⟨tbl, []⟩ (clauseRight c fn cl)).interpret I e m ↔ Res c I e r m)
    (e0 : Valuation M) (m : M) :
    (KoreAML.den (symApp c f (GroundTerm.koreList c ws))).interpret I e0 m ↔ Res c I e0 r m := by
  obtain ⟨hfnm, hlab⟩ := lookupFn_spec hfn
  subst hlab
  have hD := defOK hI
  have hc := sat_sigItem hI (sig_ceilDef (c := c))
  have hnum := hnn.2.2 fn hfnm
  obtain ⟨σr, hσr1, hσr2⟩ := sortSing hI (hnum fn.result (List.mem_cons_self ..))
  have hlen : ws.length = fn.args.length := sortsOf_length hws
  let vs := canonVars c cl.vars
  let ax : Kore.Axiom :=
    { sortVars := [KoreAML.Rv], pattern := .implies KoreAML.R prem (clauseConcl c fn cl), attributes := [] }
  let tbl : VarTable := KoreAML.tableOf ax.sortVars ax.pattern
  let e' : Valuation M := valOf tbl (clauseVal c I σr fn.args.length cl.vars.length ws σ')
  have hvarsP : ∀ k, k ∈ KoreAML.varsOf prem → k ∈ tbl := fun k hk => by
    refine List.mem_eraseDups.mpr (List.mem_append_right _ ?_)
    show k ∈ KoreAML.varsOf (.implies KoreAML.R prem (clauseConcl c fn cl))
    rw [KoreAML.varsOf]
    exact List.mem_append_left _ (List.mem_append_right _ hk)
  have hRmem : VarKey.sortVar "R" ∈ tbl :=
    List.mem_eraseDups.mpr (List.mem_append_left _ (List.mem_map.mpr ⟨KoreAML.Rv, List.mem_singleton_self _, rfl⟩))
  have hXmem : ∀ j s, (fn.args.map c.sortName)[j]? = some s →
      VarKey.evar ("X" ++ toString j) (KoreAML.srt s) ∈ tbl := fun j s hj => hvarsP _ (hXin j s hj)
  have hVmem : ∀ i, i < cl.vars.length → canonKey c cl.vars i ∈ tbl := fun i hi =>
    List.mem_eraseDups.mpr (List.mem_append_right _ (hVin i hi))
  have hRv : ∀ a, (KoreAML.trSort tbl KoreAML.R).interpret I e' a ↔ a = σr := fun a => by
    rw [trSort_R, KoreAML.interp_evar, valOf_ev hRmem]; rfl
  have hXv : ∀ j s w, (fn.args.map c.sortName)[j]? = some s → ws[j]? = some w →
      e'.evalEvar (tbl.ev (.evar ("X" ++ toString j) (KoreAML.srt s))) = elemOf c I w := fun j s w hj hw => by
    have hjn : j < fn.args.length := by simpa using (List.getElem?_eq_some_iff.mp hj).1
    rw [valOf_ev (hXmem j s hj)]
    simp only [clauseVal]
    rw [xIdx_eq hjn]
    dsimp only
    rw [List.getD_eq_getElem?_getD, hw]; rfl
  have hVv : ∀ i, i < cl.vars.length → e'.evalEvar (tbl.ev (canonKey c cl.vars i)) =
      (match σ'.lookup i with | some v => elemOf c I v | none => default) := fun i hi => by
    rw [valOf_ev (hVmem i hi), canonKey_eq c hi]
    simp only [clauseVal]
    rw [xIdx_var, varIdx_eq hi]
    all_goals rfl
  have hvsort : ∀ i, i < cl.vars.length → ∃ v, σ'.lookup i = some v ∧ c.sortOf v = some (cl.vars.getD i 0) :=
    fun i hi => hσ' i _ (by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; rfl)
  have hag : Agrees c I tbl vs σ' e' := fun i v hi hl m => by
    rw [canonVars_length] at hi
    show m = e'.evalEvar (tbl.ev (canonKey c cl.vars i)) ↔ _
    rw [hVv i hi, hl]
    obtain ⟨w, hw, hsw⟩ := hvsort i hi
    rw [hl] at hw; cases hw
    exact ((elemOf_spec hI hsw e').1 m).symm
  have hargsort : ∀ j s w, (fn.args.map c.sortName)[j]? = some s → ws[j]? = some w →
      ∃ a, s = c.sortName a ∧ c.sortOf w = some a := fun j s w hj hw => by
    rw [List.getElem?_map] at hj
    obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.mp hj
    obtain ⟨w', hw', hsw'⟩ := sortsOf_get hws ha
    rw [hw] at hw'; cases hw'
    exact ⟨a, rfl, hsw'⟩
  have hfree : ∀ k, k ∈ KoreAML.freeOf [] ax.pattern →
      (∃ j s, (fn.args.map c.sortName)[j]? = some s ∧ k = .evar ("X" ++ toString j) (KoreAML.srt s)) ∨
        ∃ i, i < cl.vars.length ∧ k = canonKey c cl.vars i := fun k hk => by
    change k ∈ KoreAML.freeOf [] (.implies KoreAML.R prem (clauseConcl c fn cl)) at hk
    rw [KoreAML.freeOf] at hk
    rcases List.mem_append.mp hk with hk | hk
    · rcases hfree k hk with h | ⟨i, hi, h⟩
      · exact Or.inl h
      · exact Or.inr ⟨i, hi, h⟩
    · unfold clauseConcl at hk
      rw [KoreAML.freeOf] at hk
      rcases List.mem_append.mp hk with hk | hk
      · unfold KoreAML.ap at hk; rw [KoreAML.freeOf] at hk
        obtain ⟨n, s, hn, rfl⟩ := freeOf_callX _ 0 hk
        exact Or.inl ⟨n, s, hn, by rw [Nat.zero_add]⟩
      · obtain ⟨i, hi, rfl⟩ := freeOf_clauseConclRight hk
        exact Or.inr ⟨i, hi.elim (hrhsv i) fun ⟨t, ht, hi⟩ => hensv t ht i hi, rfl⟩
  have hg : ∀ k ∈ (ax.sortVars.map KoreAML.sortVarKey ++
      KoreAML.freeOf [] ax.pattern).eraseDups, ∀ m,
      (KoreAML.guardOf tbl k).interpret I e' m := by
    intro k hk m'
    rcases List.mem_append.mp (List.mem_eraseDups.mp hk) with hk | hk
    · obtain ⟨_, h1, rfl⟩ := List.mem_map.mp hk
      rw [mem_one h1]
      show (KoreAML.guardOf tbl (.sortVar "R")).interpret I e' m'
      rw [KoreAML.interp_guard_sortVar hD, valOf_ev hRmem]
      exact hσr2
    · rcases hfree k hk with ⟨j, s, hj, rfl⟩ | ⟨i, hi, rfl⟩
      · rw [KoreAML.interp_guard_evar hD, trSort_srt]
        obtain ⟨w, hw, -⟩ : ∃ w, ws[j]? = some w ∧ True := by
          have hjn : j < ws.length := by rw [hlen]; simpa using (List.getElem?_eq_some_iff.mp hj).1
          exact ⟨_, List.getElem?_eq_getElem hjn, trivial⟩
        obtain ⟨a, rfl, hsw⟩ := hargsort j s w hj hw
        rw [hXv j _ w hj hw]
        exact (elemOf_spec hI hsw e').2
      · obtain ⟨w, hw, hsw⟩ := hvsort i hi
        have hk := canonKey_eq c hi
        rw [hk, KoreAML.interp_guard_evar hD, trSort_srt, ← hk, hVv i hi, hw]
        exact (elemOf_spec hI hsw e').2
  have hall' : ∀ a, Inh I σr a →
      ((KoreAML.tr ⟨tbl, []⟩ (KoreAML.ap (c.symName fn.label)
        (KoreAML.vars (KoreAML.numbered "X" 0 (fn.args.map c.sortName))))).interpret I e' a ↔
        (KoreAML.tr ⟨tbl, []⟩ (clauseRight c fn cl)).interpret I e' a) := fun m0 hm0 => by
    have hax := sat_fns hI (Or.inl ⟨_, hmem, rfl⟩)
    have hP := (KoreAML.trAxiom_at hD hax e' hg m0).mpr (by
      show (KoreAML.inhOf (KoreAML.trSort tbl KoreAML.R)).interpret I e' m0
      rw [KoreAML.interp_inhOf_of hRv]; exact hm0)
    have hP' : (KoreAML.tr ⟨tbl, []⟩ (.implies KoreAML.R prem (clauseConcl c fn cl))).interpret I e' m0 := hP
    rw [KoreAML.tr, KoreAML.interp_sImp] at hP'
    obtain ⟨-, himp⟩ := hP'
    have hprem := himp (hprem tbl e' σr m0 hvarsP hag (fun j w s hw hs => hXv j s w hs hw) hRv hσr2 hm0)
    unfold clauseConcl at hprem
    rw [KoreAML.tr, KoreAML.interp_sEquals hD hc (by rw [trSort_srt]; exact hσr1) hRv hσr2 hσr2] at hprem
    obtain ⟨-, hall⟩ := hprem
    exact hall m0 hm0
  have hcall : ∀ m, (KoreAML.den (symApp c fn.label (GroundTerm.koreList c ws))).interpret I e0 m ↔
      (KoreAML.tr ⟨tbl, []⟩ (KoreAML.ap (c.symName fn.label)
        (KoreAML.vars (KoreAML.numbered "X" 0 (fn.args.map c.sortName))))).interpret I e' m := by
    intro m
    unfold KoreAML.den
    rw [tr_symApp]
    unfold symHead
    rw [hnn.2.1 fn hfnm]
    dsimp only
    unfold KoreAML.ap
    rw [KoreAML.tr_app0]
    refine call_congr (e0 := e0) (e' := e') (fn.args.map c.sortName) ws 0 _ _ (by rw [List.length_map]; exact hlen)
      (fun k s w hk hw m => ?_) (fun m => sym_congr (e := e0) (e' := e') _ m) m
    rw [Nat.zero_add, hXv k s w hk hw]
    obtain ⟨a, -, hsw⟩ := hargsort k s w hk hw
    exact (elemOf_spec hI hsw e0).1 m
  have harity : ∀ a, (KoreAML.tr ⟨tbl, []⟩ (KoreAML.ap (c.symName fn.label)
      (KoreAML.vars (KoreAML.numbered "X" 0 (fn.args.map c.sortName))))).interpret I e' a → Inh I σr a := by
    intro a ha
    have hit := sat_sigItem hI (sig_arity (fn_sig_mem hfnm))
    unfold symArityItem at hit
    rw [show iteSort? (c.symName fn.sig.name) = none from hnn.2.1 fn hfnm] at hit
    dsimp only at hit
    unfold KoreAML.arityItem at hit
    dsimp only [KoreAML.paramTable, List.map_nil, KoreAML.appList, Fn.sig] at hit
    have hinc := (KoreAML.interp_included hD).mp (hit e' default) a
    unfold srtOf at hinc
    rw [trSort_srt, KoreAML.interp_inhOf_of (S := KoreAML.sym _) hσr1] at hinc
    apply hinc
    unfold KoreAML.ap at ha
    rw [KoreAML.tr_app0] at ha
    have := call_arity (fn.args.map c.sortName) 0 _ (KoreAML.sym (.symbol (c.symName fn.label))) a ha
      (fun k s hk => ?_) (fun _ h => h)
    · rw [List.map_map] at this
      rw [List.map_map]
      exact this
    · rw [Nat.zero_add]
      obtain ⟨w, hw, -⟩ : ∃ w, ws[k]? = some w ∧ True := by
        have hjn : k < ws.length := by rw [hlen]; simpa using (List.getElem?_eq_some_iff.mp hk).1
        exact ⟨_, List.getElem?_eq_getElem hjn, trivial⟩
      obtain ⟨b, rfl, hsw⟩ := hargsort k s w hk hw
      rw [hXv k _ w hk hw]
      exact (elemOf_spec hI hsw e').2
  constructor
  · intro hm
    have h1 := (hcall m).mp hm
    have h2 := (hall' m (harity m h1)).mp h1
    exact (Res_closed r e' e0 m).mp ((ihrhs tbl e' hag m).mp h2)
  · intro hm
    have hm' := (Res_closed r e0 e' m).mp hm
    have hin : Inh I σr m := by
      cases r with
      | none => exact hm.elim
      | some v =>
        have hsv := hr v rfl
        have hs := elemOf_spec hI hsv e'
        rw [(hs.1 m).mp hm']
        exact (KoreAML.interp_inhOf_of (S := KoreAML.sym _) hσr1).mp hs.2
    exact (hcall m).mpr ((hall' m hin).mpr ((ihrhs tbl e' hag m).mpr hm'))

end

/-! ## The variables of a clause's equation and of its exclusion -/

section
variable {c : Semantics}

/-- The formal arguments and the patterns' variables occur in a clause's premise
`⌈req = true⌉ ∧ X̄ ∈ p̄`; nothing but formal arguments and the clause's variables is free in it.
`premise_vars` without asking that the patterns bind every variable. -/

theorem premise_varsCl {fn : Fn} {cl : Clause} (hpats : sortsOfTerms c.patCtxAll cl.vars cl.pats = some fn.args)
    (hreqv : ∀ t, cl.req = some t → ∀ i ∈ varOccs t, i < cl.vars.length) :
    let prem := premise (fn.args.map c.sortName) (cl.req.map (Term.kore c (canonVars c cl.vars)))
      (Term.koreList c (canonVars c cl.vars) cl.pats)
    (∀ (j : Nat) s, (fn.args.map c.sortName)[j]? = some s →
      VarKey.evar ("X" ++ toString j) (KoreAML.srt s) ∈ KoreAML.varsOf prem) ∧
    (∀ i ∈ varOccsList cl.pats, canonKey c cl.vars i ∈ KoreAML.varsOf prem) ∧
    (∀ k ∈ KoreAML.freeOf [] prem,
      (∃ (j : Nat) (s : String), (fn.args.map c.sortName)[j]? = some s ∧ k = .evar ("X" ++ toString j) (KoreAML.srt s)) ∨
        ∃ i < cl.vars.length, k = canonKey c cl.vars i) := by
  intro prem
  let vs := canonVars c cl.vars
  let l := (fn.args.map c.sortName).zip (Term.koreList c vs cl.pats)
  have hplen : (Term.koreList c vs cl.pats).length = (fn.args.map c.sortName).length := by
    rw [koreList_length, List.length_map]; exact sortsOfTerms_length hpats
  have hA : ∀ k, k ∈ KoreAML.varsOf (KoreAML.argsConj 0 l) → k ∈ KoreAML.varsOf prem := fun k hk => by
    show k ∈ KoreAML.varsOf (premise _ _ _)
    unfold premise
    rw [KoreAML.varsOf, KoreAML.varsOfList, KoreAML.varsOfList, KoreAML.varsOfList]
    exact List.mem_append_right _ (List.mem_append_right _ (List.mem_append_left _ hk))
  refine ⟨fun j s hj => ?_, fun i hi => ?_, fun k hk => ?_⟩
  · have hjl : j < (Term.koreList c vs cl.pats).length := by
      rw [hplen]; exact (List.getElem?_eq_some_iff.mp hj).1
    have hl : l[j]? = some (s, (Term.koreList c vs cl.pats)[j]) :=
      List.getElem?_zip_eq_some.mpr ⟨hj, List.getElem?_eq_getElem hjl⟩
    have := varsOf_argsConj_X l 0 j s _ hl
    rw [Nat.zero_add] at this
    exact hA _ this
  · have h1 := varsOf_koreList c vs cl.pats hi
    obtain ⟨p', hp', hk⟩ := varsOfList_mem h1
    have hp'' : p' ∈ l.map Prod.snd := by
      rw [List.map_snd_zip (Nat.le_of_eq hplen)]; exact hp'
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp''
    exact hA _ (varsOf_argsConj_pat l 0 hq hk)
  · change k ∈ KoreAML.freeOf [] (premise _ _ _) at hk
    unfold premise at hk
    rw [KoreAML.freeOf, KoreAML.freeOfList, KoreAML.freeOfList, KoreAML.freeOfList] at hk
    simp only [List.append_nil, List.mem_append] at hk
    rcases hk with hk | hk
    · cases hq : cl.req with
      | none =>
        rw [hq] at hk; simp only [Option.map_none, reqPat] at hk; rw [KoreAML.freeOf] at hk; cases hk
      | some t =>
        rw [hq] at hk; simp only [Option.map_some, reqPat] at hk
        rw [KoreAML.freeOf] at hk
        rcases List.mem_append.mp hk with hk | hk
        · obtain ⟨i, hi, rfl⟩ := freeOf_kore c vs t hk
          exact Or.inr ⟨i, hreqv t hq i hi, rfl⟩
        · rw [KoreAML.freeOf] at hk; cases hk
    · rcases freeOf_argsConj l 0 hk with ⟨n, s, p, hn, rfl⟩ | ⟨q, hq, hk⟩
      · exact Or.inl ⟨n, s, (List.getElem?_zip_eq_some.mp hn).1, by rw [Nat.zero_add]⟩
      · have hq2 := (List.of_mem_zip (a := q.1) (b := q.2) hq).2
        obtain ⟨i, hi, rfl⟩ := freeOf_koreList c vs cl.pats (mem_freeOfList hq2 hk)
        exact Or.inr ⟨i, varOccsList_lt cl.pats hpats i hi, rfl⟩

/-- **Each variable of a clause occurs in its equation's axiom**, where each occurs in the clause
(`clauseSortedOpen`'s second conjunct) and its right side's predicate is `\top`: a variable of its
patterns, `requires` or predicate in the premise (here any pattern whose variables include those
of the premise with the predicate), one of its right side or `ensures` in the conclusion. -/
theorem clause_keys_inAx {fn : Fn} {cl : Clause} {prem : Kore.Pattern}
    (hpats : sortsOfTerms c.patCtxAll cl.vars cl.pats = some fn.args)
    (hreqv : ∀ t, cl.req = some t → ∀ i ∈ varOccs t, i < cl.vars.length)
    (hpost : cl.post = .top)
    (hocc : ∀ i < cl.vars.length, i ∈ varOccsList cl.pats ++ cl.condVars ++ varOccs cl.rhs ++
      (cl.ens.map varOccs).getD [] ++ varOccsCond cl.vars.length cl.post)
    (hP : ∀ k, k ∈ KoreAML.varsOf (withPre c (canonVars c cl.vars) cl (clausePrem c fn cl)) →
      k ∈ KoreAML.varsOf prem) :
    ∀ i < cl.vars.length, canonKey c cl.vars i ∈ KoreAML.varsOf (.implies KoreAML.R prem (clauseConcl c fn cl)) := by
  intro i hi
  have hinP : canonKey c cl.vars i ∈ KoreAML.varsOf prem →
      canonKey c cl.vars i ∈ KoreAML.varsOf (.implies KoreAML.R prem (clauseConcl c fn cl)) := fun h => by
    rw [KoreAML.varsOf]; exact List.mem_append_left _ (List.mem_append_right _ h)
  have hinR : canonKey c cl.vars i ∈ KoreAML.varsOf (clauseRight c fn cl) →
      canonKey c cl.vars i ∈ KoreAML.varsOf (.implies KoreAML.R prem (clauseConcl c fn cl)) := fun h => by
    rw [KoreAML.varsOf]
    refine List.mem_append_right _ ?_
    unfold clauseConcl
    rw [KoreAML.varsOf]
    exact List.mem_append_right _ h
  have h := hocc i hi
  simp only [List.mem_append] at h
  rcases h with (((hP' | hC) | hR) | hE) | hQ
  · exact hinP (hP _ (HoldsShape.varsOf_withPre_prem ((premise_varsCl (c := c) hpats hreqv).2.1 i hP')))
  · rcases List.mem_append.mp (show i ∈ (cl.req.map varOccs).getD [] ++ varOccsCond cl.vars.length cl.pre from hC)
      with hC | hC
    · cases ht : cl.req with
      | none => rw [ht] at hC; cases hC
      | some t =>
        rw [ht] at hC
        refine hinP (hP _ (HoldsShape.varsOf_withPre_prem ?_))
        unfold clausePrem premise
        rw [ht]
        refine Model.varsOf_and_mem (List.mem_cons_self ..) ?_
        simp only [Option.map_some, reqPat, KoreAML.varsOf]
        exact List.mem_append_left _ (List.mem_append_right _ (varsOf_kore c _ t hC))
    · have hpt : cl.pre.isTop = false := by
        cases hpt : cl.pre.isTop with
        | false => rfl
        | true => rw [Cond.eq_top_of_isTop hpt] at hC; simp [varOccsCond] at hC
      exact hinP (hP _ (HoldsShape.varsOf_withPre_pre hpt
        (Model.condKore_keys KoreAML.R cl.pre (bound := []) hi hC rfl).2))
  · exact hinR (Model.varsOf_and_mem (List.mem_cons_self ..) (varsOf_kore c _ cl.rhs hR))
  · cases ht : cl.ens with
    | none => rw [ht] at hE; cases hE
    | some t =>
      rw [ht] at hE
      refine hinR (Model.varsOf_and_mem (List.mem_cons_of_mem _ (List.mem_singleton_self _)) ?_)
      rw [ht]
      simp only [Option.map_some, reqPat, KoreAML.varsOf]
      exact List.mem_append_left _ (List.mem_append_right _ (varsOf_kore c _ t hE))
  · rw [hpost] at hQ; simp [varOccsCond] at hQ

/-- A clause's exclusion under its canonical presentation, its binders listed as variables. -/
theorem exclusion_canon_mapCl (c : Semantics) (fn : Fn) (cl : Clause) (hpre : cl.pre = .top) :
    exclusion c fn cl (canonClausePres cl) = KoreAML.existsAll KoreAML.R
      ((((List.range cl.vars.length).filter cl.leftVars.contains).map ((canonVars c cl.vars).getD · default)).map
        KoreAML.Var.kore)
      (premise (fn.args.map c.sortName) (cl.req.map (Term.kore c (canonVars c cl.vars)))
        (Term.koreList c (canonVars c cl.vars) cl.pats)) := by
  rw [exclusion_canonCl _ _ _ hpre, filterMap_getElem?_of_lt _ _ (fun i hi => by
    rw [canonVars_length]; exact List.mem_range.mp (List.mem_filter.mp hi).1)]

/-- A clause's exclusion under its canonical presentation, its binders listed as variables, its body
the premise with the predicate (`withPre`). -/
theorem exclusion_canon_mapPre (c : Semantics) (fn : Fn) (cl : Clause) :
    exclusion c fn cl (canonClausePres cl) = KoreAML.existsAll KoreAML.R
      ((((List.range cl.vars.length).filter cl.leftVars.contains).map ((canonVars c cl.vars).getD · default)).map
        KoreAML.Var.kore)
      (withPre c (canonVars c cl.vars) cl
        (premise (fn.args.map c.sortName) (cl.req.map (Term.kore c (canonVars c cl.vars)))
          (Term.koreList c (canonVars c cl.vars) cl.pats))) := by
  rw [exclusion_canonPre, filterMap_getElem?_of_lt _ _ (fun i hi => by
    rw [canonVars_length]; exact List.mem_range.mp (List.mem_filter.mp hi).1)]

/-- A free variable of a clause's premise with its predicate is a formal argument or a variable
of the clause, the predicate well sorted. -/
theorem freeOf_withPreCl {fn : Fn} {cl : Clause} (hpreOK : c.condOK cl.vars cl.pre = true)
    (hpats : sortsOfTerms c.patCtxAll cl.vars cl.pats = some fn.args)
    (hreqv : ∀ t, cl.req = some t → ∀ i ∈ varOccs t, i < cl.vars.length) {k : VarKey}
    (hk : k ∈ KoreAML.freeOf [] (withPre c (canonVars c cl.vars) cl (clausePrem c fn cl))) :
    (∃ (j : Nat) (s : String), (fn.args.map c.sortName)[j]? = some s ∧ k = .evar ("X" ++ toString j) (KoreAML.srt s)) ∨
      ∃ i < cl.vars.length, k = canonKey c cl.vars i := by
  rcases HoldsShape.freeOf_withPre hk with hk | ⟨-, hk⟩
  · exact (premise_varsCl (c := c) hpats hreqv).2.2 k hk
  · obtain ⟨-, i, hi, rfl⟩ := Model.freeOf_condKore KoreAML.R cl.pre hpreOK hk
    exact Or.inr ⟨i, varOccsCond_lt_twoT cl.pre hpreOK i hi, rfl⟩

/-- The exclusion of a clause has the formal arguments as its only free variables: it binds the
variables of the patterns and the conditions, which hold those of a well-sorted predicate. -/
theorem freeOf_exclusionCl {fn : Fn} {cl : Clause} (hpreOK : c.condOK cl.vars cl.pre = true)
    (hpats : sortsOfTerms c.patCtxAll cl.vars cl.pats = some fn.args)
    (hreqv : ∀ t, cl.req = some t → ∀ i ∈ varOccs t, i < cl.vars.length)
    {bound : List VarKey} {k : VarKey}
    (hk : k ∈ KoreAML.freeOf bound (exclusion c fn cl (canonClausePres cl))) :
    ∃ (j : Nat) (s : String), (fn.args.map c.sortName)[j]? = some s ∧ k = .evar ("X" ++ toString j) (KoreAML.srt s) := by
  rw [exclusion_canon_mapPre] at hk
  let vs := canonVars c cl.vars
  let l := (List.range cl.vars.length).filter cl.leftVars.contains
  obtain ⟨bound', hb', hk⟩ := freeOf_existsAll (S := KoreAML.R)
    (body := withPre c vs cl (premise (fn.args.map c.sortName) (cl.req.map (Term.kore c vs)) (Term.koreList c vs cl.pats)))
    ((l.map (vs.getD · default)).map KoreAML.Var.kore) hk
  have hbound : ∀ i < cl.vars.length, i ∈ cl.leftVars → bound'.contains (canonKey c cl.vars i) = true :=
    fun i hi hil => (hb' _).mpr (Or.inl (List.mem_map.mpr ⟨(vs.getD i default).kore,
      List.mem_map_of_mem (List.mem_map_of_mem (List.mem_filter.mpr ⟨List.mem_range.mpr hi, by simpa using hil⟩)),
      rfl⟩))
  rcases HoldsShape.freeOf_withPre hk with hk | ⟨-, hk⟩
  · unfold premise at hk
    rw [KoreAML.freeOf, KoreAML.freeOfList, KoreAML.freeOfList, KoreAML.freeOfList] at hk
    simp only [List.append_nil, List.mem_append] at hk
    rcases hk with hk | hk
    · exfalso
      cases hq : cl.req with
      | none =>
        rw [hq] at hk; simp only [Option.map_none, reqPat] at hk; rw [KoreAML.freeOf] at hk; cases hk
      | some t =>
        rw [hq] at hk; simp only [Option.map_some, reqPat] at hk
        rw [KoreAML.freeOf] at hk
        rcases List.mem_append.mp hk with hk | hk
        · obtain ⟨hb, i, hi, rfl⟩ := freeOf_kore_bound c vs t hk
          have h2 : bound'.contains (KoreAML.evarKey (vs.getD i default).kore) = true :=
            hbound i (hreqv t hq i hi) (Clause.req_leftVars hq i hi)
          rw [hb] at h2; cases h2
        · rw [KoreAML.freeOf] at hk; cases hk
    · rcases freeOf_argsConj _ 0 hk with ⟨n, s, p, hn, rfl⟩ | ⟨q, hq, hk⟩
      · exact ⟨n, s, (List.getElem?_zip_eq_some.mp hn).1, by rw [Nat.zero_add]⟩
      · exfalso
        have hq2 := (List.of_mem_zip (a := q.1) (b := q.2) hq).2
        obtain ⟨hb, i, hi, rfl⟩ := freeOf_koreList_bound c vs cl.pats (mem_freeOfList hq2 hk)
        have h2 : bound'.contains (KoreAML.evarKey (vs.getD i default).kore) = true :=
          hbound i (varOccsList_lt cl.pats hpats i hi) (List.mem_append_left _ hi)
        rw [hb] at h2; cases h2
  · exfalso
    obtain ⟨hb, i, hi, rfl⟩ := Model.freeOf_condKore KoreAML.R cl.pre hpreOK hk
    have h2 := hbound i (varOccsCond_lt_twoT cl.pre hpreOK i hi) (Clause.pre_leftVarsRH i hi)
    rw [hb] at h2; cases h2

/-- The binders of a clause's exclusion are the canonical variables of its patterns and
conditions. -/
theorem varsOf_exclusionCl {fn : Fn} {cl : Clause} {i : Nat} (hi : i < cl.vars.length)
    (hil : i ∈ cl.leftVars) :
    canonKey c cl.vars i ∈ KoreAML.varsOf (exclusion c fn cl (canonClausePres cl)) := by
  rw [exclusion_canon_mapPre]
  exact varsOf_existsAll_binder (S := KoreAML.R) (body := withPre _ _ _ _) _
    (List.mem_map_of_mem (List.mem_map_of_mem (List.mem_filter.mpr ⟨List.mem_range.mpr hi, by simpa using hil⟩)))

/-- The variables of a clause's predicate at `R` are variables of its exclusion, where the
predicate is not `\top`. -/
theorem varsOf_exclusion_preCl {fn : Fn} {cl : Clause} (hpt : cl.pre.isTop = false) {k : VarKey}
    (hk : k ∈ KoreAML.varsOf (Cond.kore c (canonVars c cl.vars) KoreAML.R cl.pre)) :
    k ∈ KoreAML.varsOf (exclusion c fn cl (canonClausePres cl)) := by
  rw [exclusion_canon_mapPre]
  exact Model.varsOf_existsAll_bodyEx (HoldsShape.varsOf_withPre_pre hpt hk) _

/-- The equation of a clause without existential variables: its premise with its predicate, the
right side `rhs ∧ ens`. -/
theorem clauseEquation_nilPre {f : Fn} {cl : Clause} (hex : cl.exs = []) :
    clauseEquation c f cl =
      eqnSentence c f (withPre c (canonVars c cl.vars) cl (clausePrem c f cl))
        (Term.kore c (canonVars c cl.vars) cl.rhs)
        (reqPat (srtOf c f.result) (cl.ens.map (Term.kore c (canonVars c cl.vars)))) := by
  unfold clauseEquation clausePrem; simp only [clauseRhs_nil hex]

/-- The competing equation of a clause without existential variables: no competitor applies and
its premise with its predicate holds; the right side `rhs ∧ ens`. -/
theorem competingEquation_nilPre {f : Fn} {others : List Clause} {cl : Clause} (hex : cl.exs = []) :
    competingEquation c f others cl =
      eqnSentence c f
        (.and KoreAML.R [.not KoreAML.R (KoreAML.anyOf (others.map fun cl' => exclusion c f cl' (canonClausePres cl'))),
          withPre c (canonVars c cl.vars) cl (clausePrem c f cl)])
        (Term.kore c (canonVars c cl.vars) cl.rhs)
        (reqPat (srtOf c f.result) (cl.ens.map (Term.kore c (canonVars c cl.vars)))) := by
  unfold competingEquation clausePrem; simp only [clauseRhs_nil hex]

end

/-! ## A clause's equation, read in a model -/

section
variable {c : Semantics} {M : Type} {I : Interpretation KoreAML.Sym M}

/-- A clause's premise with its predicate holds where the premise does and, the predicate not
`\top`, the predicate at `R` does, through a table that holds the variables of both. -/
theorem withPre_holdsCl {vs : List KoreAML.Var} {cl : Clause} {prem : Kore.Pattern} {tbl : VarTable}
    {e : Valuation M} {m0 : M} (h0 : (KoreAML.tr ⟨tbl, []⟩ prem).interpret I e m0)
    (hk : ∀ k ∈ KoreAML.varsOf (withPre c vs cl prem), k ∈ tbl)
    (ihpre : cl.pre.isTop = false → (∀ k ∈ KoreAML.varsOf (Cond.kore c vs KoreAML.R cl.pre), k ∈ tbl) →
      VarKey.sortVar "R" ∈ tbl → (KoreAML.tr ⟨tbl, []⟩ (Cond.kore c vs KoreAML.R cl.pre)).interpret I e m0) :
    (KoreAML.tr ⟨tbl, []⟩ (withPre c vs cl prem)).interpret I e m0 := by
  cases hpt : cl.pre.isTop with
  | true => rw [withPre_isTop hpt]; exact h0
  | false =>
    refine (HoldsShape.withPre_interp hpt).mpr ⟨h0, ihpre hpt (fun k hk' => hk k (HoldsShape.varsOf_withPre_pre hpt hk'))
      (hk _ ?_)⟩
    unfold withPre
    rw [hpt, if_neg (by simp), KoreAML.varsOf]
    exact List.mem_append_left _ (List.mem_singleton_self _)

/-- **An ordinary clause's equation, read in a model**, its variables each occurring in it (not
necessarily in its patterns), its predicate well sorted and, where it is not `\top`, holding at
`R` at the valuations that agree with σ' (`ihpre`). `plain_eq4` for such a clause. -/
theorem plain_eq4Cl [Inhabited M] (hI : I ⊧ᴵP Γ c) [OvlOK c] (hnn : NamesNumbered c) (hph : patHooksApart c = true)
    (htr : ∀ a b d, (a, b) ∈ c.subsorts → (b, d) ∈ c.subsorts → (a, d) ∈ c.subsorts)
    {f : Sym} {fn : Fn} (hfn : c.lookupFn f = some fn) {cl : Clause}
    (hmem : clauseEquation c fn cl ∈ fnEquationsK c fn) {ws : List GroundTerm} (hws : c.sortsOf ws = some fn.args)
    {σ' : Subst} (hσ' : c.WellSorted cl.vars σ') (hmatch : PatVals c σ' cl.pats ws)
    (hpats : sortsOfTerms c.patCtxAll cl.vars cl.pats = some fn.args)
    (hpreOK : c.condOK cl.vars cl.pre = true) (hpost : cl.post = .top) (hexs : cl.exs = [])
    (hocc : ∀ i < cl.vars.length, i ∈ varOccsList cl.pats ++ cl.condVars ++
      varOccs cl.rhs ++ (cl.ens.map varOccs).getD [] ++ varOccsCond cl.vars.length cl.post)
    (hreqv : ∀ t, cl.req = some t → ∀ i ∈ varOccs t, i < cl.vars.length)
    (hrhsv : ∀ i ∈ varOccs cl.rhs, i < cl.vars.length)
    (hensv : ∀ t, cl.ens = some t → ∀ i ∈ varOccs t, i < cl.vars.length)
    {r : Option GroundTerm} (hr : ∀ v, r = some v → c.sortOf v = some fn.result)
    (ihreq : ∀ (tbl : VarTable) (e : Valuation M), Agrees c I tbl (canonVars c cl.vars) σ' e →
      ∀ t, cl.req = some t → ∀ m, (KoreAML.tr ⟨tbl, []⟩ (Term.kore c (canonVars c cl.vars) t)).interpret I e m ↔
        (den c (bool true)).interpret I e m)
    (ihpre : cl.pre.isTop = false → ∀ (tbl : VarTable) (e : Valuation M) (σr m0 : M),
      Agrees c I tbl (canonVars c cl.vars) σ' e →
      (∀ k ∈ KoreAML.varsOf (Cond.kore c (canonVars c cl.vars) KoreAML.R cl.pre), k ∈ tbl) →
      VarKey.sortVar "R" ∈ tbl → (∀ a, (KoreAML.trSort tbl KoreAML.R).interpret I e a ↔ a = σr) → IsSort I σr →
      Inh I σr m0 → (KoreAML.tr ⟨tbl, []⟩ (Cond.kore c (canonVars c cl.vars) KoreAML.R cl.pre)).interpret I e m0)
    (ihrhs : ∀ (tbl : VarTable) (e : Valuation M), Agrees c I tbl (canonVars c cl.vars) σ' e →
      ∀ m, (KoreAML.tr ⟨tbl, []⟩ (clauseRight c fn cl)).interpret I e m ↔ Res c I e r m)
    (e0 : Valuation M) (m : M) :
    (KoreAML.den (symApp c f (GroundTerm.koreList c ws))).interpret I e0 m ↔ Res c I e0 r m := by
  have hfnm := (lookupFn_spec hfn).1
  have hv := premise_varsCl (c := c) hpats hreqv
  rw [clauseEquation_nilPre hexs] at hmem
  exact eqn_atCl hI hnn hfn (prem := withPre c (canonVars c cl.vars) cl (clausePrem c fn cl))
    (eqn_item_mem hfnm hmem) hws hσ' (fun j s hj => HoldsShape.varsOf_withPre_prem (hv.1 j s hj))
    (clause_keys_inAx hpats hreqv hpost hocc (fun _ h => h)) (fun k hk => freeOf_withPreCl hpreOK hpats hreqv hk)
    hrhsv hensv hr
    (fun tbl e σr m0 hk hag hX hRv hσr2 hm0 =>
      withPre_holdsCl (premise_holds4 hI hnn hph htr hfnm hws hσ' hmatch (OvlOK.nfs_bridge inferInstance hpats) hag hX hRv hσr2 hm0 (ihreq tbl e hag))
        hk (fun hpt hkp hRk => ihpre hpt tbl e σr m0 hag hkp hRk hRv hσr2 hm0))
    ihrhs e0 m

/-- **A clause's equation under negated competitors, read in a model**, its variables each occurring
in it, each competitor's exclusion empty where it fails (`ExclEmptyCl`), the predicates well sorted
and the clause's, where it is not `\top`, holding at `R` (`ihpre`). `compete_eq4` for such
clauses. -/

theorem compete_eq4Cl [Inhabited M] (hI : I ⊧ᴵP Γ c) [OvlOK c] (hnn : NamesNumbered c) (hph : patHooksApart c = true)
    (htr : ∀ a b d, (a, b) ∈ c.subsorts → (b, d) ∈ c.subsorts → (a, d) ∈ c.subsorts)
    {f : Sym} {fn : Fn} (hfn : c.lookupFn f = some fn) {others : List Clause} {cl : Clause}
    (hmem : competingEquation c fn others cl ∈ fnEquationsK c fn) {ws : List GroundTerm} (hws : c.sortsOf ws = some fn.args)
    (hothers : ∀ cl' ∈ others, c.condOK cl'.vars cl'.pre = true ∧
      sortsOfTerms c.patCtxAll cl'.vars cl'.pats = some fn.args ∧
      (∀ t, cl'.req = some t → ∀ i ∈ varOccs t, i < cl'.vars.length) ∧
      ExclEmptyCl c I fn cl' ∧ Fails c ws cl' ∧ ModelFailsCl c I cl' ws)
    {σ' : Subst} (hσ' : c.WellSorted cl.vars σ') (hmatch : PatVals c σ' cl.pats ws)
    (hpats : sortsOfTerms c.patCtxAll cl.vars cl.pats = some fn.args)
    (hpreOK : c.condOK cl.vars cl.pre = true) (hpost : cl.post = .top) (hexs : cl.exs = [])
    (hocc : ∀ i < cl.vars.length, i ∈ varOccsList cl.pats ++ cl.condVars ++
      varOccs cl.rhs ++ (cl.ens.map varOccs).getD [] ++ varOccsCond cl.vars.length cl.post)
    (hreqv : ∀ t, cl.req = some t → ∀ i ∈ varOccs t, i < cl.vars.length)
    (hrhsv : ∀ i ∈ varOccs cl.rhs, i < cl.vars.length)
    (hensv : ∀ t, cl.ens = some t → ∀ i ∈ varOccs t, i < cl.vars.length)
    {r : Option GroundTerm} (hr : ∀ v, r = some v → c.sortOf v = some fn.result)
    (ihreq : ∀ (tbl : VarTable) (e : Valuation M), Agrees c I tbl (canonVars c cl.vars) σ' e →
      ∀ t, cl.req = some t → ∀ m, (KoreAML.tr ⟨tbl, []⟩ (Term.kore c (canonVars c cl.vars) t)).interpret I e m ↔
        (den c (bool true)).interpret I e m)
    (ihpre : cl.pre.isTop = false → ∀ (tbl : VarTable) (e : Valuation M) (σr m0 : M),
      Agrees c I tbl (canonVars c cl.vars) σ' e →
      (∀ k ∈ KoreAML.varsOf (Cond.kore c (canonVars c cl.vars) KoreAML.R cl.pre), k ∈ tbl) →
      VarKey.sortVar "R" ∈ tbl → (∀ a, (KoreAML.trSort tbl KoreAML.R).interpret I e a ↔ a = σr) → IsSort I σr →
      Inh I σr m0 → (KoreAML.tr ⟨tbl, []⟩ (Cond.kore c (canonVars c cl.vars) KoreAML.R cl.pre)).interpret I e m0)
    (ihrhs : ∀ (tbl : VarTable) (e : Valuation M), Agrees c I tbl (canonVars c cl.vars) σ' e →
      ∀ m, (KoreAML.tr ⟨tbl, []⟩ (clauseRight c fn cl)).interpret I e m ↔ Res c I e r m)
    (e0 : Valuation M) (m : M) :
    (KoreAML.den (symApp c f (GroundTerm.koreList c ws))).interpret I e0 m ↔ Res c I e0 r m := by
  rw [competingEquation_nilPre hexs] at hmem
  have hfnm := (lookupFn_spec hfn).1
  have hD := defOK hI
  have hv := premise_varsCl (c := c) hpats hreqv
  let comps := others.map fun cl' => exclusion c fn cl' (canonClausePres cl')
  let P := withPre c (canonVars c cl.vars) cl (clausePrem c fn cl)
  let CP : Kore.Pattern := .and KoreAML.R [.not KoreAML.R (KoreAML.anyOf comps), P]
  have hP : ∀ k, k ∈ KoreAML.varsOf P → k ∈ KoreAML.varsOf CP := fun k hk => by
    show k ∈ KoreAML.varsOf (Kore.Pattern.and KoreAML.R [.not KoreAML.R (KoreAML.anyOf comps), P])
    rw [KoreAML.varsOf, KoreAML.varsOfList, KoreAML.varsOfList, KoreAML.varsOfList]
    exact List.mem_append_right _ (List.mem_append_right _ (List.mem_append_left _ hk))
  have hN : ∀ k, k ∈ KoreAML.varsOf (anyOfC KoreAML.R comps) → k ∈ KoreAML.varsOf CP := fun k hk => by
    show k ∈ KoreAML.varsOf (Kore.Pattern.and KoreAML.R [.not KoreAML.R (KoreAML.anyOf comps), P])
    rw [KoreAML.varsOf, KoreAML.varsOfList, KoreAML.varsOfList, KoreAML.varsOf, anyOf_eq]
    exact List.mem_append_right _ (List.mem_append_left _ (List.mem_append_right _ hk))
  refine eqn_atCl hI hnn hfn (prem := CP) (eqn_item_mem hfnm hmem) hws hσ'
    (fun j s hj => hP _ (HoldsShape.varsOf_withPre_prem (hv.1 j s hj)))
    (clause_keys_inAx hpats hreqv hpost hocc hP) (fun k hk => ?_) hrhsv hensv hr (fun tbl e σr m0 hkeys hag hX hRv hσr2 hm0 => ?_) ihrhs e0 m
  · change k ∈ KoreAML.freeOf [] (Kore.Pattern.and KoreAML.R [.not KoreAML.R (KoreAML.anyOf comps), P]) at hk
    rw [KoreAML.freeOf, KoreAML.freeOfList, KoreAML.freeOfList, KoreAML.freeOfList, KoreAML.freeOf] at hk
    simp only [List.append_nil, List.mem_append] at hk
    rcases hk with hk | hk
    · rw [anyOf_eq] at hk
      obtain ⟨φ, hφ, hk⟩ := mem_freeOf_anyOfC hk
      obtain ⟨cl', hcl', rfl⟩ := List.mem_map.mp hφ
      obtain ⟨hpre', hp', hq', -⟩ := hothers cl' hcl'
      exact Or.inl (freeOf_exclusionCl hpre' hp' hq' hk)
    · exact freeOf_withPreCl hpreOK hpats hreqv hk
  · have hR' : e.evalEvar (tbl.ev (.sortVar "R")) = σr := (hRv _).mp (by rw [trSort_R, KoreAML.interp_evar])
    have hRkey : VarKey.sortVar "R" ∈ tbl := hkeys _ (by
      show _ ∈ KoreAML.varsOf (Kore.Pattern.and KoreAML.R [.not KoreAML.R (KoreAML.anyOf comps), P])
      rw [KoreAML.varsOf]
      exact List.mem_append_left _ (List.mem_singleton_self _))
    show (KoreAML.tr ⟨tbl, []⟩ (Kore.Pattern.and KoreAML.R [.not KoreAML.R (KoreAML.anyOf comps), P])).interpret I e m0
    rw [tr_and2, KoreAML.interp_sAnd]
    refine ⟨?_, withPre_holdsCl
      (premise_holds4 hI hnn hph htr hfnm hws hσ' hmatch (OvlOK.nfs_bridge inferInstance hpats) hag hX hRv hσr2 hm0 (ihreq tbl e hag))
      (fun k hk => hkeys k (hP k hk)) (fun hpt hkp hRk => ihpre hpt tbl e σr m0 hag hkp hRk hRv hσr2 hm0)⟩
    rw [KoreAML.tr, KoreAML.interp_sNot]
    refine ⟨?_, (KoreAML.interp_inhOf_of hRv).mpr hm0⟩
    rw [anyOf_eq]
    refine anyOfC_empty hD isFree_R comps (fun φ hφ => ?_)
    obtain ⟨cl', hcl', rfl⟩ := List.mem_map.mp hφ
    obtain ⟨-, -, -, hpl', hf', hmf'⟩ := hothers cl' hcl'
    exact hpl' hws hf' hmf'
      (fun i hi hil => hkeys _ (hN _ (mem_varsOf_anyOfC hφ (varsOf_exclusionCl hi hil))))
      (fun hpt k hk => hkeys _ (hN _ (mem_varsOf_anyOfC hφ (varsOf_exclusion_preCl hpt hk))))
      (fun j s hj => hkeys _ (hP _ (HoldsShape.varsOf_withPre_prem (hv.1 j _ (by rw [List.getElem?_map, hj]; rfl)))))
      hRkey (fun j w s hw hs => hX j w _ hw (by rw [List.getElem?_map, hs]; rfl)) hR' hσr2 m0

/-- **A clause that decides, read in a model**: `clause_den4` (and `clause_den3`) for a clause whose
variables each occur in it, with a well-sorted predicate that holds at `R` where it is not `\top`
(`ihpre`) and a `\top` right side's predicate, the clauses of a smaller priority it negates each
with an empty exclusion where it fails (`ExclEmptyCl`) and failing at the arguments, at values and
in the model. -/
theorem clause_den4Cl [Inhabited M] (hI : I ⊧ᴵP Γ c) (hnn : NamesNumbered c) (hsc : SortCtx c) [OvlOK c]
    (hph : patHooksApart c = true) {f : Sym} {fn : Fn} {cl : Clause} {ws : List GroundTerm} {σ' : Subst}
    {L : List CtorSig} {r : Option GroundTerm}
    (hfn : c.lookupFn f = some fn) (hcl : cl ∈ fn.clauses)
    (hws : c.sortsOf ws = some fn.args) (hσ' : c.WellSorted cl.vars σ') (hmatch : PatVals c σ' cl.pats ws)
    (hpats : sortsOfTerms c.patCtxAll cl.vars cl.pats = some fn.args)
    (hpreOK : c.condOK cl.vars cl.pre = true) (hpost : cl.post = .top) (hexs : cl.exs = [])
    (hocc : ∀ i < cl.vars.length, i ∈ varOccsList cl.pats ++ cl.condVars ++
      varOccs cl.rhs ++ (cl.ens.map varOccs).getD [] ++ varOccsCond cl.vars.length cl.post)
    (hreqs : ∀ t, cl.req = some t → sortOfTerm (c.rhsCtx L) cl.vars t = some Srt.bool)
    (hrhss : sortOfTerm (c.rhsCtx L) cl.vars cl.rhs = some fn.result)
    (henss : ∀ t, cl.ens = some t → sortOfTerm (c.rhsCtx L) cl.vars t = some Srt.bool)
    (hr : ∀ v, r = some v → c.sortOf v = some fn.result)
    (ihright : ∀ (tbl : VarTable) (e' : Valuation M), Agrees c I tbl (canonVars c cl.vars) σ' e' →
      ∀ m', (KoreAML.tr ⟨tbl, []⟩ (clauseRight c fn cl)).interpret I e' m' ↔ Res c I e' r m')
    (ihreq : ∀ t, cl.req = some t → ∀ (tbl : VarTable) (e' : Valuation M), Agrees c I tbl (canonVars c cl.vars) σ' e' →
      ∀ m', (KoreAML.tr ⟨tbl, []⟩ (Term.kore c (canonVars c cl.vars) t)).interpret I e' m' ↔
        (den c (bool true)).interpret I e' m')
    (ihpre : cl.pre.isTop = false → ∀ (tbl : VarTable) (e : Valuation M) (σr m0 : M),
      Agrees c I tbl (canonVars c cl.vars) σ' e →
      (∀ k ∈ KoreAML.varsOf (Cond.kore c (canonVars c cl.vars) KoreAML.R cl.pre), k ∈ tbl) →
      VarKey.sortVar "R" ∈ tbl → (∀ a, (KoreAML.trSort tbl KoreAML.R).interpret I e a ↔ a = σr) → IsSort I σr →
      Inh I σr m0 → (KoreAML.tr ⟨tbl, []⟩ (Cond.kore c (canonVars c cl.vars) KoreAML.R cl.pre)).interpret I e m0)
    (hlow : ∀ cl' ∈ fn.clauses, cl'.aside = false → cl'.prio < cl.prio →
      c.condOK cl'.vars cl'.pre = true ∧ sortsOfTerms c.patCtxAll cl'.vars cl'.pats = some fn.args ∧
      (∀ t, cl'.req = some t → ∀ i ∈ varOccs t, i < cl'.vars.length) ∧
      ExclEmptyCl c I fn cl' ∧ Fails c ws cl' ∧ ModelFailsCl c I cl' ws)
    (e : Valuation M) (m : M) :
    (KoreAML.den (symApp c f (GroundTerm.koreList c ws))).interpret I e m ↔ Res c I e r m := by
  have hreqv : ∀ t, cl.req = some t → ∀ i ∈ varOccs t, i < cl.vars.length := fun t ht => varOccs_lt t (hreqs t ht)
  have hrhsv := varOccs_lt _ hrhss
  have hensv : ∀ t, cl.ens = some t → ∀ i ∈ varOccs t, i < cl.vars.length := fun t ht => varOccs_lt t (henss t ht)
  have ihreq' := fun tbl e' hag t ht m' => ihreq t ht tbl e' hag m'
  by_cases hlow' : lowerClauses fn cl = []
  · exact plain_eq4Cl hI hnn hph hsc.trans hfn (clauseEquation_mem hcl hlow') hws hσ' hmatch hpats
      hpreOK hpost hexs hocc hreqv hrhsv hensv hr ihreq' ihpre ihright e m
  · refine compete_eq4Cl hI hnn hph hsc.trans hfn (competingEquation_mem hcl hlow') hws (fun cl' hcl' => ?_) hσ' hmatch
      hpats hpreOK hpost hexs hocc hreqv hrhsv hensv hr ihreq' ihpre ihright e m
    obtain ⟨hcl'', hna'', hlt⟩ := mem_lowerClauses.mp hcl'
    exact hlow cl' hcl'' hna'' hlt

end

end Faithful

end KCore
