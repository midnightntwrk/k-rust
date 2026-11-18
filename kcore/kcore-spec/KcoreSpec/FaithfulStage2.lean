/-
  KCore. Step soundness for the second stage: functions with clauses of several priorities (an
  `[owise]` clause among them), and rules with priorities. Every called function is total and every
  pattern plain, as in the first stage.

  The equations of `Γ` that these read have a negated premise: a clause's excludes the clauses of
  a smaller priority (`lowerClauses`), a rule's the rules of a smaller priority.
  Where the kernel says the excluded clauses fail (`Fails`) or the excluded rules do not apply
  (`NotApplies`), the negated patterns are empty in every model (`exclusion_empty`,
  `applies_empty`, FaithfulNeg.lean), so the negation holds and the equation, or the rule's axiom,
  fires as in the first stage.
-/
import KcoreSpec.FaithfulNeg

set_option autoImplicit false

namespace KCore

namespace Faithful

open ML
open KoreAML (DefOK Inh IsSort Closed KGround VarKey VarTable)

/-! ## Free variables under binders -/

mutual
  theorem freeOf_kore_bound (c : Semantics) (vs : List KoreAML.Var) : ∀ (t : Term) {bound : List VarKey} {k : VarKey},
      k ∈ KoreAML.freeOf bound (Term.kore c vs t) →
        bound.contains k = false ∧ ∃ i ∈ varOccs t, k = KoreAML.evarKey (vs.getD i default).kore
    | .var i, bound, k, h => by
      rw [Term.kore] at h; unfold KoreAML.varAt at h; rw [KoreAML.freeOf] at h
      split at h
      · cases h
      · rename_i hb
        rw [mem_one h]
        exact ⟨by simpa using hb, i, by simp [varOccs], rfl⟩
    | .app f ts, bound, k, h => by
      rw [kore_app] at h
      obtain ⟨hd, ss, he, _⟩ := symApp_cases c f (Term.koreList c vs ts)
      rw [he, KoreAML.freeOf] at h
      obtain ⟨hb, i, hi, rfl⟩ := freeOf_koreList_bound c vs ts h
      exact ⟨hb, i, by rw [varOccs]; exact hi, rfl⟩
    | .inj a b t, bound, k, h => by
      rw [Term.kore] at h; unfold KoreAML.injP at h; rw [KoreAML.freeOf, KoreAML.freeOfList, KoreAML.freeOfList] at h
      simp only [List.append_nil] at h
      obtain ⟨hb, i, hi, rfl⟩ := freeOf_kore_bound c vs t h
      exact ⟨hb, i, by rw [varOccs]; exact hi, rfl⟩
    | .as t j, bound, k, h => by
      rw [Term.kore] at h
      rw [KoreAML.freeOf, KoreAML.freeOfList, KoreAML.freeOfList, KoreAML.freeOfList] at h
      simp only [List.append_nil, List.mem_append] at h
      rcases h with h | h
      · obtain ⟨hb, i, hi, rfl⟩ := freeOf_kore_bound c vs t h
        exact ⟨hb, i, by rw [varOccs]; exact List.mem_append_left _ hi, rfl⟩
      · unfold KoreAML.varAt at h; rw [KoreAML.freeOf] at h
        split at h
        · cases h
        · rename_i hb
          rw [mem_one h]
          exact ⟨by simpa using hb, j, by rw [varOccs]; exact List.mem_append_right _ (List.mem_singleton_self _), rfl⟩
    | .dv s lit, bound, k, h => by
      rw [Term.kore, KoreAML.freeOf] at h; cases h
  theorem freeOf_koreList_bound (c : Semantics) (vs : List KoreAML.Var) : ∀ (ts : List Term) {bound : List VarKey}
      {k : VarKey}, k ∈ KoreAML.freeOfList bound (Term.koreList c vs ts) →
        bound.contains k = false ∧ ∃ i ∈ varOccsList ts, k = KoreAML.evarKey (vs.getD i default).kore
    | [], bound, k, h => by rw [Term.koreList, KoreAML.freeOfList] at h; cases h
    | t :: ts, bound, k, h => by
      rw [Term.koreList, KoreAML.freeOfList] at h
      rcases List.mem_append.mp h with h | h
      · obtain ⟨hb, i, hi, rfl⟩ := freeOf_kore_bound c vs t h
        exact ⟨hb, i, by rw [varOccsList]; exact List.mem_append_left _ hi, rfl⟩
      · obtain ⟨hb, i, hi, rfl⟩ := freeOf_koreList_bound c vs ts h
        exact ⟨hb, i, by rw [varOccsList]; exact List.mem_append_right _ hi, rfl⟩
end

/-- Under the binders of `existsAll`, the bound variables are the binders' and the outer ones. -/
theorem freeOf_existsAll {S : Kore.KSort} {body : Kore.Pattern} : ∀ (bs : List Kore.EVar) {bound : List VarKey} {k : VarKey},
    k ∈ KoreAML.freeOf bound (KoreAML.existsAll S bs body) →
    ∃ bound' : List VarKey, (∀ x, bound'.contains x = true ↔ (x ∈ bs.map KoreAML.evarKey ∨ bound.contains x = true)) ∧
      k ∈ KoreAML.freeOf bound' body
  | [], bound, k, h => ⟨bound, fun x => by simp, h⟩
  | b :: bs, bound, k, h => by
    have h' : k ∈ KoreAML.freeOf bound (.exist S b (KoreAML.existsAll S bs body)) := h
    rw [KoreAML.freeOf] at h'
    obtain ⟨bound', hb', hk⟩ := freeOf_existsAll bs h'
    refine ⟨bound', fun x => ?_, hk⟩
    rw [hb']
    simp only [List.contains_cons, Bool.or_eq_true, beq_iff_eq, List.map_cons, List.mem_cons]
    constructor
    · rintro (h | h | h)
      · exact Or.inl (Or.inr h)
      · exact Or.inl (Or.inl h)
      · exact Or.inr h
    · rintro ((h | h) | h)
      · exact Or.inr (Or.inl h)
      · exact Or.inl h
      · exact Or.inr (Or.inr h)

/-! ## An equation of `Γ`, read in a model -/

section
variable {c : Semantics} {M : Type} {I : Interpretation KoreAML.Sym M}

/-- **An equation of a function, read in a model**, whatever its premise. At arguments of `f`'s
sorts and a well-sorted σ' for the clause's variables, if the premise holds at every valuation of
the equation's table that gives each `Xⱼ` the argument's element, each variable its value's
element under σ', and `R` a sort (`hprem`), then `f` applied to the arguments' elements is what
the right-hand side denotes under σ'. The premise's free variables are formal arguments and the
clause's variables (`hfree`), which occur in it (`hXin`, `hVin`). -/
theorem eqn_at [Inhabited M] (hI : I ⊧ᴵP Γ c) [OvlOK c] (hnn : NamesNumbered c)
    {f : Sym} {fn : Fn} (hfn : c.lookupFn f = some fn) {cl : Clause} {prem : Kore.Pattern}
    (hmem : KoreAML.trAxiom [] [] ⟨0, "kernel",
      { sortVars := [KoreAML.Rv], pattern := .implies KoreAML.R prem (clauseConcl c fn cl), attributes := [] }⟩ ∈ fnItems c)
    {ws : List GroundTerm} (hws : c.sortsOf ws = some fn.args)
    {σ' : Subst} (hσ' : c.WellSorted cl.vars σ')
    (hXin : ∀ (j : Nat) s, (fn.args.map c.sortName)[j]? = some s →
      VarKey.evar ("X" ++ toString j) (KoreAML.srt s) ∈ KoreAML.varsOf prem)
    (hVin : ∀ i < cl.vars.length, canonKey c cl.vars i ∈ KoreAML.varsOf prem)
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
  have hVmem : ∀ i, i < cl.vars.length → canonKey c cl.vars i ∈ tbl := fun i hi => hvarsP _ (hVin i hi)
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
      · rw [freeOf_symApp] at hk
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
      ((KoreAML.tr ⟨tbl, []⟩ (symApp c fn.label
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
      (KoreAML.tr ⟨tbl, []⟩ (symApp c fn.label
        (KoreAML.vars (KoreAML.numbered "X" 0 (fn.args.map c.sortName))))).interpret I e' m := by
    intro m
    unfold KoreAML.den
    rw [tr_symApp, tr_symApp]
    refine call_congr (e0 := e0) (e' := e') (fn.args.map c.sortName) ws 0 _ _ (by rw [List.length_map]; exact hlen)
      (fun k s w hk hw m => ?_) (fun m => symHead_congr (e := e0) (e' := e') _ m) m
    rw [Nat.zero_add, hXv k s w hk hw]
    obtain ⟨a, -, hsw⟩ := hargsort k s w hk hw
    exact (elemOf_spec hI hsw e0).1 m
  have harity : ∀ a, (KoreAML.tr ⟨tbl, []⟩ (symApp c fn.label
      (KoreAML.vars (KoreAML.numbered "X" 0 (fn.args.map c.sortName))))).interpret I e' a → Inh I σr a := by
    intro a ha
    refine (KoreAML.interp_inhOf_of (S := KoreAML.sym _) hσr1).mp (symArity_at hI (fn_sig_mem hfnm) e' a ?_)
    rw [tr_symApp] at ha
    have := call_arity (fn.args.map c.sortName) 0 _ (symHead c fn.label) a ha
      (fun k s hk => ?_) (fun _ h => h)
    · exact this
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

/-! ## The parts of a premise -/

section
variable {c : Semantics}

/-- The formal arguments and the clause's variables occur in its premise `⌈req = true⌉ ∧ X̄ ∈ p̄`;
nothing else is free in it. -/
theorem premise_vars {fn : Fn} {cl : Clause} (hpats : sortsOfTerms c.patCtxAll cl.vars cl.pats = some fn.args)
    (hbinds : ∀ i < cl.vars.length, i ∈ varOccsList cl.pats)
    (hreqv : ∀ t, cl.req = some t → ∀ i ∈ varOccs t, i < cl.vars.length) :
    let prem := premise (fn.args.map c.sortName) (cl.req.map (Term.kore c (canonVars c cl.vars)))
      (Term.koreList c (canonVars c cl.vars) cl.pats)
    (∀ (j : Nat) s, (fn.args.map c.sortName)[j]? = some s →
      VarKey.evar ("X" ++ toString j) (KoreAML.srt s) ∈ KoreAML.varsOf prem) ∧
    (∀ i < cl.vars.length, canonKey c cl.vars i ∈ KoreAML.varsOf prem) ∧
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
  · have h1 := varsOf_koreList c vs cl.pats (hbinds i hi)
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

/-- The exclusion of a clause has the formal arguments as its only free variables. -/
theorem freeOf_exclusion {fn : Fn} {cl : Clause} (hpre : cl.pre = .top)
    (hpats : sortsOfTerms c.patCtxAll cl.vars cl.pats = some fn.args)
    (hreqv : ∀ t, cl.req = some t → ∀ i ∈ varOccs t, i < cl.vars.length)
    (hbd : binds cl.vars.length (varOccsList cl.pats) = true) {bound : List VarKey} {k : VarKey}
    (hk : k ∈ KoreAML.freeOf bound (exclusion c fn cl (canonClausePres cl))) :
    ∃ (j : Nat) (s : String), (fn.args.map c.sortName)[j]? = some s ∧ k = .evar ("X" ++ toString j) (KoreAML.srt s) := by
  rw [exclusion_top _ hpre hbd] at hk
  let vs := canonVars c cl.vars
  obtain ⟨bound', hb', hk⟩ := freeOf_existsAll (S := KoreAML.R)
    (body := premise (fn.args.map c.sortName) (cl.req.map (Term.kore c vs)) (Term.koreList c vs cl.pats))
    (vs.map KoreAML.Var.kore) hk
  have hbound : ∀ i < cl.vars.length, bound'.contains (canonKey c cl.vars i) = true := fun i hi => by
    have hlt : i < vs.length := by rw [canonVars_length]; exact hi
    refine (hb' _).mpr (Or.inl (List.mem_map.mpr ⟨(vs.getD i default).kore, ?_, rfl⟩))
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]
    exact List.mem_map_of_mem (List.getElem_mem hlt)
  unfold premise at hk
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
        have h2 : bound'.contains (KoreAML.evarKey (vs.getD i default).kore) = true := hbound i (hreqv t hq i hi)
        rw [hb] at h2; cases h2
      · rw [KoreAML.freeOf] at hk; cases hk
  · rcases freeOf_argsConj _ 0 hk with ⟨n, s, p, hn, rfl⟩ | ⟨q, hq, hk⟩
    · exact ⟨n, s, (List.getElem?_zip_eq_some.mp hn).1, by rw [Nat.zero_add]⟩
    · exfalso
      have hq2 := (List.of_mem_zip (a := q.1) (b := q.2) hq).2
      obtain ⟨hb, i, hi, rfl⟩ := freeOf_koreList_bound c vs cl.pats (mem_freeOfList hq2 hk)
      have h2 : bound'.contains (KoreAML.evarKey (vs.getD i default).kore) = true := hbound i (varOccsList_lt cl.pats hpats i hi)
      rw [hb] at h2; cases h2

/-- A rule's `applies` pattern has no free variable. -/
theorem freeOf_applies {r : Rule} (hlhs : sortOfTerm c.patCtxAll r.vars r.lhs = some topCellSort)
    (hreqv : ∀ t, r.req = some t → ∀ i ∈ varOccs t, i < r.vars.length) (hpre : r.pre = .top)
    (hb : binds r.vars.length (varOccs r.lhs) = true) {bound : List VarKey} {k : VarKey}
    (hk : k ∈ KoreAML.freeOf bound (applies c r (canonRulePres r))) : False := by
  rw [applies_top _ hpre hb] at hk
  let vs := canonVars c r.vars
  obtain ⟨bound', hb', hk⟩ := freeOf_existsAll (S := srtOf c topCellSort)
    (body := .and (srtOf c topCellSort) [Term.kore c vs r.lhs, reqPat (srtOf c topCellSort) (r.req.map (Term.kore c vs))])
    (vs.map KoreAML.Var.kore) hk
  have hbound : ∀ i < r.vars.length, bound'.contains (canonKey c r.vars i) = true := fun i hi => by
    have hlt : i < vs.length := by rw [canonVars_length]; exact hi
    refine (hb' _).mpr (Or.inl (List.mem_map.mpr ⟨(vs.getD i default).kore, ?_, rfl⟩))
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]
    exact List.mem_map_of_mem (List.getElem_mem hlt)
  rw [KoreAML.freeOf, KoreAML.freeOfList, KoreAML.freeOfList, KoreAML.freeOfList] at hk
  simp only [List.append_nil, List.mem_append] at hk
  rcases hk with hk | hk
  · obtain ⟨hb, i, hi, rfl⟩ := freeOf_kore_bound c vs r.lhs hk
    have h2 : bound'.contains (KoreAML.evarKey (vs.getD i default).kore) = true := hbound i (varOccs_lt r.lhs hlhs i hi)
    rw [hb] at h2; cases h2
  · cases hq : r.req with
    | none =>
      rw [hq] at hk; simp only [Option.map_none, reqPat] at hk; rw [KoreAML.freeOf] at hk; cases hk
    | some t =>
      rw [hq] at hk; simp only [Option.map_some, reqPat] at hk
      rw [KoreAML.freeOf] at hk
      rcases List.mem_append.mp hk with hk | hk
      · obtain ⟨hb, i, hi, rfl⟩ := freeOf_kore_bound c vs t hk
        have h2 : bound'.contains (KoreAML.evarKey (vs.getD i default).kore) = true := hbound i (hreqv t hq i hi)
        rw [hb] at h2; cases h2
      · rw [KoreAML.freeOf] at hk; cases hk

theorem varsOf_existsAll_binder {S : Kore.KSort} {body : Kore.Pattern} :
    ∀ (bs : List Kore.EVar) {b : Kore.EVar}, b ∈ bs → KoreAML.evarKey b ∈ KoreAML.varsOf (KoreAML.existsAll S bs body)
  | [], _, h => absurd h List.not_mem_nil
  | b' :: bs, b, h => by
    show _ ∈ KoreAML.varsOf (.exist S b' (KoreAML.existsAll S bs body))
    rw [KoreAML.varsOf]
    rcases List.mem_cons.mp h with rfl | h
    · exact List.mem_append_left _ (List.mem_append_right _ (List.mem_singleton_self _))
    · exact List.mem_append_right _ (varsOf_existsAll_binder bs h)

/-- The binders of a clause's exclusion, and of a rule's `applies`, are its canonical variables. -/
theorem varsOf_exclusion {fn : Fn} {cl : Clause} {i : Nat} (hpre : cl.pre = .top)
    (hbd : binds cl.vars.length (varOccsList cl.pats) = true) (hi : i < cl.vars.length) :
    canonKey c cl.vars i ∈ KoreAML.varsOf (exclusion c fn cl (canonClausePres cl)) := by
  rw [exclusion_top _ hpre hbd]
  have hlt : i < (canonVars c cl.vars).length := by rw [canonVars_length]; exact hi
  refine varsOf_existsAll_binder (S := KoreAML.R) (body := premise _ _ _) _ ?_
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]
  exact List.mem_map_of_mem (List.getElem_mem hlt)

theorem varsOf_applies {r : Rule} {i : Nat} (hpre : r.pre = .top)
    (hb : binds r.vars.length (varOccs r.lhs) = true) (hi : i < r.vars.length) :
    canonKey c r.vars i ∈ KoreAML.varsOf (applies c r (canonRulePres r)) := by
  rw [applies_top _ hpre hb]
  have hlt : i < (canonVars c r.vars).length := by rw [canonVars_length]; exact hi
  refine varsOf_existsAll_binder (S := srtOf c topCellSort) (body := .and _ _) _ ?_
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]
  exact List.mem_map_of_mem (List.getElem_mem hlt)

theorem anyOf_eq : ∀ comps : List Kore.Pattern, KoreAML.anyOf comps = anyOfC KoreAML.R comps
  | [] => rfl
  | e :: es => by rw [KoreAML.anyOf, anyOfC, anyOf_eq es]

theorem mem_freeOf_anyOfC {S : Kore.KSort} {bound : List VarKey} {k : VarKey} : ∀ {comps : List Kore.Pattern},
    k ∈ KoreAML.freeOf bound (anyOfC S comps) → ∃ φ ∈ comps, k ∈ KoreAML.freeOf bound φ
  | [], h => by rw [anyOfC, KoreAML.freeOf] at h; cases h
  | φ :: comps, h => by
    rw [anyOfC, KoreAML.freeOf, KoreAML.freeOfList, KoreAML.freeOfList, KoreAML.freeOfList] at h
    simp only [List.append_nil, List.mem_append] at h
    rcases h with h | h
    · exact ⟨φ, List.mem_cons_self .., h⟩
    · obtain ⟨ψ, hψ, h⟩ := mem_freeOf_anyOfC h
      exact ⟨ψ, List.mem_cons_of_mem _ hψ, h⟩

theorem mem_varsOf_anyOfC {S : Kore.KSort} {k : VarKey} {φ : Kore.Pattern} : ∀ {comps : List Kore.Pattern},
    φ ∈ comps → k ∈ KoreAML.varsOf φ → k ∈ KoreAML.varsOf (anyOfC S comps)
  | [], h, _ => absurd h List.not_mem_nil
  | ψ :: comps, h, hk => by
    rw [anyOfC, KoreAML.varsOf, KoreAML.varsOfList, KoreAML.varsOfList]
    rcases List.mem_cons.mp h with rfl | h
    · exact List.mem_append_right _ (List.mem_append_left _ hk)
    · exact List.mem_append_right _ (List.mem_append_right _ (List.mem_append_left _ (mem_varsOf_anyOfC h hk)))

end

section
variable {M : Type} {I : Interpretation KoreAML.Sym M}

/-- A disjunction whose disjuncts are all empty at an element is empty there. -/
theorem anyOfC_empty (hD : DefOK I) {tbl : VarTable} {S : Kore.KSort} (hS : (KoreAML.trSort tbl S).isFreeEvar KoreAML.topVar = false)
    {e : Valuation M} {m : M} : ∀ comps : List Kore.Pattern,
    (∀ φ ∈ comps, ¬ (KoreAML.tr ⟨tbl, []⟩ φ).interpret I e m) → ¬ (KoreAML.tr ⟨tbl, []⟩ (anyOfC S comps)).interpret I e m
  | [], _, h => by
    rw [anyOfC, KoreAML.tr] at h
    unfold KoreAML.sBot at h
    rw [KoreAML.interp_sNot, KoreAML.interp_sTop hD hS] at h
    exact h.1 h.2
  | φ :: comps, hall, h => by
    rw [anyOfC, KoreAML.tr] at h
    simp only [KoreAML.trOrList] at h
    rw [KoreAML.interp_sOr] at h
    rcases h.2 with h | h
    · exact hall φ (List.mem_cons_self ..) h
    · exact anyOfC_empty hD hS comps (fun ψ hψ => hall ψ (List.mem_cons_of_mem _ hψ)) h

end

/-! ## The equations of a function in `Γ` -/

section
variable {c : Semantics}

theorem eqn_item_mem {fn : Fn} (hfn : fn ∈ c.allFns) {ax : Kore.Axiom} (h : Kore.Sentence.axiom ax ∈ fnEquationsK c fn) :
    KoreAML.trAxiom [] [] ⟨0, "kernel", ax⟩ ∈ fnItems c := by
  unfold fnItems
  refine List.mem_flatMap.mpr ⟨fn, hfn, ?_⟩
  unfold kernelItems
  exact List.mem_filterMap.mpr ⟨_, h, rfl⟩

theorem mem_lowerClauses {fn : Fn} {cl cl' : Clause} :
    cl' ∈ lowerClauses fn cl ↔ cl' ∈ fn.clauses ∧ cl'.aside = false ∧ cl'.prio < cl.prio := by
  simp [lowerClauses]

/-- A clause with no clause of a smaller priority has its equation without competitors. -/
theorem clauseEquation_mem {fn : Fn} {cl : Clause} (hcl : cl ∈ fn.clauses)
    (hlow : lowerClauses fn cl = []) : clauseEquation c fn cl ∈ fnEquationsK c fn :=
  List.mem_map.mpr ⟨cl, hcl, by simp [prioEquation, hlow]⟩

/-- A clause with clauses of a smaller priority has its equation with them negated. -/
theorem competingEquation_mem {fn : Fn} {cl : Clause} (hcl : cl ∈ fn.clauses)
    (hlow : lowerClauses fn cl ≠ []) :
    competingEquation c fn (lowerClauses fn cl) cl ∈ fnEquationsK c fn :=
  List.mem_map.mpr ⟨cl, hcl, by simp [prioEquation, List.isEmpty_iff, hlow]⟩

end

section
variable {c : Semantics} {M : Type} {I : Interpretation KoreAML.Sym M}

/-- **A clause's premise, read in a model**: at a valuation that gives the formal arguments the
arguments' elements and the clause's variables their values' under a match σ', where its
`requires` denotes `true`, `⌈req = true⌉ ∧ X̄ ∈ p̄` holds. -/
theorem premise_holds [Inhabited M] (hI : I ⊧ᴵP Γ c) [OvlOK c] (hnn : NamesNumbered c)
    (htr : ∀ a b d, (a, b) ∈ c.subsorts → (b, d) ∈ c.subsorts → (a, d) ∈ c.subsorts)
    {fn : Fn} (hfnm : fn ∈ c.allFns) {cl : Clause} {ws : List GroundTerm} (hws : c.sortsOf ws = some fn.args)
    {σ' : Subst} (hσ' : c.WellSorted cl.vars σ') (hmatch : PatVals c σ' cl.pats ws)
    (hplain : plainPats c cl.pats = true) (hpats : sortsOfTerms c.patCtxAll cl.vars cl.pats = some fn.args)
    {tbl : VarTable} {e : Valuation M} {σr m0 : M} (hag : Agrees c I tbl (canonVars c cl.vars) σ' e)
    (hX : ∀ (j : Nat) w s, ws[j]? = some w → (fn.args.map c.sortName)[j]? = some s →
      e.evalEvar (tbl.ev (.evar ("X" ++ toString j) (KoreAML.srt s))) = elemOf c I w)
    (hRv : ∀ a, (KoreAML.trSort tbl KoreAML.R).interpret I e a ↔ a = σr) (hσr2 : IsSort I σr) (hm0 : Inh I σr m0)
    (ihreq : ∀ t, cl.req = some t → ∀ m, (KoreAML.tr ⟨tbl, []⟩ (Term.kore c (canonVars c cl.vars) t)).interpret I e m ↔
      (den c (bool true)).interpret I e m) :
    (KoreAML.tr ⟨tbl, []⟩ (premise (fn.args.map c.sortName) (cl.req.map (Term.kore c (canonVars c cl.vars)))
      (Term.koreList c (canonVars c cl.vars) cl.pats))).interpret I e m0 := by
  have hD := defOK hI
  have hc := sat_sigItem hI (sig_ceilDef (c := c))
  have hnum := hnn.2.2 fn hfnm
  obtain ⟨σB, hσB1, hσB2⟩ := sortSing hI (bool_numbered (c := c))
  rw [sortName_bool] at hσB1
  unfold premise
  rw [tr_and2, KoreAML.interp_sAnd]
  refine ⟨?_, argsConj_den hI hnn.1 htr hσ' (canonVars_length c cl.vars) hag hRv hσr2 hm0 hmatch fn.args 0
    hplain hpats (fun s hs => hnum s (List.mem_cons_of_mem _ hs)) ?_⟩
  · cases hq : cl.req with
    | none =>
      simp only [Option.map_none, reqPat]
      rw [KoreAML.tr, KoreAML.interp_sTop hD isFree_R, KoreAML.interp_inhOf_of hRv]
      exact hm0
    | some t =>
      simp only [Option.map_some, reqPat]
      rw [KoreAML.tr, KoreAML.interp_sEquals hD hc (by rw [trSort_srt]; exact hσB1) hRv hσB2 hσr2]
      refine ⟨hm0, fun a _ => ?_⟩
      rw [ihreq t hq a, KoreAML.tr_dv]
      unfold den KoreAML.den bool
      rw [GroundTerm.kore, sortName_bool, KoreAML.tr_dv]
      exact Iff.rfl
  · intro k s w hk hw m'
    rw [Nat.zero_add]
    obtain ⟨w', hw', hsw⟩ := sortsOf_get hws hk
    rw [hw] at hw'; cases hw'
    rw [hX k w (c.sortName s) hw (by rw [List.getElem?_map, hk]; rfl)]
    exact ((elemOf_spec hI hsw e).1 m').symm

/-- **An ordinary clause's equation, read in a model** (`clauseEquation`, present for every
clause with no clause of a smaller priority). -/
theorem plain_eq [Inhabited M] (hI : I ⊧ᴵP Γ c) [OvlOK c] (hnn : NamesNumbered c)
    (htr : ∀ a b d, (a, b) ∈ c.subsorts → (b, d) ∈ c.subsorts → (a, d) ∈ c.subsorts)
    {f : Sym} {fn : Fn} (hfn : c.lookupFn f = some fn) {cl : Clause}
    (hmem : clauseEquation c fn cl ∈ fnEquationsK c fn) (hpre : cl.pre = .top) (hexs : cl.exs = [])
    {ws : List GroundTerm} (hws : c.sortsOf ws = some fn.args)
    {σ' : Subst} (hσ' : c.WellSorted cl.vars σ') (hmatch : PatVals c σ' cl.pats ws)
    (hplain : plainPats c cl.pats = true) (hpats : sortsOfTerms c.patCtxAll cl.vars cl.pats = some fn.args)
    (hbinds : ∀ i < cl.vars.length, i ∈ varOccsList cl.pats)
    (hreqv : ∀ t, cl.req = some t → ∀ i ∈ varOccs t, i < cl.vars.length)
    (hrhsv : ∀ i ∈ varOccs cl.rhs, i < cl.vars.length)
    (hensv : ∀ t, cl.ens = some t → ∀ i ∈ varOccs t, i < cl.vars.length)
    {r : Option GroundTerm} (hr : ∀ v, r = some v → c.sortOf v = some fn.result)
    (ihreq : ∀ (tbl : VarTable) (e : Valuation M), Agrees c I tbl (canonVars c cl.vars) σ' e →
      ∀ t, cl.req = some t → ∀ m, (KoreAML.tr ⟨tbl, []⟩ (Term.kore c (canonVars c cl.vars) t)).interpret I e m ↔
        (den c (bool true)).interpret I e m)
    (ihrhs : ∀ (tbl : VarTable) (e : Valuation M), Agrees c I tbl (canonVars c cl.vars) σ' e →
      ∀ m, (KoreAML.tr ⟨tbl, []⟩ (clauseRight c fn cl)).interpret I e m ↔ Res c I e r m)
    (e0 : Valuation M) (m : M) :
    (KoreAML.den (symApp c f (GroundTerm.koreList c ws))).interpret I e0 m ↔ Res c I e0 r m := by
  have hfnm := (lookupFn_spec hfn).1
  have hv := premise_vars (c := c) hpats hbinds hreqv
  rw [clauseEquation_top hpre hexs] at hmem
  exact eqn_at hI hnn hfn (prem := clausePrem c fn cl) (eqn_item_mem hfnm hmem) hws hσ' hv.1 hv.2.1 hv.2.2 hrhsv hensv hr
    (fun tbl e σr m0 _ hag hX hRv hσr2 hm0 =>
      premise_holds hI hnn htr hfnm hws hσ' hmatch hplain hpats hag hX hRv hσr2 hm0 (ihreq tbl e hag))
    ihrhs e0 m

/-- **A clause's equation under negated competitors, read in a model** (`competingEquation`: a
clause with clauses of a smaller priority). Where every competitor fails in the model, the
negation of their exclusions holds and the equation fires as an ordinary one. -/
theorem compete_eq [Inhabited M] (hI : I ⊧ᴵP Γ c) (hnn : NamesNumbered c) (hg : genWf c = true) [OvlOK c]
    (htr : ∀ a b d, (a, b) ∈ c.subsorts → (b, d) ∈ c.subsorts → (a, d) ∈ c.subsorts)
    {f : Sym} {fn : Fn} (hfn : c.lookupFn f = some fn) {others : List Clause} {cl : Clause}
    (hmem : competingEquation c fn others cl ∈ fnEquationsK c fn) (hpre : cl.pre = .top) (hexs : cl.exs = [])
    (hpres : ∀ cl' ∈ others, cl'.pre = .top) {ws : List GroundTerm} (hws : c.sortsOf ws = some fn.args)
    (hothers : ∀ cl' ∈ others, sortsOfTerms c.patCtxAll cl'.vars cl'.pats = some fn.args ∧
      (∀ i < cl'.vars.length, i ∈ varOccsList cl'.pats) ∧ (∀ t, cl'.req = some t → ∀ i ∈ varOccs t, i < cl'.vars.length) ∧
      plainPats c cl'.pats = true ∧ ModelFails c I cl' ws)
    {σ' : Subst} (hσ' : c.WellSorted cl.vars σ') (hmatch : PatVals c σ' cl.pats ws)
    (hplain : plainPats c cl.pats = true) (hpats : sortsOfTerms c.patCtxAll cl.vars cl.pats = some fn.args)
    (hbinds : ∀ i < cl.vars.length, i ∈ varOccsList cl.pats)
    (hreqv : ∀ t, cl.req = some t → ∀ i ∈ varOccs t, i < cl.vars.length)
    (hrhsv : ∀ i ∈ varOccs cl.rhs, i < cl.vars.length)
    (hensv : ∀ t, cl.ens = some t → ∀ i ∈ varOccs t, i < cl.vars.length)
    {r : Option GroundTerm} (hr : ∀ v, r = some v → c.sortOf v = some fn.result)
    (ihreq : ∀ (tbl : VarTable) (e : Valuation M), Agrees c I tbl (canonVars c cl.vars) σ' e →
      ∀ t, cl.req = some t → ∀ m, (KoreAML.tr ⟨tbl, []⟩ (Term.kore c (canonVars c cl.vars) t)).interpret I e m ↔
        (den c (bool true)).interpret I e m)
    (ihrhs : ∀ (tbl : VarTable) (e : Valuation M), Agrees c I tbl (canonVars c cl.vars) σ' e →
      ∀ m, (KoreAML.tr ⟨tbl, []⟩ (clauseRight c fn cl)).interpret I e m ↔ Res c I e r m)
    (e0 : Valuation M) (m : M) :
    (KoreAML.den (symApp c f (GroundTerm.koreList c ws))).interpret I e0 m ↔ Res c I e0 r m := by
  rw [competingEquation_top hpre hexs] at hmem
  have hfnm := (lookupFn_spec hfn).1
  have hD := defOK hI
  have hv := premise_vars (c := c) hpats hbinds hreqv
  let comps := others.map fun cl' => exclusion c fn cl' (canonClausePres cl')
  let P := premise (fn.args.map c.sortName) (cl.req.map (Term.kore c (canonVars c cl.vars)))
    (Term.koreList c (canonVars c cl.vars) cl.pats)
  have hP : ∀ k, k ∈ KoreAML.varsOf P →
      k ∈ KoreAML.varsOf (competingPremise (fn.args.map c.sortName) comps (cl.req.map (Term.kore c (canonVars c cl.vars)))
        (Term.koreList c (canonVars c cl.vars) cl.pats)) := fun k hk => by
    unfold competingPremise
    rw [KoreAML.varsOf, KoreAML.varsOfList, KoreAML.varsOfList, KoreAML.varsOfList]
    exact List.mem_append_right _ (List.mem_append_right _ (List.mem_append_left _ hk))
  have hN : ∀ k, k ∈ KoreAML.varsOf (anyOfC KoreAML.R comps) →
      k ∈ KoreAML.varsOf (competingPremise (fn.args.map c.sortName) comps (cl.req.map (Term.kore c (canonVars c cl.vars)))
        (Term.koreList c (canonVars c cl.vars) cl.pats)) := fun k hk => by
    unfold competingPremise
    rw [KoreAML.varsOf, KoreAML.varsOfList, KoreAML.varsOfList, KoreAML.varsOf, anyOf_eq]
    exact List.mem_append_right _ (List.mem_append_left _ (List.mem_append_right _ hk))
  refine eqn_at hI hnn hfn (eqn_item_mem hfnm hmem) hws hσ' (fun j s hj => hP _ (hv.1 j s hj))
    (fun i hi => hP _ (hv.2.1 i hi)) (fun k hk => ?_) hrhsv hensv hr (fun tbl e σr m0 hkeys hag hX hRv hσr2 hm0 => ?_) ihrhs e0 m
  · unfold competingPremise at hk
    rw [KoreAML.freeOf, KoreAML.freeOfList, KoreAML.freeOfList, KoreAML.freeOfList, KoreAML.freeOf] at hk
    simp only [List.append_nil, List.mem_append] at hk
    rcases hk with hk | hk
    · rw [anyOf_eq] at hk
      obtain ⟨φ, hφ, hk⟩ := mem_freeOf_anyOfC hk
      obtain ⟨cl', hcl', rfl⟩ := List.mem_map.mp hφ
      obtain ⟨hp', hb', hq', -, -⟩ := hothers cl' hcl'
      exact Or.inl (freeOf_exclusion (hpres cl' hcl') hp' hq' (binds_of_forall hb') hk)
    · exact hv.2.2 k hk
  · have hR' : e.evalEvar (tbl.ev (.sortVar "R")) = σr := (hRv _).mp (by rw [trSort_R, KoreAML.interp_evar])
    have hRkey : VarKey.sortVar "R" ∈ tbl := hkeys _ (by
      unfold competingPremise
      rw [KoreAML.varsOf]
      exact List.mem_append_left _ (List.mem_singleton_self _))
    unfold competingPremise
    rw [tr_and2, KoreAML.interp_sAnd]
    refine ⟨?_, premise_holds hI hnn htr hfnm hws hσ' hmatch hplain hpats hag hX hRv hσr2 hm0 (ihreq tbl e hag)⟩
    rw [KoreAML.tr, KoreAML.interp_sNot]
    refine ⟨?_, (KoreAML.interp_inhOf_of hRv).mpr hm0⟩
    rw [anyOf_eq]
    refine anyOfC_empty hD isFree_R comps (fun φ hφ => ?_)
    obtain ⟨cl', hcl', rfl⟩ := List.mem_map.mp hφ
    obtain ⟨hp', hb', -, hpl', hf'⟩ := hothers cl' hcl'
    exact exclusion_empty hI hg htr hnn.1 (hpres cl' hcl') hp' hb' hpl' hws
      (fun i hi => hkeys _ (hN _ (mem_varsOf_anyOfC hφ (varsOf_exclusion (hpres cl' hcl') (binds_of_forall hb') hi))))
      (fun j s hj => hkeys _ (hP _ (hv.1 j _ (by rw [List.getElem?_map, hj]; rfl))))
      hRkey (fun j w s hw hs => hX j w _ hw (by rw [List.getElem?_map, hs]; rfl)) hR' hσr2 hf' m0

end

/-! ## The second stage -/

/-- `f` may be called in the second stage: if it is a function of the definition, it has a defined
result at every argument list of its sorts. Its clauses may be of any priorities. -/
def Callable2 (c : Semantics) (f : Sym) : Prop :=
  ∀ fn, c.lookupFn f = some fn → ∀ vs, c.sortsOf vs = some fn.args → ∃ v, Eval c f vs (some v)

/-- **The second stage's scope.** The first stage's (`Stage1`) with its restrictions on
competitors lifted: a rule may have rules of a smaller priority, and a called function clauses of
several priorities. What stays: every rule's left-hand side and every clause's patterns are plain,
and every symbol a rule's or a clause's right-hand side, `requires` or `ensures` applies, and
each function among the symbols it overloads (`CallsAll`), is `Callable2` (total).
And the values are generated (`genWf`, decidable on the data), which the reading of a negated
premise takes: a value of a constructor sort is a constructor or an injection applied to values,
and distinct values of every sort are distinct elements. -/
def Stage2 (c : Semantics) : Prop :=
  genWf c = true ∧
  (∀ r ∈ c.rules, plainPat c r.lhs = true ∧
    ∀ f ∈ Term.heads r.rhs ++ (r.req.map Term.heads).getD [] ++ (r.ens.map Term.heads).getD [],
      CallsAll c (Callable2 c) f) ∧
  (∀ fn ∈ c.allFns, ∀ cl ∈ fn.clauses, plainPats c cl.pats = true ∧
      ∀ f ∈ Term.heads cl.rhs ++ (cl.req.map Term.heads).getD [] ++ (cl.ens.map Term.heads).getD [],
        CallsAll c (Callable2 c) f)

theorem callable2_of_callable {c : Semantics} {f : Sym} (h : Callable c f) : Callable2 c f :=
  fun fn hfn => (h fn hfn).2

section
variable {c : Semantics} {M : Type} {I : Interpretation KoreAML.Sym M}
variable [Inhabited M] (hI : I ⊧ᴵP Γ c) (hnn : NamesNumbered c) (hsc : SortCtx c) (hst : Stage2 c) [OvlOK c]
  (hok : c.sortedOK = true) (hbc : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, binds cl.vars.length (varOccsList cl.pats) = true) (hmi : CoherentAll c)
include hI hnn hsc hst hok hbc hmi

mutual
  /-- **L3, functions, second stage.** A function of the semantics that is callable in the second
  stage, at arguments of its sorts, applied to their elements, is what its result denotes:
  through its clause's equation, the clauses of a smaller priority it negates failing at the
  arguments. -/
  theorem eval_den2 (hpreTop : c.clausesPreTop = true) : ∀ {f : Sym} {ws : List GroundTerm} {r : Option GroundTerm}, Eval c f ws r →
      ∀ {fn : Fn}, c.lookupFn f = some fn → c.sortsOf ws = some fn.args → Callable2 c f →
      ∀ (e : Valuation M) m, (KoreAML.den (symApp c f (GroundTerm.koreList c ws))).interpret I e m ↔ Res c I e r m
    | _, _, _, .clause (fn := fn') (cl := cl) (σ := σ') hfn' hcl hσ' hmatch hreq _ hprio _ hrhs hens _,
        fn, hfn, hws, hcall, e, m => by
      rw [hfn] at hfn'; cases hfn'
      have hmem := (lookupFn_spec hfn).1
      obtain ⟨hpats, hbinds, L, hL, hreqs, hrhss, henss⟩ := clause_ctxE hok hbc hmem hcl
      obtain ⟨hplain, hcalls⟩ := hst.2.2 fn' hmem cl hcl
      have ihreq : ∀ (tbl : VarTable) (e' : Valuation M), Agrees c I tbl (canonVars c cl.vars) σ' e' →
          ∀ t, cl.req = some t → ∀ m', (KoreAML.tr ⟨tbl, []⟩ (Term.kore c (canonVars c cl.vars) t)).interpret I e' m' ↔
            (den c (bool true)).interpret I e' m' :=
        fun tbl e' hag t ht m' => evalTerm_den2 (hpreTop := hpreTop) (hreq t ht) hL hσ' (canonVars_length c cl.vars) hag (hreqs t ht)
          (fun g hg => hcalls g (List.mem_append_left _ (List.mem_append_right _ (by rw [ht]; exact hg)))) m'
      have hr : ∀ v, _ = some v → c.sortOf v = some fn'.result := fun v hv => EvalTerm.sorted hsc hrhs hL hσ' hrhss hv
      have ihrhs : ∀ (tbl : VarTable) (e' : Valuation M), Agrees c I tbl (canonVars c cl.vars) σ' e' →
          ∀ m', (KoreAML.tr ⟨tbl, []⟩ (clauseRight c fn' cl)).interpret I e' m' ↔ Res c I e' _ m' :=
        fun tbl e' hag => right_iff hI hnn hmem hr
          (fun m' => evalTerm_den2 (hpreTop := hpreTop) hrhs hL hσ' (canonVars_length c cl.vars) hag hrhss
            (fun g hg => hcalls g (List.mem_append_left _ (List.mem_append_left _ hg))) m')
          (fun t ht m' => evalTerm_den2 (hpreTop := hpreTop) (hens t ht) hL hσ' (canonVars_length c cl.vars) hag (henss t ht)
            (fun g hg => hcalls g (List.mem_append_right _ (by rw [ht]; exact hg))) m')
      have hreqv : ∀ t, cl.req = some t → ∀ i ∈ varOccs t, i < cl.vars.length := fun t ht => varOccs_lt t (hreqs t ht)
      have hrhsv := varOccs_lt _ hrhss
      have hensv : ∀ t, cl.ens = some t → ∀ i ∈ varOccs t, i < cl.vars.length := fun t ht => varOccs_lt t (henss t ht)
      by_cases hlow : lowerClauses fn' cl = []
      · exact plain_eq hI hnn hsc.trans hfn (clauseEquation_mem hcl hlow) (clause_preTop (hpreTop := hpreTop) hok hmem hcl) (clause_exsNil hok hmem hcl) hws hσ' hmatch hplain hpats
          hbinds hreqv hrhsv hensv hr ihreq ihrhs e m
      · refine compete_eq hI hnn hst.1 hsc.trans hfn (competingEquation_mem hcl hlow) (clause_preTop (hpreTop := hpreTop) hok hmem hcl)
          (clause_exsNil hok hmem hcl)
          (fun cl' hcl' => clause_preTop (hpreTop := hpreTop) hok hmem (mem_lowerClauses.mp hcl').1) hws (fun cl' hcl' => ?_)
          hσ' hmatch hplain hpats hbinds hreqv hrhsv hensv hr ihreq ihrhs e m
        obtain ⟨hcl'', hna'', hlt⟩ := mem_lowerClauses.mp hcl'
        obtain ⟨hp', hb', L', hL', hrq', -⟩ := clause_ctx hok hbc hmem hcl''
        exact ⟨hp', hb', fun t ht => varOccs_lt t (hrq' t ht), (hst.2.2 fn' hmem cl' hcl'').1,
          fails_den2 (hpreTop := hpreTop) (hprio cl' hcl'' hna'' hlt) hmem hcl''⟩
    | _, _, _, .rest (fn := fn') hfn' hnone, fn, hfn, hws, _, e, m => by
      rw [hfn] at hfn'; cases hfn'
      obtain ⟨hmem, hlab⟩ := lookupFn_spec hfn
      have h := rest_den hI hmem hws hnone e m
      rwa [hlab] at h
    | _, _, _, h@(.ensFails ..), fn, hfn, hws, hcall, e, m => by
      -- a callable function has a value at every argument list of its sorts, so none is its result
      obtain ⟨v, hv⟩ := hcall fn hfn _ hws
      exact absurd (Eval.functional hmi h hv) (by simp)
    | _, _, _, .clauseEx (fn := fn') hfn' hcl _ _ _ _ _ hne _ _ _ _, fn, hfn, _, _, _, _ => by
      rw [hfn] at hfn'; cases hfn'
      exact absurd (clause_exsNil hok (lookupFn_spec hfn).1 hcl) hne
    | _, _, _, .exNone (fn := fn') hfn' hcl hne _ _ _ _ _ _ _, fn, hfn, _, _, _, _ => by
      rw [hfn] at hfn'; cases hfn'
      exact absurd (clause_exsNil hok (lookupFn_spec hfn).1 hcl) hne
  termination_by structural _ _ _ h => h
  /-- A clause that fails at arguments of its function's sorts fails in the model. -/
  theorem fails_den2 (hpreTop : c.clausesPreTop = true) : ∀ {ws : List GroundTerm} {cl : Clause}, Fails c ws cl →
      ∀ {fn : Fn}, fn ∈ c.allFns → cl ∈ fn.clauses → ModelFails c I cl ws
    | _, _, .intro h, fn, hfn, hcl => fun σ hσ hpv tbl e hag => reqFails_den2 (hpreTop := hpreTop) (h σ (hσ.at _) hpv) hfn hcl hσ tbl e hag
  termination_by structural _ _ h => h
  theorem reqFails_den2 (hpreTop : c.clausesPreTop = true) : ∀ {σ : Subst} {cl : Clause}, ReqFails c σ cl →
      ∀ {fn : Fn}, fn ∈ c.allFns → cl ∈ fn.clauses → c.WellSorted cl.vars σ →
      ∀ (tbl : VarTable) (e : Valuation M), Agrees c I tbl (canonVars c cl.vars) σ e →
      ∃ t r, cl.req = some t ∧ r ≠ some (bool true) ∧ (∀ v, r = some v → c.sortOf v = some Srt.bool) ∧
        ∀ m, (KoreAML.tr ⟨tbl, []⟩ (Term.kore c (canonVars c cl.vars) t)).interpret I e m ↔ Res c I e r m
    | _, cl, .pre h, fn, hfn, hcl, hσ, tbl, e, hag => by
      rw [clause_preTop (hpreTop := hpreTop) hok hfn hcl] at h; exact absurd h.top_eq (by simp)
    | _, cl, .intro (t := t) (r := r) ht he hr, fn, hfn, hcl, hσ, tbl, e, hag => by
      obtain ⟨-, -, L, hL, hreqs, -⟩ := clause_ctx hok hbc hfn hcl
      obtain ⟨-, hcalls⟩ := hst.2.2 fn hfn cl hcl
      exact ⟨t, r, ht, hr, fun v hv => EvalTerm.sorted hsc he hL hσ (hreqs t ht) hv,
        evalTerm_den2 (hpreTop := hpreTop) he hL hσ (canonVars_length c cl.vars) hag (hreqs t ht)
          (fun g hg => hcalls g (List.mem_append_left _ (List.mem_append_right _ (by rw [ht]; exact hg))))⟩
  termination_by structural _ _ h => h
  /-- **L3, terms, second stage.** A well-sorted right-hand side or `requires` whose symbols are
  callable in the second stage, at a valuation that agrees with a well-sorted σ, translates to what
  its result under σ denotes: the value's element, or nothing where it is undefined. -/
  theorem evalTerm_den2 (hpreTop : c.clausesPreTop = true) : ∀ {σ : Subst} {t : Term} {r : Option GroundTerm}, EvalTerm c σ t r →
      ∀ {L : List CtorSig} {vars : List Srt} {vs : List KoreAML.Var} {tbl : VarTable} {e : Valuation M} {s : Srt},
      HeadsOK c L → c.WellSorted vars σ → vs.length = vars.length → Agrees c I tbl vs σ e →
      sortOfTerm (c.rhsCtx L) vars t = some s → (∀ f ∈ Term.heads t, CallsAll c (Callable2 c) f) →
      ∀ m, (KoreAML.tr ⟨tbl, []⟩ (Term.kore c vs t)).interpret I e m ↔ Res c I e r m
    | _, _, _, .var (i := i), L, vars, vs, tbl, e, s, hL, hσ, hvs, hag, ht, _, m => by
      have hi := sortOfTerm_var.mp ht
      have hlt : i < vs.length := by rw [hvs]; exact (List.getElem?_eq_some_iff.mp hi).1
      obtain ⟨v, hv, -⟩ := hσ i s hi
      rw [hv, tr_var]
      exact hag i v hlt hv m
    | _, _, _, .dv (s := s') (lit := lit), _, _, vs, tbl, e, _, _, _, _, _, _, _, m => by
      show _ ↔ (den c (.dv s' lit)).interpret I e m
      rw [Term.kore]; unfold den KoreAML.den; rw [GroundTerm.kore]; unfold srtOf
      rw [KoreAML.tr_dv, KoreAML.tr_dv]
    | _, _, _, .inj (a := a) (b := b) (t := t) (r := r) h', L, vars, vs, tbl, e, s, hL, hσ, hvs, hag, ht, hcall, m => by
      obtain ⟨hab, ht', -⟩ := sortOfTerm_inj.mp ht
      rw [Term.heads] at hcall
      have ih := evalTerm_den2 (hpreTop := hpreTop) h' hL hσ hvs hag ht' hcall
      rw [Term.kore, KoreAML.tr_injP]
      cases r with
      | none =>
        simp only [Option.map_none, Res, iff_false]
        exact injApp_empty (fun m h => ((ih m).mp h)) m
      | some w =>
        have hw := EvalTerm.sorted hsc h' hL hσ ht' rfl
        simp only [Option.map_some, Res]
        rcases injNormal_cases a b w with ⟨a', a'', w', rfl, hn⟩ | hn
        · rw [hn]
          obtain ⟨h1, -, h3, rfl⟩ := sortOf_inj.mp hw
          obtain ⟨x, hx, hxs⟩ := den_single hI h3 e
          rw [injApp_congr ih m]
          show (KoreAML.appList _ [_, _, den c (.inj a' a w')]).interpret I e m ↔ _
          rw [den_inj, den_inj]
          exact coh_at hI h1 hab hx hxs m
        · rw [hn, den_inj]
          exact injApp_congr ih m
    | _, _, _, .ctor (f := f) (ts := ts) (rs := rs) hk hts, L, vars, vs, tbl, e, s, hL, hσ, hvs, hag, ht, hcall, m => by
      obtain ⟨k, hk', hargs, -⟩ := sortOfTerm_app.mp ht
      obtain ⟨k0, hk0⟩ := Option.isSome_iff_exists.mp hk
      obtain ⟨-, hcalls⟩ := heads_app hcall
      have ih := evalTerms_den2 (hpreTop := hpreTop) hts hL hσ hvs hag hargs hcalls
      rw [kore_app_plain hnn.1 hk0]
      cases hall : allSome rs with
      | none =>
        simp only [Option.map_none, Res, iff_false]
        exact ih.2 hall _ m
      | some ws =>
        simp only [Option.map_some, Res]
        rw [den_ctor]
        exact ih.1 ws hall _ _ (fun _ => Iff.rfl) m
    | _, _, _, .hook (f := f) (rs := rs) (r := r) hk hhk hts hh hund, L, vars, vs, tbl, e, s, hL, hσ, hvs, hag, ht, hcall, m => by
      obtain ⟨k, hk', hargs, -⟩ := sortOfTerm_app.mp ht
      obtain ⟨hks, hkn⟩ := rhs_lookup_hook hk hhk hk'
      obtain ⟨-, hcalls⟩ := heads_app hcall
      have ih := evalTerms_den2 (hpreTop := hpreTop) hts hL hσ hvs hag hargs hcalls
      rw [kore_app, tr_symApp]
      cases hall : allSome rs with
      | none =>
        rw [hund hall]
        simp only [Res, iff_false]
        exact ih.2 hall _ m
      | some ws =>
        have hv := hh ws hall
        have hws := EvalTerms.sorted hsc hts hL hσ hargs hall
        have hax := sat_hookRes hI hks hws (by rw [hkn]; exact hv)
        have hgr := (KoreAML.interp_equal (defOK hI)).mp (hax e default) m
        rw [hkn] at hgr
        unfold KoreAML.den at hgr
        rw [tr_symApp] at hgr
        rw [ih.1 ws hall _ _ (fun _ => Iff.rfl) m, hgr]
        cases r with
        | none => simp [Res, Pattern.interpret]
        | some v => rfl
    | _, _, _, .param (f := f) (rs := rs) (r := r) hk hhk hp hts hr, L, vars, vs, tbl, e, s, hL, hσ, hvs, hag, ht, hcall, m => by
      obtain ⟨k, hk', hargs, -⟩ := sortOfTerm_app.mp ht
      obtain ⟨kp, hkp, rfl, hkn⟩ := rhs_lookup_param hk hhk hp hk'
      obtain ⟨-, hcalls⟩ := heads_app hcall
      have ih := evalTerms_den2 (hpreTop := hpreTop) hts hL hσ hvs hag hargs hcalls
      rw [kore_app, tr_symApp]
      cases hall : allSome rs with
      | none =>
        rw [hr, hall]
        simp only [Option.bind_none, Res, iff_false]
        exact ih.2 hall _ m
      | some ws =>
        have hws := EvalTerms.sorted hsc hts hL hσ hargs hall
        have hax := sat_dom hI (Or.inr (Or.inl ⟨kp, ws, hkp, hws, rfl⟩))
        have hgr := (KoreAML.interp_equal (defOK hI)).mp (hax e default) m
        rw [hkn] at hgr
        unfold KoreAML.den at hgr
        rw [tr_symApp] at hgr
        rw [ih.1 ws hall _ _ (fun _ => Iff.rfl) m, hgr, hr, hall]
        simp only [Option.bind_some]
        cases c.paramVal f ws with
        | none => simp [Res, Pattern.interpret]
        | some v => rfl
    | _, _, _, .call (f := f) (rs := rs) (vs := ws) hk hh hts hvs' hf hp, L, vars, vs, tbl, e, s, hL, hσ, hvs, hag, ht, hcall, m => by
      obtain ⟨k, hk', hargs, -⟩ := sortOfTerm_app.mp ht
      obtain ⟨fn, hfnm, rfl, hlook⟩ := rhs_lookup_call hsc hL hk hh hp (Eval.lookupFn_ne hf) hk'
      obtain ⟨hcf, hcalls⟩ := heads_app hcall
      have ih := evalTerms_den2 (hpreTop := hpreTop) hts hL hσ hvs hag hargs hcalls
      have hws := EvalTerms.sorted hsc hts hL hσ hargs hvs'
      rw [kore_app, tr_symApp, ih.1 ws hvs' _ _ (fun _ => Iff.rfl) m]
      have := eval_den2 (hpreTop := hpreTop) hf hlook hws hcf.1 e m
      unfold KoreAML.den at this
      rw [tr_symApp] at this
      exact this
    | _, _, _, .callUndef (f := f) (rs := rs) hk hh hts hvs' hp, L, vars, vs, tbl, e, s, hL, hσ, hvs, hag, ht, hcall, m => by
      obtain ⟨k, hk', hargs, -⟩ := sortOfTerm_app.mp ht
      obtain ⟨-, hcalls⟩ := heads_app hcall
      have ih := evalTerms_den2 (hpreTop := hpreTop) hts hL hσ hvs hag hargs hcalls
      rw [kore_app, tr_symApp]
      simp only [Res, iff_false]
      exact ih.2 hvs' _ m
    | _, _, _, .ovlFn (f := f) (rs := rs) (vs := ws) (o := o) (kg := kg) (r := r) hk ho hts hvs' hlo hcov hf,
        L, vars, vs, tbl, e, s, hL, hσ, hvs, hag, ht, hcall, m => by
      obtain ⟨k, hk', hargs, -⟩ := sortOfTerm_app.mp ht
      obtain ⟨o', hlo', rfl⟩ := rhs_lookup_ovl hsc hL hk' ho
      rw [hlo] at hlo'; cases hlo'
      obtain ⟨hcf, hcalls⟩ := heads_app hcall
      have ih := evalTerms_den2 (hpreTop := hpreTop) hts hL hσ hvs hag hargs hcalls
      have hws := EvalTerms.sorted hsc hts hL hσ hargs hvs'
      obtain ⟨fn, hfn, hlook, hsig, hkg, hb, -, hus⟩ :=
        OvlLaws.fnCover_fn_ovlF ((inferInstance : OvlOK c).hyp hsc.trans).fnFacts hlo hws hcov
      have hname : kg.name = fn.label := by rw [hsig]
      have hres : kg.result = fn.result := by rw [hsig]
      have hgd := eval_den2 (hpreTop := hpreTop) hf hlook hus (hcf.2 o hlo kg hkg hb) e
      rw [kore_app, tr_symApp, ih.1 ws hvs' _ _ (fun _ => Iff.rfl) m]
      have := covDen_of hI hsc.trans hlo hws hcov (namesNumbered_cover hnn hlo hcov)
        (fun v hv => by rw [hres]; exact Eval.sorted hsc hf hlook hus hv) e hgd m
      unfold KoreAML.den at this
      rw [tr_symApp] at this
      exact this
    | _, _, _, .ovl (f := f) (rs := rs) hk ho hts hnf, L, vars, vs, tbl, e, s, hL, hσ, hvs, hag, ht, hcall, m => by
      obtain ⟨k, hk', hargs, -⟩ := sortOfTerm_app.mp ht
      obtain ⟨o, hlo, rfl⟩ := rhs_lookup_ovl hsc hL hk' ho
      obtain ⟨-, hcalls⟩ := heads_app hcall
      have ih := evalTerms_den2 (hpreTop := hpreTop) hts hL hσ hvs hag hargs hcalls
      rw [kore_app, tr_symApp]
      cases hall : allSome rs with
      | none =>
        simp only [Option.map_none, Res, iff_false]
        exact ih.2 hall _ m
      | some ws =>
        have hws := EvalTerms.sorted hsc hts hL hσ hargs hall
        simp only [Option.map_some, Res]
        rw [ih.1 ws hall _ _ (fun _ => Iff.rfl) m]
        have := (normDen_of hI hsc.trans).1 hlo hws (hnf ws hall) e m
        unfold KoreAML.den at this
        rw [tr_symApp] at this
        exact this
  termination_by structural _ _ _ h => h
  theorem evalTerms_den2 (hpreTop : c.clausesPreTop = true) : ∀ {σ : Subst} {ts : List Term} {rs : List (Option GroundTerm)}, EvalTerms c σ ts rs →
      ∀ {L : List CtorSig} {vars : List Srt} {vs : List KoreAML.Var} {tbl : VarTable} {e : Valuation M} {ss : List Srt},
      HeadsOK c L → c.WellSorted vars σ → vs.length = vars.length → Agrees c I tbl vs σ e →
      sortsOfTerms (c.rhsCtx L) vars ts = some ss → (∀ f ∈ Term.headsList ts, CallsAll c (Callable2 c) f) →
      (∀ ws, allSome rs = some ws → ∀ (acc acc' : KoreAML.P), (∀ m, acc.interpret I e m ↔ acc'.interpret I e m) →
        ∀ m, (KoreAML.trArgs ⟨tbl, []⟩ acc (Term.koreList c vs ts)).interpret I e m ↔
          (KoreAML.trArgs ⟨[], []⟩ acc' (GroundTerm.koreList c ws)).interpret I e m) ∧
      (allSome rs = none → ∀ (acc : KoreAML.P) m, ¬ (KoreAML.trArgs ⟨tbl, []⟩ acc (Term.koreList c vs ts)).interpret I e m)
    | _, _, _, .nil, _, _, _, _, _, _, _, _, _, _, _, _ => by
      refine ⟨fun ws hws acc acc' hacc m => ?_, fun h => by simp [allSome] at h⟩
      simp only [allSome, Option.some.injEq] at hws
      subst hws
      rw [Term.koreList, GroundTerm.koreList, KoreAML.trArgs_nil, KoreAML.trArgs_nil]
      exact hacc m
    | _, _, _, .cons (t := t) (ts := ts) (r := r) (rs := rs) h hs, L, vars, vs, tbl, e, ss, hL, hσ, hvs, hag, ht, hcall => by
      obtain ⟨s, ss', h1, h2, -⟩ := sortsOfTerms_cons.mp ht
      rw [Term.headsList] at hcall
      have ih1 := evalTerm_den2 (hpreTop := hpreTop) h hL hσ hvs hag h1 (fun g hg => hcall g (List.mem_append_left _ hg))
      have ih2 := evalTerms_den2 (hpreTop := hpreTop) hs hL hσ hvs hag h2 (fun g hg => hcall g (List.mem_append_right _ hg))
      constructor
      · intro ws hws acc acc' hacc m
        simp only [allSome, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hws
        obtain ⟨w, rfl, ws', hws', rfl⟩ := hws
        rw [Term.koreList, GroundTerm.koreList, KoreAML.trArgs_cons, KoreAML.trArgs_cons]
        exact ih2.1 ws' hws' _ _ (KoreAML.interp_app_congr hacc ih1) m
      · intro hn acc m
        rw [Term.koreList, KoreAML.trArgs_cons]
        cases r with
        | none =>
          exact trArgs_empty (fun m' hm' => by
            obtain ⟨_, b, _, hb, _⟩ := KoreAML.interp_app.mp hm'
            exact (ih1 b).mp hb) _ m
        | some w =>
          cases hrs : allSome rs with
          | none => exact ih2.2 hrs _ m
          | some ws' => simp [allSome, hrs] at hn
  termination_by structural _ _ _ h => h
end

end

/-! ## L4, second stage: a rule's step, its competitors negated -/

section
variable {c : Semantics} {M : Type} {I : Interpretation KoreAML.Sym M}
variable [Inhabited M] (hI : I ⊧ᴵP Γ c) (hnn : NamesNumbered c) (hsc : SortCtx c) (hst : Stage2 c) [OvlOK c]
  (hok : c.sortedOK = true) (hbc : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, binds cl.vars.length (varOccsList cl.pats) = true) (hmi : CoherentAll c)
include hI hnn hsc hst hok hbc hmi

/-- A rule that does not apply to a configuration (`NotApplies`) does not apply in the model. -/
theorem notApplies_model (hpreTop : c.clausesPreTop = true) {r : Rule} (hr : r ∈ c.rules) (hpre : r.pre = .top) {x : GroundTerm} (h : NotApplies c r x) :
    ModelNotApplies c I r x := by
  intro σ hσ hpv tbl e hag
  obtain ⟨-, hreqs, -⟩ := rule_ctx hok hr
  obtain ⟨-, hcalls⟩ := hst.2.1 r hr
  obtain ⟨_, _, ht, he, hv⟩ := (h σ (hσ.at _) hpv).req_of_top hpre
  · exact ⟨_, _, ht, hv, fun u hu => EvalTerm.sorted hsc he fns_headsOK hσ (hreqs _ ht) hu,
      evalTerm_den2 (hpreTop := hpreTop) hI hnn hsc hst hok hbc hmi he fns_headsOK hσ (canonVars_length c r.vars) hag (hreqs _ ht)
        (fun g hg => hcalls g (List.mem_append_left _ (List.mem_append_right _ (by rw [ht]; exact hg))))⟩

/-- **A rule's axiom, read in a model**, whatever its left-hand part `L`: if `L` holds of the
configuration's element at every valuation of the axiom's table that agrees with σ (`hL`), the
configuration has the right-hand side's value as a successor. -/
theorem rule_at (hpreTop : c.clausesPreTop = true) {r : Rule} (hr : r ∈ c.rules) {L : Kore.Pattern}
    (hpat : prioRuleK c r = .rewrites (srtOf c topCellSort) L
      (.and (srtOf c topCellSort) [Term.kore c (canonVars c r.vars) r.rhs,
        reqPat (srtOf c topCellSort) (r.ens.map (Term.kore c (canonVars c r.vars)))]))
    (hVin : ∀ i < r.vars.length, canonKey c r.vars i ∈ KoreAML.varsOf L)
    (hfree : ∀ k ∈ KoreAML.freeOf [] L, ∃ i < r.vars.length, k = canonKey c r.vars i)
    {σ : Subst} (hσ : c.WellSorted r.vars σ) {x y : Config c} (heval : EvalTerm c σ r.rhs (some y.val))
    (hens : ∀ t, r.ens = some t → EvalTerm c σ t (some (bool true)))
    (hL : ∀ (tbl : VarTable) (e : Valuation M), (∀ k ∈ KoreAML.varsOf L, k ∈ tbl) →
      Agrees c I tbl (canonVars c r.vars) σ e →
      (∀ b, (KoreAML.tr ⟨tbl, []⟩ (.and (srtOf c topCellSort) [Term.kore c (canonVars c r.vars) r.rhs,
        reqPat (srtOf c topCellSort) (r.ens.map (Term.kore c (canonVars c r.vars)))])).interpret I e b ↔ (den c y.val).interpret I e b) →
      (KoreAML.tr ⟨tbl, []⟩ L).interpret I e (elemOf c I x.val))
    (e : Valuation M) (m : M) (hm : (den c x.val).interpret I e m) :
    (KoreAML.sNext (den c y.val)).interpret I e m := by
  have hD := defOK hI
  obtain ⟨-, -, hrhss⟩ := rule_ctx hok hr
  obtain ⟨-, hcalls⟩ := hst.2.1 r hr
  have hax := sat_rules hI (Or.inl ⟨_, List.mem_map.mpr ⟨r, hr, rfl⟩, rfl⟩)
  rw [hpat] at hax
  let C := srtOf c topCellSort
  let vs := canonVars c r.vars
  let ax : Kore.Axiom :=
    { sortVars := [], pattern := .rewrites C L (.and C [Term.kore c vs r.rhs, reqPat C (r.ens.map (Term.kore c vs))]),
      attributes := [] }
  let tbl : VarTable := KoreAML.tableOf ax.sortVars ax.pattern
  let e' : Valuation M := valOf tbl (ruleVal c I r.vars.length σ)
  have hvarsL : ∀ k ∈ KoreAML.varsOf L, k ∈ tbl := fun k hk => by
    refine List.mem_eraseDups.mpr (List.mem_append_right _ ?_)
    show k ∈ KoreAML.varsOf (.rewrites C L _)
    rw [KoreAML.varsOf]
    exact List.mem_append_left _ (List.mem_append_right _ hk)
  have hVmem : ∀ i, i < r.vars.length → canonKey c r.vars i ∈ tbl := fun i hi => hvarsL _ (hVin i hi)
  have hVv : ∀ i, i < r.vars.length → e'.evalEvar (tbl.ev (canonKey c r.vars i)) =
      (match σ.lookup i with | some v => elemOf c I v | none => default) := fun i hi => by
    rw [valOf_ev (hVmem i hi), canonKey_eq c hi]
    simp only [ruleVal]
    rw [varIdx_eq hi]
    all_goals rfl
  have hvsort : ∀ i, i < r.vars.length → ∃ v, σ.lookup i = some v ∧ c.sortOf v = some (r.vars.getD i 0) :=
    fun i hi => hσ i _ (by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; rfl)
  have hag : Agrees c I tbl vs σ e' := fun i v hi hl m => by
    rw [canonVars_length] at hi
    show m = e'.evalEvar (tbl.ev (canonKey c r.vars i)) ↔ _
    rw [hVv i hi, hl]
    obtain ⟨w, hw, hsw⟩ := hvsort i hi
    rw [hl] at hw; cases hw
    exact ((elemOf_spec hI hsw e').1 m).symm
  have hfree' : ∀ k, k ∈ KoreAML.freeOf [] ax.pattern → ∃ i, i < r.vars.length ∧ k = canonKey c r.vars i := by
    intro k hk
    change k ∈ KoreAML.freeOf [] (.rewrites C L _) at hk
    rw [KoreAML.freeOf] at hk
    rcases List.mem_append.mp hk with hk | hk
    · obtain ⟨i, hi, h⟩ := hfree k hk; exact ⟨i, hi, h⟩
    · obtain ⟨i, hi, h⟩ := freeOf_right hok hr hk; exact ⟨i, hi, h⟩
  have hg : ∀ k ∈ (ax.sortVars.map KoreAML.sortVarKey ++ KoreAML.freeOf [] ax.pattern).eraseDups, ∀ m,
      (KoreAML.guardOf tbl k).interpret I e' m := by
    intro k hk m'
    have hk' : k ∈ KoreAML.freeOf [] ax.pattern := by simpa [ax] using List.mem_eraseDups.mp hk
    obtain ⟨i, hi, rfl⟩ := hfree' k hk'
    obtain ⟨w, hw, hsw⟩ := hvsort i hi
    have hkk := canonKey_eq c hi
    rw [hkk, KoreAML.interp_guard_evar hD, trSort_srt, ← hkk, hVv i hi, hw]
    exact (elemOf_spec hI hsw e').2
  obtain ⟨a, ha, has⟩ := den_single hI x.property e'
  have hxa : elemOf c I x.val = a := (ha _).mp ((elemOf_spec hI x.property e').1 _ |>.mpr rfl)
  have hP := (KoreAML.trAxiom_at hD hax e' hg a).mpr (by
    show (KoreAML.inhOf (KoreAML.trSort tbl (srtOf c topCellSort))).interpret I e' a
    unfold srtOf; rw [trSort_srt]; exact has)
  have hP' : (KoreAML.tr ⟨tbl, []⟩ ax.pattern).interpret I e' a := hP
  change (KoreAML.tr ⟨tbl, []⟩ (.rewrites C L _)).interpret I e' a at hP'
  rw [KoreAML.tr] at hP'
  unfold KoreAML.sRewrites at hP'
  rw [KoreAML.interp_sImp] at hP'
  obtain ⟨-, himp⟩ := hP'
  have hrhsR : ∀ b, (KoreAML.tr ⟨tbl, []⟩ (Term.kore c vs r.rhs)).interpret I e' b ↔ (den c y.val).interpret I e' b :=
    fun b => evalTerm_den2 (hpreTop := hpreTop) hI hnn hsc hst hok hbc hmi heval fns_headsOK hσ (canonVars_length c r.vars) hag hrhss
    (fun g hg => hcalls g (List.mem_append_left _ (List.mem_append_left _ hg))) b
  have hensS := rule_ctx_ens hok hr
  have hrightR := right_den hI hrhsR (fun a' ha' => reqPat_holds hI (fun t ht b =>
    evalTerm_den2 (hpreTop := hpreTop) hI hnn hsc hst hok hbc hmi (hens t ht) fns_headsOK hσ (canonVars_length c r.vars) hag (hensS t ht)
    (fun g hg => hcalls g (List.mem_append_right _ (by rw [ht]; exact hg))) b) ha')
  have hL' := himp (by rw [← hxa]; exact hL tbl e' hvarsL hag hrightR)
  obtain ⟨n, b, hn, hb, happ⟩ := KoreAML.interp_app.mp hL'
  rw [tr_and2, KoreAML.interp_sAnd] at hb
  have hby := (hrhsR b).mp hb.1
  have hma : m = a := by
    have := ((den_closed c x.val).interp e e' m).mp hm
    exact (ha m).mp this
  rw [hma]
  exact KoreAML.interp_app.mpr ⟨n, b, hn, ((den_closed c y.val).interp e' e b).mp hby, happ⟩

/-- The left-hand side and the `requires` of a rule's axiom hold of the configuration it
matches, at a valuation that agrees with the match. -/
theorem lhs_req_hold (hpreTop : c.clausesPreTop = true) {r : Rule} (hr : r ∈ c.rules) {σ : Subst} (hσ : c.WellSorted r.vars σ) {x : Config c}
    (hmatch : PatVal c σ r.lhs x.val) (hreq : ∀ t, r.req = some t → EvalTerm c σ t (some (bool true)))
    {tbl : VarTable} {e : Valuation M} (hag : Agrees c I tbl (canonVars c r.vars) σ e) :
    (KoreAML.tr ⟨tbl, []⟩ (Term.kore c (canonVars c r.vars) r.lhs)).interpret I e (elemOf c I x.val) ∧
      (KoreAML.tr ⟨tbl, []⟩ (reqPat (srtOf c topCellSort) (r.req.map (Term.kore c (canonVars c r.vars))))).interpret I e
        (elemOf c I x.val) := by
  have hD := defOK hI
  have hc := sat_sigItem hI (sig_ceilDef (c := c))
  obtain ⟨hlhs, hreqs, -⟩ := rule_ctx hok hr
  obtain ⟨hplain, hcalls⟩ := hst.2.1 r hr
  obtain ⟨σC, hσC1, hσC2⟩ := sortSing hI (top_numbered (c := c))
  obtain ⟨σB, hσB1, hσB2⟩ := sortSing hI (bool_numbered (c := c))
  rw [sortName_bool] at hσB1
  have hxs := elemOf_spec hI x.property e
  have hSC : ∀ b, (KoreAML.trSort tbl (srtOf c topCellSort)).interpret I e b ↔ b = σC := by
    unfold srtOf; rw [trSort_srt]; exact hσC1
  have haC : Inh I σC (elemOf c I x.val) := by
    have := hxs.2
    exact (KoreAML.interp_inhOf_of (S := KoreAML.sym _) hσC1).mp this
  refine ⟨(patVal_den hI hnn.1 hsc.trans hσ (canonVars_length c r.vars) hag hmatch hplain hlhs).2 _ |>.mpr
    ((hxs.1 _).mpr rfl), ?_⟩
  cases hq : r.req with
  | none =>
    simp only [Option.map_none, reqPat]
    rw [KoreAML.tr, KoreAML.interp_sTop hD (by unfold srtOf; rw [trSort_srt]; rfl), KoreAML.interp_inhOf_of hSC]
    exact haC
  | some t =>
    simp only [Option.map_some, reqPat]
    rw [KoreAML.tr, KoreAML.interp_sEquals hD hc (by rw [trSort_srt]; exact hσB1) hSC hσB2 hσC2]
    refine ⟨haC, fun b _ => ?_⟩
    rw [evalTerm_den2 (hpreTop := hpreTop) hI hnn hsc hst hok hbc hmi (hreq t hq) fns_headsOK hσ (canonVars_length c r.vars) hag (hreqs t hq)
      (fun g hg => hcalls g (List.mem_append_left _ (List.mem_append_right _ (by rw [hq]; exact hg)))) b, KoreAML.tr_dv]
    show (den c (bool true)).interpret I e b ↔ _
    unfold den KoreAML.den bool
    rw [GroundTerm.kore, sortName_bool, KoreAML.tr_dv]
    exact Iff.rfl

end

/-- **L4, second stage.** Every step of `Step` is a consequence of `Γ`, for a semantics in the
second stage: in every model, the configuration `x` has the configuration `y` as a successor. A
rule with rules of a smaller priority fires through its axiom with their `applies` negated, which
holds because none of them applies to `x` (`NotApplies`, `applies_empty`); the functions it calls
are read through their equations, those with clauses of a smaller priority negated among them
(`eval_den2`). -/
theorem step_sound_stage2 (c : Semantics) [OvlOK c] (hy : Hyp c) (hb : ∀ r ∈ c.rules, binds r.vars.length (varOccs r.lhs) = true) (htop : ∀ r ∈ c.rules, r.pre = .top ∧ r.post = .top)
    (hbc : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, binds cl.vars.length (varOccsList cl.pats) = true) (hs : Stage2 c) :
    ∀ x y : Config c, Step c x y → Γ c ⊧ (den c x.val ⇒ KoreAML.sNext (den c y.val)) := by
  have hpreTop := Semantics.preTop_of_okAll hy.1
  have hy : HypCore c := hy.core (Semantics.overloadsOK_pats OvlOK.ok)
  have hnn : NamesNumbered c := hy.2.2.2.2.2.2
  intro x y hstep M _ I hI e m hm
  obtain ⟨r, hr, σ, hσ, hmatch, hreq, -, heval, hens, -, hprio⟩ := hstep
  obtain ⟨hpre₀, hpost₀⟩ := htop _ hr
  have hex₀ : r.exs = [] := Semantics.sortedOK_exsNil hy.1 hr (hb r hr)
  have hD := defOK hI
  have hsc := sortCtx_of_all hy.1 hy.2.1 (OvlOK.ovlCase inferInstance)
  have hmi := CoherentAll_of hy
  obtain ⟨hlhs, hreqs, -⟩ := rule_ctx hy.1 hr
  have hbinds := Exec.binds_all (hb _ hr)
  let C := srtOf c topCellSort
  let vs := canonVars c r.vars
  let comps := (c.rules.filter (·.prio < r.prio)).map fun r' => applies c r' (canonRulePres r')
  let L0 : Kore.Pattern := .and C [Term.kore c vs r.lhs, reqPat C (r.req.map (Term.kore c vs)),
    .ceil C C (.and C [Term.kore c vs r.rhs, reqPat C (r.ens.map (Term.kore c vs))])]
  -- the variables of the left-hand side and the requires
  have hV0 : ∀ i < r.vars.length, canonKey c r.vars i ∈ KoreAML.varsOf (Term.kore c vs r.lhs) :=
    fun i hi => varsOf_kore c vs r.lhs (hbinds i hi)
  have hfree0 : ∀ k ∈ KoreAML.freeOf [] (Term.kore c vs r.lhs) ++ KoreAML.freeOf [] (reqPat C (r.req.map (Term.kore c vs))),
      ∃ i < r.vars.length, k = canonKey c r.vars i := by
    intro k hk
    rcases List.mem_append.mp hk with hk | hk
    · obtain ⟨i, hi, rfl⟩ := freeOf_kore c vs r.lhs hk
      exact ⟨i, varOccs_lt r.lhs hlhs i hi, rfl⟩
    · cases hq : r.req with
      | none => rw [hq] at hk; simp only [Option.map_none, reqPat] at hk; rw [KoreAML.freeOf] at hk; cases hk
      | some t =>
        rw [hq] at hk; simp only [Option.map_some, reqPat] at hk
        rw [KoreAML.freeOf] at hk
        rcases List.mem_append.mp hk with hk | hk
        · obtain ⟨i, hi, rfl⟩ := freeOf_kore c vs t hk
          exact ⟨i, varOccs_lt t (hreqs t hq) i hi, rfl⟩
        · rw [KoreAML.freeOf] at hk; cases hk
  by_cases hce : comps.isEmpty
  · -- no competitor: the rule's axiom as written
    have hpat : prioRuleK c r = .rewrites C L0
        (.and C [Term.kore c vs r.rhs, reqPat C (r.ens.map (Term.kore c vs))]) := by
      rw [prioRuleK_top hex₀ hpre₀ hpost₀]; dsimp only; rw [if_pos hce]
    refine rule_at (hpreTop := hpreTop) hI hnn hsc hs hy.1 hbc hmi hr hpat (fun i hi => ?_) (fun k hk => ?_) hσ heval hens
      (fun tbl e' _ hag hrhsR => ?_) e m hm
    · show _ ∈ KoreAML.varsOf (.and C _)
      rw [KoreAML.varsOf, KoreAML.varsOfList]
      exact List.mem_append_right _ (List.mem_append_left _ (hV0 i hi))
    · change k ∈ KoreAML.freeOf [] (.and C _) at hk
      simp only [KoreAML.freeOf, KoreAML.freeOfList, List.append_nil, List.mem_append] at hk
      exact freeOf_rule_parts hy.1 hr hk
    · have h := lhs_req_hold (hpreTop := hpreTop) hI hnn hsc hs hy.1 hbc hmi hr hσ hmatch hreq hag
      show (KoreAML.tr ⟨tbl, []⟩ (.and C _)).interpret I e' _
      rw [tr_and3, KoreAML.interp_sAnd, KoreAML.interp_sAnd]
      exact ⟨h.1, h.2, ceil_rhs_at hI hrhsR (elemOf_top hI x tbl e')⟩
  · -- competitors: the axiom with their `applies` negated
    have hpat : prioRuleK c r = .rewrites C (.and C [Term.kore c vs r.lhs, reqPat C (r.req.map (Term.kore c vs)),
        .not C (anyOfC C comps), .ceil C C (.and C [Term.kore c vs r.rhs, reqPat C (r.ens.map (Term.kore c vs))])])
        (.and C [Term.kore c vs r.rhs, reqPat C (r.ens.map (Term.kore c vs))]) := by
      rw [prioRuleK_top hex₀ hpre₀ hpost₀]; dsimp only; rw [if_neg hce]
    have hcomp : ∀ φ ∈ comps, ∃ r' ∈ c.rules, r'.prio < r.prio ∧ φ = applies c r' (canonRulePres r') := by
      intro φ hφ
      obtain ⟨r', hr', rfl⟩ := List.mem_map.mp hφ
      obtain ⟨hr'm, hp⟩ := List.mem_filter.mp hr'
      exact ⟨r', hr'm, by simpa using hp, rfl⟩
    refine rule_at (hpreTop := hpreTop) hI hnn hsc hs hy.1 hbc hmi hr hpat (fun i hi => ?_) (fun k hk => ?_) hσ heval hens
      (fun tbl e' hkeys hag hrhsR => ?_) e m hm
    · show _ ∈ KoreAML.varsOf (.and C _)
      rw [KoreAML.varsOf, KoreAML.varsOfList]
      exact List.mem_append_right _ (List.mem_append_left _ (hV0 i hi))
    · change k ∈ KoreAML.freeOf [] (.and C _) at hk
      simp only [KoreAML.freeOf, KoreAML.freeOfList, List.append_nil, List.mem_append] at hk
      rcases hk with hk | hk | hk | hk
      · exact freeOf_rule_parts hy.1 hr (Or.inl hk)
      · exact freeOf_rule_parts hy.1 hr (Or.inr (Or.inl hk))
      · exfalso
        obtain ⟨φ, hφ, hk⟩ := mem_freeOf_anyOfC hk
        obtain ⟨r', hr', -, rfl⟩ := hcomp φ hφ
        obtain ⟨hlhs', hreqs', -⟩ := rule_ctx hy.1 hr'
        exact freeOf_applies hlhs' (fun t ht => varOccs_lt t (hreqs' t ht)) (htop _ hr').1 (hb _ hr') hk
      · exact freeOf_rule_parts hy.1 hr (Or.inr (Or.inr hk))
    · have h := lhs_req_hold (hpreTop := hpreTop) hI hnn hsc hs hy.1 hbc hmi hr hσ hmatch hreq hag
      show (KoreAML.tr ⟨tbl, []⟩ (.and C _)).interpret I e' _
      rw [tr_and4, KoreAML.interp_sAnd, KoreAML.interp_sAnd, KoreAML.interp_sAnd]
      refine ⟨h.1, h.2, ?_, ceil_rhs_at hI hrhsR (elemOf_top hI x tbl e')⟩
      rw [KoreAML.tr, KoreAML.interp_sNot]
      refine ⟨anyOfC_empty hD (by
        show (KoreAML.trSort tbl (KoreAML.srt (c.sortName topCellSort))).isFreeEvar KoreAML.topVar = false
        rw [trSort_srt]; rfl) comps (fun φ hφ => ?_), ?_⟩
      · obtain ⟨r', hr', hp, rfl⟩ := hcomp φ hφ
        obtain ⟨hlhs', -, -⟩ := rule_ctx hy.1 hr'
        have hbinds' := Exec.binds_all (hb _ hr')
        refine applies_empty hI hs.1 hsc.trans hnn.1 hlhs' hbinds' (hs.2.1 r' hr').1 (htop _ hr').1 x.property
          (fun i hi => hkeys _ ?_) e' (notApplies_model (hpreTop := hpreTop) hI hnn hsc hs hy.1 hbc hmi hr' (htop _ hr').1 (hprio r' hr' hp))
        rw [KoreAML.varsOf, KoreAML.varsOfList, KoreAML.varsOfList, KoreAML.varsOfList, KoreAML.varsOf]
        exact List.mem_append_right _ (List.mem_append_right _ (List.mem_append_right _ (List.mem_append_left _
          (List.mem_append_right _ (mem_varsOf_anyOfC hφ (varsOf_applies (htop _ hr').1 (hb _ hr') hi))))))
      · have hxs := elemOf_spec hI x.property e'
        show (KoreAML.inhOf (KoreAML.trSort tbl (KoreAML.srt (c.sortName topCellSort)))).interpret I e' _
        rw [trSort_srt]
        exact hxs.2

end Faithful

end KCore
