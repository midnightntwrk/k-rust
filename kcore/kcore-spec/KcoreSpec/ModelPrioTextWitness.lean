/-
  KCore. A semantics with one function of two equations of different priorities, both applying at
  its one argument list with different results: `Γ` reads the priorities and has a model
  (`has_model`), while the theory read with each equation's premise only its own `requires` and
  patterns, as the text states them (`ΓFnText`), has none (`not_model_text`).

  The function `f : Int` has no argument and two clauses, `f() = 1` of priority 50 and `f() = 2` of
  priority 60. In `Γ` the second equation's premise negates the first clause, which applies, so it
  says nothing. Read without that negation, the two equations say that `f()` is both `1` and `2`,
  two distinct values of Int. The decidable facts are kernel decisions.
-/
import KcoreSpec.ModelHas

set_option autoImplicit false
set_option maxRecDepth 100000

namespace KCore

namespace Faithful

namespace PrioTextWitness

open ML

/-! ## The theory with plain premises -/

/-- A clause's equation as the text states it: an `[owise]` clause's (priority 200) under the
negation of the clauses of a smaller priority (`prioEquation`, the premise kompile writes for
`[owise]`), every other clause's with its own premise (`clauseEquation`: its `requires` and its
patterns, no clause of a smaller priority negated). -/
def textEquation (c : Semantics) (f : Fn) (cl : Clause) : Kore.Sentence :=
  if cl.prio = 200 then prioEquation c f cl else clauseEquation c f cl

/-- The functions' equations as the text states them (`textEquation`). -/
def fnItemsText (c : Semantics) : List KoreAML.Item :=
  c.allFns.flatMap fun f => kernelItems (f.clauses.map (textEquation c f))

def ΓFnsText (c : Semantics) : Premises KoreAML.Sym := KoreAML.itemsPremises (fnItemsText c)

/-- `Γ` with the functions' equations read with plain premises (`ΓFnsText` in place of `ΓFns`). -/
def ΓFnText (c : Semantics) : Premises KoreAML.Sym :=
  ΓSig c ∪ ΓCons c ∪ ΓDomains c ∪ ΓColls c ∪ ΓFnsText c ∪ ΓRules c ∪ ΓFallback c

/-! ## The semantics -/

def kIds : CellIds := { sort := nRegSorts, opt := some (nRegSorts + 1), label := nRegSyms + 2, no := some (nRegSyms + 3) }

/-- The configuration `<k> K </k>` with the generated counter, as ordinary sorts, constructors
and subsorts: the top cell's, its fragment's, the `k` cell's and the counter's. -/
def cellSorts : List Srt := [Srt.top, Srt.topFrag, nRegSorts, nRegSorts + 1, Srt.counter, Srt.counterOpt]
def cellCtors : List CtorSig :=
  [⟨topLabel, [nRegSorts, Srt.counter], Srt.top⟩, ⟨topFragLabel, [nRegSorts + 1, Srt.counterOpt], Srt.topFrag⟩,
   ⟨nRegSyms + 2, [Srt.k], nRegSorts⟩, ⟨nRegSyms + 3, [], nRegSorts + 1⟩,
   ⟨counterLabel, [Srt.int], Srt.counter⟩, ⟨noCounter, [], Srt.counterOpt⟩]
def cellSubsorts : List (Srt × Srt) := [(nRegSorts, nRegSorts + 1), (Srt.counter, Srt.counterOpt)]

/-- The function `f`, numbered after the cell's symbols. -/
def fl : Sym := nRegSyms + 4

def v1 : GroundTerm := .dv Srt.int (.int 1)
def v2 : GroundTerm := .dv Srt.int (.int 2)

/-- `f() = 1`, priority 50. -/
def cl1 : Clause := { vars := [], pats := [], req := none, rhs := .dv Srt.int (.int 1), prio := 50, ens := none }
/-- `f() = 2`, priority 60. -/
def cl2 : Clause := { vars := [], pats := [], req := none, rhs := .dv Srt.int (.int 2), prio := 60, ens := none }

def fn : Fn := { label := fl, args := [], result := Srt.int, clauses := [cl1, cl2] }

def c : Semantics :=
  { lib := { sortsBelowKItem := [Srt.int] }
    sortNames := ["KCell", "KCellOpt"]
    symNames := ["LblisKCell", "LblisKCellOpt", "Lbl'-LT-'k'-GT-'", "LblnoKCell", "Lblf"]
    userSorts := cellSorts
    ctors := cellCtors
    fns := [fn]
    userSubsorts := cellSubsorts
    pgmSort := Srt.k
    rules := [] }

instance : OvlOK c := .of_nil rfl (by decide +kernel)

theorem okAll : c.okAll = true := by decide +kernel
theorem srReady : c.srReady = true := by decide +kernel
theorem idsOK : c.idsOK = true := by decide +kernel
theorem names_plain : c.ctorSigs.all (fun k => (iteSort? (c.symName k.name)).isNone) = true := by decide +kernel
theorem names_fns : c.allFns.all (fun fn => (iteSort? (c.symName fn.label)).isNone &&
    (fn.result :: fn.args).all (· < nRegSorts + c.sortNames.length)) = true := by decide +kernel

theorem namesNumbered : NamesNumbered c := by
  refine ⟨fun k hk => ?_, fun fn hfn => ?_, fun fn hfn s hs => ?_⟩
  · exact Option.isNone_iff_eq_none.mp (List.all_eq_true.mp names_plain k hk)
  · have := List.all_eq_true.mp names_fns fn hfn
    simp only [Bool.and_eq_true] at this
    exact Option.isNone_iff_eq_none.mp this.1
  · have := List.all_eq_true.mp names_fns fn hfn
    simp only [Bool.and_eq_true] at this
    exact of_decide_eq_true (List.all_eq_true.mp this.2 s hs)

theorem lookup_f : c.lookupFn fl = some fn := rfl

/-- `f()` is `1`: the clause of priority 50 applies, and no clause has a smaller priority. -/
theorem eval_f : Eval c fl [] (some v1) :=
  .clause (σ := []) lookup_f (List.mem_cons_self ..) (fun _ _ h => by simp [cl1] at h) .nil (fun _ h => by cases h) .top
    (fun cl' h _ hlt => by
      rcases List.mem_cons.mp h with rfl | h
      · exact absurd hlt (Nat.lt_irrefl _)
      · rw [List.mem_singleton.mp h] at hlt; exact absurd hlt (by decide)) rfl
    .dv (fun _ h => by simp [cl1] at h) .top

theorem hyp : Hyp c := by
  refine ⟨okAll, srReady, fun g hg vs hvs => ?_, fun g hg ht => ?_, fun g hg => ?_, fun g hg cl' hcl' => ?_,
    namesNumbered⟩
  · rw [List.mem_singleton.mp hg] at hvs ⊢
    have : vs = [] := by
      cases vs with
      | nil => rfl
      | cons v vs => obtain ⟨_, _, _, _, h⟩ := sortsOf_cons.mp hvs; cases h
    subst this
    exact ⟨_, eval_f⟩
  · rw [List.mem_singleton.mp hg] at ht; cases ht
  · rw [List.mem_singleton.mp hg]
    intro a b hp hprio
    have h0 : pairs fn.clauses = [(cl1, cl2)] := rfl
    rw [h0, List.mem_singleton] at hp
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hp
    exact absurd hprio (by decide)
  · rw [List.mem_singleton.mp hg] at hcl'
    rcases List.mem_cons.mp hcl' with rfl | h
    · exact (matchIndependent_iff_noExs rfl).mpr fun vs σ σ' _ _ _ _ _ _ _ =>
        Or.inl ⟨rfl, rfl, rfl, rfl, fun i hi => (by simp [cl1, varOccs] at hi), fun t ht => (by simp [cl1] at ht)⟩
    · rw [List.mem_singleton.mp h]
      exact (matchIndependent_iff_noExs rfl).mpr fun vs σ σ' _ _ _ _ _ _ _ =>
        Or.inl ⟨rfl, rfl, rfl, rfl, fun i hi => (by simp [cl2, varOccs] at hi), fun t ht => (by simp [cl2] at ht)⟩

theorem hypSound : HypSound c :=
  ⟨okAll, srReady, namesNumbered, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, inferInstance⟩

set_option maxHeartbeats 1000000 in
theorem hypModel : Model.HypModel c :=
  ⟨hyp, hypSound, by decide +kernel, by decide +kernel, idsOK, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- **`Γ c`, which reads the priorities, has a model.** -/
theorem has_model : ∃ (M : Type) (_ : Inhabited M) (I : ML.Interpretation KoreAML.Sym M), I ⊧ᴵP (Γ c ∪ Γstep c) :=
  Model.has_model hypModel (Semantics.rulesTop_of_isTop (by decide +kernel)) (openLaws_of_plain (by decide +kernel))

/-! ## A clause's equation, read from its axiom

`clause_eq` (FaithfulStep.lean) with the clause's axiom `clauseAxiom` given as a hypothesis in place
of its membership in `Γ`'s functions (`lowerClauses fn cl = []`). Its proof is `clause_eq`'s. -/

section
variable {c : Semantics} {M : Type} {I : Interpretation KoreAML.Sym M}
open KoreAML (DefOK Inh IsSort Closed KGround VarKey VarTable)

theorem clause_eq_ax [Inhabited M] (hI : I ⊧ᴵP Γ c) [OvlOK c] (hnn : NamesNumbered c)
    (htr : ∀ a b d, (a, b) ∈ c.subsorts → (b, d) ∈ c.subsorts → (a, d) ∈ c.subsorts)
    {f : Sym} {fn : Fn} (hfn : c.lookupFn f = some fn) {cl : Clause}
    (hax : I ⊧ᴵ (KoreAML.trAxiom [] [] ⟨0, "kernel", clauseAxiom c fn cl⟩).pat) {ws : List GroundTerm} (hws : c.sortsOf ws = some fn.args)
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
  obtain ⟨hfnm, hlab⟩ := lookupFn_spec hfn
  subst hlab
  have hD := defOK hI
  have hc := sat_sigItem hI (sig_ceilDef (c := c))
  have hnum := hnn.2.2 fn hfnm
  obtain ⟨σr, hσr1, hσr2⟩ := sortSing hI (hnum fn.result (List.mem_cons_self ..))
  obtain ⟨σB, hσB1, hσB2⟩ := sortSing hI (bool_numbered (c := c))
  rw [sortName_bool] at hσB1
  have hlen : ws.length = fn.args.length := sortsOf_length hws
  have hplen : (Term.koreList c (canonVars c cl.vars) cl.pats).length = (fn.args.map c.sortName).length := by
    rw [koreList_length, List.length_map]; exact sortsOfTerms_length hpats
  let vs := canonVars c cl.vars
  let l := (fn.args.map c.sortName).zip (Term.koreList c vs cl.pats)
  let tbl : VarTable := KoreAML.tableOf (clauseAxiom c fn cl).sortVars (clauseAxiom c fn cl).pattern
  let e' : Valuation M := valOf tbl (clauseVal c I σr fn.args.length cl.vars.length ws σ')
  have hvarsP : ∀ k, k ∈ KoreAML.varsOf (KoreAML.argsConj 0 l) → k ∈ tbl := fun k hk => by
    refine List.mem_eraseDups.mpr (List.mem_append_right _ ?_)
    unfold clauseAxiom; dsimp only
    rw [KoreAML.varsOf]; unfold clausePrem premise
    rw [KoreAML.varsOf, KoreAML.varsOfList, KoreAML.varsOfList, KoreAML.varsOfList]
    exact List.mem_append_left _ (List.mem_append_right _ (List.mem_append_right _
      (List.mem_append_right _ (List.mem_append_left _ hk))))
  have hRmem : VarKey.sortVar "R" ∈ tbl :=
    List.mem_eraseDups.mpr (List.mem_append_left _ (List.mem_map.mpr ⟨KoreAML.Rv, List.mem_singleton_self _, rfl⟩))
  have hXmem : ∀ j s, (fn.args.map c.sortName)[j]? = some s →
      VarKey.evar ("X" ++ toString j) (KoreAML.srt s) ∈ tbl := fun j s hj => by
    have hjl : j < (Term.koreList c vs cl.pats).length := by
      rw [hplen]; exact (List.getElem?_eq_some_iff.mp hj).1
    have hl : l[j]? = some (s, (Term.koreList c vs cl.pats)[j]) :=
      List.getElem?_zip_eq_some.mpr ⟨hj, List.getElem?_eq_getElem hjl⟩
    have := varsOf_argsConj_X l 0 j s _ hl
    rw [Nat.zero_add] at this
    exact hvarsP _ this
  have hVmem : ∀ i, i < cl.vars.length → canonKey c cl.vars i ∈ tbl := fun i hi => by
    have h1 := varsOf_koreList c vs cl.pats (hbinds i hi)
    obtain ⟨p', hp', hk⟩ := varsOfList_mem h1
    have hp'' : p' ∈ l.map Prod.snd := by
      rw [List.map_snd_zip (Nat.le_of_eq hplen)]; exact hp'
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp''
    exact hvarsP _ (varsOf_argsConj_pat l 0 hq hk)
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
    try rfl
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
  have hfree : ∀ k, k ∈ KoreAML.freeOf [] (clauseAxiom c fn cl).pattern →
      (∃ j s, (fn.args.map c.sortName)[j]? = some s ∧ k = .evar ("X" ++ toString j) (KoreAML.srt s)) ∨
        ∃ i, i < cl.vars.length ∧ k = canonKey c cl.vars i := fun k hk => by
    unfold clauseAxiom at hk; dsimp only at hk
    rw [KoreAML.freeOf] at hk
    rcases List.mem_append.mp hk with hk | hk
    · unfold clausePrem premise at hk
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
    · unfold clauseConcl at hk
      rw [KoreAML.freeOf] at hk
      rcases List.mem_append.mp hk with hk | hk
      · unfold KoreAML.ap at hk; rw [KoreAML.freeOf] at hk
        obtain ⟨n, s, hn, rfl⟩ := freeOf_callX _ 0 hk
        exact Or.inl ⟨n, s, hn, by rw [Nat.zero_add]⟩
      · obtain ⟨i, hi, rfl⟩ := freeOf_clauseConclRight hk
        exact Or.inr ⟨i, hi.elim (hrhsv i) fun ⟨t, ht, hi⟩ => hensv t ht i hi, rfl⟩
  have hg : ∀ k ∈ ((clauseAxiom c fn cl).sortVars.map KoreAML.sortVarKey ++
      KoreAML.freeOf [] (clauseAxiom c fn cl).pattern).eraseDups, ∀ m,
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
    have hP := (KoreAML.trAxiom_at hD hax e' hg m0).mpr (by
      show (KoreAML.inhOf (KoreAML.trSort tbl KoreAML.R)).interpret I e' m0
      rw [KoreAML.interp_inhOf_of hRv]; exact hm0)
    have hP' : (KoreAML.tr ⟨tbl, []⟩ (.implies KoreAML.R (clausePrem c fn cl) (clauseConcl c fn cl))).interpret I e' m0 := hP
    rw [KoreAML.tr, KoreAML.interp_sImp] at hP'
    obtain ⟨-, himp⟩ := hP'
    have hprem := himp (by
      unfold clausePrem premise
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
          rw [ihreq tbl e' hag t hq a, KoreAML.tr_dv]
          unfold den KoreAML.den bool
          rw [GroundTerm.kore, sortName_bool, KoreAML.tr_dv]
          exact Iff.rfl
      · intro k s w hk hw m'
        rw [Nat.zero_add]
        obtain ⟨w', hw', hsw⟩ := sortsOf_get hws hk
        rw [hw] at hw'; cases hw'
        rw [hXv k (c.sortName s) w (by rw [List.getElem?_map, hk]; rfl) hw]
        exact ((elemOf_spec hI hsw e').1 m').symm)
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

/-! ## `ΓFnText c` has no model -/

def item1 : KoreAML.Item := KoreAML.trAxiom [] [] ⟨0, "kernel", clauseAxiom c fn cl1⟩
def item2 : KoreAML.Item := KoreAML.trAxiom [] [] ⟨0, "kernel", clauseAxiom c fn cl2⟩

/-- The second clause's axiom in `Γ`: its premise negates the first clause. -/
def axC : Kore.Axiom :=
  { sortVars := [KoreAML.Rv]
    pattern := .implies KoreAML.R
      (competingPremise (fn.args.map c.sortName) [exclusion c fn cl1 (canonClausePres cl1)] none [])
      (clauseConcl c fn cl2)
    attributes := [] }

def item2C : KoreAML.Item := KoreAML.trAxiom [] [] ⟨0, "kernel", axC⟩

def restItems : List KoreAML.Item :=
  c.sortPreds.flatMap fun f => kernelItems (fnEquationsK c f)

theorem fnItems_eq : fnItems c = [item1, item2C] ++ restItems := rfl

theorem fnItemsText_eq : fnItemsText c = [item1, item2] ++ restItems := rfl

theorem table_eq : KoreAML.tableOf axC.sortVars axC.pattern =
    KoreAML.tableOf (clauseAxiom c fn cl2).sortVars (clauseAxiom c fn cl2).pattern := by decide +kernel

theorem free_eq : (axC.sortVars.map KoreAML.sortVarKey ++ KoreAML.freeOf [] axC.pattern).eraseDups =
    ((clauseAxiom c fn cl2).sortVars.map KoreAML.sortVarKey ++
      KoreAML.freeOf [] (clauseAxiom c fn cl2).pattern).eraseDups := by decide +kernel

/-- The second clause's axiom with its own premise implies its axiom in `Γ`, whose premise is
stronger. -/
theorem item2C_of {M : Type} {I : Interpretation KoreAML.Sym M} (hD : KoreAML.DefOK I) (h : I ⊧ᴵ item2.pat) :
    I ⊧ᴵ item2C.pat := by
  intro e m
  have h1 := h e m
  unfold item2 KoreAML.trAxiom at h1
  unfold item2C KoreAML.trAxiom
  dsimp only at h1 ⊢
  rw [table_eq, free_eq]
  have hs : KoreAML.sortOf [] axC.pattern = KoreAML.sortOf [] (clauseAxiom c fn cl2).pattern := rfl
  rw [hs]
  rw [interpret_impl] at h1 ⊢
  intro hg
  have h2 := h1 hg
  rw [KoreAML.interp_equal hD] at h2 ⊢
  intro a
  have h3 := h2 a
  generalize KoreAML.tableOf (clauseAxiom c fn cl2).sortVars (clauseAxiom c fn cl2).pattern = tb at h3 ⊢
  unfold axC
  unfold clauseAxiom at h3
  dsimp only at h3 ⊢
  rw [KoreAML.tr, KoreAML.interp_sImp] at h3 ⊢
  refine ⟨fun h' => h'.1, fun ha => ⟨ha, fun hL => (h3.mpr ha).2 ?_⟩⟩
  unfold competingPremise at hL
  rw [tr_and2, KoreAML.interp_sAnd] at hL
  exact hL.2

theorem defOK_text {M : Type} {I : Interpretation KoreAML.Sym M} (hI : I ⊧ᴵP ΓFnText c) : KoreAML.DefOK I :=
  KoreAML.defOK_of fun x => hI _ (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨x, rfl⟩))))))))

theorem text_item {M : Type} {I : Interpretation KoreAML.Sym M} (hI : I ⊧ᴵP ΓFnText c) {it : KoreAML.Item}
    (h : it ∈ fnItemsText c) : I ⊧ᴵ it.pat :=
  hI _ (Or.inl (Or.inl (Or.inr (Or.inl ⟨it, h, rfl⟩))))

/-- A model of `ΓFnText c` is a model of `Γ c`. -/
theorem gamma_of_text {M : Type} {I : Interpretation KoreAML.Sym M} (hI : I ⊧ᴵP ΓFnText c) : I ⊧ᴵP Γ c := by
  intro φ hφ
  rcases hφ with ((((((h | h) | h) | h) | h) | h) | h)
  · exact hI φ (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl h))))))
  · exact hI φ (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h))))))
  · exact hI φ (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h)))))
  · exact hI φ (Or.inl (Or.inl (Or.inl (Or.inr h))))
  · rcases h with ⟨it, hit, rfl⟩ | ⟨x, rfl⟩
    · rw [fnItems_eq] at hit
      rcases List.mem_append.mp hit with hit | hit
      · rcases List.mem_cons.mp hit with rfl | hit
        · exact text_item hI (by rw [fnItemsText_eq]; exact List.mem_cons_self ..)
        rcases List.mem_cons.mp hit with rfl | hit
        · exact item2C_of (defOK_text hI)
            (text_item hI (by rw [fnItemsText_eq]; exact List.mem_cons_of_mem _ (List.mem_cons_self ..)))
        · cases hit
      · exact text_item hI (by rw [fnItemsText_eq]; exact List.mem_append_right _ hit)
    · exact hI _ (Or.inl (Or.inl (Or.inr (Or.inr ⟨x, rfl⟩))))
  · exact hI φ (Or.inl (Or.inr h))
  · exact hI φ (Or.inr h)

theorem v1_sort : c.sortOf v1 = some Srt.int := by decide +kernel
theorem v2_sort : c.sortOf v2 = some Srt.int := by decide +kernel
theorem genWf_ok : genWf c = true := by decide +kernel
theorem int_apart : apartSort c Srt.int = true := by decide +kernel

/-- **`ΓFnText c` has no model**: its two equations say that `f()` is `1` and that it is `2`. -/
theorem not_model_text : ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M), ¬ (I ⊧ᴵP ΓFnText c) := by
  intro M _ I hI'
  have hI := gamma_of_text hI'
  have htr := (sortCtx_of_all (Semantics.sortedOK_of_okAll okAll (Semantics.ovlPatsOK_of_ovlCase (OvlOK.ovlCase inferInstance))) srReady (OvlOK.ovlCase inferInstance)).trans
  have heq1 := clause_eq hI namesNumbered htr lookup_f (cl := cl1) (List.mem_cons_self ..) rfl rfl rfl (ws := [])
    (by decide +kernel) (σ' := []) (fun _ _ h => by simp [cl1] at h) .nil rfl (by decide +kernel)
    (fun _ h => by simp [cl1] at h) (fun _ h => by cases h) (fun _ h => by simp [cl1, varOccs] at h)
    (fun _ h => by simp [cl1] at h)
    (r := some v1) (fun v hv => by cases hv; exact v1_sort) (fun _ _ _ _ h => by cases h)
    (fun tbl e _ => right_iff hI namesNumbered (lookupFn_spec lookup_f).1 (fun v hv => by cases hv; exact v1_sort)
      (fun m => by
        show (KoreAML.tr ⟨tbl, []⟩ (GroundTerm.kore c v1)).interpret I e m ↔ (den c v1).interpret I e m
        rfl)
      (fun t ht => by simp [cl1] at ht))
  have hax2 : I ⊧ᴵ item2.pat :=
    text_item hI' (by rw [fnItemsText_eq]; exact List.mem_cons_of_mem _ (List.mem_cons_self ..))
  have heq2 := clause_eq_ax hI namesNumbered htr lookup_f (cl := cl2) hax2 (ws := [])
    (by decide +kernel) (σ' := []) (fun _ _ h => by simp [cl2] at h) .nil rfl (by decide +kernel)
    (fun _ h => by simp [cl2] at h) (fun _ h => by cases h) (fun _ h => by simp [cl2, varOccs] at h)
    (fun _ h => by simp [cl2] at h)
    (r := some v2) (fun v hv => by cases hv; exact v2_sort) (fun _ _ _ _ h => by cases h)
    (fun tbl e _ => right_iff hI namesNumbered (lookupFn_spec lookup_f).1 (fun v hv => by cases hv; exact v2_sort)
      (fun m => by
        show (KoreAML.tr ⟨tbl, []⟩ (GroundTerm.kore c v2)).interpret I e m ↔ (den c v2).interpret I e m
        rfl)
      (fun t ht => by simp [cl2] at ht))
  have he : elemOf c I v1 = elemOf c I v2 := by
    have h1 := (elemOf_spec hI v1_sort KoreAML.val0).1
    have h2 := (elemOf_spec hI v2_sort KoreAML.val0).1
    have := (heq2 KoreAML.val0 (elemOf c I v1)).mp ((heq1 KoreAML.val0 _).mpr ((h1 _).mpr rfl))
    exact (h2 _).mp this
  have := values_apart hI genWf_ok htr int_apart v1_sort v2_sort he
  exact absurd this (by decide)

end PrioTextWitness


end Faithful

end KCore
