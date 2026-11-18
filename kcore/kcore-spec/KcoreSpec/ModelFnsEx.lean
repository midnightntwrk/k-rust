/-
  KCore. The value model satisfies the two equations of a clause with existential variables.

  The equation of such a clause is `⌈req = true⌉ ∧ X̄ ∈ p̄ ∧ pre → f(X̄) = (∃ē. rhs ∧ ens ∧ post) ∧ ⊤`
  (`clauseEquation` through `clauseRhs`), under the negation of the exclusions of the clauses of a
  smaller priority where there are some (`competingEquation`). The axiom's guards give an element of
  its sort to each variable that is free in it. An existential variable is bound on the right and,
  being in no pattern, `requires` or premise predicate, occurs nowhere else: the guards give it
  nothing.

  - `AtT.withPre_readEx`: the premise with its predicate, read at a valuation that gives a value of
    its sort to each variable other than the existential ones: the clause applies under the
    valuation's substitution (`Clause.AppliesAt`, which asks sortedness on `Clause.univ` only). It
    is `withPre_readPre` without a sort for the existential variables.
  - `AtT.sat_eqnPremEx`: the equation under any premise that gives the clause's own premise and a
    fact `D` of the arguments, where the clause applying under `D` gives the function's values as
    the values its instances give (`hsolve`, the conclusion of `eval_of_decides_ex`).
  - `AtT.sat_clauseEqEx`, `AtT.sat_competingEqEx`: the two equations, as `sat_clauseEqPre` and
    `sat_competingEqPre` are for a clause without existential variables.
  - `clauseEquation_axEx`, `competingEquation_axEx`: the two sentences are those axioms.

  Two hypotheses are truth values of predicates. `hdec` is `withPre_readPre`'s: the premise's
  predicate has a truth value where the patterns match. `hpostDec` is the same for the right side's
  predicate at each well-sorted instance: the model reads the predicate as `TrueV`, `Clause.Gives`
  reads `Holds … true`, and the two agree only where `Holds` has a truth value (`holds_trueV`).
  A predicate has none where a term of it has no result (`trueV_without_holds`), and it has one
  where every function has a result (`clausePost_decided_of_total`).

  The clause is given by its facts (`EqnFactsEx`), not as a clause of the semantics: `HypModelCore`
  holds `sortedOKCl`, under which no clause of a function of the semantics has an existential
  variable.
-/
import KcoreSpec.ClauseExModel
import KcoreSpec.ClausePreFn

set_option autoImplicit false

namespace KCore

namespace Faithful

namespace Model

open ML

variable {c : Semantics}

/-- **What the model side reads of a clause with existential variables whose equation it reads**,
as a clause of `fn`: `ExclFactsPre`; the existential variables are distinct variables of the clause,
of numbered sorts, and none is in its patterns, `requires` or premise predicate; the right side's
predicate is well sorted with binders that range where values and elements agree; each variable is
existential or occurs in the clause; the right-hand side and the `ensures` are sorted. -/
structure EqnFactsEx (c : Semantics) (fn : Fn) (cl : Clause) : Prop extends ExclFactsPre c fn cl where
  exLt : ∀ i ∈ cl.exs, i < cl.vars.length
  exNodup : cl.exs.Nodup
  exLeft : ∀ i ∈ cl.exs, i ∉ cl.leftVars
  exNum : ∀ i ∈ cl.exs, cl.vars.getD i 0 < nRegSorts + c.sortNames.length
  postOK : c.condOK cl.vars cl.post = true
  postBound : Cond.bound c cl.vars.length cl.post = true
  occ : ∀ i < cl.vars.length, i ∈ cl.exs ∨ i ∈ varOccsList cl.pats ++ cl.condVars ++ varOccs cl.rhs ++
    (cl.ens.map varOccs).getD [] ++ varOccsCond cl.vars.length cl.post
  concl : ∃ L, HeadsOK c L ∧ sortOfTerm (c.rhsCtx L) cl.vars cl.rhs = some fn.result ∧
    ∀ t, cl.ens = some t → sortOfTerm (c.rhsCtx L) cl.vars t = some Srt.bool

/-- Where no existential variable is in the left side, the instances vary every existential
variable. -/
theorem exsFree_eq_of_leftEx {cl : Clause} (h : ∀ i ∈ cl.exs, i ∉ cl.leftVars) : cl.exsFree = cl.exs :=
  List.filter_eq_self.mpr fun i hi => by simpa [List.contains_iff_mem] using h i hi

/-- The variables of a clause with existential variables have numbered sorts. -/
theorem vars_numEx (h : HypModelCore c) {fn : Fn} (hfn : fn ∈ c.allFns) {cl : Clause}
    (F : EqnFactsEx c fn cl) :
    ∀ i < cl.vars.length, cl.vars.getD i 0 < nRegSorts + c.sortNames.length := by
  obtain ⟨L, hL, hrhs, hens⟩ := F.concl
  intro i hi
  have hg : cl.vars[i]? = some (cl.vars.getD i 0) := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; rfl
  have hx : ∀ k ∈ (c.rhsCtx L).heads, k ∈ kernelSyms c := fun k hk => rhsHead_kernel hL hk
  have hsub : ∀ a b, (a, b) ∈ (c.rhsCtx L).subs → (a, b) ∈ c.subsorts := fun _ _ h' => h'
  have hleft := leftVars_numPre h hfn F.toExclFactsPre i hi
  rcases F.occ i hi with hX | hO
  · exact F.exNum i hX
  simp only [List.mem_append] at hO
  rcases hO with (((hl | hR) | hE) | hQ)
  · exact hleft (List.mem_append.mpr hl)
  · exact varOccs_numOpen h hx hsub cl.rhs hrhs (h.fnSorts hfn fn.result (List.mem_cons_self ..)) i hR _ hg
  · cases ht : cl.ens with
    | none => rw [ht] at hE; cases hE
    | some t =>
      rw [ht] at hE
      exact varOccs_numOpen h hx hsub t (hens t ht) bool_numbered i hE _ hg
  · exact varOccsCond_numCN h cl.post F.postOK i hQ _ hg

/-- A variable of a clause other than its existential ones is not bound by the right side's
binders. -/
theorem notBound_clauseEx {cl : Clause} (hlt : ∀ i ∈ cl.exs, i < cl.vars.length) {i : Nat}
    (hi : i < cl.vars.length) (hx : i ∉ cl.exs) :
    (((clauseExBinders c cl).map KoreAML.evarKey).reverse).contains (canonKey c cl.vars i) = false := by
  rw [clauseExBinders_keys]
  apply Bool.eq_false_iff.mpr
  intro hc
  rw [List.contains_iff_mem, List.mem_reverse, List.mem_map] at hc
  obtain ⟨j, hj, he⟩ := hc
  rw [canonKey_inj (hlt j hj) hi he] at hj
  exact hx hj

/-- **Each variable of a clause other than its existential ones is free in its equation's axiom**:
one of its patterns, `requires` or premise predicate in the premise (here any pattern whose free
variables include those of the premise with the predicate), one of the right-hand side, `ensures`
or right side's predicate under the binders, which bind the existential variables only. -/
theorem clause_keys_freeEx {fn : Fn} {cl : Clause} {prem : Kore.Pattern} (F : EqnFactsEx c fn cl)
    (hP : ∀ k, k ∈ KoreAML.freeOf [] (withPre c (canonVars c cl.vars) cl (clausePrem c fn cl)) →
      k ∈ KoreAML.freeOf [] prem) :
    ∀ i < cl.vars.length, i ∉ cl.exs → canonKey c cl.vars i ∈
      KoreAML.freeOf [] (.implies KoreAML.R prem (eqConclEx c fn (clauseRightEx c fn cl))) := by
  intro i hi hx
  have hlen : cl.pats.length = fn.args.length := sortsOfTerms_length F.pats
  have hinP : ∀ {k}, k ∈ KoreAML.freeOf [] (withPre c (canonVars c cl.vars) cl (clausePrem c fn cl)) →
      k ∈ KoreAML.freeOf [] (.implies KoreAML.R prem (eqConclEx c fn (clauseRightEx c fn cl))) := fun hk => by
    rw [KoreAML.freeOf]; exact List.mem_append_left _ (hP _ hk)
  have hb := notBound_clauseEx (c := c) F.exLt hi hx
  have hinB : ∀ {φ : Kore.Pattern},
      canonKey c cl.vars i ∈ KoreAML.freeOf (((clauseExBinders c cl).map KoreAML.evarKey).reverse) φ →
      φ ∈ ([Term.kore c (canonVars c cl.vars) cl.rhs,
        reqPat (srtOf c fn.result) (cl.ens.map (Term.kore c (canonVars c cl.vars)))] ++
        Cond.conj c (canonVars c cl.vars) (srtOf c fn.result) cl.post) →
      canonKey c cl.vars i ∈ KoreAML.freeOf [] (.implies KoreAML.R prem (eqConclEx c fn (clauseRightEx c fn cl))) :=
    fun {φ} hk hφ => by
      rw [KoreAML.freeOf]
      refine List.mem_append_right _ ?_
      unfold eqConclEx
      rw [KoreAML.freeOf]
      refine List.mem_append_right _ ?_
      unfold clauseRightEx
      refine freeOf_and_memOpen (List.mem_cons_self ..) ?_
      rw [freeOf_existsAll_eqEx, List.append_nil]
      unfold clauseRhsBody
      exact freeOf_and_memB hk hφ
  rcases F.occ i hi with hX | hO
  · exact absurd hX hx
  simp only [List.mem_append] at hO
  rcases hO with ((((hp | hC) | hR) | hE) | hQ)
  · exact hinP (freeOf_withPre_premPre (freeOf_premise_var hlen hp))
  · simp only [Clause.condVars, List.mem_append] at hC
    rcases hC with hC | hC
    · cases ht : cl.req with
      | none => rw [ht] at hC; cases hC
      | some t =>
        rw [ht] at hC
        exact hinP (freeOf_withPre_premPre (freeOf_premise_req ht hC))
    · exact hinP (freeOf_withPre_prePre hi hC)
  · exact hinB (kore_freeOfBEx c _ cl.rhs hR hb) (List.mem_cons_self ..)
  · cases ht : cl.ens with
    | none => rw [ht] at hE; cases hE
    | some t =>
      rw [ht] at hE
      refine hinB (φ := reqPat (srtOf c fn.result) (cl.ens.map (Term.kore c (canonVars c cl.vars)))) ?_
        (List.mem_cons_of_mem _ (List.mem_cons_self ..))
      rw [ht]
      simp only [Option.map_some, reqPat]
      rw [KoreAML.freeOf]
      exact List.mem_append_left _ (kore_freeOfBEx c _ t hE hb)
  · have hT : cl.post.isTop = false := by
      cases hq : cl.post
      case top => rw [hq] at hQ; simp [varOccsCond] at hQ
      all_goals rfl
    refine hinB (condKore_keys (srtOf c fn.result) cl.post hi hQ hb).1 ?_
    simp [Cond.conj, hT]

namespace AtT

variable {T : GroundTerm → GroundTerm → Prop}

/-- **A clause's premise with its predicate, read at a valuation that gives the existential
variables nothing**: where it holds and each variable of the clause other than the existential
ones is at a value of its sort, the clause applies at the arguments under the substitution the
valuation gives, provided the predicate has a truth value at such a match (`hdec`). No existential
variable is in the patterns, the `requires` or the predicate (`hexL`), so none is read. -/
theorem withPre_readEx (h : HypModelCore c) {fn : Fn} {cl : Clause} (F : ExclFactsPre c fn cl)
    (hexL : ∀ i ∈ cl.exs, i ∉ cl.leftVars)
    (hdec : ∀ σ ws, c.WellSortedAt cl.vars cl.leftVars σ → PatVals c σ cl.pats ws →
      (∀ t, cl.req = some t → EvalTerm c σ t (some (bool true))) → ∃ b, Holds c cl.vars.length σ cl.pre b)
    {tbl : KoreAML.VarTable} {e : Valuation Elem} {ws : List GroundTerm} {a : Elem}
    (hR : KoreAML.VarKey.sortVar "R" ∈ tbl)
    (hRs : KoreAML.IsSort (stdI_T c T) (e.evalEvar (tbl.ev (.sortVar "R"))))
    (hargs : ArgsAt c tbl e fn.args ws)
    (hVk : ∀ i < cl.vars.length, i ∉ cl.exs → canonKey c cl.vars i ∈ tbl)
    (hvin : ∀ i < cl.vars.length, i ∉ cl.exs →
      InSort c (cl.vars.getD i 0) (e.evalEvar (tbl.ev (canonKey c cl.vars i))))
    (hvT : ∀ k ∈ KoreAML.varsOf (withPre c (canonVars c cl.vars) cl (clausePrem c fn cl)), k ∈ tbl)
    (ha : KoreAML.Inh (stdI_T c T) (e.evalEvar (tbl.ev (.sortVar "R"))) a)
    (hprem : (KoreAML.tr ⟨tbl, []⟩ (withPre c (canonVars c cl.vars) cl (clausePrem c fn cl))).interpret
      (stdI_T c T) e a) :
    cl.AppliesAt c (substE c tbl cl.vars e) ws := by
  obtain ⟨L, hL, hreqs⟩ := F.req
  have hlen : cl.pats.length = fn.args.length := sortsOfTerms_length F.pats
  let P : Nat → Prop := fun i => i < cl.vars.length ∧ i ∉ cl.exs
  have hval : ∀ i, P i → ∃ v, e.evalEvar (tbl.ev (canonKey c cl.vars i)) = .val v ∧
      c.sortOf v = some (cl.vars.getD i 0) := fun i hi => inSort_val (hvin i hi.1 hi.2)
  have hvar : ∀ i, P i → ∀ m,
      (KoreAML.tr ⟨tbl, []⟩ (KoreAML.varAt (canonVars c cl.vars) i)).interpret (stdI_T c T) e m ↔
        ∃ v, (substE c tbl cl.vars e).lookup i = some v ∧ m = .val v := by
    intro i hi m
    obtain ⟨v, he, -⟩ := hval i hi
    rw [var_read, substE_lookup hi.1]
    show m = e.evalEvar (tbl.ev (canonKey c cl.vars i)) ↔ _
    rw [he]
    simp [toVal]
  have hσP : ∀ i, P i → ∀ s, cl.vars[i]? = some s →
      ∃ v, (substE c tbl cl.vars e).lookup i = some v ∧ c.sortOf v = some s := by
    intro i hi s hs
    obtain ⟨v, he, hsv⟩ := hval i hi
    refine ⟨v, by rw [substE_lookup hi.1, he]; rfl, ?_⟩
    rwa [List.getD_eq_getElem?_getD, hs, Option.getD_some] at hsv
  have hleftP : ∀ i ∈ cl.leftVars, i < cl.vars.length → P i := fun i hi hl => ⟨hl, fun hx => hexL i hx hi⟩
  have hσ : c.WellSortedAt cl.vars cl.univ (substE c tbl cl.vars e) := by
    intro i hi s hs
    have hx : i ∉ cl.exs := by
      have := (List.mem_filter.mp hi).2
      simpa [List.contains_iff_mem] using this
    exact hσP i ⟨(List.getElem?_eq_some_iff.mp hs).1, hx⟩ s hs
  have hσl : c.WellSortedAt cl.vars cl.leftVars (substE c tbl cl.vars e) := fun i hi s hs =>
    hσP i (hleftP i hi (List.getElem?_eq_some_iff.mp hs).1) s hs
  have hsplit : (KoreAML.tr ⟨tbl, []⟩ (clausePrem c fn cl)).interpret (stdI_T c T) e a ∧
      (cl.pre.isTop = false →
        (KoreAML.tr ⟨tbl, []⟩ (Cond.kore c (canonVars c cl.vars) KoreAML.R cl.pre)).interpret (stdI_T c T) e a) := by
    cases hpt : cl.pre.isTop with
    | true => rw [withPre_isTop hpt] at hprem; exact ⟨hprem, fun h' => Bool.noConfusion h'⟩
    | false => exact ⟨((HoldsShape.withPre_interp hpt).mp hprem).1, fun _ => ((HoldsShape.withPre_interp hpt).mp hprem).2⟩
  obtain ⟨-, hq, hpv⟩ := (premise_iffCl h (P := P) (R_read e) hRs hvar
    (fun t ht => (termOK_of_sorted h hL (hreqs t ht)).monoOpen fun i hi =>
      hleftP i (Clause.req_leftVars ht i hi) (varOccs_lt t (hreqs t ht) i hi))
    (fun p hp => (patOKs_of_sorted h F.pats p hp).monoOpen fun i hi =>
      have hil : i ∈ varOccsList cl.pats := varOccsList_of_memOpen hp hi
      hleftP i (List.mem_append_left _ hil) (varOccsList_lt cl.pats F.pats i hil))
    hlen hargs a).mp hsplit.1
  refine ⟨hσ, hpv, hq, ?_⟩
  cases hpt : cl.pre.isTop with
  | true => exact Clause.holds_preTop (Cond.eq_top_of_isTop hpt) _
  | false =>
    obtain ⟨b, hb⟩ := hdec _ ws hσl hpv hq
    have hr : ReadsT c cl.vars P (substE c tbl cl.vars e) tbl e := fun i hi => by
      obtain ⟨v, he, hsv⟩ := hval i hi
      exact ⟨hi.1, hVk i hi.1 hi.2, v, by rw [substE_lookup hi.1, he]; rfl, hsv, he⟩
    have hbt := (holdsT_atR h cl.pre F.preOK F.bound
      (fun i hi hlt => hleftP i (Clause.pre_leftVarsRH i hi) hlt) hr
      (fun k hk => hvT k (HoldsShape.varsOf_withPre_pre hpt hk)) hR hRs hb a ha).mp (hsplit.2 hpt)
    rw [hbt] at hb
    exact hb

/-- **The equation of a clause with existential variables holds in the value model under a premise
that gives the clause's own**: where the premise holds, the clause's premise with its predicate
holds and the arguments have the fact `D` (`hpremD`); and the clause applying at arguments with
`D` gives the function's values as the values its instances give (`hsolve`). The predicates have
truth values: the premise's where the patterns match (`hdec`), the right side's at each well-sorted
instance (`hpostDec`). -/
theorem sat_eqnPremEx (h : HypModelCore c) {fn : Fn} (hfn : fn ∈ c.allFns) {cl : Clause}
    (F : EqnFactsEx c fn cl) {prem : Kore.Pattern} {D : List GroundTerm → Prop}
    (hPf : ∀ k, k ∈ KoreAML.freeOf [] (withPre c (canonVars c cl.vars) cl (clausePrem c fn cl)) →
      k ∈ KoreAML.freeOf [] prem)
    (hPv : ∀ k, k ∈ KoreAML.varsOf (withPre c (canonVars c cl.vars) cl (clausePrem c fn cl)) →
      k ∈ KoreAML.varsOf prem)
    (hdec : ∀ σ ws, c.WellSortedAt cl.vars cl.leftVars σ → PatVals c σ cl.pats ws →
      (∀ t, cl.req = some t → EvalTerm c σ t (some (bool true))) → ∃ b, Holds c cl.vars.length σ cl.pre b)
    (hpostDec : ∀ σ', c.WellSorted cl.vars σ' → ∃ b, Holds c cl.vars.length σ' cl.post b)
    (hpremD : ∀ (tbl : KoreAML.VarTable) (e : Valuation Elem) (ws : List GroundTerm) (a : Elem),
      KoreAML.VarKey.sortVar "R" ∈ tbl → (∀ k ∈ KoreAML.varsOf prem, k ∈ tbl) →
      (∀ (j : Nat) (s : String), (fn.args.map c.sortName)[j]? = some s →
        KoreAML.VarKey.evar ("X" ++ toString j) (KoreAML.srt s) ∈ tbl) →
      KoreAML.IsSort (stdI_T c T) (e.evalEvar (tbl.ev (.sortVar "R"))) → ArgsAt c tbl e fn.args ws →
      KoreAML.Inh (stdI_T c T) (e.evalEvar (tbl.ev (.sortVar "R"))) a →
      (KoreAML.tr ⟨tbl, []⟩ prem).interpret (stdI_T c T) e a →
      (KoreAML.tr ⟨tbl, []⟩ (withPre c (canonVars c cl.vars) cl (clausePrem c fn cl))).interpret
        (stdI_T c T) e a ∧ D ws)
    (hsolve : ∀ σ ws, c.sortsOf ws = some fn.args → cl.AppliesAt c σ ws → D ws →
      ∀ v, Eval c fn.label ws (some v) ↔
        ∃ σ', AgreeOff cl.exsFree σ σ' ∧ c.WellSorted cl.vars σ' ∧ cl.Gives c σ' v) :
    stdI_T c T ⊧ᴵ (KoreAML.trAxiom [] [] ⟨0, "kernel", (⟨[KoreAML.Rv],
      .implies KoreAML.R prem (eqConclEx c fn (clauseRightEx c fn cl)), []⟩ : Kore.Axiom)⟩).pat := by
  obtain ⟨L, hL, hrhs, hens⟩ := F.concl
  obtain ⟨L', hL', hreqs⟩ := F.req
  obtain ⟨hok, hsr, -, -, -, -, -, -, hno⟩ := h.sound
  haveI : OvlOK c := hno
  have hsc := sortCtx_of_allCl hok hsr (OvlOK.ovlCase hno)
  have hreqv : ∀ t, cl.req = some t → ∀ i ∈ varOccs t, i < cl.vars.length := fun t ht =>
    varOccs_lt t (hreqs t ht)
  have hVv := clause_keys_inAxEx (c := c) (prem := prem) F.pats hreqv F.occ hPv
  refine sat_eqnClauseEx h hfn (vars_numEx h hfn F) F.exLt F.exNodup (termOK_of_sorted h hL hrhs)
    (fun t ht => termOK_of_sorted h hL (hens t ht)) (varOccs_lt cl.rhs hrhs)
    (fun t ht => varOccs_lt t (hens t ht)) F.postOK F.postBound
    (fun σ' y hσ' hy => EvalTerm.sorted_at hsc hy hL (hσ'.at _) hrhs rfl) hpostDec
    (clause_keys_freeEx F hPf) hVv fun tbl e ws a hR hk hRs hws hvin ha hp => ?_
  have hXk : ∀ (j : Nat) (s : String), (fn.args.map c.sortName)[j]? = some s →
      KoreAML.VarKey.evar ("X" ++ toString j) (KoreAML.srt s) ∈ tbl := fun j s hj => by
    refine hk _ ?_
    rw [KoreAML.varsOf]
    refine List.mem_append_right _ ?_
    unfold eqConclEx
    rw [KoreAML.varsOf]
    refine List.mem_append_left _ (List.mem_append_right _ ?_)
    unfold KoreAML.ap
    rw [KoreAML.varsOf]
    refine List.mem_append_right _ ?_
    have := X_mem_varsOf_call _ 0 j s hj
    rwa [Nat.zero_add] at this
  have hkP : ∀ k ∈ KoreAML.varsOf prem, k ∈ tbl := fun k hk' =>
    hk k (by rw [KoreAML.varsOf]; exact List.mem_append_left _ (List.mem_append_right _ hk'))
  obtain ⟨hw, hD⟩ := hpremD tbl e ws a hR hkP hXk hRs hws ha hp
  have happ := withPre_readEx h F.toExclFactsPre F.exLeft hdec hR hRs hws (fun i hi _ => hk _ (hVv i hi)) hvin
    (fun k hk' => hkP k (hPv k hk')) ha hw
  refine ⟨substE c tbl cl.vars e, fun i hi hx => ?_, ?_⟩
  · obtain ⟨v, he, -⟩ := inSort_val (hvin i hi hx)
    exact ⟨v, by rw [substE_lookup hi, he]; rfl, he⟩
  · have hs := hsolve _ ws hws.sorts happ hD
    rwa [exsFree_eq_of_leftEx F.exLeft] at hs

/-- **The equation of a clause with existential variables and no competitor holds**, where its
applying gives the function's values as the values its instances give (`hsolve`): `f` at the
arguments is the value an instance gives, and has no element where none gives one. -/
theorem sat_clauseEqEx (h : HypModelCore c) {fn : Fn} (hfn : fn ∈ c.allFns) {cl : Clause}
    (F : EqnFactsEx c fn cl)
    (hdec : ∀ σ ws, c.WellSortedAt cl.vars cl.leftVars σ → PatVals c σ cl.pats ws →
      (∀ t, cl.req = some t → EvalTerm c σ t (some (bool true))) → ∃ b, Holds c cl.vars.length σ cl.pre b)
    (hpostDec : ∀ σ', c.WellSorted cl.vars σ' → ∃ b, Holds c cl.vars.length σ' cl.post b)
    (hsolve : ∀ σ ws, c.sortsOf ws = some fn.args → cl.AppliesAt c σ ws →
      ∀ v, Eval c fn.label ws (some v) ↔
        ∃ σ', AgreeOff cl.exsFree σ σ' ∧ c.WellSorted cl.vars σ' ∧ cl.Gives c σ' v) :
    stdI_T c T ⊧ᴵ (KoreAML.trAxiom [] [] ⟨0, "kernel", (⟨[KoreAML.Rv], .implies KoreAML.R
      (withPre c (canonVars c cl.vars) cl (clausePrem c fn cl))
      (eqConclEx c fn (clauseRightEx c fn cl)), []⟩ : Kore.Axiom)⟩).pat :=
  sat_eqnPremEx h hfn F (D := fun _ => True) (fun _ hk => hk) (fun _ hk => hk) hdec hpostDec
    (fun _ _ _ _ _ _ _ _ _ _ hp => ⟨hp, trivial⟩) fun σ ws hws happ _ => hsolve σ ws hws happ

/-- **The equation of a clause with existential variables under the negation of its competitors
holds**: where they all fail with their predicates (`fails_of_not_exclPre`) and it applies, its
applying gives the function's values as the values its instances give (`hsolve`). -/
theorem sat_competingEqEx (h : HypModelCore c) {fn : Fn} (hfn : fn ∈ c.allFns) {cl : Clause}
    (F : EqnFactsEx c fn cl)
    (hdec : ∀ σ ws, c.WellSortedAt cl.vars cl.leftVars σ → PatVals c σ cl.pats ws →
      (∀ t, cl.req = some t → EvalTerm c σ t (some (bool true))) → ∃ b, Holds c cl.vars.length σ cl.pre b)
    (hpostDec : ∀ σ', c.WellSorted cl.vars σ' → ∃ b, Holds c cl.vars.length σ' cl.post b)
    {others : List Clause} (hF : ∀ cl' ∈ others, ExclFactsPre c fn cl')
    (hsolve : ∀ σ ws, c.sortsOf ws = some fn.args → cl.AppliesAt c σ ws →
      (∀ cl' ∈ others, ∀ σ', c.WellSortedAt cl'.vars cl'.leftVars σ' → PatVals c σ' cl'.pats ws →
        ¬ ((∀ t, cl'.req = some t → EvalTerm c σ' t (some (bool true))) ∧
           Holds c cl'.vars.length σ' cl'.pre true)) →
      ∀ v, Eval c fn.label ws (some v) ↔
        ∃ σ', AgreeOff cl.exsFree σ σ' ∧ c.WellSorted cl.vars σ' ∧ cl.Gives c σ' v) :
    stdI_T c T ⊧ᴵ (KoreAML.trAxiom [] [] ⟨0, "kernel", (⟨[KoreAML.Rv], .implies KoreAML.R
      (.and KoreAML.R [.not KoreAML.R (KoreAML.anyOf (others.map fun cl' => exclusion c fn cl' (canonClausePres cl'))),
        withPre c (canonVars c cl.vars) cl (clausePrem c fn cl)])
      (eqConclEx c fn (clauseRightEx c fn cl)), []⟩ : Kore.Axiom)⟩).pat := by
  refine sat_eqnPremEx h hfn F
    (D := fun ws => ∀ cl' ∈ others, ∀ σ', c.WellSortedAt cl'.vars cl'.leftVars σ' → PatVals c σ' cl'.pats ws →
      ¬ ((∀ t, cl'.req = some t → EvalTerm c σ' t (some (bool true))) ∧
         Holds c cl'.vars.length σ' cl'.pre true))
    (fun _ hk => freeOf_and_memOpen (List.mem_cons_of_mem _ (List.mem_singleton_self _)) hk)
    (fun _ hk => varsOf_and_mem (List.mem_cons_of_mem _ (List.mem_singleton_self _)) hk) hdec hpostDec
    (fun tbl e ws a hR hkP hXk hRs hws ha hp => ?_) hsolve
  rw [tr_and2, KoreAML.interp_sAnd] at hp
  obtain ⟨hnot, hp⟩ := hp
  have hvN : ∀ k ∈ KoreAML.varsOf (.not KoreAML.R (KoreAML.anyOf
      (others.map fun cl' => exclusion c fn cl' (canonClausePres cl')))), k ∈ tbl :=
    fun k hk => hkP k (varsOf_and_mem (List.mem_cons_self ..) hk)
  obtain ⟨-, hfails⟩ := fails_of_not_exclPre (T := T) h hfn hF hR hXk hRs hws
    (fun cl' hcl' i hi hil => hvN _ (varsOf_not_exclPre hcl' hi hil))
    (fun cl' hcl' hpt k hk => hvN _ (varsOf_not_excl_prePre hcl' hpt hk)) hnot
  exact ⟨hp, fun cl' hcl' σ' hw hp' hqh => hfails cl' hcl' σ' ⟨hw, hp', hqh.1, hqh.2⟩⟩

end AtT

/-! ## The two sentences -/

/-- The equation of a clause with existential variables is the axiom `sat_clauseEqEx` reads. -/
theorem clauseEquation_axEx {fn : Fn} {cl : Clause} (hne : cl.exs ≠ []) (hlt : ∀ i ∈ cl.exs, i < cl.vars.length) :
    clauseEquation c fn cl = .axiom ⟨[KoreAML.Rv], .implies KoreAML.R
      (withPre c (canonVars c cl.vars) cl (clausePrem c fn cl))
      (eqConclEx c fn (clauseRightEx c fn cl)), []⟩ := by
  unfold clauseEquation
  rw [clauseRhs_eqEx hne hlt]
  rfl

/-- The competing equation of a clause with existential variables is the axiom `sat_competingEqEx`
reads. -/
theorem competingEquation_axEx {fn : Fn} {others : List Clause} {cl : Clause} (hne : cl.exs ≠ [])
    (hlt : ∀ i ∈ cl.exs, i < cl.vars.length) :
    competingEquation c fn others cl = .axiom ⟨[KoreAML.Rv], .implies KoreAML.R
      (.and KoreAML.R [.not KoreAML.R (KoreAML.anyOf (others.map fun cl' => exclusion c fn cl' (canonClausePres cl'))),
        withPre c (canonVars c cl.vars) cl (clausePrem c fn cl)])
      (eqConclEx c fn (clauseRightEx c fn cl)), []⟩ := by
  unfold competingEquation
  rw [clauseRhs_eqEx hne hlt]
  rfl

/-! ## The right side's predicate and its truth value -/

/-- **The right side's predicate has a truth value at every well-sorted instance**, where it is
well sorted over the clause's variables and every function has a result at arguments of its
sorts. -/
theorem clausePost_decided_of_total (hs : HypSoundCore c) (ht : FnTerminates c) {cl : Clause}
    (hok : c.condOK cl.vars cl.post = true) {σ : Subst} (hσ : c.WellSorted cl.vars σ) :
    ∃ b, Holds c cl.vars.length σ cl.post b :=
  holds_decided hs ht cl.post hok (hσ.at _)

/-- **A predicate can be true in the value model where `Holds` gives it no truth value**: where a
term has no result at all, `¬⌈t⌉` is true in the value model's reading and has no truth value. So
`TrueV` gives `Holds … true` only under a hypothesis that the predicate is decided. -/
theorem trueV_without_holds {n : Nat} {σ : Subst} {s : Srt} {t : Term} (hno : ∀ r, ¬ EvalTerm c σ t r) :
    TrueV c n σ (.not (.ceil s t)) ∧ ¬ ∃ b, Holds c n σ (.not (.ceil s t)) b := by
  refine ⟨fun ⟨v, hv⟩ => hno _ hv, ?_⟩
  rintro ⟨b, hb⟩
  cases hb with
  | not hb' => cases hb' with
    | ceil he => exact hno _ he

end Model

end Faithful

end KCore
