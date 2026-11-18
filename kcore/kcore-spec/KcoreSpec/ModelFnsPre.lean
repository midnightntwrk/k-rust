/-
  KCore. The value model satisfies the equation of a clause with a predicate in its premise.

  A clause's equation is `⌈req = true⌉ ∧ X̄ ∈ p̄ ∧ pre → f(X̄) = rhs ∧ ens` (`withPre`), and a clause
  of a smaller priority is negated by its exclusion `∃ȳ. ⌈req = true⌉ ∧ X̄ ∈ p̄ ∧ pre`, ȳ the
  variables of its patterns and conditions (`exclusion_canon_mapPre`). The predicate is read at the
  sort variable `R` in the value model by `holdsT_atR`: at a valuation that reads its variables as
  their values under σ, an element of `R`'s sort is in it exactly where the truth value `Holds`
  gives it under σ is `true`.

  - `exclusion_ofPre`: where a clause matches under a substitution well sorted on the variables of
    its patterns and conditions, its `requires` is `true` and its predicate is true, its exclusion
    holds. So where the negated disjunction of exclusions holds, none of those clauses does
    (`fails_of_not_exclPre`). This direction reads the predicate's truth value `true` only.
  - `withPre_readPre`: where a clause's premise with its predicate holds, the patterns match, the
    `requires` is `true`, and the predicate is true, provided the predicate has a truth value there
    (`hdec`). The premise states only that the predicate's pattern holds, and `holdsT_atR` turns
    that into a truth value only where `Holds` gives one: a predicate without a truth value (one
    whose terms have no result) is read in the value model as a set that `Holds` does not decide.
  - `sat_clauseEqPre`, `sat_competingEqPre`: the two kinds of equation hold for a clause given by
    explicit facts (`EqnFactsPre`), its competitors by `ExclFactsPre`, where its applying under
    the competitors' failure gives the function's values (`hsolve`, what `eval_of_decides` gives
    for a clause of the function).
  - `satFnsGoalPre`: the functions' equations hold where every clause's predicate is well sorted
    and has a truth value where its patterns match and its `requires` is `true`; each clause's facts
    come from `HypModelCore` without reading its predicate as `\top` (`clause_eqnFactsPre`).
-/
import KcoreSpec.CondResortModel
import KcoreSpec.CondNumbered

set_option autoImplicit false

namespace KCore

namespace Faithful

namespace Model

open ML

variable {c : Semantics}

/-- **What the model side reads of a clause whose exclusion it reads**, as a clause of `fn`: its
patterns have the argument sorts, its `requires` is a Bool over some functions' signatures, and its
predicate is well sorted with binders that range where values and elements agree. -/
structure ExclFactsPre (c : Semantics) (fn : Fn) (cl : Clause) : Prop where
  pats : sortsOfTerms c.patCtxAll cl.vars cl.pats = some fn.args
  req : ∃ L, HeadsOK c L ∧ ∀ t, cl.req = some t → sortOfTerm (c.rhsCtx L) cl.vars t = some Srt.bool
  preOK : c.condOK cl.vars cl.pre = true
  bound : Cond.bound c cl.vars.length cl.pre = true

/-- **What the model side reads of a clause whose equation it reads**, as a clause of `fn`:
`ExclFactsPre`, no existential variable, each variable occurring in its patterns, its `requires`,
its predicate, its right side or its `ensures`, and its right side and `ensures` sorted. -/
structure EqnFactsPre (c : Semantics) (fn : Fn) (cl : Clause) : Prop extends ExclFactsPre c fn cl where
  exs : cl.exs = []
  occ : ∀ i < cl.vars.length, i ∈ varOccsList cl.pats ∨ (∃ t, cl.req = some t ∧ i ∈ varOccs t) ∨
    i ∈ varOccsCond cl.vars.length cl.pre ∨ i ∈ varOccs cl.rhs ∨ ∃ t, cl.ens = some t ∧ i ∈ varOccs t
  concl : ∃ L, HeadsOK c L ∧ sortOfTerm (c.rhsCtx L) cl.vars cl.rhs = some fn.result ∧
    ∀ t, cl.ens = some t → sortOfTerm (c.rhsCtx L) cl.vars t = some Srt.bool

/-- The variables of a clause's patterns and conditions have numbered sorts: those of its patterns
by the argument sorts, those of its `requires` and its predicate by their sorting. -/
theorem leftVars_numPre (h : HypModelCore c) {fn : Fn} (hfn : fn ∈ c.allFns) {cl : Clause}
    (F : ExclFactsPre c fn cl) :
    ∀ i < cl.vars.length, i ∈ cl.leftVars → cl.vars.getD i 0 < nRegSorts + c.sortNames.length := by
  obtain ⟨L, hL, hreqs⟩ := F.req
  intro i hi hil
  have hg : cl.vars[i]? = some (cl.vars.getD i 0) := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; rfl
  have hx : ∀ k ∈ (c.rhsCtx L).heads, k ∈ kernelSyms c := fun k hk => rhsHead_kernel hL hk
  have hsub : ∀ a b, (a, b) ∈ (c.rhsCtx L).subs → (a, b) ∈ c.subsorts := fun _ _ h' => h'
  simp only [Clause.leftVars, Clause.condVars, List.mem_append] at hil
  rcases hil with hP | hR | hC
  · exact varOccsList_num h cl.pats F.pats (fun s hs => h.fnSorts hfn s (List.mem_cons_of_mem _ hs)) i hP _ hg
  · cases ht : cl.req with
    | none => rw [ht] at hR; cases hR
    | some t =>
      rw [ht] at hR
      exact varOccs_numOpen h hx hsub t (hreqs t ht) bool_numbered i hR _ hg
  · exact varOccsCond_numCN h cl.pre F.preOK i hC _ hg

/-- A clause's variables have numbered sorts: each occurs in its patterns, its conditions, its right
side or its `ensures`. -/
theorem vars_numPre (h : HypModelCore c) {fn : Fn} (hfn : fn ∈ c.allFns) {cl : Clause}
    (F : EqnFactsPre c fn cl) :
    ∀ i < cl.vars.length, cl.vars.getD i 0 < nRegSorts + c.sortNames.length := by
  obtain ⟨L, hL, hrhs, hens⟩ := F.concl
  intro i hi
  have hg : cl.vars[i]? = some (cl.vars.getD i 0) := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; rfl
  have hx : ∀ k ∈ (c.rhsCtx L).heads, k ∈ kernelSyms c := fun k hk => rhsHead_kernel hL hk
  have hsub : ∀ a b, (a, b) ∈ (c.rhsCtx L).subs → (a, b) ∈ c.subsorts := fun _ _ h' => h'
  have hleft := leftVars_numPre h hfn F.toExclFactsPre i hi
  rcases F.occ i hi with hP | ⟨t, ht, hit⟩ | hC | hR | ⟨t, ht, hit⟩
  · exact hleft (List.mem_append_left _ hP)
  · exact hleft (Clause.req_leftVars ht i hit)
  · exact hleft (Clause.pre_leftVarsRH i hC)
  · exact varOccs_numOpen h hx hsub cl.rhs hrhs (h.fnSorts hfn fn.result (List.mem_cons_self ..)) i hR _ hg
  · exact varOccs_numOpen h hx hsub t (hens t ht) bool_numbered i hit _ hg

/-! ## The variables of a clause's equation -/

/-- A free variable of a clause's premise is free in the premise with its predicate. -/
theorem freeOf_withPre_premPre {vs : List KoreAML.Var} {cl : Clause} {prem : Kore.Pattern} {k : KoreAML.VarKey}
    (hk : k ∈ KoreAML.freeOf [] prem) : k ∈ KoreAML.freeOf [] (withPre c vs cl prem) := by
  unfold withPre
  split
  · exact hk
  · exact freeOf_and_memOpen (List.mem_cons_self ..) hk

/-- A variable of a clause's predicate is free in its premise with the predicate. -/
theorem freeOf_withPre_prePre {fn : Fn} {cl : Clause} {i : Nat} (hi : i < cl.vars.length)
    (hC : i ∈ varOccsCond cl.vars.length cl.pre) :
    canonKey c cl.vars i ∈ KoreAML.freeOf [] (withPre c (canonVars c cl.vars) cl (clausePrem c fn cl)) := by
  have hpt : cl.pre.isTop = false := by
    cases hpt : cl.pre.isTop with
    | false => rfl
    | true => rw [Cond.eq_top_of_isTop hpt] at hC; simp [varOccsCond] at hC
  unfold withPre
  rw [hpt, if_neg (by simp)]
  exact freeOf_and_memOpen (List.mem_cons_of_mem _ (List.mem_singleton_self _))
    (Model.condKore_keys KoreAML.R cl.pre (bound := []) hi hC rfl).1

/-- **Each variable of a clause is free in its equation's axiom**, where each occurs in its
patterns, `requires`, predicate, right side or `ensures`: one of the first three in the premise with
the predicate (here any pattern whose free variables include that premise's), one of the right side
or the `ensures` in the conclusion. -/
theorem clause_keys_freePre {fn : Fn} {cl : Clause} {prem : Kore.Pattern} (hlen : cl.pats.length = fn.args.length)
    (hocc : ∀ i < cl.vars.length, i ∈ varOccsList cl.pats ∨ (∃ t, cl.req = some t ∧ i ∈ varOccs t) ∨
      i ∈ varOccsCond cl.vars.length cl.pre ∨ i ∈ varOccs cl.rhs ∨ ∃ t, cl.ens = some t ∧ i ∈ varOccs t)
    (hP : ∀ k, k ∈ KoreAML.freeOf [] (withPre c (canonVars c cl.vars) cl (clausePrem c fn cl)) →
      k ∈ KoreAML.freeOf [] prem) :
    ∀ i < cl.vars.length, canonKey c cl.vars i ∈ KoreAML.freeOf [] (.implies KoreAML.R prem
      (fnConcl c fn (Term.kore c (canonVars c cl.vars) cl.rhs)
        (reqPat (srtOf c fn.result) (cl.ens.map (Term.kore c (canonVars c cl.vars)))))) := by
  intro i hi
  have hinP : ∀ {k}, k ∈ KoreAML.freeOf [] (withPre c (canonVars c cl.vars) cl (clausePrem c fn cl)) →
      k ∈ KoreAML.freeOf [] (.implies KoreAML.R prem (fnConcl c fn (Term.kore c (canonVars c cl.vars) cl.rhs)
        (reqPat (srtOf c fn.result) (cl.ens.map (Term.kore c (canonVars c cl.vars)))))) := fun hk => by
    rw [KoreAML.freeOf]; exact List.mem_append_left _ (hP _ hk)
  have hinR : ∀ {k}, k ∈ KoreAML.freeOf [] (Kore.Pattern.and (KoreAML.srt (c.sortName fn.result))
      [Term.kore c (canonVars c cl.vars) cl.rhs,
        reqPat (srtOf c fn.result) (cl.ens.map (Term.kore c (canonVars c cl.vars)))]) →
      k ∈ KoreAML.freeOf [] (.implies KoreAML.R prem (fnConcl c fn (Term.kore c (canonVars c cl.vars) cl.rhs)
        (reqPat (srtOf c fn.result) (cl.ens.map (Term.kore c (canonVars c cl.vars)))))) := fun hk => by
    rw [KoreAML.freeOf]
    refine List.mem_append_right _ ?_
    unfold fnConcl
    rw [KoreAML.freeOf]
    exact List.mem_append_right _ hk
  rcases hocc i hi with hp | ⟨t, ht, hit⟩ | hC | hr | ⟨t, ht, hit⟩
  · exact hinP (freeOf_withPre_premPre (freeOf_premise_var hlen hp))
  · exact hinP (freeOf_withPre_premPre (freeOf_premise_req ht hit))
  · exact hinP (freeOf_withPre_prePre hi hC)
  · exact hinR (freeOf_and_memOpen (List.mem_cons_self ..) (kore_freeOf c _ cl.rhs hr))
  · refine hinR (freeOf_and_memOpen (List.mem_cons_of_mem _ (List.mem_singleton_self _)) ?_)
    rw [ht]
    simp only [Option.map_some, reqPat]
    rw [KoreAML.freeOf]
    exact List.mem_append_left _ (kore_freeOf c _ t hit)

/-- `clause_keys_freePre` for the variables of the axiom. -/
theorem clause_keys_varsPre {fn : Fn} {cl : Clause} {prem : Kore.Pattern} (hlen : cl.pats.length = fn.args.length)
    (hocc : ∀ i < cl.vars.length, i ∈ varOccsList cl.pats ∨ (∃ t, cl.req = some t ∧ i ∈ varOccs t) ∨
      i ∈ varOccsCond cl.vars.length cl.pre ∨ i ∈ varOccs cl.rhs ∨ ∃ t, cl.ens = some t ∧ i ∈ varOccs t)
    (hP : ∀ k, k ∈ KoreAML.varsOf (withPre c (canonVars c cl.vars) cl (clausePrem c fn cl)) →
      k ∈ KoreAML.varsOf prem) :
    ∀ i < cl.vars.length, canonKey c cl.vars i ∈ KoreAML.varsOf (.implies KoreAML.R prem
      (fnConcl c fn (Term.kore c (canonVars c cl.vars) cl.rhs)
        (reqPat (srtOf c fn.result) (cl.ens.map (Term.kore c (canonVars c cl.vars)))))) := by
  intro i hi
  have hinP : ∀ {k}, k ∈ KoreAML.varsOf (withPre c (canonVars c cl.vars) cl (clausePrem c fn cl)) →
      k ∈ KoreAML.varsOf (.implies KoreAML.R prem (fnConcl c fn (Term.kore c (canonVars c cl.vars) cl.rhs)
        (reqPat (srtOf c fn.result) (cl.ens.map (Term.kore c (canonVars c cl.vars)))))) := fun hk => by
    rw [KoreAML.varsOf]; exact List.mem_append_left _ (List.mem_append_right _ (hP _ hk))
  have hinR : ∀ {k}, k ∈ KoreAML.varsOf (Kore.Pattern.and (KoreAML.srt (c.sortName fn.result))
      [Term.kore c (canonVars c cl.vars) cl.rhs,
        reqPat (srtOf c fn.result) (cl.ens.map (Term.kore c (canonVars c cl.vars)))]) →
      k ∈ KoreAML.varsOf (.implies KoreAML.R prem (fnConcl c fn (Term.kore c (canonVars c cl.vars) cl.rhs)
        (reqPat (srtOf c fn.result) (cl.ens.map (Term.kore c (canonVars c cl.vars)))))) := fun hk => by
    rw [KoreAML.varsOf]
    refine List.mem_append_right _ ?_
    unfold fnConcl
    rw [KoreAML.varsOf]
    exact List.mem_append_right _ hk
  rcases hocc i hi with hp | ⟨t, ht, hit⟩ | hC | hr | ⟨t, ht, hit⟩
  · exact hinP (HoldsShape.varsOf_withPre_prem (varsOf_premise_var hlen hp))
  · exact hinP (HoldsShape.varsOf_withPre_prem (varsOf_premise_req ht hit))
  · have hpt : cl.pre.isTop = false := by
      cases hpt : cl.pre.isTop with
      | false => rfl
      | true => rw [Cond.eq_top_of_isTop hpt] at hC; simp [varOccsCond] at hC
    exact hinP (HoldsShape.varsOf_withPre_pre hpt (Model.condKore_keys KoreAML.R cl.pre (bound := []) hi hC rfl).2)
  · exact hinR (varsOf_and_mem (List.mem_cons_self ..) (varsOf_kore c _ cl.rhs hr))
  · refine hinR (varsOf_and_mem (List.mem_cons_of_mem _ (List.mem_singleton_self _)) ?_)
    rw [ht]
    simp only [Option.map_some, reqPat, KoreAML.varsOf]
    exact List.mem_append_left _ (List.mem_append_right _ (varsOf_kore c _ t hit))

/-- The binders of a clause's exclusion are variables of a negated disjunction holding it. -/
theorem varsOf_not_exclPre {fn : Fn} {cls : List Clause} {cl : Clause} (hcl : cl ∈ cls) {i : Nat}
    (hi : i < cl.vars.length) (hil : i ∈ cl.leftVars) :
    canonKey c cl.vars i ∈ KoreAML.varsOf (.not KoreAML.R (KoreAML.anyOf
      (cls.map fun cl => exclusion c fn cl (canonClausePres cl)))) := by
  simp only [KoreAML.varsOf]
  rw [anyOf_eq]
  exact List.mem_append_right _ (mem_varsOf_anyOfC (List.mem_map.mpr ⟨cl, hcl, rfl⟩) (varsOf_exclusionCl hi hil))

/-- The variables of a clause's predicate at `R` are variables of a negated disjunction holding its
exclusion, where the predicate is not `\top`. -/
theorem varsOf_not_excl_prePre {fn : Fn} {cls : List Clause} {cl : Clause} (hcl : cl ∈ cls)
    (hpt : cl.pre.isTop = false) {k : KoreAML.VarKey}
    (hk : k ∈ KoreAML.varsOf (Cond.kore c (canonVars c cl.vars) KoreAML.R cl.pre)) :
    k ∈ KoreAML.varsOf (.not KoreAML.R (KoreAML.anyOf
      (cls.map fun cl => exclusion c fn cl (canonClausePres cl)))) := by
  simp only [KoreAML.varsOf]
  rw [anyOf_eq]
  exact List.mem_append_right _ (mem_varsOf_anyOfC (List.mem_map.mpr ⟨cl, hcl, rfl⟩) (varsOf_exclusion_preCl hpt hk))

namespace AtT

variable {T : GroundTerm → GroundTerm → Prop}

/-! ## A clause's exclusion -/

/-- **A clause's exclusion holds where the clause applies with its predicate true**: at a
valuation giving the formal arguments the values `w̄`, through a table holding the keys of the
variables of the clause's patterns and conditions and those of its predicate at `R`, the exclusion
`∃ȳ. ⌈req = true⌉ ∧ X̄ ∈ p̄ ∧ pre` holds where, under a substitution well sorted on those
variables, the patterns match `w̄`, the `requires` is `true` and the predicate is true. -/
theorem exclusion_ofPre (h : HypModelCore c) {fn : Fn} (hfn : fn ∈ c.allFns) {cl : Clause}
    (F : ExclFactsPre c fn cl)
    {tbl : KoreAML.VarTable} (hkeys : ∀ i < cl.vars.length, i ∈ cl.leftVars → canonKey c cl.vars i ∈ tbl)
    (hpkeys : cl.pre.isTop = false →
      ∀ k ∈ KoreAML.varsOf (Cond.kore c (canonVars c cl.vars) KoreAML.R cl.pre), k ∈ tbl)
    (hRkey : KoreAML.VarKey.sortVar "R" ∈ tbl)
    (hXkeys : ∀ (j : Nat) (s : String), (fn.args.map c.sortName)[j]? = some s →
      KoreAML.VarKey.evar ("X" ++ toString j) (KoreAML.srt s) ∈ tbl)
    {e : Valuation Elem} (hRs : KoreAML.IsSort (stdI_T c T) (e.evalEvar (tbl.ev (.sortVar "R"))))
    {ws : List GroundTerm} (hX : ArgsAt c tbl e fn.args ws) {a : Elem}
    (ha : KoreAML.Inh (stdI_T c T) (e.evalEvar (tbl.ev (.sortVar "R"))) a)
    {σ : Subst} (hσ : c.WellSortedAt cl.vars cl.leftVars σ) (hpv : PatVals c σ cl.pats ws)
    (hq : ∀ t, cl.req = some t → EvalTerm c σ t (some (bool true)))
    (hpre : Holds c cl.vars.length σ cl.pre true) :
    (KoreAML.tr ⟨tbl, []⟩ (exclusion c fn cl (canonClausePres cl))).interpret (stdI_T c T) e a := by
  have hn := h.namesK
  obtain ⟨L, hL, hreqs⟩ := F.req
  have hpats := F.pats
  have hnum := leftVars_numPre h hfn F
  have hlen : cl.pats.length = fn.args.length := sortsOfTerms_length hpats
  let vs := canonVars c cl.vars
  let n := cl.vars.length
  let l := (List.range n).filter cl.leftVars.contains
  have hl : ∀ i ∈ l, i < n := fun i hi => List.mem_range.mp (List.mem_filter.mp hi).1
  have hlm : ∀ i ∈ l, i ∈ cl.leftVars := fun i hi => by simpa using (List.mem_filter.mp hi).2
  have hml : ∀ i < n, i ∈ cl.leftVars → i ∈ l := fun i hi hil =>
    List.mem_filter.mpr ⟨List.mem_range.mpr hi, by simpa using hil⟩
  have hnd : (((l.map (vs.getD · default)).map KoreAML.Var.kore).map fun b => tbl.ev (KoreAML.evarKey b)).Nodup := by
    rw [List.map_map, List.map_map]
    refine nodup_map_of_injOn _ (fun i hi j hj he => ?_) (List.nodup_range.filter _)
    exact canonKey_inj (hl i hi) (hl j hj) (ev_inj (hkeys i (hl i hi) (hlm i hi)) (hkeys j (hl j hj) (hlm j hj)) he)
  have hsrt : ∀ b ∈ (l.map (vs.getD · default)).map KoreAML.Var.kore, ∃ n, b.sort = KoreAML.srt n := fun b hb => by
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hb
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hv
    show ∃ n, ((canonVars c cl.vars).getD i default).kore.sort = KoreAML.srt n
    rw [canonVars_getD c (hl i hi)]; exact ⟨_, rfl⟩
  let P : Nat → Prop := fun i => i < n ∧ i ∈ cl.leftVars
  have hpatOK : ∀ p ∈ cl.pats, PatOK c P p := fun p hp =>
    (patOKs_of_sorted h (h.ovlOKI.nfs_bridge hpats) p hp).monoOpen fun i hi =>
      ⟨varOccsList_lt cl.pats hpats i (varOccsList_of_memOpen hp hi), List.mem_append_left _ (varOccsList_of_memOpen hp hi)⟩
  have hreqOK : ∀ t, cl.req = some t → TermOK c P t := fun t ht =>
    (termOK_of_sorted h hL (hreqs t ht)).monoOpen fun i hi =>
      ⟨varOccs_lt t (hreqs t ht) i hi, Clause.req_leftVars ht i hi⟩
  have hRne : ∀ i < n, KoreAML.VarKey.sortVar "R" ≠ canonKey c cl.vars i := fun i hi he => by
    rw [canonKey_eq c hi] at he; cases he
  rw [exclusion_canon_mapPre]
  have hσv : ∀ i < n, i ∈ cl.leftVars → ∃ w, σ.lookup i = some w ∧ c.sortOf w = some (cl.vars.getD i 0) :=
    fun i hi hil => hσ i hil _ (by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; rfl)
  let f : Nat → Elem := fun j => .val ((σ.lookup j).getD default)
  let e' := setV c tbl cl.vars cl.leftVars f e
  have hoff : ∀ k, k ∈ tbl → (∀ i < n, k ≠ canonKey c cl.vars i) → e'.evalEvar (tbl.ev k) = e.evalEvar (tbl.ev k) :=
    fun k hk hne => by
      show (if h : _ then _ else _) = _
      rw [dif_neg]
      rintro ⟨i, hi, hil, he⟩
      exact hne i hi (ev_inj hk (hkeys i hi hil) he)
  have hon : ∀ i < n, i ∈ cl.leftVars → ∃ w, σ.lookup i = some w ∧ c.sortOf w = some (cl.vars.getD i 0) ∧
      e'.evalEvar (tbl.ev (canonKey c cl.vars i)) = .val w := fun i hi hil => by
    obtain ⟨w, hw, hws⟩ := hσv i hi hil
    refine ⟨w, hw, hws, ?_⟩
    show (setV c tbl cl.vars cl.leftVars f e).evalEvar (tbl.ev (canonKey c cl.vars i)) = _
    rw [setV_on hkeys hi hil]
    simp [f, hw]
  have hvar : ∀ i, P i → ∀ m, (KoreAML.tr ⟨tbl, []⟩ (KoreAML.varAt vs i)).interpret (stdI_T c T) e' m ↔
      ∃ v, σ.lookup i = some v ∧ m = .val v := by
    rintro i ⟨hi, hil⟩ m
    rw [var_read]
    show m = e'.evalEvar (tbl.ev (canonKey c cl.vars i)) ↔ _
    obtain ⟨w, hw, -, he⟩ := hon i hi hil
    rw [he, hw]
    simp
  have he'R : e'.evalEvar (tbl.ev (.sortVar "R")) = e.evalEvar (tbl.ev (.sortVar "R")) := hoff _ hRkey hRne
  have hX' : ArgsAt c tbl e' fn.args ws := ⟨hX.sorts, hX.num, fun j w s hw hs => by
    rw [hoff _ (hXkeys j s hs) (fun i hi => canonKey_ne_X' hi _ _)]; exact hX.X j w s hw hs⟩
  refine existsAll_intro _ e e' _ hnd hsrt (fun z hz => ?_) rfl (fun b hb k hk => ?_) ?_
  · show (if h : _ then _ else _) = _
    rw [dif_neg]
    rintro ⟨i, hi, hil, rfl⟩
    exact hz _ (List.mem_map_of_mem (List.mem_map_of_mem (hml i hi hil))) rfl
  · obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hb
    obtain ⟨i, hil, rfl⟩ := List.mem_map.mp hv
    have hs' : ((canonVars c cl.vars).getD i default).kore.sort = KoreAML.srt (c.sortName (cl.vars.getD i 0)) := by
      rw [canonVars_getD c (hl i hil)]; rfl
    change ((canonVars c cl.vars).getD i default).kore.sort = KoreAML.srt k at hk
    rw [hs'] at hk
    rw [← srt_inj hk]
    show InS (stdI_T c T) _ (e'.evalEvar (tbl.ev (canonKey c cl.vars i)))
    obtain ⟨w, -, hws, he⟩ := hon i (hl i hil) (hlm i hil)
    rw [he]
    exact (inhOf_sort hn (hnum i (hl i hil) (hlm i hil)) KoreAML.val0 _).mpr hws
  · have hprem := (AtT.premise_iffCl h (R_read e') (by rw [he'R]; exact hRs) hvar hreqOK hpatOK hlen hX' a).mpr
      ⟨by rw [he'R]; exact ha, hq, hpv⟩
    cases hpt : cl.pre.isTop with
    | true => rw [withPre_isTop hpt]; exact hprem
    | false =>
      refine (HoldsShape.withPre_interp hpt).mpr ⟨hprem, ?_⟩
      have hr : ReadsT c cl.vars P σ tbl e' := fun i ⟨hi, hil⟩ => ⟨hi, hkeys i hi hil, hon i hi hil⟩
      exact (holdsT_atR h cl.pre F.preOK F.bound (fun i hi hlt => ⟨hlt, Clause.pre_leftVarsRH i hi⟩) hr
        (hpkeys hpt) hRkey (by rw [he'R]; exact hRs) hpre a (by rw [he'R]; exact ha)).mpr rfl

/-- **Where a negated disjunction of exclusions holds, none of their clauses applies with its
predicate true**: under no substitution well sorted on a clause's patterns' and conditions'
variables do its patterns match, its `requires` evaluate to `true` and its predicate hold. -/
theorem fails_of_not_exclPre (h : HypModelCore c) {fn : Fn} (hfn : fn ∈ c.allFns) {cls : List Clause}
    (hF : ∀ cl ∈ cls, ExclFactsPre c fn cl)
    {tbl : KoreAML.VarTable} {e : Valuation Elem} {ws : List GroundTerm} (hEqR : KoreAML.VarKey.sortVar "R" ∈ tbl)
    (hXk : ∀ (j : Nat) (s : String), (fn.args.map c.sortName)[j]? = some s →
      KoreAML.VarKey.evar ("X" ++ toString j) (KoreAML.srt s) ∈ tbl)
    (hRs : KoreAML.IsSort (stdI_T c T) (e.evalEvar (tbl.ev (.sortVar "R")))) (hX : ArgsAt c tbl e fn.args ws)
    (hkeys : ∀ cl ∈ cls, ∀ i < cl.vars.length, i ∈ cl.leftVars → canonKey c cl.vars i ∈ tbl)
    (hpkeys : ∀ cl ∈ cls, cl.pre.isTop = false →
      ∀ k ∈ KoreAML.varsOf (Cond.kore c (canonVars c cl.vars) KoreAML.R cl.pre), k ∈ tbl) {a : Elem}
    (hnot : (KoreAML.tr ⟨tbl, []⟩ (.not KoreAML.R (KoreAML.anyOf
      (cls.map fun cl => exclusion c fn cl (canonClausePres cl))))).interpret (stdI_T c T) e a) :
    KoreAML.Inh (stdI_T c T) (e.evalEvar (tbl.ev (.sortVar "R"))) a ∧ ∀ cl ∈ cls, ∀ σ,
      ¬ (c.WellSortedAt cl.vars cl.leftVars σ ∧ PatVals c σ cl.pats ws ∧
        (∀ t, cl.req = some t → EvalTerm c σ t (some (bool true))) ∧ Holds c cl.vars.length σ cl.pre true) := by
  rw [KoreAML.tr, KoreAML.interp_sNot, anyOf_eq, anyOfC_iff (R_read e) isFree_R, KoreAML.interp_inhOf_of (R_read e)]
    at hnot
  obtain ⟨hn1, hi⟩ := hnot
  refine ⟨hi, fun cl hcl σ ⟨hw, hp, hq, hpre⟩ => hn1 ⟨hi, _, List.mem_map.mpr ⟨cl, hcl, rfl⟩, ?_⟩⟩
  exact exclusion_ofPre h hfn (hF cl hcl) (hkeys cl hcl) (hpkeys cl hcl) hEqR hXk hRs hX hi hw hp hq hpre

/-! ## A clause's premise with its predicate -/

/-- **A clause's premise with its predicate, read at the valuation of an equation**: where it
holds, the substitution the valuation gives is well sorted, the patterns match the arguments, the
`requires` is `true`, and the predicate is true, provided the predicate has a truth value at such a
match (`hdec`). -/
theorem withPre_readPre (h : HypModelCore c) {fn : Fn} {cl : Clause} (F : EqnFactsPre c fn cl)
    (hdec : ∀ σ ws, c.WellSorted cl.vars σ → PatVals c σ cl.pats ws →
      (∀ t, cl.req = some t → EvalTerm c σ t (some (bool true))) → ∃ b, Holds c cl.vars.length σ cl.pre b)
    {tbl : KoreAML.VarTable} {e : Valuation Elem} {ws : List GroundTerm} {a : Elem}
    (hEq : EqnAt c T fn cl.vars tbl e ws)
    (hvT : ∀ k ∈ KoreAML.varsOf (withPre c (canonVars c cl.vars) cl (clausePrem c fn cl)), k ∈ tbl)
    (ha : KoreAML.Inh (stdI_T c T) (e.evalEvar (tbl.ev (.sortVar "R"))) a)
    (hprem : (KoreAML.tr ⟨tbl, []⟩ (withPre c (canonVars c cl.vars) cl (clausePrem c fn cl))).interpret
      (stdI_T c T) e a) :
    c.WellSorted cl.vars (substE c tbl cl.vars e) ∧ PatVals c (substE c tbl cl.vars e) cl.pats ws ∧
      (∀ t, cl.req = some t → EvalTerm c (substE c tbl cl.vars e) t (some (bool true))) ∧
      Holds c cl.vars.length (substE c tbl cl.vars e) cl.pre true := by
  obtain ⟨L, hL, hreqs⟩ := F.req
  have hlen : cl.pats.length = fn.args.length := sortsOfTerms_length F.pats
  obtain ⟨hσ, hvar⟩ := substE_ok (T := T) hEq.vin
  have hsplit : (KoreAML.tr ⟨tbl, []⟩ (clausePrem c fn cl)).interpret (stdI_T c T) e a ∧
      (cl.pre.isTop = false →
        (KoreAML.tr ⟨tbl, []⟩ (Cond.kore c (canonVars c cl.vars) KoreAML.R cl.pre)).interpret (stdI_T c T) e a) := by
    cases hpt : cl.pre.isTop with
    | true => rw [withPre_isTop hpt] at hprem; exact ⟨hprem, fun h' => Bool.noConfusion h'⟩
    | false => exact ⟨((HoldsShape.withPre_interp hpt).mp hprem).1, fun _ => ((HoldsShape.withPre_interp hpt).mp hprem).2⟩
  obtain ⟨-, hq, hpv⟩ := (premise_iff h (R_read e) hEq.Rs hvar (fun t ht => termOK_of_sorted h hL (hreqs t ht))
    (patOKs_of_sorted h (h.ovlOKI.nfs_bridge F.pats)) hlen hEq.args a).mp hsplit.1
  refine ⟨hσ, hpv, hq, ?_⟩
  cases hpt : cl.pre.isTop with
  | true => exact Clause.holds_preTop (Cond.eq_top_of_isTop hpt) _
  | false =>
    obtain ⟨b, hb⟩ := hdec _ ws hσ hpv hq
    have hr : ReadsT c cl.vars (· < cl.vars.length) (substE c tbl cl.vars e) tbl e := fun i hi => by
      obtain ⟨v, he, hsv⟩ := inSort_val (hEq.vin i hi)
      exact ⟨hi, hEq.Vk i hi, v, by rw [substE_lookup hi, he]; rfl, hsv, he⟩
    have hbt := (holdsT_atR h cl.pre F.preOK F.bound (fun i _ hlt => hlt) hr
      (fun k hk => hvT k (HoldsShape.varsOf_withPre_pre hpt hk)) hEq.R hEq.Rs hb a ha).mp (hsplit.2 hpt)
    rw [hbt] at hb
    exact hb

/-! ## The two kinds of equation -/

/-- **The equation of a clause with a predicate and no competitor holds**, where its applying gives
the function's values (`hsolve`) and its predicate has a truth value where it matches (`hdec`). -/
theorem sat_clauseEqPre (h : HypModelCore c) {fn : Fn} (hfn : fn ∈ c.allFns) {cl : Clause}
    (F : EqnFactsPre c fn cl)
    (hdec : ∀ σ ws, c.WellSorted cl.vars σ → PatVals c σ cl.pats ws →
      (∀ t, cl.req = some t → EvalTerm c σ t (some (bool true))) → ∃ b, Holds c cl.vars.length σ cl.pre b)
    (hsolve : ∀ σ ws, c.sortsOf ws = some fn.args → cl.AppliesAt c σ ws →
      ∀ v, Eval c fn.label ws (some v) ↔
        EvalTerm c σ cl.rhs (some v) ∧ ∀ t, cl.ens = some t → EvalTerm c σ t (some (bool true))) :
    stdI_T c T ⊧ᴵ (KoreAML.trAxiom [] [] ⟨0, "kernel", (⟨[KoreAML.Rv], .implies KoreAML.R
      (withPre c (canonVars c cl.vars) cl (clausePrem c fn cl))
      (fnConcl c fn (Term.kore c (canonVars c cl.vars) cl.rhs)
        (reqPat (srtOf c fn.result) (cl.ens.map (Term.kore c (canonVars c cl.vars))))), []⟩ : Kore.Axiom)⟩).pat := by
  obtain ⟨L, hL, hrhs, hens⟩ := F.concl
  have hlen : cl.pats.length = fn.args.length := sortsOfTerms_length F.pats
  refine sat_eqnCl h hfn (vars_numPre h hfn F) (termOK_of_sorted h hL hrhs)
    (fun t ht => termOK_of_sorted h hL (hens t ht))
    (clause_keys_freePre hlen F.occ fun _ hk => hk) (clause_keys_varsPre hlen F.occ fun _ hk => hk)
    fun tbl e ws a hEq hvT ha hprem => ?_
  obtain ⟨hσ, hpv, hq, hpre⟩ := withPre_readPre h F hdec hEq hvT ha hprem
  exact hsolve _ ws hEq.args.sorts ⟨hσ.at _, hpv, hq, hpre⟩

/-- **The equation of a clause with a predicate under the negation of its competitors holds**:
where they all fail with their predicates (`fails_of_not_exclPre`) and it applies, its applying
gives the function's values (`hsolve`); its predicate has a truth value where it matches
(`hdec`). -/
theorem sat_competingEqPre (h : HypModelCore c) {fn : Fn} (hfn : fn ∈ c.allFns) {cl : Clause}
    (F : EqnFactsPre c fn cl)
    (hdec : ∀ σ ws, c.WellSorted cl.vars σ → PatVals c σ cl.pats ws →
      (∀ t, cl.req = some t → EvalTerm c σ t (some (bool true))) → ∃ b, Holds c cl.vars.length σ cl.pre b)
    {others : List Clause} (hF : ∀ cl' ∈ others, ExclFactsPre c fn cl')
    (hsolve : ∀ σ ws, c.sortsOf ws = some fn.args → cl.AppliesAt c σ ws →
      (∀ cl' ∈ others, ∀ σ', c.WellSortedAt cl'.vars cl'.leftVars σ' → PatVals c σ' cl'.pats ws →
        ¬ ((∀ t, cl'.req = some t → EvalTerm c σ' t (some (bool true))) ∧
           Holds c cl'.vars.length σ' cl'.pre true)) →
      ∀ v, Eval c fn.label ws (some v) ↔
        EvalTerm c σ cl.rhs (some v) ∧ ∀ t, cl.ens = some t → EvalTerm c σ t (some (bool true))) :
    stdI_T c T ⊧ᴵ (KoreAML.trAxiom [] [] ⟨0, "kernel", (⟨[KoreAML.Rv], .implies KoreAML.R
      (.and KoreAML.R [.not KoreAML.R (KoreAML.anyOf (others.map fun cl' => exclusion c fn cl' (canonClausePres cl'))),
        withPre c (canonVars c cl.vars) cl (clausePrem c fn cl)])
      (fnConcl c fn (Term.kore c (canonVars c cl.vars) cl.rhs)
        (reqPat (srtOf c fn.result) (cl.ens.map (Term.kore c (canonVars c cl.vars))))), []⟩ : Kore.Axiom)⟩).pat := by
  obtain ⟨L, hL, hrhs, hens⟩ := F.concl
  have hlen : cl.pats.length = fn.args.length := sortsOfTerms_length F.pats
  refine sat_eqnCl h hfn (vars_numPre h hfn F) (termOK_of_sorted h hL hrhs)
    (fun t ht => termOK_of_sorted h hL (hens t ht))
    (clause_keys_freePre hlen F.occ fun _ hk =>
      freeOf_and_memOpen (List.mem_cons_of_mem _ (List.mem_singleton_self _)) hk)
    (clause_keys_varsPre hlen F.occ fun _ hk => varsOf_and_mem (List.mem_cons_of_mem _ (List.mem_singleton_self _)) hk)
    fun tbl e ws a hEq hvT ha hprem => ?_
  rw [tr_and2, KoreAML.interp_sAnd] at hprem
  obtain ⟨hnot, hp⟩ := hprem
  have hvW : ∀ k ∈ KoreAML.varsOf (withPre c (canonVars c cl.vars) cl (clausePrem c fn cl)), k ∈ tbl :=
    fun k hk => hvT k (varsOf_and_mem (List.mem_cons_of_mem _ (List.mem_singleton_self _)) hk)
  have hvN : ∀ k ∈ KoreAML.varsOf (.not KoreAML.R (KoreAML.anyOf
      (others.map fun cl' => exclusion c fn cl' (canonClausePres cl')))), k ∈ tbl :=
    fun k hk => hvT k (varsOf_and_mem (List.mem_cons_self ..) hk)
  obtain ⟨hσ, hpv, hq, hpre⟩ := withPre_readPre h F hdec hEq hvW ha hp
  obtain ⟨-, hfails⟩ := fails_of_not_exclPre (T := T) h hfn hF hEq.R hEq.Xk hEq.Rs hEq.args
    (fun cl' hcl' i hi hil => hvN _ (varsOf_not_exclPre hcl' hi hil))
    (fun cl' hcl' hpt k hk => hvN _ (varsOf_not_excl_prePre hcl' hpt hk)) hnot
  exact hsolve _ ws hEq.args.sorts ⟨hσ.at _, hpv, hq, hpre⟩ fun cl' hcl' σ' hw hp' hqh =>
    hfails cl' hcl' σ' ⟨hw, hp', hqh.1, hqh.2⟩

end AtT

/-! ## The functions' axioms -/

/-- **What `HypModelCore` gives of a clause without existential variables of a function of the
semantics**, without reading its predicate as `\top`, where the predicate is well sorted: the
user's clauses by `sortedOKClEx` (`clauseSortedOpen`, and `clausePlainOpenEx` for `post`), a sort
predicate's by its text. -/
theorem clause_eqnFactsPre (h : HypModelCore c) {fn : Fn} (hfn : fn ∈ c.allFns) {cl : Clause}
    (hcl : cl ∈ fn.clauses) (hex : cl.exs = []) (hpreOK : c.condOK cl.vars cl.pre = true) : EqnFactsPre c fn cl := by
  rcases List.mem_append.mp hfn with hu | hp
  · obtain ⟨-, hfns, -, -, -⟩ := Semantics.sortedOKClEx_parts h.hyp.1
    obtain ⟨hs, hpl⟩ := hfns fn hu cl hcl
    have hbd : Cond.bound c cl.vars.length cl.pre = true := by
      simp only [Semantics.clauseSortedOpen, Bool.and_eq_true] at hs; exact hs.1.2.1
    obtain ⟨hpats, hocc, hreq, hrhs, hens⟩ := Semantics.clauseSortedOpen_parts hs
    have hpost := (Semantics.clausePlainOpenEx_parts hpl).2.1 hex
    refine ⟨⟨hpats, ⟨c.fns.map Fn.sig, fun k hk => ?_, hreq⟩, hpreOK, hbd⟩, hex, fun i hi => ?_,
      ⟨c.fns.map Fn.sig, fun k hk => ?_, hrhs, hens⟩⟩
    · obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hk
      exact ⟨g, List.mem_append_left _ hg, rfl⟩
    · have h1 := hocc i hi
      simp only [Clause.condVars, List.mem_append] at h1
      rcases h1 with ((((h1 | h1 | h1) | h1) | h1) | h1)
      · exact Or.inl h1
      · cases ht : cl.req with
        | none => rw [ht] at h1; cases h1
        | some t => rw [ht] at h1; exact Or.inr (Or.inl ⟨t, rfl, h1⟩)
      · exact Or.inr (Or.inr (Or.inl h1))
      · exact Or.inr (Or.inr (Or.inr (Or.inl h1)))
      · cases ht : cl.ens with
        | none => rw [ht] at h1; cases h1
        | some t => rw [ht] at h1; exact Or.inr (Or.inr (Or.inr (Or.inr ⟨t, rfl, h1⟩)))
      · rw [hpost] at h1; simp [varOccsCond] at h1
    · obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hk
      exact ⟨g, List.mem_append_left _ hg, rfl⟩
  · obtain ⟨hpats, -, hb, hreq, hrhs, hens⟩ := sortPreds_ctx hp cl hcl
    have hpre := Semantics.sortPreds_pre hp cl hcl
    refine ⟨⟨sortsOfTerms_heads c.patCtx (c.collPatSigs ++ c.ovlSigs) cl.vars cl.pats hpats,
      ⟨[], fun k hk => absurd hk List.not_mem_nil, fun t ht => ?_⟩, hpreOK, by rw [hpre]; rfl⟩,
      Semantics.sortPreds_exs hp cl hcl, fun i hi => ?_, ⟨[], fun k hk => absurd hk List.not_mem_nil, hrhs, fun t ht => ?_⟩⟩
    · rw [ht] at hreq
      simpa [reqOK] using hreq
    · simp only [binds, List.all_eq_true, List.mem_range, List.contains_iff_mem] at hb
      exact Or.inl (hb i hi)
    · rw [ht] at hens
      simpa [reqOK] using hens

namespace AtT

variable {T : GroundTerm → GroundTerm → Prop}

/-- **The value model satisfies the functions' equations with their predicates**, where each
clause of a function of the definition has a well-sorted predicate with a truth value wherever its
patterns match and its `requires` is `true`. -/
theorem satFnsGoalPre (h : HypModelCore c) (hne : c.FnsNoExs)
    (hpreOK : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, c.condOK cl.vars cl.pre = true)
    (hdec : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, ∀ σ ws, c.WellSorted cl.vars σ → PatVals c σ cl.pats ws →
      (∀ t, cl.req = some t → EvalTerm c σ t (some (bool true))) → ∃ b, Holds c cl.vars.length σ cl.pre b) :
    (stdI_T c T ⊧ᴵP ΓFns c) := by
  have hokA : ∀ fn ∈ c.allFns, ∀ cl ∈ fn.clauses, c.condOK cl.vars cl.pre = true := fun fn hfn cl hcl => by
    rcases List.mem_append.mp hfn with hu | hp
    · exact hpreOK fn hu cl hcl
    · rw [Semantics.sortPreds_pre hp cl hcl]; rfl
  have hdecA : ∀ fn ∈ c.allFns, ∀ cl ∈ fn.clauses, ∀ σ ws, c.WellSorted cl.vars σ → PatVals c σ cl.pats ws →
      (∀ t, cl.req = some t → EvalTerm c σ t (some (bool true))) → ∃ b, Holds c cl.vars.length σ cl.pre b :=
    fun fn hfn cl hcl σ ws hσ hpv hq => by
      rcases List.mem_append.mp hfn with hu | hp
      · exact hdec fn hu cl hcl σ ws hσ hpv hq
      · exact ⟨true, Clause.holds_preTop (Semantics.sortPreds_pre hp cl hcl) σ⟩
  refine sat_itemsPremises c fun it hit => ?_
  obtain ⟨fn, hfn, hit⟩ := List.mem_flatMap.mp hit
  obtain ⟨s, hs, hit⟩ := List.mem_filterMap.mp hit
  unfold fnEquationsK at hs
  obtain ⟨cl, hcl, rfl⟩ := List.mem_map.mp hs
  have hexA := hne.allFns
  have F := clause_eqnFactsPre h hfn hcl (hexA fn hfn cl hcl) (hokA fn hfn cl hcl)
  by_cases hlow : (lowerClauses fn cl).isEmpty = true
  · rw [show prioEquation c fn cl = clauseEquation c fn cl from if_pos hlow] at hit
    refine sat_kernelItem_of hit (clauseEquation_nilPre F.exs)
      (sat_clauseEqPre h hfn F (hdecA fn hfn cl hcl) fun σ ws hws happ => ?_)
    refine eval_of_decides h hfn hcl (hexA fn hfn cl hcl) hws ⟨happ, fun cl' hcl' hna hlt => ?_⟩
    have : cl' ∈ lowerClauses fn cl := by simp [lowerClauses, hcl', hna, hlt]
    rw [List.isEmpty_iff.mp hlow] at this
    exact absurd this List.not_mem_nil
  · rw [show prioEquation c fn cl = competingEquation c fn (lowerClauses fn cl) cl from if_neg hlow] at hit
    have hdl : ∀ cl' ∈ lowerClauses fn cl, cl' ∈ fn.clauses := fun cl' h' => (List.mem_filter.mp h').1
    refine sat_kernelItem_of hit (competingEquation_nilPre F.exs)
      (sat_competingEqPre h hfn F (hdecA fn hfn cl hcl)
        (fun cl' hcl' => (clause_eqnFactsPre h hfn (hdl cl' hcl') (hexA fn hfn cl' (hdl cl' hcl')) (hokA fn hfn cl' (hdl cl' hcl'))).toExclFactsPre)
        fun σ ws hws happ hfails => ?_)
    exact eval_of_decides h hfn hcl (hexA fn hfn cl hcl) hws ⟨happ, fun cl' hcl' hna hlt σ' hw hp' =>
      hfails cl' (List.mem_filter.mpr ⟨hcl', by simp [hna, hlt]⟩) σ' hw hp'⟩

end AtT

/-- **`SatFnsGoal` with the clauses' predicates**: `AtT.satFnsGoalPre` in the value model. -/
theorem satFnsGoalPre (h : HypModelCore c) (hne : c.FnsNoExs)
    (hpreOK : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, c.condOK cl.vars cl.pre = true)
    (hdec : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, ∀ σ ws, c.WellSorted cl.vars σ → PatVals c σ cl.pats ws →
      (∀ t, cl.req = some t → EvalTerm c σ t (some (bool true))) → ∃ b, Holds c cl.vars.length σ cl.pre b) :
    SatFnsGoal c :=
  AtT.satFnsGoalPre (c := c) (T := StepM c) h hne hpreOK hdec

end Model

end Faithful

end KCore
