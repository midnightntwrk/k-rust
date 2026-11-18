/-
  KCore. The value model satisfies the functions' equations (`satFnsGoal`), for a semantics whose
  clauses are asked CN-4's bodies (`sortedOKCl`, which `HypModelCore` carries): a clause's
  patterns need not bind every variable, each variable occurs in the clause.

  A clause's equation is read at a valuation that gives each formal argument a value and each
  variable of the clause an element of its sort: each variable is free in the axiom, in its
  premise (a variable of the patterns or the `requires`) or in its conclusion (one of the right
  side or the `ensures`) (`clause_keys_freeCl`), and the value model's elements of a sort are its
  values. So the valuation is a substitution well sorted on every variable, and where the premise
  holds the clause decides (`eval_of_decides`). Where a variable's sort has no value there is no
  such valuation and the equation holds vacuously, as the clause never applies.

  A clause of a smaller priority is negated by its exclusion, which binds the variables of its
  patterns and conditions only (`exclusion_canon_mapCl`); it holds exactly where the clause
  matches under a substitution well sorted on those variables and its `requires` is `true`
  (`exclusion_iffCl`), which is what `Clause.DecidesAt` asks to fail.
-/
import KcoreSpec.OpenClauseEval
import KcoreSpec.OpenModel

set_option autoImplicit false

namespace KCore

namespace Faithful

namespace Model

open ML

variable {c : Semantics}

/-- **What `sortedOKCl` says of a clause** of a function of the semantics (the user's or a sort
predicate's): its patterns have the argument sorts, each variable occurs in its patterns, its
`requires`, its right side or its `ensures`, and its `requires`, right side and `ensures` are
sorted over some functions' signatures `L`. -/
theorem clause_factsCl (h : HypModelCore c) {fn : Fn} (hfn : fn ∈ c.allFns) {cl : Clause} (hcl : cl ∈ fn.clauses) :
    sortsOfTerms c.patCtxAll cl.vars cl.pats = some fn.args ∧
      (∀ i < cl.vars.length, i ∈ varOccsList cl.pats ∨ (∃ t, cl.req = some t ∧ i ∈ varOccs t) ∨
        i ∈ varOccs cl.rhs ∨ ∃ t, cl.ens = some t ∧ i ∈ varOccs t) ∧
      ∃ L, HeadsOK c L ∧ (∀ t, cl.req = some t → sortOfTerm (c.rhsCtx L) cl.vars t = some Srt.bool) ∧
        sortOfTerm (c.rhsCtx L) cl.vars cl.rhs = some fn.result ∧
        (∀ t, cl.ens = some t → sortOfTerm (c.rhsCtx L) cl.vars t = some Srt.bool) := by
  rcases List.mem_append.mp hfn with hu | hp
  · obtain ⟨-, hfns, -, -, -⟩ := Semantics.sortedOKCl_parts h.hyp.1
    obtain ⟨hs, hpl⟩ := hfns fn hu cl hcl
    obtain ⟨hpats, hocc, hreq, hrhs, hens⟩ := Semantics.clauseSortedOpen_parts hs
    obtain ⟨-, hpre, hpost, -⟩ := Semantics.clausePlainOpen_parts hpl
    refine ⟨hpats, fun i hi => ?_, c.fns.map Fn.sig, fun k hk => ?_, hreq, hrhs, hens⟩
    · have h1 := hocc i hi
      simp only [List.mem_append] at h1
      rcases h1 with (((h1 | h1) | h1) | h1) | h1
      · exact Or.inl h1
      · rw [Clause.condVars_of_top hpre] at h1
        cases ht : cl.req with
        | none => rw [ht] at h1; cases h1
        | some t => rw [ht] at h1; exact Or.inr (Or.inl ⟨t, rfl, h1⟩)
      · exact Or.inr (Or.inr (Or.inl h1))
      · cases ht : cl.ens with
        | none => rw [ht] at h1; cases h1
        | some t => rw [ht] at h1; exact Or.inr (Or.inr (Or.inr ⟨t, rfl, h1⟩))
      · rw [hpost] at h1; simp [varOccsCond] at h1
    · obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hk
      exact ⟨g, List.mem_append_left _ hg, rfl⟩
  · obtain ⟨hpats, -, hb, hreq, hrhs, hens⟩ := sortPreds_ctx hp cl hcl
    refine ⟨sortsOfTerms_heads c.patCtx (c.collPatSigs ++ c.ovlSigs) cl.vars cl.pats hpats, fun i hi => ?_, [],
      fun k hk => absurd hk List.not_mem_nil, fun t ht => ?_, hrhs, fun t ht => ?_⟩
    · simp only [binds, List.all_eq_true, List.mem_range, List.contains_iff_mem] at hb
      exact Or.inl (hb i hi)
    · rw [ht] at hreq
      simpa [reqOK] using hreq
    · rw [ht] at hens
      simpa [reqOK] using hens

/-- A clause of a function of the semantics (the user's or a sort predicate's) has the premise
predicate `\top`: the user's by `sortedOKCl` (`clausePlainOpen`), a sort predicate's by its text. -/
theorem clause_preCl (h : HypModelCore c) {fn : Fn} (hfn : fn ∈ c.allFns) {cl : Clause} (hcl : cl ∈ fn.clauses) :
    cl.pre = .top := by
  rcases List.mem_append.mp hfn with hu | hp
  · obtain ⟨-, hfns, -, -, -⟩ := Semantics.sortedOKCl_parts h.hyp.1
    exact (Semantics.clausePlainOpen_parts (hfns fn hu cl hcl).2).2.1
  · exact Semantics.sortPreds_pre hp cl hcl

/-- A clause of a function of the semantics (the user's or a sort predicate's) has no existential
variable: the user's by `sortedOKCl` (`clausePlainOpen`), a sort predicate's by its text. -/
theorem clause_exsCl (h : HypModelCore c) {fn : Fn} (hfn : fn ∈ c.allFns) {cl : Clause} (hcl : cl ∈ fn.clauses) :
    cl.exs = [] := by
  rcases List.mem_append.mp hfn with hu | hp
  · obtain ⟨-, hfns, -, -, -⟩ := Semantics.sortedOKCl_parts h.hyp.1
    exact (Semantics.clausePlainOpen_parts (hfns fn hu cl hcl).2).1
  · exact Semantics.sortPreds_exs hp cl hcl

/-- A clause's variables have numbered sorts: each occurs in its patterns, of the function's
argument sorts, or in its `requires`, right side or `ensures`, of numbered sorts. -/
theorem clause_vars_num (h : HypModelCore c) {fn : Fn} (hfn : fn ∈ c.allFns) {cl : Clause} (hcl : cl ∈ fn.clauses) :
    ∀ i < cl.vars.length, cl.vars.getD i 0 < nRegSorts + c.sortNames.length := by
  obtain ⟨hpats, hocc, L, hL, hreqs, hrhs, hens⟩ := clause_factsCl h hfn hcl
  intro i hi
  have hg : cl.vars[i]? = some (cl.vars.getD i 0) := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; rfl
  have hx : ∀ k ∈ (c.rhsCtx L).heads, k ∈ kernelSyms c := fun k hk => rhsHead_kernel hL hk
  have hsub : ∀ a b, (a, b) ∈ (c.rhsCtx L).subs → (a, b) ∈ c.subsorts := fun _ _ h' => h'
  rcases hocc i hi with hP | ⟨t, ht, hit⟩ | hR | ⟨t, ht, hit⟩
  · exact varOccsList_num h cl.pats hpats (fun s hs => h.fnSorts hfn s (List.mem_cons_of_mem _ hs)) i hP _ hg
  · exact varOccs_numOpen h hx hsub t (hreqs t ht) bool_numbered i hit _ hg
  · exact varOccs_numOpen h hx hsub cl.rhs hrhs (h.fnSorts hfn fn.result (List.mem_cons_self ..)) i hR _ hg
  · exact varOccs_numOpen h hx hsub t (hens t ht) bool_numbered i hit _ hg

namespace AtT

variable {T : GroundTerm → GroundTerm → Prop}

/-- `premise_iff` at the variables a predicate `P` names: the `requires` and the patterns read
only those, and σ gives them their values. -/
theorem premise_iffCl (h : HypModelCore c) {P : Nat → Prop} {vars args : List Srt} {req : Option Term}
    {pats : List Term} {tbl : KoreAML.VarTable} {e : Valuation Elem} {σR : Elem}
    (hR : ∀ a, (KoreAML.trSort tbl KoreAML.R).interpret (stdI_T c T) e a ↔ a = σR) (hRs : KoreAML.IsSort (stdI_T c T) σR)
    {σ : Subst}
    (hvar : ∀ i, P i → ∀ m, (KoreAML.tr ⟨tbl, []⟩ (KoreAML.varAt (canonVars c vars) i)).interpret (stdI_T c T) e m ↔
      ∃ v, σ.lookup i = some v ∧ m = .val v)
    (hreqOK : ∀ t, req = some t → TermOK c P t)
    (hpatOK : ∀ p ∈ pats, PatOK c P p) (hlen : pats.length = args.length)
    {ws : List GroundTerm} (hX : ArgsAt c tbl e args ws) (a : Elem) :
    (KoreAML.tr ⟨tbl, []⟩ (premise (args.map c.sortName) (req.map (Term.kore c (canonVars c vars)))
      (Term.koreList c (canonVars c vars) pats))).interpret (stdI_T c T) e a ↔
      KoreAML.Inh (stdI_T c T) σR a ∧ (∀ t, req = some t → EvalTerm c σ t (some (bool true))) ∧ PatVals c σ pats ws := by
  have hn := h.namesK
  have hwl : ws.length = args.length := sortsOf_len hX.sorts
  unfold premise
  rw [tr_and2, KoreAML.interp_sAnd]
  have hreq : (KoreAML.tr ⟨tbl, []⟩ (reqPat KoreAML.R (req.map (Term.kore c (canonVars c vars))))).interpret (stdI_T c T) e a ↔
      KoreAML.Inh (stdI_T c T) σR a ∧ ∀ t, req = some t → EvalTerm c σ t (some (bool true)) := by
    cases hq : req with
    | none =>
      simp only [Option.map_none, reqPat]
      rw [KoreAML.tr, KoreAML.interp_sTop defOK_std isFree_R, KoreAML.interp_inhOf_of hR]
      simp
    | some t =>
      simp only [Option.map_some]
      rw [reqPat_iff h hvar (hreqOK t hq) hR hRs]
      simp
  rw [hreq, argsConj_iff hR hRs 0 _ (fun n s p hn' => ?_)]
  · constructor
    · rintro ⟨⟨hi, hq⟩, -, hall⟩
      refine ⟨hi, hq, patVals_of_get (by rw [hlen, hwl]) fun n p w hp hw => ?_⟩
      have hlt : n < args.length := by rw [← hwl]; exact (List.getElem?_eq_some_iff.mp hw).1
      have hs : (args.map c.sortName)[n]? = some (c.sortName (args[n]'hlt)) := by
        rw [List.getElem?_map, List.getElem?_eq_getElem hlt]; rfl
      have hl : ((args.map c.sortName).zip (Term.koreList c (canonVars c vars) pats))[n]? =
          some (c.sortName (args[n]'hlt), Term.kore c (canonVars c vars) p) := by
        rw [List.getElem?_zip_eq_some]
        refine ⟨hs, ?_⟩
        rw [koreList_get hp]
      have := hall n _ _ hl
      rw [Nat.zero_add, hX.X n w _ hw hs] at this
      obtain ⟨v, hv, he⟩ := (tr_pat h hvar (hpatOK p (List.mem_of_getElem? hp)) _).mp this
      cases he
      exact hv
    · rintro ⟨hi, hq, hpv⟩
      refine ⟨⟨hi, hq⟩, hi, fun n s p hl => ?_⟩
      obtain ⟨hs, hp⟩ := List.getElem?_zip_eq_some.mp hl
      obtain ⟨p0, hp0, rfl⟩ := koreList_get_inv (c := c) hp
      rw [List.getElem?_map] at hs
      obtain ⟨a0, ha0, rfl⟩ := Option.map_eq_some_iff.mp hs
      obtain ⟨w, hw, -⟩ := sortsOf_get hX.sorts ha0
      rw [Nat.zero_add, hX.X n w _ hw (by rw [List.getElem?_map, ha0]; rfl)]
      exact (tr_pat h hvar (hpatOK p0 (List.mem_of_getElem? hp0)) _).mpr ⟨w, patVals_get hpv n p0 w hp0 hw, rfl⟩
  · obtain ⟨hs, -⟩ := List.getElem?_zip_eq_some.mp hn'
    rw [List.getElem?_map] at hs
    obtain ⟨a0, ha0, rfl⟩ := Option.map_eq_some_iff.mp hs
    have hnum := hX.num a0 (List.mem_of_getElem? ha0)
    obtain ⟨w, hw, hsw⟩ := sortsOf_get hX.sorts ha0
    refine ⟨.srt a0, fun b => by rw [trSort_srt]; exact sort_den hn hnum e b,
      (isSort_iff _).mpr ⟨a0, List.mem_range.mpr hnum, rfl⟩, ?_⟩
    rw [Nat.zero_add, hX.X n w _ hw (by rw [List.getElem?_map, ha0]; rfl), inh_srt]
    exact hsw

end AtT

/-- `premise_iff` at the variables a predicate `P` names: the `requires` and the patterns read
only those, and σ gives them their values. -/
theorem premise_iffCl (h : HypModelCore c) {P : Nat → Prop} {vars args : List Srt} {req : Option Term}
    {pats : List Term} {tbl : KoreAML.VarTable} {e : Valuation Elem} {σR : Elem}
    (hR : ∀ a, (KoreAML.trSort tbl KoreAML.R).interpret (stdI c) e a ↔ a = σR) (hRs : KoreAML.IsSort (stdI c) σR)
    {σ : Subst}
    (hvar : ∀ i, P i → ∀ m, (KoreAML.tr ⟨tbl, []⟩ (KoreAML.varAt (canonVars c vars) i)).interpret (stdI c) e m ↔
      ∃ v, σ.lookup i = some v ∧ m = .val v)
    (hreqOK : ∀ t, req = some t → TermOK c P t)
    (hpatOK : ∀ p ∈ pats, PatOK c P p) (hlen : pats.length = args.length)
    {ws : List GroundTerm} (hX : ArgsAt c tbl e args ws) (a : Elem) :
    (KoreAML.tr ⟨tbl, []⟩ (premise (args.map c.sortName) (req.map (Term.kore c (canonVars c vars)))
      (Term.koreList c (canonVars c vars) pats))).interpret (stdI c) e a ↔
      KoreAML.Inh (stdI c) σR a ∧ (∀ t, req = some t → EvalTerm c σ t (some (bool true))) ∧ PatVals c σ pats ws :=
  AtT.premise_iffCl (c := c) (T := StepM c) (h := h) (P := P) (vars := vars) (args := args) (req := req) (pats := pats) (tbl := tbl) (e := e) (σR := σR) (hR := hR) (hRs := hRs) (σ := σ) (hvar := hvar) (hreqOK := hreqOK) (hpatOK := hpatOK) (hlen := hlen) (ws := ws) (hX := hX) (a := a)

namespace AtT

variable {T : GroundTerm → GroundTerm → Prop}

/-- **The reading of an exclusion whose clause's patterns need not bind every variable**: at a
valuation giving the formal arguments the values `w̄`, the clause's exclusion
`∃ȳ. ⌈req = true⌉ ∧ X̄ ∈ p̄`, ȳ the variables of its patterns and conditions, holds exactly where
the patterns match `w̄` and the `requires` is `true` under a substitution well sorted on those
variables. -/
theorem exclusion_iffCl (h : HypModelCore c) {fn : Fn} (hfn : fn ∈ c.allFns) {cl : Clause} (hcl : cl ∈ fn.clauses)
    {tbl : KoreAML.VarTable} (hkeys : ∀ i < cl.vars.length, i ∈ cl.leftVars → canonKey c cl.vars i ∈ tbl)
    (hRkey : KoreAML.VarKey.sortVar "R" ∈ tbl)
    (hXkeys : ∀ (j : Nat) (s : String), (fn.args.map c.sortName)[j]? = some s →
      KoreAML.VarKey.evar ("X" ++ toString j) (KoreAML.srt s) ∈ tbl)
    {e : Valuation Elem} (hRs : KoreAML.IsSort (stdI_T c T) (e.evalEvar (tbl.ev (.sortVar "R"))))
    {ws : List GroundTerm} (hX : ArgsAt c tbl e fn.args ws) {a : Elem}
    (ha : KoreAML.Inh (stdI_T c T) (e.evalEvar (tbl.ev (.sortVar "R"))) a) :
    (KoreAML.tr ⟨tbl, []⟩ (exclusion c fn cl (canonClausePres cl))).interpret (stdI_T c T) e a ↔
      ∃ σ, c.WellSortedAt cl.vars cl.leftVars σ ∧ PatVals c σ cl.pats ws ∧
        ∀ t, cl.req = some t → EvalTerm c σ t (some (bool true)) := by
  have hn := h.namesK
  obtain ⟨hpats, -, L, hL, hreqs, -⟩ := clause_factsCl h hfn hcl
  have hnum := clause_vars_num h hfn hcl
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
  -- the patterns and the `requires` read the variables of the patterns and the conditions only
  let P : Nat → Prop := fun i => i < n ∧ i ∈ cl.leftVars
  have hpatOK : ∀ p ∈ cl.pats, PatOK c P p := fun p hp =>
    (patOKs_of_sorted h hpats p hp).monoOpen fun i hi =>
      ⟨varOccsList_lt cl.pats hpats i (varOccsList_of_memOpen hp hi), List.mem_append_left _ (varOccsList_of_memOpen hp hi)⟩
  have hreqOK : ∀ t, cl.req = some t → TermOK c P t := fun t ht =>
    (termOK_of_sorted h hL (hreqs t ht)).monoOpen fun i hi =>
      ⟨varOccs_lt t (hreqs t ht) i hi, Clause.req_leftVars ht i hi⟩
  -- the keys that are not binders
  have hnotb : ∀ k, k ∈ tbl → (∀ i < n, k ≠ canonKey c cl.vars i) →
      ∀ b ∈ (l.map (vs.getD · default)).map KoreAML.Var.kore, tbl.ev k ≠ tbl.ev (KoreAML.evarKey b) := by
    intro k hk hne b hb heq
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hb
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hv
    exact hne i (hl i hi) (ev_inj hk (hkeys i (hl i hi) (hlm i hi)) heq)
  have hRne : ∀ i < n, KoreAML.VarKey.sortVar "R" ≠ canonKey c cl.vars i := fun i hi he => by
    rw [canonKey_eq c hi] at he; cases he
  rw [exclusion_canon_mapCl _ _ _ (clause_preCl h hfn hcl)]
  constructor
  · intro hm
    obtain ⟨e', hag, hguard, hbody⟩ := existsAll_elim defOK_std _ e a hnd hsrt hm
    have he'R : e'.evalEvar (tbl.ev (.sortVar "R")) = e.evalEvar (tbl.ev (.sortVar "R")) :=
      hag _ (hnotb _ hRkey hRne)
    have hX' : ArgsAt c tbl e' fn.args ws := ⟨hX.sorts, hX.num, fun j w s hw hs => by
      rw [hag _ (hnotb _ (hXkeys j s hs) (fun i hi => canonKey_ne_X' hi _ _))]; exact hX.X j w s hw hs⟩
    have hin : ∀ i < n, i ∈ cl.leftVars → InSort c (cl.vars.getD i 0) (e'.evalEvar (tbl.ev (canonKey c cl.vars i))) :=
      fun i hi hil => (inhOf_sort hn (hnum i hi) KoreAML.val0 _).mp
        (hguard _ (List.mem_map_of_mem (List.mem_map_of_mem (hml i hi hil))) _
          (by show (vs.getD i default).kore.sort = _; rw [canonVars_getD c hi]; rfl))
    let σ := substE c tbl cl.vars e'
    have hvar : ∀ i, P i → ∀ m, (KoreAML.tr ⟨tbl, []⟩ (KoreAML.varAt vs i)).interpret (stdI_T c T) e' m ↔
        ∃ v, σ.lookup i = some v ∧ m = .val v := by
      rintro i ⟨hi, hil⟩ m
      obtain ⟨v, he, -⟩ := inSort_val (hin i hi hil)
      rw [var_read, substE_lookup hi]
      show m = e'.evalEvar (tbl.ev (canonKey c cl.vars i)) ↔ _
      rw [he]
      simp [toVal]
    have hσ : c.WellSortedAt cl.vars cl.leftVars σ := fun i hil s hs' => by
      have hi : i < n := (List.getElem?_eq_some_iff.mp hs').1
      obtain ⟨v, he, hsv⟩ := inSort_val (hin i hi hil)
      refine ⟨v, by rw [substE_lookup hi, he]; rfl, ?_⟩
      rwa [List.getD_eq_getElem?_getD, hs', Option.getD_some] at hsv
    obtain ⟨-, hq, hpv⟩ := (premise_iffCl h (R_read e') (by rw [he'R]; exact hRs) hvar hreqOK hpatOK hlen hX' a).mp
      hbody
    exact ⟨σ, hσ, hpv, hq⟩
  · rintro ⟨σ, hσ, hpv, hq⟩
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
    have hvar : ∀ i, P i → ∀ m, (KoreAML.tr ⟨tbl, []⟩ (KoreAML.varAt vs i)).interpret (stdI_T c T) e' m ↔
        ∃ v, σ.lookup i = some v ∧ m = .val v := by
      rintro i ⟨hi, hil⟩ m
      rw [var_read]
      show m = (setV c tbl cl.vars cl.leftVars f e).evalEvar (tbl.ev (canonKey c cl.vars i)) ↔ _
      rw [setV_on hkeys hi hil]
      obtain ⟨w, hw, -⟩ := hσv i hi hil
      simp [f, hw]
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
      show InS (stdI_T c T) _ ((setV c tbl cl.vars cl.leftVars f e).evalEvar (tbl.ev (canonKey c cl.vars i)))
      rw [setV_on hkeys (hl i hil) (hlm i hil)]
      obtain ⟨w, hw, hws⟩ := hσv i (hl i hil) (hlm i hil)
      show InS (stdI_T c T) _ (Elem.val ((σ.lookup i).getD default))
      rw [hw, Option.getD_some]
      exact (inhOf_sort hn (hnum i (hl i hil)) KoreAML.val0 _).mpr hws
    · exact (premise_iffCl h (R_read e') (by rw [he'R]; exact hRs) hvar hreqOK hpatOK hlen hX' a).mpr
        ⟨by rw [he'R]; exact ha, hq, hpv⟩

end AtT

/-- **The reading of an exclusion whose clause's patterns need not bind every variable**: at a
valuation giving the formal arguments the values `w̄`, the clause's exclusion
`∃ȳ. ⌈req = true⌉ ∧ X̄ ∈ p̄`, ȳ the variables of its patterns and conditions, holds exactly where
the patterns match `w̄` and the `requires` is `true` under a substitution well sorted on those
variables. -/
theorem exclusion_iffCl (h : HypModelCore c) {fn : Fn} (hfn : fn ∈ c.allFns) {cl : Clause} (hcl : cl ∈ fn.clauses)
    {tbl : KoreAML.VarTable} (hkeys : ∀ i < cl.vars.length, i ∈ cl.leftVars → canonKey c cl.vars i ∈ tbl)
    (hRkey : KoreAML.VarKey.sortVar "R" ∈ tbl)
    (hXkeys : ∀ (j : Nat) (s : String), (fn.args.map c.sortName)[j]? = some s →
      KoreAML.VarKey.evar ("X" ++ toString j) (KoreAML.srt s) ∈ tbl)
    {e : Valuation Elem} (hRs : KoreAML.IsSort (stdI c) (e.evalEvar (tbl.ev (.sortVar "R"))))
    {ws : List GroundTerm} (hX : ArgsAt c tbl e fn.args ws) {a : Elem}
    (ha : KoreAML.Inh (stdI c) (e.evalEvar (tbl.ev (.sortVar "R"))) a) :
    (KoreAML.tr ⟨tbl, []⟩ (exclusion c fn cl (canonClausePres cl))).interpret (stdI c) e a ↔
      ∃ σ, c.WellSortedAt cl.vars cl.leftVars σ ∧ PatVals c σ cl.pats ws ∧
        ∀ t, cl.req = some t → EvalTerm c σ t (some (bool true)) :=
  AtT.exclusion_iffCl (c := c) (T := StepM c) (h := h) (fn := fn) (hfn := hfn) (cl := cl) (hcl := hcl) (tbl := tbl) (hkeys := hkeys) (hRkey := hRkey) (hXkeys := hXkeys) (e := e) (hRs := hRs) (ws := ws) (hX := hX) (a := a) (ha := ha)

/-! ## The variables of a clause's equation -/

/-- A variable of a clause's `requires` is free in its premise. -/
theorem freeOf_premise_req {args : List Srt} {req : Option Term} {pats : List Term} {vars : List Srt}
    {t : Term} (ht : req = some t) {i : Nat} (hi : i ∈ varOccs t) :
    canonKey c vars i ∈ KoreAML.freeOf [] (premise (args.map c.sortName) (req.map (Term.kore c (canonVars c vars)))
      (Term.koreList c (canonVars c vars) pats)) := by
  subst ht
  unfold premise
  rw [KoreAML.freeOf, KoreAML.freeOfList, KoreAML.freeOfList, KoreAML.freeOfList]
  simp only [List.append_nil, List.mem_append]
  refine Or.inl ?_
  simp only [Option.map_some, reqPat]
  rw [KoreAML.freeOf]
  exact List.mem_append_left _ (kore_freeOf c _ t hi)

/-- A variable of a clause's `requires` is a variable of its premise. -/
theorem varsOf_premise_req {args : List Srt} {req : Option Term} {pats : List Term} {vars : List Srt}
    {t : Term} (ht : req = some t) {i : Nat} (hi : i ∈ varOccs t) :
    canonKey c vars i ∈ KoreAML.varsOf (premise (args.map c.sortName) (req.map (Term.kore c (canonVars c vars)))
      (Term.koreList c (canonVars c vars) pats)) := by
  subst ht
  unfold premise
  refine varsOf_and_mem (List.mem_cons_self ..) ?_
  simp only [Option.map_some, reqPat, KoreAML.varsOf]
  exact List.mem_append_left _ (List.mem_append_right _ (varsOf_kore c _ t hi))

/-- **Each variable of a clause is free in its equation's axiom**, where each occurs in its
patterns, `requires`, right side or `ensures`: one of the patterns or the `requires` in the premise
(here any pattern whose free variables include the clause premise's), one of the right side or the
`ensures` in the conclusion. -/
theorem clause_keys_freeCl {fn : Fn} {cl : Clause} {prem : Kore.Pattern} (hlen : cl.pats.length = fn.args.length)
    (hocc : ∀ i < cl.vars.length, i ∈ varOccsList cl.pats ∨ (∃ t, cl.req = some t ∧ i ∈ varOccs t) ∨
      i ∈ varOccs cl.rhs ∨ ∃ t, cl.ens = some t ∧ i ∈ varOccs t)
    (hP : ∀ k, k ∈ KoreAML.freeOf [] (premise (fn.args.map c.sortName) (cl.req.map (Term.kore c (canonVars c cl.vars)))
      (Term.koreList c (canonVars c cl.vars) cl.pats)) → k ∈ KoreAML.freeOf [] prem) :
    ∀ i < cl.vars.length, canonKey c cl.vars i ∈ KoreAML.freeOf [] (.implies KoreAML.R prem
      (fnConcl c fn (Term.kore c (canonVars c cl.vars) cl.rhs)
        (reqPat (srtOf c fn.result) (cl.ens.map (Term.kore c (canonVars c cl.vars)))))) := by
  intro i hi
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
  rcases hocc i hi with hp | ⟨t, ht, hit⟩ | hr | ⟨t, ht, hit⟩
  · rw [KoreAML.freeOf]; exact List.mem_append_left _ (hP _ (freeOf_premise_var hlen hp))
  · rw [KoreAML.freeOf]; exact List.mem_append_left _ (hP _ (freeOf_premise_req ht hit))
  · exact hinR (freeOf_and_memOpen (List.mem_cons_self ..) (kore_freeOf c _ cl.rhs hr))
  · refine hinR (freeOf_and_memOpen (List.mem_cons_of_mem _ (List.mem_singleton_self _)) ?_)
    rw [ht]
    simp only [Option.map_some, reqPat]
    rw [KoreAML.freeOf]
    exact List.mem_append_left _ (kore_freeOf c _ t hit)

/-- `clause_keys_freeCl` for the variables of the axiom. -/
theorem clause_keys_varsCl {fn : Fn} {cl : Clause} {prem : Kore.Pattern} (hlen : cl.pats.length = fn.args.length)
    (hocc : ∀ i < cl.vars.length, i ∈ varOccsList cl.pats ∨ (∃ t, cl.req = some t ∧ i ∈ varOccs t) ∨
      i ∈ varOccs cl.rhs ∨ ∃ t, cl.ens = some t ∧ i ∈ varOccs t)
    (hP : ∀ k, k ∈ KoreAML.varsOf (premise (fn.args.map c.sortName) (cl.req.map (Term.kore c (canonVars c cl.vars)))
      (Term.koreList c (canonVars c cl.vars) cl.pats)) → k ∈ KoreAML.varsOf prem) :
    ∀ i < cl.vars.length, canonKey c cl.vars i ∈ KoreAML.varsOf (.implies KoreAML.R prem
      (fnConcl c fn (Term.kore c (canonVars c cl.vars) cl.rhs)
        (reqPat (srtOf c fn.result) (cl.ens.map (Term.kore c (canonVars c cl.vars)))))) := by
  intro i hi
  have hinP : ∀ {k}, k ∈ KoreAML.varsOf prem → k ∈ KoreAML.varsOf (.implies KoreAML.R prem
      (fnConcl c fn (Term.kore c (canonVars c cl.vars) cl.rhs)
        (reqPat (srtOf c fn.result) (cl.ens.map (Term.kore c (canonVars c cl.vars)))))) := fun hk => by
    rw [KoreAML.varsOf]; exact List.mem_append_left _ (List.mem_append_right _ hk)
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
  rcases hocc i hi with hp | ⟨t, ht, hit⟩ | hr | ⟨t, ht, hit⟩
  · exact hinP (hP _ (varsOf_premise_var hlen hp))
  · exact hinP (hP _ (varsOf_premise_req ht hit))
  · exact hinR (varsOf_and_mem (List.mem_cons_self ..) (varsOf_kore c _ cl.rhs hr))
  · refine hinR (varsOf_and_mem (List.mem_cons_of_mem _ (List.mem_singleton_self _)) ?_)
    rw [ht]
    simp only [Option.map_some, reqPat, KoreAML.varsOf]
    exact List.mem_append_left _ (List.mem_append_right _ (varsOf_kore c _ t hit))

/-! ## The two kinds of equation -/

section
variable (h : HypModelCore c) {fn : Fn} (hfn : fn ∈ c.allFns)
include h hfn

namespace AtT

variable {T : GroundTerm → GroundTerm → Prop}

/-- **The equation of a clause with no clause of a smaller priority holds.** -/
theorem sat_clauseEq {cl : Clause} (hcl : cl ∈ fn.clauses) (hlow : lowerClauses fn cl = []) :
    stdI_T c T ⊧ᴵ (KoreAML.trAxiom [] [] ⟨0, "kernel", (⟨[KoreAML.Rv], .implies KoreAML.R
      (premise (fn.args.map c.sortName) (cl.req.map (Term.kore c (canonVars c cl.vars)))
        (Term.koreList c (canonVars c cl.vars) cl.pats))
      (fnConcl c fn (Term.kore c (canonVars c cl.vars) cl.rhs)
        (reqPat (srtOf c fn.result) (cl.ens.map (Term.kore c (canonVars c cl.vars))))), []⟩ : Kore.Axiom)⟩).pat := by
  obtain ⟨hpats, hocc, L, hL, hreqs, hrhs, hens⟩ := clause_factsCl h hfn hcl
  have hlen : cl.pats.length = fn.args.length := sortsOfTerms_length hpats
  refine sat_eqnCl h hfn (clause_vars_num h hfn hcl) (termOK_of_sorted h hL hrhs)
    (fun t ht => termOK_of_sorted h hL (hens t ht))
    (clause_keys_freeCl hlen hocc fun _ hk => hk) (clause_keys_varsCl hlen hocc fun _ hk => hk)
    fun tbl e ws a hEq _ ha hprem => ?_
  obtain ⟨hσ, hvar⟩ := substE_ok (T := T) hEq.vin
  obtain ⟨-, hq, hpv⟩ := (premise_iff h (R_read e) hEq.Rs hvar (fun t ht => termOK_of_sorted h hL (hreqs t ht))
    (patOKs_of_sorted h hpats) hlen hEq.args a).mp hprem
  refine eval_of_decides h hfn hcl hEq.args.sorts ⟨⟨hσ.at _, hpv, hq, Clause.holds_preTop (clause_preCl h hfn hcl) _⟩, fun cl' hcl' hna hlt => ?_⟩
  have : cl' ∈ lowerClauses fn cl := by simp [lowerClauses, hcl', hna, hlt]
  rw [hlow] at this
  exact absurd this List.not_mem_nil

end AtT

/-- **The equation of a clause with no clause of a smaller priority holds.** -/
theorem sat_clauseEq {cl : Clause} (hcl : cl ∈ fn.clauses) (hlow : lowerClauses fn cl = []) :
    stdI c ⊧ᴵ (KoreAML.trAxiom [] [] ⟨0, "kernel", (⟨[KoreAML.Rv], .implies KoreAML.R
      (premise (fn.args.map c.sortName) (cl.req.map (Term.kore c (canonVars c cl.vars)))
        (Term.koreList c (canonVars c cl.vars) cl.pats))
      (fnConcl c fn (Term.kore c (canonVars c cl.vars) cl.rhs)
        (reqPat (srtOf c fn.result) (cl.ens.map (Term.kore c (canonVars c cl.vars))))), []⟩ : Kore.Axiom)⟩).pat :=
  AtT.sat_clauseEq (c := c) (T := StepM c) (cl := cl) (hcl := hcl) (hlow := hlow) (h := h) (hfn := hfn)

namespace AtT

variable {T : GroundTerm → GroundTerm → Prop}

/-- Where a negated disjunction of exclusions holds, none of their clauses matches with a `true`
`requires` under a substitution well sorted on its patterns' and conditions' variables. -/
theorem fails_of_not_exclCl {cls : List Clause} (hcls : ∀ cl ∈ cls, cl ∈ fn.clauses)
    {tbl : KoreAML.VarTable} {e : Valuation Elem} {ws : List GroundTerm} (hEqR : KoreAML.VarKey.sortVar "R" ∈ tbl)
    (hXk : ∀ (j : Nat) (s : String), (fn.args.map c.sortName)[j]? = some s →
      KoreAML.VarKey.evar ("X" ++ toString j) (KoreAML.srt s) ∈ tbl)
    (hRs : KoreAML.IsSort (stdI_T c T) (e.evalEvar (tbl.ev (.sortVar "R")))) (hX : ArgsAt c tbl e fn.args ws)
    (hkeys : ∀ cl ∈ cls, ∀ i < cl.vars.length, i ∈ cl.leftVars → canonKey c cl.vars i ∈ tbl) {a : Elem}
    (hnot : (KoreAML.tr ⟨tbl, []⟩ (.not KoreAML.R (KoreAML.anyOf
      (cls.map fun cl => exclusion c fn cl (canonClausePres cl))))).interpret (stdI_T c T) e a) :
    KoreAML.Inh (stdI_T c T) (e.evalEvar (tbl.ev (.sortVar "R"))) a ∧ ∀ cl ∈ cls, ∀ σ,
      ¬ (c.WellSortedAt cl.vars cl.leftVars σ ∧ PatVals c σ cl.pats ws ∧
        ∀ t, cl.req = some t → EvalTerm c σ t (some (bool true))) := by
  rw [KoreAML.tr, KoreAML.interp_sNot, anyOf_eq, anyOfC_iff (R_read e) isFree_R, KoreAML.interp_inhOf_of (R_read e)]
    at hnot
  obtain ⟨hn1, hi⟩ := hnot
  refine ⟨hi, fun cl hcl σ hap => hn1 ⟨hi, _, List.mem_map.mpr ⟨cl, hcl, rfl⟩, ?_⟩⟩
  exact (exclusion_iffCl h hfn (hcls cl hcl) (hkeys cl hcl) hEqR hXk hRs hX hi).mpr ⟨σ, hap⟩

end AtT

/-- Where a negated disjunction of exclusions holds, none of their clauses matches with a `true`
`requires` under a substitution well sorted on its patterns' and conditions' variables. -/
theorem fails_of_not_exclCl {cls : List Clause} (hcls : ∀ cl ∈ cls, cl ∈ fn.clauses)
    {tbl : KoreAML.VarTable} {e : Valuation Elem} {ws : List GroundTerm} (hEqR : KoreAML.VarKey.sortVar "R" ∈ tbl)
    (hXk : ∀ (j : Nat) (s : String), (fn.args.map c.sortName)[j]? = some s →
      KoreAML.VarKey.evar ("X" ++ toString j) (KoreAML.srt s) ∈ tbl)
    (hRs : KoreAML.IsSort (stdI c) (e.evalEvar (tbl.ev (.sortVar "R")))) (hX : ArgsAt c tbl e fn.args ws)
    (hkeys : ∀ cl ∈ cls, ∀ i < cl.vars.length, i ∈ cl.leftVars → canonKey c cl.vars i ∈ tbl) {a : Elem}
    (hnot : (KoreAML.tr ⟨tbl, []⟩ (.not KoreAML.R (KoreAML.anyOf
      (cls.map fun cl => exclusion c fn cl (canonClausePres cl))))).interpret (stdI c) e a) :
    KoreAML.Inh (stdI c) (e.evalEvar (tbl.ev (.sortVar "R"))) a ∧ ∀ cl ∈ cls, ∀ σ,
      ¬ (c.WellSortedAt cl.vars cl.leftVars σ ∧ PatVals c σ cl.pats ws ∧
        ∀ t, cl.req = some t → EvalTerm c σ t (some (bool true))) :=
  AtT.fails_of_not_exclCl (c := c) (T := StepM c) (cls := cls) (hcls := hcls) (tbl := tbl) (e := e) (ws := ws) (hEqR := hEqR) (hXk := hXk) (hRs := hRs) (hX := hX) (hkeys := hkeys) (a := a) (hnot := hnot) (h := h) (hfn := hfn)

/-- `fails_of_not_exclCl` at a table holding every variable's key: none of the clauses applies. -/
theorem fails_of_not_excl {cls : List Clause} (hcls : ∀ cl ∈ cls, cl ∈ fn.clauses)
    {tbl : KoreAML.VarTable} {e : Valuation Elem} {ws : List GroundTerm} (hEqR : KoreAML.VarKey.sortVar "R" ∈ tbl)
    (hXk : ∀ (j : Nat) (s : String), (fn.args.map c.sortName)[j]? = some s →
      KoreAML.VarKey.evar ("X" ++ toString j) (KoreAML.srt s) ∈ tbl)
    (hRs : KoreAML.IsSort (stdI c) (e.evalEvar (tbl.ev (.sortVar "R")))) (hX : ArgsAt c tbl e fn.args ws)
    (hkeys : ∀ cl ∈ cls, ∀ i < cl.vars.length, canonKey c cl.vars i ∈ tbl) {a : Elem}
    (hnot : (KoreAML.tr ⟨tbl, []⟩ (.not KoreAML.R (KoreAML.anyOf
      (cls.map fun cl => exclusion c fn cl (canonClausePres cl))))).interpret (stdI c) e a) :
    KoreAML.Inh (stdI c) (e.evalEvar (tbl.ev (.sortVar "R"))) a ∧ ∀ cl ∈ cls, ∀ σ, ¬ cl.AppliesAt c σ ws :=
  let ⟨hi, hf⟩ := fails_of_not_exclCl h hfn hcls hEqR hXk hRs hX (fun cl hcl i hi _ => hkeys cl hcl i hi) hnot
  ⟨hi, fun cl hcl σ hap => hf cl hcl σ ⟨((wellSortedAt_univ (clause_exsCl h hfn (hcls cl hcl))).mp hap.1).at _, hap.2.1, hap.2.2.1⟩⟩

omit h hfn in
theorem varsOf_not_exclCl {cls : List Clause} {cl : Clause} (hcl : cl ∈ cls) (_hpre : cl.pre = .top) {i : Nat}
    (hi : i < cl.vars.length) (hil : i ∈ cl.leftVars) :
    canonKey c cl.vars i ∈ KoreAML.varsOf (.not KoreAML.R (KoreAML.anyOf
      (cls.map fun cl => exclusion c fn cl (canonClausePres cl)))) := by
  simp only [KoreAML.varsOf]
  rw [anyOf_eq]
  exact List.mem_append_right _ (mem_varsOf_anyOfC (List.mem_map.mpr ⟨cl, hcl, rfl⟩) (varsOf_exclusionCl hi hil))

namespace AtT

variable {T : GroundTerm → GroundTerm → Prop}

/-- **The equation of a clause with clauses of a smaller priority holds**: where they all fail and
it applies. -/
theorem sat_competingEq {cl : Clause} (hcl : cl ∈ fn.clauses) :
    stdI_T c T ⊧ᴵ (KoreAML.trAxiom [] [] ⟨0, "kernel", (⟨[KoreAML.Rv], .implies KoreAML.R
      (competingPremise (fn.args.map c.sortName)
        ((lowerClauses fn cl).map fun cl' => exclusion c fn cl' (canonClausePres cl'))
        (cl.req.map (Term.kore c (canonVars c cl.vars))) (Term.koreList c (canonVars c cl.vars) cl.pats))
      (fnConcl c fn (Term.kore c (canonVars c cl.vars) cl.rhs)
        (reqPat (srtOf c fn.result) (cl.ens.map (Term.kore c (canonVars c cl.vars))))), []⟩ : Kore.Axiom)⟩).pat := by
  have hdl : ∀ cl' ∈ lowerClauses fn cl, cl' ∈ fn.clauses := fun cl' h' => (List.mem_filter.mp h').1
  obtain ⟨hpats, hocc, L, hL, hreqs, hrhs, hens⟩ := clause_factsCl h hfn hcl
  have hlen : cl.pats.length = fn.args.length := sortsOfTerms_length hpats
  refine sat_eqnCl h hfn (clause_vars_num h hfn hcl) (termOK_of_sorted h hL hrhs)
    (fun t ht => termOK_of_sorted h hL (hens t ht))
    (clause_keys_freeCl hlen hocc fun _ hk => ?_) (clause_keys_varsCl hlen hocc fun _ hk => ?_)
    fun tbl e ws a hEq hvT ha hprem => ?_
  · unfold competingPremise
    simp only [KoreAML.freeOf, KoreAML.freeOfList, List.append_nil, List.mem_append]
    exact Or.inr hk
  · unfold competingPremise
    exact varsOf_and_mem (List.mem_cons_of_mem _ (List.mem_singleton_self _)) hk
  · obtain ⟨hσ, hvar⟩ := substE_ok (T := T) hEq.vin
    unfold competingPremise at hprem
    rw [tr_and2, KoreAML.interp_sAnd] at hprem
    obtain ⟨hnot, hp⟩ := hprem
    obtain ⟨-, hfails⟩ := fails_of_not_exclCl (T := T) h hfn hdl hEq.R hEq.Xk hEq.Rs hEq.args
      (fun cl' hcl' i hi hil => hvT _ (by
        unfold competingPremise
        exact varsOf_and_mem (List.mem_cons_self ..) (varsOf_not_exclCl hcl' (clause_preCl h hfn (hdl cl' hcl')) hi hil))) hnot
    obtain ⟨-, hq, hpv⟩ := (premise_iff h (R_read e) hEq.Rs hvar (fun t ht => termOK_of_sorted h hL (hreqs t ht))
      (patOKs_of_sorted h hpats) hlen hEq.args a).mp hp
    exact eval_of_decides h hfn hcl hEq.args.sorts ⟨⟨hσ.at _, hpv, hq, Clause.holds_preTop (clause_preCl h hfn hcl) _⟩, fun cl' hcl' hna hlt σ' hw hp' hq' =>
      hfails cl' (List.mem_filter.mpr ⟨hcl', by simp [hna, hlt]⟩) σ' ⟨hw, hp', hq'.1⟩⟩

end AtT

/-- **The equation of a clause with clauses of a smaller priority holds**: where they all fail and
it applies. -/
theorem sat_competingEq {cl : Clause} (hcl : cl ∈ fn.clauses) :
    stdI c ⊧ᴵ (KoreAML.trAxiom [] [] ⟨0, "kernel", (⟨[KoreAML.Rv], .implies KoreAML.R
      (competingPremise (fn.args.map c.sortName)
        ((lowerClauses fn cl).map fun cl' => exclusion c fn cl' (canonClausePres cl'))
        (cl.req.map (Term.kore c (canonVars c cl.vars))) (Term.koreList c (canonVars c cl.vars) cl.pats))
      (fnConcl c fn (Term.kore c (canonVars c cl.vars) cl.rhs)
        (reqPat (srtOf c fn.result) (cl.ens.map (Term.kore c (canonVars c cl.vars))))), []⟩ : Kore.Axiom)⟩).pat :=
  AtT.sat_competingEq (c := c) (T := StepM c) (cl := cl) (hcl := hcl) (h := h) (hfn := hfn)

end

/-! ## The functions' axioms -/

namespace AtT

variable {T : GroundTerm → GroundTerm → Prop}

theorem sat_kernelItem_of {s : Kore.Sentence} {it : KoreAML.Item}
    (hit : (match s with
      | .axiom a => some (KoreAML.trAxiom [] [] ⟨0, "kernel", a⟩)
      | _ => none) = some it) {a : Kore.Axiom} (hs : s = .axiom a)
    (ha : stdI_T c T ⊧ᴵ (KoreAML.trAxiom [] [] ⟨0, "kernel", a⟩).pat) : stdI_T c T ⊧ᴵ it.pat := by
  subst hs
  cases hit
  exact ha

end AtT

theorem sat_kernelItem_of {s : Kore.Sentence} {it : KoreAML.Item}
    (hit : (match s with
      | .axiom a => some (KoreAML.trAxiom [] [] ⟨0, "kernel", a⟩)
      | _ => none) = some it) {a : Kore.Axiom} (hs : s = .axiom a)
    (ha : stdI c ⊧ᴵ (KoreAML.trAxiom [] [] ⟨0, "kernel", a⟩).pat) : stdI c ⊧ᴵ it.pat :=
  AtT.sat_kernelItem_of (c := c) (T := StepM c) (s := s) (it := it) (hit := hit) (a := a) (hs := hs) (ha := ha)

namespace AtT

variable {T : GroundTerm → GroundTerm → Prop}

/-- **`SatFnsGoal`**: the value model satisfies the functions' equations. -/
theorem satFnsGoal (h : HypModelCore c) : (stdI_T c T ⊧ᴵP ΓFns c) := by
  refine sat_itemsPremises c fun it hit => ?_
  obtain ⟨fn, hfn, hit⟩ := List.mem_flatMap.mp hit
  obtain ⟨s, hs, hit⟩ := List.mem_filterMap.mp hit
  unfold fnEquationsK at hs
  obtain ⟨cl, hcl, rfl⟩ := List.mem_map.mp hs
  by_cases hlow : (lowerClauses fn cl).isEmpty = true
  · rw [show prioEquation c fn cl = clauseEquation c fn cl from if_pos hlow] at hit
    exact sat_kernelItem_of hit (clauseEquation_top (clause_preCl h hfn hcl) (clause_exsCl h hfn hcl))
      (sat_clauseEq h hfn hcl (List.isEmpty_iff.mp hlow))
  · rw [show prioEquation c fn cl = competingEquation c fn (lowerClauses fn cl) cl from if_neg hlow] at hit
    exact sat_kernelItem_of hit (competingEquation_top (clause_preCl h hfn hcl) (clause_exsCl h hfn hcl)) (sat_competingEq h hfn hcl)

end AtT

/-- **`SatFnsGoal`**: the value model satisfies the functions' equations. -/
theorem satFnsGoal (h : HypModelCore c) : SatFnsGoal c :=
  AtT.satFnsGoal (c := c) (T := StepM c) (h := h)

end Model

end Faithful

end KCore
