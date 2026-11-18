/-
  KCore, outside the cone. A function's equation read in a model of `Γ` at a clause whose patterns
  need not bind every variable.

  A clause's equation `∀x̄. premise → f(X̄) = rhs ∧ ens` has the clause's variables free, so each is
  universal, guarded by its sort. `clause_eq_open` reads it at every substitution σ' that is well
  sorted on all of the clause's variables and matches the arguments: the variables the patterns do
  not bind take any value of their sorts, and the equation holds at each choice. It has
  `clause_eq`'s hypotheses with the patterns' binding of every variable (`hbinds`) replaced by the
  weaker fact that each variable occurs in the equation's axiom, in the patterns, the `requires`,
  the right side or the `ensures` (`hocc`): the axiom's table then holds a key for each, and the
  valuation of σ' gives each key its value's element. Where every variable occurs in the patterns
  (`hbinds`), `hocc` holds, so `clause_eq` is `clause_eq_open` at such a clause.

  `clause_two_elems`: two such substitutions that match the same arguments, the `requires` holding
  at both and the right side giving the values `v₁` and `v₂`, put `f(ws)`'s elements equal to
  `v₁`'s and to `v₂`'s, so `v₁` and `v₂` denote one element. `clause_two_instances`: distinct
  values of an `apartSort` sort are distinct elements (`values_apart`), so `v₁ ≠ v₂` gives `False`:
  `Γ` has no model.
-/
import KcoreSpec.OpenClauseEval
import KcoreSpec.FaithfulNeg

set_option autoImplicit false

namespace KCore

open ML Faithful
open KoreAML (DefOK Inh IsSort Closed KGround VarKey VarTable)

section
variable {c : Semantics} {M : Type} {I : Interpretation KoreAML.Sym M}

/-- Each variable of a clause occurs in its equation's axiom where it occurs in the clause's
patterns, `requires`, right side or `ensures`, its predicate in the premise being `\top`. -/
theorem clause_keys_inAxOpen {fn : Fn} {cl : Clause}
    (hpats : sortsOfTerms c.patCtxAll cl.vars cl.pats = some fn.args)
    (hreqv : ∀ t, cl.req = some t → ∀ i ∈ varOccs t, i < cl.vars.length)
    (hpre : cl.pre = .top)
    (hocc : ∀ i < cl.vars.length, i ∈ varOccsList cl.pats ++ cl.condVars ++ varOccs cl.rhs ++
      (cl.ens.map varOccs).getD []) :
    ∀ i < cl.vars.length,
      canonKey c cl.vars i ∈ KoreAML.varsOf (.implies KoreAML.R (clausePrem c fn cl) (clauseConcl c fn cl)) := by
  intro i hi
  have hinP : canonKey c cl.vars i ∈ KoreAML.varsOf (clausePrem c fn cl) →
      canonKey c cl.vars i ∈ KoreAML.varsOf (.implies KoreAML.R (clausePrem c fn cl) (clauseConcl c fn cl)) :=
    fun h => by rw [KoreAML.varsOf]; exact List.mem_append_left _ (List.mem_append_right _ h)
  have hinR : canonKey c cl.vars i ∈ KoreAML.varsOf (clauseRight c fn cl) →
      canonKey c cl.vars i ∈ KoreAML.varsOf (.implies KoreAML.R (clausePrem c fn cl) (clauseConcl c fn cl)) :=
    fun h => by
      rw [KoreAML.varsOf]
      refine List.mem_append_right _ ?_
      unfold clauseConcl
      rw [KoreAML.varsOf]
      exact List.mem_append_right _ h
  have h := hocc i hi
  simp only [List.mem_append] at h
  rcases h with ((hP' | hC) | hR) | hE
  · exact hinP ((premise_varsCl (c := c) hpats hreqv).2.1 i hP')
  · rcases List.mem_append.mp (show i ∈ (cl.req.map varOccs).getD [] ++ varOccsCond cl.vars.length cl.pre from hC)
      with hC | hC
    · cases ht : cl.req with
      | none => rw [ht] at hC; cases hC
      | some t =>
        rw [ht] at hC
        refine hinP ?_
        unfold clausePrem premise
        rw [ht]
        refine Model.varsOf_and_mem (List.mem_cons_self ..) ?_
        simp only [Option.map_some, reqPat, KoreAML.varsOf]
        exact List.mem_append_left _ (List.mem_append_right _ (varsOf_kore c _ t hC))
    · rw [hpre] at hC; simp [varOccsCond] at hC
  · exact hinR (Model.varsOf_and_mem (List.mem_cons_self ..) (varsOf_kore c _ cl.rhs hR))
  · cases ht : cl.ens with
    | none => rw [ht] at hE; cases hE
    | some t =>
      rw [ht] at hE
      refine hinR (Model.varsOf_and_mem (List.mem_cons_of_mem _ (List.mem_singleton_self _)) ?_)
      rw [ht]
      simp only [Option.map_some, reqPat, KoreAML.varsOf]
      exact List.mem_append_left _ (List.mem_append_right _ (varsOf_kore c _ t hE))

/-- **A clause's equation, read in a model, at a clause whose patterns need not bind every
variable.** At arguments of `f`'s sorts and any σ' well sorted on all of the clause's variables
whose values the patterns match, where the `requires` holds, `f` applied to the arguments'
elements is what the right-hand side denotes under σ'. `clause_eq` with `hbinds` replaced by
`hocc`: each variable occurs in the patterns, the `requires`, the right side or the `ensures`. -/
theorem clause_eq_open [Inhabited M] (hI : I ⊧ᴵP Γ c) [OvlOK c] (hnn : NamesNumbered c)
    (htr : ∀ a b d, (a, b) ∈ c.subsorts → (b, d) ∈ c.subsorts → (a, d) ∈ c.subsorts)
    {f : Sym} {fn : Fn} (hfn : c.lookupFn f = some fn) {cl : Clause} (hcl : cl ∈ fn.clauses)
    (hlow : lowerClauses fn cl = []) (hpre : cl.pre = .top) (hexs : cl.exs = [])
    {ws : List GroundTerm} (hws : c.sortsOf ws = some fn.args)
    {σ' : Subst} (hσ' : c.WellSorted cl.vars σ') (hmatch : PatVals c σ' cl.pats ws)
    (hplain : plainPats c cl.pats = true) (hpats : sortsOfTerms c.patCtxAll cl.vars cl.pats = some fn.args)
    (hocc : ∀ i < cl.vars.length, i ∈ varOccsList cl.pats ++ cl.condVars ++ varOccs cl.rhs ++
      (cl.ens.map varOccs).getD [])
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
  have hv := premise_varsCl (c := c) hpats hreqv
  exact eqn_atCl hI hnn hfn (prem := clausePrem c fn cl)
    (clause_item_mem hfnm hcl hlow hpre hexs) hws hσ' hv.1
    (clause_keys_inAxOpen hpats hreqv hpre hocc) hv.2.2 hrhsv hensv hr
    (fun tbl e σr m0 _ hag hX hRv hσr2 hm0 =>
      premise_holds hI hnn htr hfnm hws hσ' hmatch hplain hpats hag hX hRv hσr2 hm0 (ihreq tbl e hag))
    ihrhs e0 m

/-- A clause whose patterns bind every variable (`clause_eq`'s `hbinds`) has each variable
occurring in it (`clause_eq_open`'s `hocc`). -/
theorem clause_occ_of_binds {cl : Clause} (hbinds : ∀ i < cl.vars.length, i ∈ varOccsList cl.pats) :
    ∀ i < cl.vars.length, i ∈ varOccsList cl.pats ++ cl.condVars ++ varOccs cl.rhs ++
      (cl.ens.map varOccs).getD [] :=
  fun i hi => List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (hbinds i hi)))

/-- **Two instances of a clause give `f(ws)` one element.** In a model of `Γ c`, two
substitutions σ₁, σ₂, each well sorted on all of the clause's variables and matching the same
arguments, at which the `requires` holds and the right side gives the values `v₁` and `v₂`: by
`clause_eq_open` at each, `f(ws)`'s elements are `v₁`'s and `v₂`'s, so the two values denote one
element. -/
theorem clause_two_elems [Inhabited M] (hI : I ⊧ᴵP Γ c) [OvlOK c] (hnn : NamesNumbered c)
    (htr : ∀ a b d, (a, b) ∈ c.subsorts → (b, d) ∈ c.subsorts → (a, d) ∈ c.subsorts)
    {f : Sym} {fn : Fn} (hfn : c.lookupFn f = some fn)
    {cl : Clause} (hcl : cl ∈ fn.clauses)
    (hlow : lowerClauses fn cl = []) (hpre : cl.pre = .top) (hexs : cl.exs = [])
    {ws : List GroundTerm} (hws : c.sortsOf ws = some fn.args)
    (hplain : plainPats c cl.pats = true) (hpats : sortsOfTerms c.patCtxAll cl.vars cl.pats = some fn.args)
    (hocc : ∀ i < cl.vars.length, i ∈ varOccsList cl.pats ++ cl.condVars ++ varOccs cl.rhs ++
      (cl.ens.map varOccs).getD [])
    (hreqv : ∀ t, cl.req = some t → ∀ i ∈ varOccs t, i < cl.vars.length)
    (hrhsv : ∀ i ∈ varOccs cl.rhs, i < cl.vars.length)
    (hensv : ∀ t, cl.ens = some t → ∀ i ∈ varOccs t, i < cl.vars.length)
    {σ₁ σ₂ : Subst} (hσ₁ : c.WellSorted cl.vars σ₁) (hσ₂ : c.WellSorted cl.vars σ₂)
    (hm₁ : PatVals c σ₁ cl.pats ws) (hm₂ : PatVals c σ₂ cl.pats ws)
    {v₁ v₂ : GroundTerm} (hv₁ : c.sortOf v₁ = some fn.result) (hv₂ : c.sortOf v₂ = some fn.result)
    (ihreq₁ : ∀ (tbl : VarTable) (e : Valuation M), Agrees c I tbl (canonVars c cl.vars) σ₁ e →
      ∀ t, cl.req = some t → ∀ m, (KoreAML.tr ⟨tbl, []⟩ (Term.kore c (canonVars c cl.vars) t)).interpret I e m ↔
        (den c (bool true)).interpret I e m)
    (ihreq₂ : ∀ (tbl : VarTable) (e : Valuation M), Agrees c I tbl (canonVars c cl.vars) σ₂ e →
      ∀ t, cl.req = some t → ∀ m, (KoreAML.tr ⟨tbl, []⟩ (Term.kore c (canonVars c cl.vars) t)).interpret I e m ↔
        (den c (bool true)).interpret I e m)
    (ihrhs₁ : ∀ (tbl : VarTable) (e : Valuation M), Agrees c I tbl (canonVars c cl.vars) σ₁ e →
      ∀ m, (KoreAML.tr ⟨tbl, []⟩ (clauseRight c fn cl)).interpret I e m ↔ Res c I e (some v₁) m)
    (ihrhs₂ : ∀ (tbl : VarTable) (e : Valuation M), Agrees c I tbl (canonVars c cl.vars) σ₂ e →
      ∀ m, (KoreAML.tr ⟨tbl, []⟩ (clauseRight c fn cl)).interpret I e m ↔ Res c I e (some v₂) m)
    : elemOf c I v₁ = elemOf c I v₂ := by
  have h1 := clause_eq_open hI hnn htr hfn hcl hlow hpre hexs hws hσ₁ hm₁ hplain hpats hocc hreqv hrhsv hensv
    (r := some v₁) (fun v h => by cases h; exact hv₁) ihreq₁ ihrhs₁ KoreAML.val0 (elemOf c I v₁)
  have h2 := clause_eq_open hI hnn htr hfn hcl hlow hpre hexs hws hσ₂ hm₂ hplain hpats hocc hreqv hrhsv hensv
    (r := some v₂) (fun v h => by cases h; exact hv₂) ihreq₂ ihrhs₂ KoreAML.val0 (elemOf c I v₁)
  have hin : Res c I KoreAML.val0 (some v₂) (elemOf c I v₁) :=
    h2.mp (h1.mpr (((elemOf_spec hI hv₁ KoreAML.val0).1 _).mpr rfl))
  exact ((elemOf_spec hI hv₂ KoreAML.val0).1 _).mp hin

/-- **Two instances of a clause with different values: no model.** In a model of `Γ c`, two
substitutions σ₁, σ₂, each well sorted on all of the clause's variables and matching the same
arguments, at which the `requires` holds and the right side gives the values `v₁` and `v₂`, of
the function's result sort, an `apartSort` sort: `v₁ ≠ v₂` is refuted. The two values denote one
element (`clause_two_elems`), and distinct values of the sort are distinct elements
(`values_apart`). -/
theorem clause_two_instances [Inhabited M] (hI : I ⊧ᴵP Γ c) [OvlOK c] (hnn : NamesNumbered c)
    (htr : ∀ a b d, (a, b) ∈ c.subsorts → (b, d) ∈ c.subsorts → (a, d) ∈ c.subsorts)
    (hg : genWf c = true)
    {f : Sym} {fn : Fn} (hfn : c.lookupFn f = some fn) (hap : apartSort c fn.result = true)
    {cl : Clause} (hcl : cl ∈ fn.clauses)
    (hlow : lowerClauses fn cl = []) (hpre : cl.pre = .top) (hexs : cl.exs = [])
    {ws : List GroundTerm} (hws : c.sortsOf ws = some fn.args)
    (hplain : plainPats c cl.pats = true) (hpats : sortsOfTerms c.patCtxAll cl.vars cl.pats = some fn.args)
    (hocc : ∀ i < cl.vars.length, i ∈ varOccsList cl.pats ++ cl.condVars ++ varOccs cl.rhs ++
      (cl.ens.map varOccs).getD [])
    (hreqv : ∀ t, cl.req = some t → ∀ i ∈ varOccs t, i < cl.vars.length)
    (hrhsv : ∀ i ∈ varOccs cl.rhs, i < cl.vars.length)
    (hensv : ∀ t, cl.ens = some t → ∀ i ∈ varOccs t, i < cl.vars.length)
    {σ₁ σ₂ : Subst} (hσ₁ : c.WellSorted cl.vars σ₁) (hσ₂ : c.WellSorted cl.vars σ₂)
    (hm₁ : PatVals c σ₁ cl.pats ws) (hm₂ : PatVals c σ₂ cl.pats ws)
    {v₁ v₂ : GroundTerm} (hv₁ : c.sortOf v₁ = some fn.result) (hv₂ : c.sortOf v₂ = some fn.result)
    (ihreq₁ : ∀ (tbl : VarTable) (e : Valuation M), Agrees c I tbl (canonVars c cl.vars) σ₁ e →
      ∀ t, cl.req = some t → ∀ m, (KoreAML.tr ⟨tbl, []⟩ (Term.kore c (canonVars c cl.vars) t)).interpret I e m ↔
        (den c (bool true)).interpret I e m)
    (ihreq₂ : ∀ (tbl : VarTable) (e : Valuation M), Agrees c I tbl (canonVars c cl.vars) σ₂ e →
      ∀ t, cl.req = some t → ∀ m, (KoreAML.tr ⟨tbl, []⟩ (Term.kore c (canonVars c cl.vars) t)).interpret I e m ↔
        (den c (bool true)).interpret I e m)
    (ihrhs₁ : ∀ (tbl : VarTable) (e : Valuation M), Agrees c I tbl (canonVars c cl.vars) σ₁ e →
      ∀ m, (KoreAML.tr ⟨tbl, []⟩ (clauseRight c fn cl)).interpret I e m ↔ Res c I e (some v₁) m)
    (ihrhs₂ : ∀ (tbl : VarTable) (e : Valuation M), Agrees c I tbl (canonVars c cl.vars) σ₂ e →
      ∀ m, (KoreAML.tr ⟨tbl, []⟩ (clauseRight c fn cl)).interpret I e m ↔ Res c I e (some v₂) m)
    (hne : v₁ ≠ v₂) : False :=
  hne (values_apart hI hg htr hap hv₁ hv₂ (clause_two_elems hI hnn htr hfn hcl hlow hpre hexs hws hplain hpats
    hocc hreqv hrhsv hensv hσ₁ hσ₂ hm₁ hm₂ hv₁ hv₂ ihreq₁ ihreq₂ ihrhs₁ ihrhs₂))

end

end KCore
