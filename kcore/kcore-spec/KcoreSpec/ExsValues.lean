/-
  KCore. An element valuation that extends a match of values and satisfies a clause's right-side
  predicate gives each existential variable the element of a value (`exs_values`).

  Take a definition with `coreOK` that reads confined sorts, a model of `Γc` in which `EvalTerm` is
  sound, and a clause whose existential variables are in scope, apart, in no pattern or condition
  of the left side, whose predicate `post` is sorted (`Semantics.clauseExOK`) with binders of
  confined sorts or of sorts with a value whose body fixes them (`Cond.bound`), and each of whose
  existential variables is of a confined sort or fixed by `post` (`Semantics.clausePlainEx`). Let σ give each variable that is not existential a
  value of its sort, and let `post` have a truth value at every extension of σ by values of the
  existential variables, one such extension existing. Then an element valuation that agrees with σ
  on the variables that are not existential, gives each existential variable an element of its
  sort and satisfies `post` gives each existential variable the element of a value.

  A variable of a confined sort by `confined_value`. A fixed variable by `fixes_value`, over the
  rounds of `Clause.fixedExs`: the variables its fixing term may read are the ones that are not
  existential (at σ's values), the ones fixed in an earlier round, and the other existential ones
  of a confined sort. `fixes_value` asks `post` a truth value at each substitution of values that
  agrees with the valuation on those variables; such a substitution is, on the variables in scope,
  an extension of σ (two values of one sort with one element are one value), and `post` reads the
  variables in scope only.

  The extensions vary the existential variables the left side does not hold, the list
  `cl.exs.filter (!cl.leftVars.contains ·)`; under `clauseExOK` it is `cl.exs`.

  `exs_values_hr` is the statement with the constructors' facts in place of the soundness of
  `EvalTerm`: each truth value of `post` comes with the readings of the terms it evaluates
  (`HoldsRead`). `fixes_value_hr` asks a truth value at the substitutions that are σ beyond the
  variables in scope, which are extensions of σ as they stand. `exs_values` is it where `EvalTerm`
  is sound in the model.
-/
import KcoreSpec.FixesValue
import KcoreSpec.CondTwoTables
import KcoreSpec.ClausePlainEx

set_option autoImplicit false

namespace KCore

open ML Faithful HoldsShape

/-- **`clausePlainEx` with `clauseExOK` and `clausesPlain`'s two conjuncts on the premise and the open
condition variables gives
`clausePlainOpenEx`**: the latter is the former without "each existential variable is of a confined
sort or fixed by the predicate", which the value model does not read. -/
theorem Semantics.clausePlainOpenEx_of_plainEx {c : Semantics} {cl : Clause}
    (h : (c.clausePlainEx cl && c.clauseExOK cl && (cl.pre.isTop || !cl.needsWitness c) &&
      (!cl.reqOpen || cl.reqClosed || cl.openCondVars.all fun i => (cl.vars[i]?.map c.confined).getD false ||
      memHeld c (varOccsList cl.pats) cl.pre i)) = true) :
    c.clausePlainOpenEx cl = true := by
  simp only [Semantics.clausePlainEx, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨h1, -⟩, h2⟩, h3⟩, h4⟩ := h
  simp only [Semantics.clausePlainOpenEx, Bool.and_eq_true]
  exact ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩

namespace CE

section ExsValues
variable {c : Semantics} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}

/-- A substitution that is `σ₁` on the first n variables and σ elsewhere. -/
theorem lookup_overEV (σ σ₁ : Subst) (n i : Nat) :
    (((List.range n).map fun j => (j, (σ₁.lookup j).getD default)) ++ σ).lookup i =
      if i < n then some ((σ₁.lookup i).getD default) else σ.lookup i := by
  rw [List.lookup_append, List.range_eq_range', lookup_range']
  by_cases hi : i < n
  · simp [hi]
  · simp [hi]

/-- **An element valuation that extends a match of values and satisfies `post` gives each
existential variable a value's element**, where `post` has a truth value at every extension of the
match by values, with the reading in I of each term it evaluates (`HoldsRead`), and one such
extension exists. Asked of I: the constructors' facts (`N`), not the soundness of `EvalTerm`. -/
theorem exs_values_hr (h : c.coreOK = true) (hrc : c.readsConfined = true) (hIc : I ⊧ᴵP Γc c)
    (N : NodeFacts c I) {cl : Clause} (hs : c.clauseExOK cl = true)
    (hb : Cond.bound c cl.vars.length cl.post = true) (hp : c.clausePlainEx cl = true)
    {σ : Subst} (hσ : c.WellSortedAt cl.vars cl.univ σ)
    (hsome : ∃ σ', AgreeOff (cl.exs.filter (!cl.leftVars.contains ·)) σ σ' ∧ c.WellSorted cl.vars σ')
    (hdec : ∀ σ', AgreeOff (cl.exs.filter (!cl.leftVars.contains ·)) σ σ' → c.WellSorted cl.vars σ' →
      ∃ b, HoldsRead c I cl.vars.length σ' cl.post b)
    {tbl : KoreAML.VarTable} {e : Valuation M} {S : Srt}
    (hag : ∀ i ∈ cl.univ, ∀ v, σ.lookup i = some v →
      ∀ m, m = e.evalEvar (tbl.ev (keyAt (canonVars c cl.vars) i)) ↔ (den c v).interpret I e m)
    (hin : ∀ i ∈ cl.exs, ∀ s, cl.vars[i]? = some s →
      (KoreAML.inhOf (sortP (c.sortName s))).interpret I e (e.evalEvar (tbl.ev (keyAt (canonVars c cl.vars) i))))
    (hkv : ∀ j, j < cl.vars.length → keyAt (canonVars c cl.vars) j ∈ tbl)
    (hk : ∀ k ∈ KoreAML.varsOf (Cond.kore c (canonVars c cl.vars) (srtOf c S) cl.post), k ∈ tbl)
    (hS : S < nRegSorts + c.sortNames.length)
    (hpost : ∃ a, (KoreAML.inhOf (KoreAML.trSort tbl (srtOf c S))).interpret I e a ∧
      (KoreAML.tr ⟨tbl, []⟩ (Cond.kore c (canonVars c cl.vars) (srtOf c S) cl.post)).interpret I e a) :
    ∀ i ∈ cl.exs, Witnessed c I tbl (canonVars c cl.vars) cl.vars e i := by
  have hI : I ⊧ᴵP Γ c := fun φ hφ => hIc φ (Or.inl hφ)
  simp only [Semantics.clauseExOK, Bool.and_eq_true] at hs
  obtain ⟨⟨⟨hlt, -⟩, hleft⟩, hok⟩ := hs
  have hlt : ∀ i ∈ cl.exs, i < cl.vars.length := fun i hi => of_decide_eq_true (List.all_eq_true.mp hlt i hi)
  have hfree : cl.exs.filter (!cl.leftVars.contains ·) = cl.exs :=
    List.filter_eq_self.mpr fun i hi => List.all_eq_true.mp hleft i hi
  rw [hfree] at hsome hdec
  have hsj : ∀ j, j < cl.vars.length → cl.vars[j]? = some (cl.vars.getD j 0) := fun j hj => by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]
  have huniv : ∀ j, j < cl.vars.length → j ∉ cl.exs → j ∈ cl.univ := fun j hj hne => by
    simp [Clause.univ, hj, hne]
  -- a variable that is not existential is at the element of σ's value
  have hunivV : ∀ j, j < cl.vars.length → j ∉ cl.exs → ∃ v, σ.lookup j = some v ∧
      c.sortOf v = some (cl.vars.getD j 0) ∧ elemOf c I v = e.evalEvar (tbl.ev (keyAt (canonVars c cl.vars) j)) :=
    fun j hj hne => by
      obtain ⟨v, hv, hsv⟩ := hσ j (huniv j hj hne) _ (hsj j hj)
      exact ⟨v, hv, hsv, (((elemOf_spec hI hsv e).1 _).mp ((hag j (huniv j hj hne) v hv _).mp rfl)).symm⟩
  have hunivW : ∀ j, j < cl.vars.length → j ∉ cl.exs → Witnessed c I tbl (canonVars c cl.vars) cl.vars e j :=
    fun j hj hne => by
      obtain ⟨v, -, hsv, hev⟩ := hunivV j hj hne
      exact ⟨v, hsv, hev⟩
  -- every variable in scope is at an element of its sort
  have hinAll : ∀ j, j < cl.vars.length →
      InS I (c.sortName (cl.vars.getD j 0)) (e.evalEvar (tbl.ev (keyAt (canonVars c cl.vars) j))) := fun j hj => by
    by_cases hje : j ∈ cl.exs
    · exact (inS_iff e).mp (hin j hje _ (hsj j hj))
    · obtain ⟨v, hsv, hev⟩ := hunivW j hj hje
      rw [← hev]
      exact (inS_iff e).mp (elemOf_spec hI hsv e).2
  -- a variable of a confined sort is at the element of a value
  have hconfW : ∀ j, j < cl.vars.length → (cl.vars[j]?.map c.confined).getD false = true →
      Witnessed c I tbl (canonVars c cl.vars) cl.vars e j := fun j hj hc => by
    rw [hsj j hj] at hc
    obtain ⟨v, hv, hd⟩ := confined_value h hrc hIc (by simpa using hc) e _ ((inS_iff e).mpr (hinAll j hj))
    exact ⟨v, hv, (((elemOf_spec hI hv e).1 _).mp ((hd _).mpr rfl)).symm⟩
  have hσ0 : ∃ σ', c.WellSorted cl.vars σ' := by
    obtain ⟨σ', -, hw⟩ := hsome
    exact ⟨σ', hw⟩
  -- `post` has a truth value at a substitution of values that agrees with the valuation on the
  -- variables that are not existential and is σ beyond the variables in scope: an extension of σ
  have hdecG : ∀ (ok : Nat → Bool), (∀ j, j < cl.vars.length → j ∉ cl.exs → ok j = true) → ∀ σ₁,
      (∀ j, cl.vars.length ≤ j → σ₁.lookup j = σ.lookup j) → c.WellSorted cl.vars σ₁ →
      AtElems c I tbl cl.vars e ok (fun _ => True) σ₁ → ∃ b, HoldsRead c I cl.vars.length σ₁ cl.post b := by
    intro ok hokU σ₁ htl hσ₁ hat
    refine hdec σ₁ (fun i hi => ?_) hσ₁
    by_cases hil : i < cl.vars.length
    · obtain ⟨v, hv, hsv, hev⟩ := hunivV i hil hi
      obtain ⟨v₁, hv₁, hev₁⟩ := hat i (hokU i hil hi) trivial hil
      have hev₁ : elemOf c I v₁ = e.evalEvar (tbl.ev (keyAt (canonVars c cl.vars) i)) := hev₁
      obtain ⟨v₁', hv₁', hsv₁⟩ := hσ₁ i _ (hsj i hil)
      rw [hv₁] at hv₁'; cases hv₁'
      have hd : (den c v₁).interpret I e (elemOf c I v) := by
        rw [hev, ← hev₁]
        exact ((elemOf_spec hI hsv₁ e).1 _).mpr rfl
      rw [hv₁, hv, N.apart hsv₁ hsv e _ hd (((elemOf_spec hI hsv e).1 _).mpr rfl)]
    · exact htl i (by omega)
  -- the rounds of `fixedExs`
  have key : ∀ (l acc : List Nat), (∀ i ∈ acc, Witnessed c I tbl (canonVars c cl.vars) cl.vars e i) →
      ∀ i ∈ l.foldl (fun acc _ =>
        cl.exs.filter fun i => acc.contains i ||
          Cond.fixes c.confined c.valued (fun j => !cl.exs.contains j || acc.contains j ||
            (j != i && (cl.vars[j]?.map c.confined).getD false)) i cl.vars.length cl.post) acc,
        Witnessed c I tbl (canonVars c cl.vars) cl.vars e i := by
    intro l
    induction l with
    | nil => intro acc hacc i hi; exact hacc i hi
    | cons _ l ih =>
      intro acc hacc
      rw [List.foldl_cons]
      refine ih _ fun i hi => ?_
      obtain ⟨hie, hcond⟩ := List.mem_filter.mp hi
      rw [Bool.or_eq_true] at hcond
      rcases hcond with hc | hfix
      · exact hacc i (List.contains_iff_mem.mp hc)
      · refine fixes_value_hr h hrc hIc N (val := c.valued) (fun _ => Semantics.valued_value) σ cl.post _ i cl.vars tbl e S
          hok (Cond.boundV_valued_of_bound c cl.post _ hb) hfix (hlt i hie) hσ0
          (hdecG _ fun j _ hne => by simp [hne]) (fun j hj hjl => ?_)
          (fun j hj => ⟨hkv j hj, hinAll j hj⟩) hk hS hpost
        simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hj
        rcases hj with (hj | hj) | hj
        · exact hunivW j hjl (by simpa using hj)
        · exact hacc j (List.contains_iff_mem.mp hj)
        · exact hconfW j hjl hj.2
  intro i hi
  simp only [Semantics.clausePlainEx, Bool.and_eq_true] at hp
  have hpi := List.all_eq_true.mp hp.2 i hi
  rw [Bool.or_eq_true] at hpi
  rcases hpi with hc | hf
  · exact hconfW i (hlt i hi) hc
  · exact key _ [] (fun _ hm => nomatch hm) i (List.contains_iff_mem.mp hf)

/-- **An element valuation that extends a match of values and satisfies `post` gives each
existential variable a value's element**, where `post` has a truth value at every extension of the
match by values and one such extension exists. -/
theorem exs_values (h : c.coreOK = true) (hrc : c.readsConfined = true) (hIc : I ⊧ᴵP Γc c)
    (hT : TermSound c I) {cl : Clause} (hs : c.clauseExOK cl = true)
    (hb : Cond.bound c cl.vars.length cl.post = true) (hp : c.clausePlainEx cl = true)
    {σ : Subst} (hσ : c.WellSortedAt cl.vars cl.univ σ)
    (hsome : ∃ σ', AgreeOff (cl.exs.filter (!cl.leftVars.contains ·)) σ σ' ∧ c.WellSorted cl.vars σ')
    (hdec : ∀ σ', AgreeOff (cl.exs.filter (!cl.leftVars.contains ·)) σ σ' → c.WellSorted cl.vars σ' →
      ∃ b, Holds c cl.vars.length σ' cl.post b)
    {tbl : KoreAML.VarTable} {e : Valuation M} {S : Srt}
    (hag : ∀ i ∈ cl.univ, ∀ v, σ.lookup i = some v →
      ∀ m, m = e.evalEvar (tbl.ev (keyAt (canonVars c cl.vars) i)) ↔ (den c v).interpret I e m)
    (hin : ∀ i ∈ cl.exs, ∀ s, cl.vars[i]? = some s →
      (KoreAML.inhOf (sortP (c.sortName s))).interpret I e (e.evalEvar (tbl.ev (keyAt (canonVars c cl.vars) i))))
    (hkv : ∀ j, j < cl.vars.length → keyAt (canonVars c cl.vars) j ∈ tbl)
    (hk : ∀ k ∈ KoreAML.varsOf (Cond.kore c (canonVars c cl.vars) (srtOf c S) cl.post), k ∈ tbl)
    (hS : S < nRegSorts + c.sortNames.length)
    (hpost : ∃ a, (KoreAML.inhOf (KoreAML.trSort tbl (srtOf c S))).interpret I e a ∧
      (KoreAML.tr ⟨tbl, []⟩ (Cond.kore c (canonVars c cl.vars) (srtOf c S) cl.post)).interpret I e a) :
    ∀ i ∈ cl.exs, Witnessed c I tbl (canonVars c cl.vars) cl.vars e i := by
  have F : AtomFacts c I := atomFacts_of_core h hIc hT
  exact exs_values_hr h hrc hIc F.node hs hb hp hσ hsome
    (fun σ' ha hw' => by
      obtain ⟨b, hb'⟩ := hdec σ' ha hw'
      exact ⟨b, HoldsReadT.of_holds F.termAt cl.post hb'⟩) hag hin hkv hk hS hpost

end ExsValues

end CE

end KCore
