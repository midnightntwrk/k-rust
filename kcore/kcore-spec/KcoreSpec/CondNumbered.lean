/-
  KCore. The variables a well-sorted condition holds have numbered sorts.

  `condOK` asks the sort each atom of a condition names to be a numbered sort of the definition.
  A variable a condition holds occurs in a term of an atom, at the atom's sort (for an `exMatch`,
  in its term or its pattern), so its sort is numbered as the variables of any sorted term of a
  numbered sort are (`varOccs_numOpen`, `varOccs_num`); a binder extends the variable sorts and
  leaves the outer variables' sorts as they are.

  - `varOccsCond_numCN`: the free variables of a condition with `condOK` have numbered sorts.
  - `rule_vars_numCN`: every variable of a well-sorted rule has a numbered sort, its predicates
    `pre` and `post` arbitrary: the variables `rule_vars_numEx` reads (left side, `requires`, right
    side, `ensures`) and those held only by `pre` or `post`.
-/
import KcoreSpec.OpenModel

set_option autoImplicit false

namespace KCore

namespace Faithful

namespace Model

open ML

variable {c : Semantics}

/-- **The free variables of a well-sorted condition have numbered sorts.** -/
theorem varOccsCond_numCN (h : HypModelCore c) : ∀ (p : Cond) {vars : List Srt}, c.condOK vars p = true →
    ∀ i ∈ varOccsCond vars.length p, ∀ s', vars[i]? = some s' → s' < nRegSorts + c.sortNames.length
  | .top, _, _, i, hi, _, _ => by simp [varOccsCond] at hi
  | .bot, _, _, i, hi, _, _ => by simp [varOccsCond] at hi
  | .not p, vars, hok, i, hi, s', hs' => by
    rw [Semantics.condOK] at hok; rw [varOccsCond] at hi
    exact varOccsCond_numCN h p hok i hi s' hs'
  | .and p q, vars, hok, i, hi, s', hs' | .or p q, vars, hok, i, hi, s', hs'
  | .implies p q, vars, hok, i, hi, s', hs' => by
    rw [Semantics.condOK, Bool.and_eq_true] at hok; rw [varOccsCond, List.mem_append] at hi
    rcases hi with hi | hi
    · exact varOccsCond_numCN h p hok.1 i hi s' hs'
    · exact varOccsCond_numCN h q hok.2 i hi s' hs'
  | .ceil s t, vars, hok, i, hi, s', hs' => by
    simp only [Semantics.condOK, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hok
    rw [varOccsCond] at hi
    exact varOccs_numOpen h (fun k hk => rhsHead_kernel fns_headsOK hk) (fun _ _ h' => h') t hok.1 hok.2
      i hi s' hs'
  | .equals s t u, vars, hok, i, hi, s', hs' | .mem s t u, vars, hok, i, hi, s', hs' => by
    simp only [Semantics.condOK, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hok
    obtain ⟨⟨ht, hu⟩, hn⟩ := hok
    rw [varOccsCond, List.mem_append] at hi
    rcases hi with hi | hi
    · exact varOccs_numOpen h (fun k hk => rhsHead_kernel fns_headsOK hk) (fun _ _ h' => h') t ht hn
        i hi s' hs'
    · exact varOccs_numOpen h (fun k hk => rhsHead_kernel fns_headsOK hk) (fun _ _ h' => h') u hu hn
        i hi s' hs'
  | .exMatch ys s p t body, vars, hok, i, hi, s', hs' => by
    simp only [Semantics.condOK, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hok
    obtain ⟨⟨⟨hp, ht⟩, hb⟩, hn⟩ := hok
    rw [varOccsCond, List.mem_append] at hi
    rcases hi with hi | hi
    · exact varOccs_numOpen h (fun k hk => rhsHead_kernel fns_headsOK hk) (fun _ _ h' => h') t ht hn
        i hi s' hs'
    · obtain ⟨hi, hlt⟩ := List.mem_filter.mp hi
      have hlt : i < vars.length := by simpa using hlt
      have hs'' : (vars ++ ys)[i]? = some s' := by rw [List.getElem?_append_left hlt]; exact hs'
      rcases List.mem_append.mp hi with hi | hi
      · exact varOccs_num h p (sortOfTerm_all_of_nf hp) hn i hi s' hs''
      · have hi' : i ∈ varOccsCond (vars ++ ys).length body := by rw [List.length_append]; exact hi
        exact varOccsCond_numCN h body hb i hi' s' hs''
  | .ex s body, vars, hok, i, hi, s', hs' | .all s body, vars, hok, i, hi, s', hs' => by
    rw [Semantics.condOK] at hok; rw [varOccsCond] at hi
    obtain ⟨hi, hlt⟩ := List.mem_filter.mp hi
    have hlt : i < vars.length := by simpa using hlt
    have hs'' : (vars ++ [s])[i]? = some s' := by rw [List.getElem?_append_left hlt]; exact hs'
    have hi' : i ∈ varOccsCond (vars ++ [s]).length body := by
      rw [List.length_append, List.length_singleton]; exact hi
    exact varOccsCond_numCN h body hok i hi' s' hs''

/-- **Every variable of a well-sorted rule has a numbered sort**, whatever its predicates: each
occurs in its left side, `requires`, `pre`, right side, `ensures` or `post`, each of them sorted at
a numbered sort (`condOK` for the predicates). -/
theorem rule_vars_numCN (h : HypModelCore c) {r : Rule} (hs : c.ruleSorted r = true) :
    ∀ i < r.vars.length, r.vars.getD i 0 < nRegSorts + c.sortNames.length := by
  obtain ⟨hlhs, hreqK, hensK, hrhs⟩ := Semantics.ruleSorted_parts c hs
  have hs' := hs
  simp only [Semantics.ruleSorted, Bool.and_eq_true] at hs'
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, hb⟩, -⟩, -⟩, -⟩, hokP⟩, -⟩, hokQ⟩, -⟩, -⟩, -⟩ := hs'
  have hx : ∀ k ∈ (c.rhsCtx (c.fns.map Fn.sig)).heads, k ∈ kernelSyms c := fun k hk => rhsHead_kernel fns_headsOK hk
  have hsub : ∀ a b, (a, b) ∈ (c.rhsCtx (c.fns.map Fn.sig)).subs → (a, b) ∈ c.subsorts := fun _ _ h' => h'
  intro i hi
  have hg : r.vars[i]? = some (r.vars.getD i 0) := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; rfl
  have hocc := List.all_eq_true.mp hb i (List.mem_range.mpr hi)
  simp only [Rule.condVars, List.contains_iff_mem, List.mem_append] at hocc
  have hterm : ∀ (q : Option Term), reqOK (c.rhsCtx (c.fns.map Fn.sig)) r.vars q = true →
      i ∈ (q.map varOccs).getD [] → r.vars.getD i 0 < nRegSorts + c.sortNames.length := by
    intro q hq hiq
    cases q with
    | none => cases hiq
    | some t =>
      have ht : sortOfTerm (c.rhsCtx (c.fns.map Fn.sig)) r.vars t = some Srt.bool := by simpa [reqOK] using hq
      exact varOccs_numOpen h hx hsub t ht bool_numbered i hiq _ hg
  rcases hocc with ((((hL | hQ | hP) | hR) | hE) | hPo)
  · exact varOccs_num h r.lhs hlhs top_numbered i hL _ hg
  · exact hterm r.req hreqK hQ
  · exact varOccsCond_numCN h r.pre hokP i hP _ hg
  · exact varOccs_numOpen h hx hsub r.rhs hrhs top_numbered i hR _ hg
  · exact hterm r.ens hensK hE
  · exact varOccsCond_numCN h r.post hokQ i hPo _ hg

end Model

end Faithful

end KCore
