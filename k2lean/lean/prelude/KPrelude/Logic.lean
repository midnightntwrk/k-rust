/-! Logic lemmas for the generated proofs that the core simp set lacks. -/

namespace KPrelude

/-- An existential over a proof of `False` is false. Simp rewrites a leaf condition
`leafOK s l = true` to `False` inside the binder of `∃ h : leafOK s l = true, …` (the
unfolding of a projection `if h : leafOK s l = true then some (Term.inj … h x) else none` of the
arity-indexed universe), but the core simp set has no lemma for the dependent existential that
remains; without it the per-rule determinism lemmas' `repeat' (k2l_split_hyps <;> try simp_all)`
re-splits the same `if` forever. -/
@[simp] theorem exists_false_dom {p : False → Prop} : (∃ h : False, p h) ↔ False :=
  ⟨fun ⟨h, _⟩ => h, False.elim⟩

end KPrelude
