/-
  KCore. What `coreOK` gives of the theory and of `OpenDecided` where a clause's patterns need not
  bind every variable.

  The statements below take what they need of the clauses as hypotheses (that each clause's
  patterns bind every variable is not read), and read of `sortedOK` only what it says of
  the rules and the clauses' predicates (`\top`): with no clause opening a variable, the definition
  reads no confined sort and its theory is `Γ` (`readsConfined_of_coreCl`, `Γc_coreCl`); with each
  clause's closed conditions decided where `needsWitness` holds, `OpenDecided` holds
  (`openDecided_of_sortedOKCl`, `openDecided_of_coreCl`). A definition that reads no confined sort
  has `OpenDecided` by `openDecided_of_readsConfined` (Obligations.lean).
-/
import KcoreSpec.Obligations

set_option autoImplicit false

namespace KCore

open Faithful

/-- **A semantics `coreOK` accepts, none of whose clauses has a variable its patterns do not bind,
reads no confined sort.** -/
theorem Semantics.readsConfined_of_coreCl {c : Semantics} (hpreTop : c.clausesPreTop = true) (h : c.coreOK = true) (hb : ∀ r ∈ c.rules, binds r.vars.length (varOccs r.lhs) = true) (htop : ∀ r ∈ c.rules, r.pre = .top ∧ r.post = .top)
    (hcl : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, cl.opens = []) : c.readsConfined = false := by
  have hok := (Semantics.coreOK_parts h).1
  simp only [Semantics.readsConfined, Bool.or_eq_false_iff, List.any_eq_false]
  refine ⟨fun r hr => ?_, fun fn hfn => ?_⟩
  · obtain ⟨hpre, hpost⟩ := htop _ hr
    simp [Rule.opens_of_binds (hb r hr), hpre, hpost, Cond.hasBinder]
  · simp only [List.any_eq_true, not_exists, not_and]
    intro cl hcl'
    have hpre := Semantics.clausesPreTop_spec hpreTop hfn hcl'
    have hpost := Semantics.sortedOK_clausePost hok hfn hcl'
      (Semantics.exs_nil_of_opens_nil (Semantics.sortedOK_clauseEx hok hfn hcl').1 (hcl fn hfn cl hcl'))
    simp [hcl fn hfn cl hcl', hpre, hpost, Cond.hasBinder]

/-- **The theory of such a semantics is `Γ`.** -/
theorem Γc_coreCl {c : Semantics} (hpreTop : c.clausesPreTop = true) (h : c.coreOK = true) (hb : ∀ r ∈ c.rules, binds r.vars.length (varOccs r.lhs) = true) (htop : ∀ r ∈ c.rules, r.pre = .top ∧ r.post = .top) (hcl : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, cl.opens = []) :
    Γc c = Γ c :=
  Γc_plain (Semantics.readsConfined_of_coreCl (hpreTop := hpreTop) h hb htop hcl)

/-- **`OpenDecided` of a semantics `sortedOK` accepts, where each clause's conditions are decided
when `needsWitness` holds**: no rule has an open variable. -/
theorem openDecided_of_sortedOKCl {c : Semantics} (h : c.sortedOK = true) (hb : ∀ r ∈ c.rules, binds r.vars.length (varOccs r.lhs) = true)
    (hcl : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, cl.needsWitness c = true → cl.CondDecided c) : OpenDecided c :=
  ⟨fun r hr hw => absurd hw (by rw [needsWitness_of_binds (hb _ hr)]; decide), hcl⟩

/-- **`OpenDecided` of a semantics `coreOK` accepts, where each clause's conditions are decided when
`needsWitness` holds.** -/
theorem openDecided_of_coreCl {c : Semantics} (h : c.coreOK = true) (hb : ∀ r ∈ c.rules, binds r.vars.length (varOccs r.lhs) = true)
    (hcl : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, cl.needsWitness c = true → cl.CondDecided c) : OpenDecided c :=
  openDecided_of_sortedOKCl (Semantics.coreOK_parts h).1 hb hcl

end KCore
