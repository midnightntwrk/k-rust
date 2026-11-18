/-
  The extension of a model of the theory without the detached names satisfies the functions'
  premises, and with them the rules', the step's closure, the domains', the fallbacks' and the
  closure axiom of Bool, where they name nothing of `D` (KcoreSpec/ConsTransferFns.lean): the
  statements exist as stated and depend on no axiom but `propext`, `Classical.choice` and
  `Quot.sound`. Run from the package root: `lake env lean test/ConsTransferFns.lean`.
-/
import KcoreSpec.ConsTransferFns

open KCore KCore.Cons ML Faithful

example {c : Semantics} {D : KoreAML.Sym → Prop} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
    (hD : ∀ σ, D σ → plainSym σ) (hI : I ⊧ᴵP Γown c D)
    (hne : ∃ τ, KoreAML.IsSort I τ ∧ ∃ m, KoreAML.Inh I τ m)
    (hsig : ∀ fn ∈ c.allFns, ∀ s ∈ fn.result :: fn.args, s < nRegSorts + c.sortNames.length)
    (hvars : ∀ fn ∈ c.allFns, ∀ cl ∈ fn.clauses, ∀ s ∈ cl.vars, s < nRegSorts + c.sortNames.length)
    (hpre : ∀ fn ∈ c.allFns, ∀ cl ∈ fn.clauses, cl.pre = .top)
    (hexs : ∀ fn ∈ c.allFns, ∀ cl ∈ fn.clauses, cl.exs = [])
    {φ : KoreAML.P} (hφ : ΓFns c φ) (hn : ∀ σ ∈ psyms φ, ¬ D σ) : extModel c D I ⊧ᴵ φ :=
  sat_own_fns hD hI hne hsig hvars hpre hexs hφ hn

example {c : Semantics} {D : KoreAML.Sym → Prop} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
    (hD : ∀ σ, D σ → plainSym σ) (hI : I ⊧ᴵP Γown c D)
    (hne : ∃ τ, KoreAML.IsSort I τ ∧ ∃ m, KoreAML.Inh I τ m)
    (hsig : ∀ fn ∈ c.allFns, ∀ s ∈ fn.result :: fn.args, s < nRegSorts + c.sortNames.length)
    (hvars : ∀ fn ∈ c.allFns, ∀ cl ∈ fn.clauses, ∀ s ∈ cl.vars, s < nRegSorts + c.sortNames.length)
    (hpre : ∀ fn ∈ c.allFns, ∀ cl ∈ fn.clauses, cl.pre = .top)
    (hexs : ∀ fn ∈ c.allFns, ∀ cl ∈ fn.clauses, cl.exs = [])
    {φ : KoreAML.P}
    (hφ : ΓFns c φ ∨ ΓRules c φ ∨ Γstep c φ ∨ ΓDomains c φ ∨ ΓFallback c φ ∨ Γcl c φ)
    (hn : ∀ σ ∈ psyms φ, ¬ D σ) : extModel c D I ⊧ᴵ φ :=
  sat_own_fns_rules hD hI hne hsig hvars hpre hexs hφ hn

/-- A competitor's exclusion binds its variables under the equation's own names: the pattern of a
clause's equation is of the class whatever the clauses before it are. -/
example {c : Semantics} {S : String → Prop} (hB : S ("Sort" ++ "Bool")) {f : Fn} {cl : Clause}
    (ha : ∀ s ∈ f.result :: f.args, S ("Sort" ++ c.sortName s))
    (hv : ∀ cl' ∈ f.clauses, ∀ s ∈ cl'.vars, S ("Sort" ++ c.sortName s))
    (hpre : ∀ cl' ∈ f.clauses, cl'.pre = .top) (hcl : cl ∈ f.clauses) (hexs : cl.exs = []) :
    ∃ P, prioEquation c f cl = .axiom { sortVars := [KoreAML.Rv], pattern := P, attributes := [] } ∧
      RFrag S P ∧ KoreAML.sortOf [] P = some KoreAML.R :=
  rfrag_prioEquation_fn hB ha hv hpre hcl hexs

/-- info: 'KCore.Cons.sat_own_fns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms sat_own_fns

/-- info: 'KCore.Cons.sat_own_fns_rules' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms sat_own_fns_rules
