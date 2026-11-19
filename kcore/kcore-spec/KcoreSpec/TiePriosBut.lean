/-
  KCore, outside the cone: `AttrsAgree.prios` with named sentences left out of its text side and
  named clauses left out of its clause side (`AttrsAgree.priosBut`).

  `prios` compares the priorities the text's attributes state with the clauses' priorities. Two
  kinds of item are compared there with nothing that speaks of them:
  - a sentence of the text that is an equation with a function at its head and that the definition
    holds as no clause of it (a user's instance of a generated sort predicate's clause), so its
    priority answers no clause;
  - a clause whose priority a reading gives and no attribute states (the clause read from a
    selector-domain axiom, of priority 200; the clause read from an overload axiom, of priority 0),
    so its priority answers no attribute.
  `priosBut outAx outCl k d` is `prios k d` with the sentences of `k` whose index is in `outAx`
  left out of the text side, and, for each function, the clauses at the positions `outCl` names
  for its name left out of the clause side. With nothing left out it is `prios` (`priosBut_nil`).
  Leaving an item out only removes it from the comparison: what is left out is not shown to agree
  here, and a tie that states `priosBut` true names, for each item left out, the theorem that ties
  it to its sentence.
-/
import KcoreSpec.TieDefs

set_option autoImplicit false

namespace KCore

namespace AttrsAgree

/-- The text's equations of the symbol `n` (`eqnsOf`'s test), among the sentences of `k` whose
index (`AxiomDecl.index`) is not in `outAx`. -/
def eqnsOfBut (outAx : List Nat) (k : Kore.Definition) (n : String) : List Kore.Axiom :=
  ((k.axiomDecls.filter fun ad => !outAx.contains ad.index).map (·.ax)).filter fun a =>
    eqnHeadIs n a.pattern && !isLaw a && !has a.attributes "simplification"

/-- The clauses `cls` of the function named `n`, without those at the positions `outCl` names for
`n` (a pair `(n, i)` names the clause at position `i` of `n`'s clause list). -/
def clausesBut (outCl : List (String × Nat)) (n : String) (cls : List Clause) : List Clause :=
  (cls.zipIdx.filter fun (_, i) => !outCl.contains (n, i)).map (·.1)

/-- **`prios` with named items left out**: the rules' priorities as `prios` reads them, and for
each function the priorities the text's equations of it state (`eqnsOfBut`: without the sentences
whose index is in `outAx`) against its clauses' (`clausesBut`: without the clauses `outCl` names
for its name), as lists up to order. -/
def priosBut (outAx : List Nat) (outCl : List (String × Nat)) (k : Kore.Definition) (d : Definition) :
    Bool :=
  let c := d.sem
  let axs := k.axiomDecls.map (·.ax)
  d.pres.rules.length == c.rules.length &&
  ((c.rules.zip d.pres.rules).all fun (r, rp) => rewritePrioOf k rp.info.uid == some r.prio) &&
  ((axs.filter (isRewrite ·.pattern)).all fun a => d.pres.rules.any fun rp => uidOf a.attributes == some rp.info.uid) &&
  c.allFns.all fun f =>
    ((eqnsOfBut outAx k (c.symName f.label)).map (prioOf ·.attributes)).isPerm
      ((clausesBut outCl (c.symName f.label) f.clauses).map (·.prio))

theorem eqnsOfBut_nil (k : Kore.Definition) (n : String) : eqnsOfBut [] k n = eqnsOf k n := by
  simp only [eqnsOfBut, eqnsOf, List.contains_nil, Bool.not_false]
  rw [List.filter_eq_self.mpr fun _ _ => rfl]

theorem clausesBut_nil (n : String) (cls : List Clause) : clausesBut [] n cls = cls := by
  simp only [clausesBut, List.contains_nil, Bool.not_false]
  rw [List.filter_eq_self.mpr fun _ _ => rfl]
  exact List.zipIdx_map_fst 0 cls

/-- With nothing left out, `priosBut` is `prios`. -/
theorem priosBut_nil (k : Kore.Definition) (d : Definition) : priosBut [] [] k d = prios k d := by
  simp only [priosBut, prios, eqnsOfBut_nil, clausesBut_nil]

end AttrsAgree

end KCore
