/-
  A function equation's left side and its premise's memberships (FIX-core.setvar-eq-refuse).
  Run from the package root: `lake env lean test/SetVarLhs.lean`.

  kompile writes `rule f(@S, @S) => r()` as `(X0 ∈ @S ∧ X1 ∈ @S) → f(X0, X1) = r()`: the left side
  applies f to the element variables the memberships bind, and the reader takes the memberships'
  patterns as the clause's (`Parse.rawEqn?`, `argPats`). It reads the sentence so only where the
  left side's arguments are exactly those variables, distinct and in order (`lhsArgsOK_lhs`).
  - `f2-examples/svnonlinear.kompile.kore` (e3-setvar-nonlinear), the kept control: read, the
    memberships dropped (`setVarInDropped`), the clause of f with two patterns;
  - `hw-scope-setvar-eq-memb` (the same text, the left side `f(@VarS, @VarS)`, the memberships
    kept) and `hw-scope-setvar-eq` (the direct form, the memberships removed): refused
    `setVariable`, the detail naming the variable and the function (`lhsSetVar?`). The sentence
    states f(a, a) = r and, at a ≠ b, only that f(a, b) is r or undefined; read as the clause
    f(X0, X1) = r it stated f(a, b) = r (before this change, the first was so read, the second as a
    clause of f with no patterns);
  - the control with the left side `f(X1, X0)` and with `f(X0, X0)`: no equation is read from the
    sentence (refused `axiomShape`): the first states f at the swapped pair, the second f(a, a) = r
    alone, and the clause read from the memberships would state f(a, b) = r at every pair.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

open KCore

/-- The equation of `Lblf` with its left side's arguments `ls` replaced by `ed ls`. -/
def editLhs (ed : List Kore.Pattern → List Kore.Pattern) (k : Kore.Definition) : Kore.Definition :=
  let edit : Kore.Pattern → Kore.Pattern
    | .implies s p (.equals s₁ s₂ (.app f [] ls) r) =>
      if f.ident.name == "Lblf" then .implies s p (.equals s₁ s₂ (.app f [] (ed ls)) r)
      else .implies s p (.equals s₁ s₂ (.app f [] ls) r)
    | p => p
  let sent := fun (s : Kore.Sentence) => match s with
    | .axiom a => .axiom { a with pattern := edit a.pattern }
    | s => s
  { k with modules := k.modules.dropLast ++
      (k.modules.getLast?.map fun m => [{ m with sentences := m.sentences.map sent }]).getD [] }

/-- The reader's verdict on the text at `path` (edited by `edit`): "read" with the number of
patterns of f's clauses, or the refusal with its detail. -/
def verdict (path : String) (edit : Kore.Definition → Kore.Definition := id) : IO String := do
  match Kore.parseDefinition (← IO.FS.readFile path) with
  | .error e => return s!"KORE read error {e}"
  | .ok k =>
    let k := edit k
    return match Parse.parse k with
    | .ok d =>
      let f := d.sem.fns.find? fun f => d.sem.symName f.label == "Lblf"
      s!"read; f's clauses' patterns {(f.map fun f => f.clauses.map (·.pats.length)).getD []}; \
        coreOK {d.sem.coreOK}"
    | .error r => if r.detail.isEmpty then r.reason.name else s!"{r.reason.name}: {r.detail}"

/--
info: read; f's clauses' patterns [2]; coreOK true
setVariable: VarS: an argument of Lblf on the equation's left side: the sentence states Lblf at every set's elements, at a set of two elements a, b only that Lblf(a, b) is the right side or undefined; no clause states that
setVariable: VarS: an argument of Lblf on the equation's left side: the sentence states Lblf at every set's elements, at a set of two elements a, b only that Lblf(a, b) is the right side or undefined; no clause states that
axiomShape
axiomShape
-/
#guard_msgs in
#eval show IO Unit from do
  IO.println (← verdict "f2-examples/svnonlinear.kompile.kore")
  IO.println (← verdict "test/constructs/fixtures/hw-scope-setvar-eq-memb/hw-scope-setvar-eq-memb.kore")
  IO.println (← verdict "test/constructs/fixtures/hw-scope-setvar-eq/hw-scope-setvar-eq.kore")
  IO.println (← verdict "f2-examples/svnonlinear.kompile.kore" (editLhs List.reverse))
  IO.println (← verdict "f2-examples/svnonlinear.kompile.kore"
    (editLhs fun ls => ls.take 1 ++ ls.take 1))
