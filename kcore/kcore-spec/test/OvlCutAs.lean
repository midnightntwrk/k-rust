/-
  The cut of an application whose arguments hold `#as` (`Parse.cutOvlApps`, `Parse.cutAsBinds`),
  on literal terms. Run from the package root: `lake env lean test/OvlCutAs.lean`.

  `p #as Z` is `p ∧ Z`: Z's element where it is in p, nothing elsewhere. An application is pointwise
  over its arguments' elements and empty at an empty argument, so `g(…, D[p ∧ Z], …)` is
  `g(…, D[Z], …) ∧ Z ∈ p`: the membership of the cut holds Z in the alias's place, and `Z ∈ p` (at
  Z's sort) is a further conjunct after it, p read the same way (a nested alias its own conjunct,
  after the one whose term holds it). An alias outside the cut application stays in the term.
-/
import KcoreSpec

set_option autoImplicit false

open KCore KoreAML

/-- Two user sorts A and B and an open generator `and : A A → B` (symbol 7); symbol 8 stands for a
constructor, 9 for another symbol. -/
def cutAsN : Parse.Names :=
  { sorts := ["A", "B"], syms := [], openCutSyms := [(7, "B")] }

def cutAsA : Srt := (cutAsN.srt? "A").getD 0
def cutAsB : Srt := (cutAsN.srt? "B").getD 0

/-- What a cut gives, printed: the term, the variables with their sorts' names, the condition. -/
def cutAsStr {α : Type} [Repr α] (x : Parse.Rd (α × List Var × Cond)) : String :=
  match x with
  | .ok (t, vs, p) => s!"{repr t} {vs.map (fun v => (v.name, v.sort))} {repr p}"
  | .error f => s!"error {f.detail}"

/-! A and B are user sorts, apart. -/
#guard cutAsA != cutAsB && (cutAsN.srt? "A").isSome && (cutAsN.srt? "B").isSome

/-! A rule's left side `c((X #as Z) & Y)`: `c(Open0)`, pre `Open0 ∈ and(Z, Y) ∧ Z ∈ X`. -/
#guard cutAsStr (Parse.ovlCut cutAsN (.app 8 [.app 7 [.as (.var 0) 1, .var 2]])
    [⟨"X", "A"⟩, ⟨"Z", "A"⟩, ⟨"Y", "A"⟩]) ==
  cutAsStr (pure (Term.app 8 [.var 3], [⟨"X", "A"⟩, ⟨"Z", "A"⟩, ⟨"Y", "A"⟩, ⟨"Open0", "B"⟩],
    Cond.and (.mem cutAsB (.var 3) (.app 7 [.var 1, .var 2])) (.mem cutAsA (.var 1) (.var 0))) : Parse.Rd _)

/-! A nested alias `c(((X #as W) #as Z) & Y)`: `Open0 ∈ and(Z, Y) ∧ Z ∈ W ∧ W ∈ X`. -/
#guard cutAsStr (Parse.ovlCut cutAsN (.app 8 [.app 7 [.as (.as (.var 0) 1) 2, .var 3]])
    [⟨"X", "A"⟩, ⟨"W", "A"⟩, ⟨"Z", "A"⟩, ⟨"Y", "A"⟩]) ==
  cutAsStr (pure (Term.app 8 [.var 4],
    [⟨"X", "A"⟩, ⟨"W", "A"⟩, ⟨"Z", "A"⟩, ⟨"Y", "A"⟩, ⟨"Open0", "B"⟩],
    Cond.and (.mem cutAsB (.var 4) (.app 7 [.var 2, .var 3]))
      (.and (.mem cutAsA (.var 2) (.var 1)) (.mem cutAsA (.var 1) (.var 0)))) : Parse.Rd _)

/-! A clause's pattern `X & (Y #as Z)` (`Parse.ovlCutList`): `[Open0]`, pre
`Open0 ∈ and(X, Z) ∧ Z ∈ Y`. -/
#guard cutAsStr (Parse.ovlCutList cutAsN [.app 7 [.var 0, .as (.var 1) 2]]
    [⟨"X", "A"⟩, ⟨"Y", "A"⟩, ⟨"Z", "A"⟩]) ==
  cutAsStr (pure ([Term.var 3], [⟨"X", "A"⟩, ⟨"Y", "A"⟩, ⟨"Z", "A"⟩, ⟨"Open0", "B"⟩],
    Cond.and (.mem cutAsB (.var 3) (.app 7 [.var 0, .var 2])) (.mem cutAsA (.var 2) (.var 1))) : Parse.Rd _)

/-! An alias outside the application, `(X & Y) #as Z`: the alias stays in the term, around the
cut's variable; the membership holds no binding. -/
#guard cutAsStr (Parse.ovlCut cutAsN (.as (.app 7 [.var 0, .var 1]) 2)
    [⟨"X", "A"⟩, ⟨"Y", "A"⟩, ⟨"Z", "B"⟩]) ==
  cutAsStr (pure (Term.as (.var 3) 2, [⟨"X", "A"⟩, ⟨"Y", "A"⟩, ⟨"Z", "B"⟩, ⟨"Open0", "B"⟩],
    Cond.mem cutAsB (.var 3) (.app 7 [.var 0, .var 1])) : Parse.Rd _)

/-! An alias under an injection and another symbol, and an alias of an inner application of the
generator (which stays in the binding's term, evaluated): the bindings left to right. -/

/--
info: (Term.app 8 [Term.var 6], 7,
  [(6, "B", Term.app 7 [Term.inj 1 2 (Term.app 9 [Term.var 1]), Term.var 3],
      [(1, Term.var 0), (3, Term.app 7 [Term.var 4, Term.var 5])])])
-/
#guard_msgs in
#eval Parse.cutOvlApps [(7, "B")] 6
  (.app 8 [.app 7 [.inj 1 2 (.app 9 [.as (.var 0) 1]), .as (.app 7 [.var 4, .var 5]) 3]])
