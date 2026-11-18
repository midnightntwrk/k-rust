/-
  Function equations whose variables the arguments do not bind, through the reader, on K 7.1.337
  kompile's own texts. Run from the package root: `lake env lean -j1 test/B1bClauses.lean`.
  Kernel-checked (`decide +kernel`) where a fact is about the semantics.

  - `cooleq` (fixture e2-cool-eq): `f(X) => X [cool]`, written `requires true andBool
    isKResult(HOLE:K)`: `wf` true; the equation read, the second sentence (`[simplification, cool]`)
    `inert simplification`; the clause owes its `CondDecided` (HOLE of K, unconfined).
  - `openh` (F1-DECISION 7.3's title clause, `f() => 0 requires 1 ==Int 2 *Int H`) and `clgenless`
    (fixture e2-clause-genless-arg, `f(_) => 1 requires isC(H:S)` beside `f(_) => 0 [owise]`):
    each read with `coreOK`, its clause's `CondDecided` owed (`owedClauses`; neither is
    `Witnessed`: test/ClauseOpenCond.lean). The pinned `sound_at` is stated for each only under the
    owed fact as a hypothesis, named with its clause (`hc_of_owed`). At `openh` the owed fact is
    open. At `clgenless` it is false (`KCore.TieClauseGenless.owed_false`), so `Genless.Owed` does
    not hold and the statement under it is vacuous; soundness itself fails there
    (`KCore.TieClauseGenless.step_not_sound`).
  - `rhsempty` (fixture e2-clause-rhs-empty, `f() => g(Y:Empty)`): read with `coreOK`; `f` is
    held-named (`Semantics.heldObligations`), Empty having no value, so `rightValued` is false.
  - `rhsunit` (e2-clause-rhs-unit, `f() => h(Y:U)`, `U ::= "u"`) and `rhsint` (e2-clause-rhs-int,
    `f() => c(Y:Int)`): read with `coreOK` and `rightValued`, `MatchIndependent` of the clause named
    (`matchObligations`, `matchObligationsL`), none owed.
  The peer-shadowed clause (a right-only variable of a sort without a value beside a clause of the
  same priority that decides) at a semantics with `coreOK` and `rightValued` false is
  test/OpenClausePins.lean's `c3` (`shape`); test/RightOnly.lean's `cEA` has the same clauses over a
  hand-written vocabulary that is not `coreOK` (`faithCoreOK` and `idsOK` fail there with or
  without the clause).
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

open KCore

namespace B1bClauses

/-- The reader's verdict on the text at `path`: `wf` and `coreOK`, or the refusal. -/
def verdict (path : String) : IO String := do
  match Kore.parseDefinition (← IO.FS.readFile path) with
  | .error e => return s!"KORE read error {e}"
  | .ok k => return match Parse.parse k with
    | .error r => s!"refused {r.reason.name} {r.detail}"
    | .ok d => s!"wf {wf d}, coreOK {d.sem.coreOK}"

/-- The classes of the user module's axioms that apply `f`. -/
def fClasses (path : String) : IO String := do
  match Kore.parseDefinition (← IO.FS.readFile path) with
  | .error e => return s!"KORE read error {e}"
  | .ok k =>
    let ss := (k.modules.getLast?.map (·.sentences)).getD []
    return toString <| ss.filterMap fun s => match s with
      | .axiom a => if ((Parse.canon a.pattern).splitOn "Lblf{}").length > 1 then some (Parse.classifyShape s).name else none
      | _ => none

/--
info: cooleq: wf true, coreOK true
openh: wf true, coreOK true
clgenless: wf true, coreOK true
rhsempty: wf true, coreOK true
rhsunit: wf true, coreOK true
rhsint: wf true, coreOK true
cooleq, the axioms applying f: [read, inert simplification]
-/
#guard_msgs in
#eval show IO Unit from do
  for n in ["cooleq", "openh", "clgenless", "rhsempty", "rhsunit", "rhsint"] do
    IO.println s!"{n}: {← verdict s!"f2-examples/{n}.kompile.kore"}"
  IO.println s!"cooleq, the axioms applying f: {← fClasses "f2-examples/cooleq.kompile.kore"}"

/-! ## e2-cool-eq -/

namespace Cool

definition_of defn from "f2-examples/cooleq.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem

/-- `f`'s one clause owes its `CondDecided`, over HOLE (index 1); no rule owes. -/
example : c.coreOK = true ∧ c.owedClauses = [(0, 0)] ∧ Parse.owedClauseCondDecided c = [(0, 0, [1])] ∧
    c.owedRules = [] ∧ (c.fns.map fun fn => c.symName fn.label) = ["Lblf"] := by
  decide_cheap

end Cool

/-! ## The title clause and the genless clause: admitted, `CondDecided` owed -/

namespace Title

definition_of defn from "f2-examples/openh.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem

theorem shape : c.coreOK = true ∧ c.owedClauses = [(0, 0)] ∧ Parse.owedClauseCondDecided c = [(0, 0, [0])] ∧
    c.owedRules = [] ∧ (c.fns.map fun fn => c.symName fn.label) = ["Lblf"] ∧
    c.rules.all (fun r => !r.needsWitness c) = true := by
  decide_cheap

/-- The owed fact: the condition of `f`'s clause (function 0, clause 0) is decided. -/
def Owed : Prop := ∀ fn, c.fns[0]? = some fn → ∀ cl, fn.clauses[0]? = some cl → cl.CondDecided c

/-- **The clauses' hypothesis of the pinned statements from the owed fact** (`openClauses_of_owed`). -/
theorem hc_of_owed (hH : Owed) :
    ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, cl.needsWitness c = true → cl.CondDecided c :=
  openClauses_of_owed (by
    rw [shape.2.1]
    intro p hp
    cases List.mem_singleton.mp hp
    exact hH)

/-- **`sound_at` at the text, under the owed fact**; no rule needs a witness. -/
example (hH : Owed) (x y : Config c) (r : Rule) (σ : Subst) (hs : StepBy c r σ x y) :
    (Faithful.Γc c ⊧ (den c x.val ⇒ KoreAML.sNext (Faithful.famEx c r σ))) ∧
      (Faithful.Γc c ⊧ (den c y.val ⇒ Faithful.famEx c r σ)) :=
  sound_at c shape.1 x y r σ hs
    (fun r' hr' _ hw _ => absurd hw (by
      have := List.all_eq_true.mp shape.2.2.2.2.2 r' hr'
      simpa using this))
    (hc_of_owed hH)

end Title

namespace Genless

definition_of defn from "f2-examples/clgenless.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem

theorem shape : c.coreOK = true ∧ c.owedClauses = [(0, 0)] ∧ Parse.owedClauseCondDecided c = [(0, 0, [1])] ∧
    c.owedRules = [] ∧ (c.fns.map fun fn => c.symName fn.label) = ["Lblf", "LblisC"] ∧ c.confined 32 = false ∧
    c.rules.all (fun r => !r.needsWitness c) = true := by
  decide_cheap

/-- The owed fact: the condition of `f`'s first clause is decided. -/
def Owed : Prop := ∀ fn, c.fns[0]? = some fn → ∀ cl, fn.clauses[0]? = some cl → cl.CondDecided c

theorem hc_of_owed (hH : Owed) :
    ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, cl.needsWitness c = true → cl.CondDecided c :=
  openClauses_of_owed (by
    rw [shape.2.1]
    intro p hp
    cases List.mem_singleton.mp hp
    exact hH)

/-- **`sound_at` at the text, under the owed fact.** -/
example (hH : Owed) (x y : Config c) (r : Rule) (σ : Subst) (hs : StepBy c r σ x y) :
    (Faithful.Γc c ⊧ (den c x.val ⇒ KoreAML.sNext (Faithful.famEx c r σ))) ∧
      (Faithful.Γc c ⊧ (den c y.val ⇒ Faithful.famEx c r σ)) :=
  sound_at c shape.1 x y r σ hs
    (fun r' hr' _ hw _ => absurd hw (by
      have := List.all_eq_true.mp shape.2.2.2.2.2.2 r' hr'
      simpa using this))
    (hc_of_owed hH)

end Genless

/-! ## Right-only variables of a sort with a value -/

namespace Unit

definition_of defn from "f2-examples/rhsunit.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem

/-- `f() => h(Y:U)`: `coreOK` and `rightValued`; `MatchIndependent` of the clause named; none owed. -/
example : c.coreOK = true ∧ c.rightValued = true ∧ (c.fns.map fun fn => c.symName fn.label) = ["Lblf"] ∧
    (c.matchObligations.map fun p => (c.symName p.1, p.2)) = [("Lblf", 0)] ∧
    (c.matchObligationsL.map fun p => (c.symName p.1, p.2)) = [("Lblf", 0)] ∧
    c.owedClauses = [] ∧ c.owedRules = [] := by
  decide_cheap

theorem rh : c.RightHeld := Semantics.rightHeld_of_valued (by decide +kernel)

end Unit

namespace IntRhs

definition_of defn from "f2-examples/rhsint.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem

/-- `f() => c(Y:Int)`: `coreOK` and `rightValued`; `MatchIndependent` of the clause named (it is
false: Y = 0 and Y = 1 give `c(0)` and `c(1)`, test/RightOnly.lean's `not_matchIndependent_I`). -/
example : c.coreOK = true ∧ c.rightValued = true ∧ (c.fns.map fun fn => c.symName fn.label) = ["Lblf"] ∧
    (c.matchObligations.map fun p => (c.symName p.1, p.2)) = [("Lblf", 0)] ∧
    (c.matchObligationsL.map fun p => (c.symName p.1, p.2)) = [("Lblf", 0)] ∧
    c.owedClauses = [] ∧ c.owedRules = [] := by
  decide_cheap

end IntRhs

end B1bClauses
