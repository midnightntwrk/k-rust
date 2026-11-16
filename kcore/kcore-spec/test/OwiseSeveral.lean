/-
  Several `[owise]` equations of one function, read from K 7.1.337 kompile's own KORE. Run from the
  package root: `lake env lean test/OwiseSeveral.lean`.
  - `f2-examples/owise2.kompile.kore` (`owise2.k`): `f(0, _) => 0`, `f(_, 0) => 1`, and the two
    `[owise]` equations `f(1, Y) => Y` and `f(X, 1) => X`. Each `[owise]` premise negates the two
    other equations and not the other `[owise]` equation, so both are clauses of priority 200,
    after the two others and unordered between themselves (they overlap at `f(1, 1)` and agree).
    In the kernel: `f(1, 5)` is 5 and `f(7, 1)` is 7 (each `[owise]` clause), `f(1, 0)` is 1 (the
    clause of priority 50 is taken where it applies, not the `[owise]` one), `f(2, 3)` has no value.
  - the same text with the second `[owise]` equation's exclusion naming one of the other equations
    twice and the other not at all: its premise is not the negation of the other equations, so
    the reader refuses it (`exclusionShape`), as it does for a single `[owise]` equation.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

open KCore

/-- The exclusion of the `[owise]` equation with unique id `uid`, `¬(d₁ ∨ (d₂ ∨ ⊥))`, made
`¬(d₂ ∨ (d₂ ∨ ⊥))`. -/
def repeatDisjunct (uid : String) (k : Kore.Definition) : Kore.Definition :=
  let isIt := fun (a : Kore.Axiom) => a.attributes.any fun ap =>
    ap.head.ident.name == "UNIQUE'Unds'ID" && match ap.args with
      | [.string v] => v == uid
      | _ => false
  let edit : Kore.Pattern → Kore.Pattern
    | .implies s (.and s' [.not s'' (.or s₁ [_, .or s₂ [d₂, b]]), rest]) c =>
      .implies s (.and s' [.not s'' (.or s₁ [d₂, .or s₂ [d₂, b]]), rest]) c
    | p => p
  let sent := fun (s : Kore.Sentence) => match s with
    | .axiom a => if isIt a then .axiom { a with pattern := edit a.pattern } else .axiom a
    | s => s
  { k with modules := k.modules.dropLast ++
      (k.modules.getLast?.map fun m => [{ m with sentences := m.sentences.map sent }]).getD [] }

/-- The reader's verdict on the text at `path` (edited by `edit`): "read", or its refusal. -/
def verdict (path : String) (edit : Kore.Definition → Kore.Definition := id) : IO String := do
  match Kore.parseDefinition (← IO.FS.readFile path) with
  | .error e => return s!"KORE read error {e}"
  | .ok k => return match Parse.parse (edit k) with
    | .ok _ => "read"
    | .error r => r.reason.name

/--
info: read
exclusionShape
-/
#guard_msgs in
#eval show IO Unit from do
  IO.println (← verdict "f2-examples/owise2.kompile.kore")
  IO.println (← verdict "f2-examples/owise2.kompile.kore"
    (repeatDisjunct "0dc5c0ffd2ec880d900eee67ec7c3cc92cb43bb544d8133d11b8dfc57f5209b4"))

namespace Owise2

definition_of defn from "f2-examples/owise2.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem

/-- `f`, the definition's function. -/
def f : Sym := 383

theorem f_named : c.symName f = "Lblf" := by decide +kernel

def int (n : Int) : GroundTerm := .dv Srt.int (.int n)

private theorem hok : c.ok = true := by decide +kernel
private theorem hsr : c.srReady = true := by decide +kernel
private theorem hmr : c.matchReady = true := by decide +kernel
private theorem hfn : c.lookupFn f = some (c.fns[0]'(by decide +kernel)) := rfl

/-- `f`'s clauses: the two of priority 50, then both `[owise]` equations at priority 200. -/
theorem f_prios : (c.fns[0]'(by decide +kernel)).clauses.map (·.prio) = [50, 50, 200, 200] := by
  decide +kernel

/-- The first `[owise]` clause: `f(1, 5) = 5`. -/
theorem f_1_5 : Eval c f [int 1, int 5] (some (int 5)) :=
  Exec.evalF_sound (sortCtx_of hok hsr (Exec.ovlCase_of hmr)) (Exec.clauseCtx_of hok) (Exec.matchCtx_of hmr) 10
    (by decide +kernel) hfn (by decide +kernel)

/-- The second `[owise]` clause: `f(7, 1) = 7`. -/
theorem f_7_1 : Eval c f [int 7, int 1] (some (int 7)) :=
  Exec.evalF_sound (sortCtx_of hok hsr (Exec.ovlCase_of hmr)) (Exec.clauseCtx_of hok) (Exec.matchCtx_of hmr) 10
    (by decide +kernel) hfn (by decide +kernel)

/-- Where a clause of priority 50 applies, the `[owise]` ones do not: `f(1, 0) = 1`. -/
theorem f_1_0 : Eval c f [int 1, int 0] (some (int 1)) :=
  Exec.evalF_sound (sortCtx_of hok hsr (Exec.ovlCase_of hmr)) (Exec.clauseCtx_of hok) (Exec.matchCtx_of hmr) 10
    (by decide +kernel) hfn (by decide +kernel)

/-- No clause applies: `f(2, 3)` has no value. -/
theorem f_2_3 : Eval c f [int 2, int 3] none :=
  Exec.evalF_sound (sortCtx_of hok hsr (Exec.ovlCase_of hmr)) (Exec.clauseCtx_of hok) (Exec.matchCtx_of hmr) 10
    (by decide +kernel) hfn (by decide +kernel)

end Owise2

#print axioms Owise2.f_1_5
#print axioms Owise2.f_7_1
#print axioms Owise2.f_1_0
#print axioms Owise2.f_2_3
