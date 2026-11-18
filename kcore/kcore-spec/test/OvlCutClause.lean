/-
  A function-overloaded symbol or an open generator in an equation's argument pattern, read
  through the cut (`Parse.ovlCutList`). Run from the package root:
  `lake env lean test/OvlCutClause.lean`.

  - `hw-h10.kore` (test/constructs/fixtures/hw-h10: `rule first(X & _) => X`, `&` an open generator
    of the confined sort B over A ::= x | y): the clause of `first` is read with the pattern `Open0`
    and `pre := Open0 ∈ and(X, _Gen0)`. X and `_Gen0` are variables the arguments do not bind, in a
    condition with one they bind, of the confined sort A: `clausesPlain` holds, the account names no
    `openGeneratorPattern`, `coreOK` holds. `clausesPreTop` does not (the checks outside `coreOK`
    read no clause predicate), so `wf` is false with that row failing.
  - `openCutRefusalCl` on the semantics of `openrecheld` (`&` an open generator of the recursive
    sort B): a clause with the pattern `V` and `pre := V ∈ and(X, Y)`, X and Y in no pattern, is
    refused `openGeneratorPattern`, the detail naming the first of them; with X and Y in the
    patterns it is not refused.
-/
import KcoreSpec

set_option autoImplicit false

open KCore

/-- A term, variables by name. -/
partial def cutClTermStr (c : Semantics) (ns : List String) : Term → String
  | .var i => ns.getD i s!"?{i}"
  | .app f as => s!"{c.symName f}(" ++ ", ".intercalate (as.map (cutClTermStr c ns)) ++ ")"
  | .inj a b t => s!"inj[{c.sortName a},{c.sortName b}](" ++ cutClTermStr c ns t ++ ")"
  | .as t i => "(" ++ cutClTermStr c ns t ++ s!" as {ns.getD i s!"?{i}"})"
  | .dv s l => s!"dv[{c.sortName s}]({reprStr l})"

/-- A condition, terms as `cutClTermStr` prints them. -/
partial def cutClCondStr (c : Semantics) (ns : List String) : Cond → String
  | .top => "top"
  | .and p q => "and(" ++ cutClCondStr c ns p ++ ", " ++ cutClCondStr c ns q ++ ")"
  | .mem s t u => s!"in[{c.sortName s}](" ++ cutClTermStr c ns t ++ ", " ++ cutClTermStr c ns u ++ ")"
  | _ => "other"

/-- The reader's verdict on the text at `path`: the refusal, or each clause of the function `fn`
(its variables, patterns, `pre` and right side), with `clausesPlain`, `clausesPreTop`, the
account's `openGeneratorPattern` and `functionInPattern` refusals, `coreOK`, `wf` and its failing
rows. -/
def cutClVerdict (path fn : String) : IO String := do
  let .ok k := Kore.parseDefinition (← IO.FS.readFile path) | return "KORE read error"
  return match Parse.parse k with
    | .error r => s!"{r.reason.name} ({r.detail})"
    | .ok d =>
      let c := d.sem
      let cls := (withPres c.fns d.pres.fns).flatMap fun (f, fp) =>
        if c.symName f.label != fn then [] else
          (withPres f.clauses fp.clauses).map fun (cl, cp) =>
            s!"[{cp.names}] {cl.pats.map (cutClTermStr c cp.names)} pre {cutClCondStr c cp.names cl.pre} => {cutClTermStr c cp.names cl.rhs}"
      s!"read; {cls}; clausesPlain {c.clausesPlain}; clausesPreTop {c.clausesPreTop}; \
        openGeneratorPattern {(Parse.openGeneratorInPattern k d).length}; \
        functionInPattern {(Parse.functionInPattern k d).length}; coreOK {c.coreOK}; wf {wf d}; \
        failing {(d.report.filter (!·.2)).map (·.1)}"

/--
info: read; [[[X, 'Unds'Gen0, Open0]] [Open0] pre in[B](Open0, Lbland(X, 'Unds'Gen0)) => X]; clausesPlain true; clausesPreTop false; openGeneratorPattern 0; functionInPattern 0; coreOK true; wf false; failing [clauses' premise predicates \top (clausesPreTop): the checks outside coreOK read no clause predicate]
-/
#guard_msgs in
#eval show IO Unit from do
  IO.println (← cutClVerdict "test/constructs/fixtures/hw-h10/hw-h10.kore" "Lblfirst")

/-- `openCutRefusalCl` on two hand-built clauses over the open generator of the text at `path`:
the pattern `V` with `pre := V ∈ g(X, Y)`, and the patterns `V, X, Y` with the same `pre`. -/
def cutClRefusals (path : String) : IO String := do
  let .ok k := Kore.parseDefinition (← IO.FS.readFile path) | return "KORE read error"
  return match Parse.parse k with
    | .error r => s!"{r.reason.name} ({r.detail})"
    | .ok d =>
      let c := d.sem
      match c.params.find? (·.raw) with
      | none => "no open generator"
      | some g =>
        let s := g.sig.result
        let pre := Cond.mem s (.var 0) (.app g.sig.name [.var 1, .var 2])
        let cl : List Term → Clause := fun pats => { vars := [s, s, s], pats, req := none, rhs := .var 0, ens := none, pre }
        let show1 := fun (r : Option (Parse.RefusalReason × String)) => match r with
          | some (reason, detail) => s!"{reason.name} ({detail})"
          | none => "none"
        s!"confined {c.confined s}\n{show1 (Parse.openCutRefusalCl c (cl [.var 0]) ["V", "X", "Y"])}\n\
          {show1 (Parse.openCutRefusalCl c (cl [.var 0, .var 1, .var 2]) ["V", "X", "Y"])}"

/--
info: confined false
openGeneratorPattern (Lbland: its sort B is recursive or reaches an unconfined sort: the arguments it matches depend on elements of B the text does not name (VarX:B, under Lbland, held by no other part of the arguments' patterns))
none
-/
#guard_msgs in
#eval show IO Unit from do
  IO.println (← cutClRefusals "f2-examples/openrecheld.kompile.kore")
