/-
  KCore, checked layer: reading a configuration and printing successors for the executable step of
  CollExec.lean (`kcore exec`, KcoreGen.lean, and test/CollExec.lean).

  A configuration is a KORE pattern without variables. It is read with the reader's own
  translation of patterns (`Parse.term`, the definition's names) into a term, and its value is that
  term's value (`CExec.evalT` under the empty substitution: constructors build terms, the
  collection symbols build collections, functions are evaluated), kept when it is a configuration
  (`sortOf` is the top cell's sort). A value is printed back as KORE by `GroundTerm.kore`.
-/
import KcoreSpec.CollExec
import KcoreSpec.Statements

set_option autoImplicit false

namespace KCore.CExec

open KCore

/-- The reader's names of a core: its own sorts and symbols, numbered after the registry's; a
registry name that is also one of its own symbols (a library sort's projection) reads as its own. -/
def namesOf (c : Semantics) : Parse.Names :=
  { sorts := c.sortNames, syms := c.symNames, own := c.symNames.filter regSymNames.contains }

/-- The value of a term without variables built by constructors, literals, injections, interpreted
symbols and parameters implemented by a registry hook, as `evalT` gives it, except that a parameter's
result is not checked against its sort (`paramVal`'s filter): `valueOfPattern` checks the whole
value's sort once, which checks every collection in it. On a large collection the per-level check
is quadratic. `none` for anything else (a function call), which `evalT` then evaluates. -/
partial def quickValue (c : Semantics) : Term → Option GroundTerm
  | .dv s l => some (.dv s l)
  | .inj a b t => (quickValue c t).map (injNormal a b)
  | .app f ts => do
    let vs ← ts.mapM (quickValue c)
    if c.isCtor f then some (.ctor f vs)
    else if isHook f then (c.hookRes f vs).join
    else match c.lookupParam f with
      | some k => match k.impl with
        | some g => (c.hookRes g (c.libArgs g vs)).join.map (GroundTerm.asSort c.lib k.sig.result)
        | none => none
      | none => none
  | _ => none

/-- The value of a KORE pattern without variables, or why it has none. -/
def valueOfPattern (c : Semantics) (p : Kore.Pattern) : Except String GroundTerm := do
  let (t, vs) ← match Parse.term (namesOf c) [] p with
    | .ok r => pure r
    | .error f => throw s!"not read: {reprStr f.reason} {f.detail}"
  unless vs.isEmpty do throw s!"the pattern has variables ({vs.length})"
  if let some v := quickValue c t then return v
  match evalT c Exec.fuel [] t with
  | some (some v) => pure v
  | some none => throw "the pattern has no value (undefined)"
  | none => throw "the pattern's value is out of fuel"

/-- A configuration read from KORE text. -/
def configOfText (c : Semantics) (text : String) : Except String GroundTerm := do
  let p ← match Kore.parsePattern text.trimAscii.toString with
    | .ok p => pure p
    | .error e => throw s!"KORE read error {e}"
  let v ← valueOfPattern c p
  unless c.sortOf v == some topCellSort do throw "the value is not a configuration (not of the top cell's sort)"
  pure v

/-- A value as KORE text. -/
def showValue (c : Semantics) (v : GroundTerm) : String := Kore.Printer.pattern (v.kore c)

/-- The run from x: at most `bound` steps, each to the first successor; the configurations visited
after x, and whether a step had several successors. -/
def runFrom (c : Semantics) (n : Nat) : Nat → GroundTerm → List GroundTerm × Bool
  | 0, _ => ([], false)
  | k + 1, x =>
    match successorsN c n x with
    | [] => ([], false)
    | y :: ys =>
      let (rest, br) := runFrom c n k y
      (y :: rest, br || ys.any (fun z => !Exec.same z y))

end KCore.CExec
