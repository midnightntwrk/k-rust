/-
  The equations `emit` writes for a sort's predicate (`KCore.predEquationsPE`), against the text's.
  Run from the package root: `lake env lean -j1 test/PredEmit.lean`.

  Where the reader holds the predicate as the function its equations define (a function of
  `c.fns`), `emit` writes one equation per clause, each with the id of the equation the clause was
  read from and, at priority 200, `owise{}()`; otherwise it writes the two equations of
  `isEquations` with the sort's ids.

  On the kompiled texts (K 7.1.337 kompile's KORE, from the cache `kfix.py` keeps), each sentence of
  the user module that is an equation of `isKResult` is compared with the equations of `isKResult`
  in the user module of `Definition.emit` of the text's reading, sentence by sentence:
  - `c3-strict-hybrid` and `e2-frontend-effect` (`pair` declared `hybrid`; isKResult a function of
    `c.fns` of three clauses): the `[owise]`, pair and standard equations are each emitted, and
    nothing else is emitted for isKResult;
  - `c3-strict-base` (the same text as `c3-strict-hybrid` without `hybrid`; isKResult `sortPreds`'
    function): its `[owise]` and standard equations are each emitted, and nothing else.
-/
import KcoreSpec.Parse

set_option autoImplicit false

open KCore KCore.Parse

namespace PredEmit

def cacheDir : IO String := do
  let get := fun (n : String) => do
    match ← IO.getEnv n with
    | some d => pure (if d.isEmpty then none else some d)
    | none => pure none
  if let some d ← get "KCORE_KFIX_CACHE" then return d
  if let some d ← get "XDG_CACHE_HOME" then return s!"{d}/kcore-kfix"
  let home := (← get "HOME").getD "."
  return s!"{home}/.cache/kcore-kfix"

/-- The kompiled text of fixture `n`, its `BUILTIN/` and `FIXTURE/` paths restored to made-up
directories (as `kfix.py accounts` restores them before reading). -/
def load (n : String) : IO Kore.Definition := do
  let t ← IO.FS.readFile s!"test/constructs/fixtures/{n}/kompile.txt"
  let some l := (t.splitOn "\n").find? (·.startsWith "definition.kore sha256: ")
    | throw (IO.userError s!"{n}: kompile.txt names no sha256")
  let sha := (l.splitOn ": ").getD 1 ""
  let raw ← IO.FS.readFile s!"{← cacheDir}/{sha}.kore"
  let raw := ((raw.replace "BUILTIN/" "/made-up-k/include/kframework/builtin/").replace "FIXTURE/" "/made-up-fx/").replace
    "FIXTURE" "/made-up-fx"
  match Kore.parseDefinition raw with
  | .ok k => pure k
  | .error e => throw (IO.userError s!"{n}: KORE read error {e}")

/-- The equation of the predicate `p` a sentence is, by its kind: `owise`, `pair` (its pattern
applies `pair`) or `standard`. -/
def kindOf (p : String) (s : Kore.Sentence) : Option String :=
  match s with
  | .axiom a => (rawEqn? a).bind fun e =>
    if e.fn != p then none
    else some (if e.competitors.isSome then "owise" else if ((eqnShape e).splitOn "Lblpair").length > 1 then "pair"
      else "standard")
  | _ => none

/-- For each equation of `p` in the user module of the text `n` (in text order), its kind and
whether `emit` of the text's reading writes that sentence; then the kinds of the equations of `p`
`emit` writes that are no sentence of the text. -/
def compare (p n : String) : IO Unit := do
  let k ← load n
  let some m := k.modules.getLast? | throw (IO.userError "no module")
  let txt := m.sentences.filter (kindOf p · |>.isSome)
  match Parse.parse k with
  | .error r => IO.println s!"{n}: refused {repr r.reason}"
  | .ok d =>
    let some em := d.emit.modules.getLast? | throw (IO.userError "no emitted module")
    let out := em.sentences.filter (kindOf p · |>.isSome)
    let held := if d.sem.fns.any (d.sem.symName ·.label == p) then "a function of c.fns" else "sortPreds' function"
    IO.println s!"{n}: {p} {held}; {txt.length} equations in the text, {out.length} emitted"
    for s in txt do
      IO.println s!"  {(kindOf p s).getD "?"}: emitted {out.contains s}"
    IO.println s!"  emitted, not in the text: {(out.filter (!txt.contains ·)).filterMap (kindOf p)}"

/--
info: c3-strict-hybrid: LblisKResult a function of c.fns; 3 equations in the text, 3 emitted
  owise: emitted true
  pair: emitted true
  standard: emitted true
  emitted, not in the text: []
e2-frontend-effect: LblisKResult a function of c.fns; 3 equations in the text, 3 emitted
  owise: emitted true
  pair: emitted true
  standard: emitted true
  emitted, not in the text: []
c3-strict-base: LblisKResult sortPreds' function; 2 equations in the text, 2 emitted
  owise: emitted true
  standard: emitted true
  emitted, not in the text: []
-/
#guard_msgs in
#eval show IO Unit from do
  compare "LblisKResult" "c3-strict-hybrid"
  compare "LblisKResult" "e2-frontend-effect"
  compare "LblisKResult" "c3-strict-base"

end PredEmit
