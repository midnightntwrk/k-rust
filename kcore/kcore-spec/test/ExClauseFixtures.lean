/-
  The fixtures of an equation with existential variables, each with what the text states, the
  clause `Parse.ceRead` reads from it and what `Semantics.clausePlainEx` says of that clause in the
  definition built from the text. Run from the package root:
  `lake env lean -j1 test/ExClauseFixtures.lean`.

  The kompiled texts are read from the cache `kfix.py` keeps (K 7.1.337 kompile's KORE), as
  test/ExClauseReader.lean reads them. `Parse.clauseBody` does not call `ceRead`: `today` prints
  what the reader does with the text as it is.

  ## e3-eq-exists-int

  `rule h(X) => ?Z ensures ?Z *Int 2 ==Int X`. kompile rejects `?Z` on an equation (fixture
  `e3-eq-exists-int`, exit 113, "Cannot encode equations with existential variables to KORE"), so
  the text exists in the `#Exists` spelling only (`e3-eq-exists-int-ml`):
  `h(X) => #Exists Z:Int. (Z #And {(Z *Int 2 ==Int X) #Equals true})`.

  From the sentence: `h(x)` is the set of the elements z of Int with `(z *Int 2 ==Int x) = true`.
  Int is not confined, and the predicate equates Z with no term: `Z *Int 2 ==Int X` holds of an
  element the text does not name as well as of a value. So the function's elements are not
  decided by values, and the clause is one to refuse, the reason `existentialEquation`, the sort
  Int.

  - The clause read: `[X:Int, Z:Int]`, `exs [1]`, `rhs Z`, `post (Z *Int 2 ==Int X) = true`; it is
    the hand-built `Int.clZ` (`read is clZ: true`).
  - `clausePlainEx` is false of it in the built definition (Z not confined, `fixedExs` empty), and
    of `clZ` by the kernel on any semantics where Int is not confined (`Int.clZ_no`, at `Int.c`).
  - Today the reader refuses the sentence `manyValuedRightSide (\exists)` before reading a clause:
    the refusal is there, the reason is not yet the one above.

  ## The account's lines for a clause holding existential variables

  `Parse.owedExsText` (KcoreSpec/Account.lean), which `kcore account` prints: for each clause with
  `exs` its match obligation, with the fact owed, and the statements stated only under it. No text
  reaches the lines through the reader today (`clauseBody` does not call `ceRead`), so `owed`
  prints them for the definition built from the patched text with the clause `ceRead` reads put
  in place of the patched one.
  - `e3-eq-exists-partial-ml`, `f(X) => #Exists B:Bool. (B #And {B #Equals notBool X})`: one line,
    f's clause 0 with `VarB:Bool`; `matchObligationsL` names the clause (B is in no pattern, so the
    patterns do not fix the clause's variables).
  - `e3-eq-exists-noens-ml`, `f(_) => #Exists B:Bool. B`: the same line; the fact is false of
    this clause (its two instances give two results), and the line does not say it holds.
  - The patched text itself, whose clauses hold no existential variable: no line.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 100000

open KCore KCore.Parse

namespace ExClauseFixtures

/-! ## The harness -/

/-- The cache of kompiled fixture texts, as test/constructs/kfix.py names it. -/
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

/-- kompile's exit code on fixture `n`, from its record. -/
def kompileExit (n : String) : IO String := do
  let t ← IO.FS.readFile s!"test/constructs/fixtures/{n}/kompile.txt"
  return ((t.splitOn "\n").find? (·.startsWith "exit: ")).getD "no exit line"

/-- The text with the right side of each equation of the functions `fns` replaced by the first
argument's variable where the sorts agree, else a literal, so that the definition is built and the
clauses read here can be put in it. -/
def patch (fns : List String) (k : Kore.Definition) : Kore.Definition :=
  let fix := fun (s : Kore.Sentence) => match s with
    | .axiom a => match rawEqn? a, a.pattern with
      | some e, .implies r prem (.equals s1 s2 l (.and s3 [_, en])) =>
        if fns.contains e.fn then
          let rs := (KoreAML.Parse.sortName? s1).getD ""
          let arg := e.pats.findSome? fun p => match p with | .var (.evar x) => some x | _ => none
          let rhs : Kore.Pattern := match arg with
            | some x => if KoreAML.Parse.sortName? x.sort == some rs then .var (.evar x)
                        else if rs == "Int" then .dv s1 "0" else .dv s1 "true"
            | none => if rs == "Int" then .dv s1 "0" else .dv s1 "true"
          Kore.Sentence.axiom { a with pattern := .implies r prem (.equals s1 s2 l (.and s3 [rhs, en])) }
        else s
      | _, _ => s
    | s => s
  match k.modules.reverse with
  | m :: rest => { k with modules := (({ m with sentences := m.sentences.map fix }) :: rest).reverse }
  | [] => k

/-- What the reader does with the text of fixture `n` as it is. -/
def today (n : String) : IO Unit := do
  match Parse.parse (← load n) with
  | .error r => IO.println s!"{n}: today refused {repr r.reason} ({r.detail})"
  | .ok _ => IO.println s!"{n}: today read"

/-- `ceRead` on the one equation of the function `fnName` of fixture `n`; the clause in the
definition built from the patched text, with `clausePlainEx`; and whether it is `expect` (the two
printed alike). -/
def run (n fnName : String) (expect : Clause) : IO Unit := do
  let k ← load n
  let some m := k.modules.getLast? | IO.println s!"{n}: no module"
  let S := scan m.sentences
  match envOf m S with
  | .error f => IO.println s!"{n}: envOf fails {repr f.reason}"
  | .ok E =>
    match Parse.parse (patch [fnName] k), S.eqs.filter (·.fn == fnName) with
    | .error r, _ => IO.println s!"{n}: patched text refused {repr r.reason} {r.detail}"
    | .ok d, [e] =>
      let c := d.sem
      match ceRead E.N e with
      | .error f => IO.println s!"{n} {fnName}: refused {repr f.reason} ({f.detail})"
      | .ok (cl, vs) =>
        IO.println s!"{n} {fnName}: vars {vs.map fun v => v.name ++ ":" ++ v.sort} exs {cl.exs}"
        IO.println s!"  sorts {cl.exs.map fun i => (cl.vars[i]?.map c.sortName).getD "?"}; confined {cl.exs.map fun i => (cl.vars[i]?.map c.confined).getD false}; fixedExs {cl.fixedExs c.confined (fun _ => false)}; clausePlainEx {c.clausePlainEx cl}"
        IO.println s!"  read is {if toString (repr cl) == toString (repr expect) then "the hand-built clause" else "not the hand-built clause"}"
    | .ok _, es => IO.println s!"{n} {fnName}: {es.length} equations"

/-- The account's lines on the clauses holding existential variables (`Parse.owedExsText`) for the
definition built from the patched text of fixture `n`, and for that definition with the clause
`ceRead` reads from the one equation of `fnName` in place of the patched one (its variables' names
in the presentation); with what `matchObligationsL` names there. -/
def owed (n fnName : String) : IO Unit := do
  let k ← load n
  let some m := k.modules.getLast? | IO.println s!"{n}: no module"
  let S := scan m.sentences
  match envOf m S with
  | .error f => IO.println s!"{n}: envOf fails {repr f.reason}"
  | .ok E =>
    match Parse.parse (patch [fnName] k), S.eqs.filter (·.fn == fnName) with
    | .error r, _ => IO.println s!"{n}: patched text refused {repr r.reason} {r.detail}"
    | .ok d, [e] =>
      match ceRead E.N e with
      | .error f => IO.println s!"{n} {fnName}: refused {repr f.reason} ({f.detail})"
      | .ok (cl, vs) =>
        let here := fun (g : Fn) => d.sem.symName g.label == fnName
        let fns := d.sem.fns.map fun g => if here g then { g with clauses := [cl] } else g
        let pfns := (withPres d.sem.fns d.pres.fns).map fun (g, gp) =>
          if here g then { gp with clauses := gp.clauses.map fun cp => { cp with names := vs.map (·.name) } } else gp
        let d' : Definition := { d with sem := { d.sem with fns }, pres := { d.pres with fns := pfns } }
        IO.println s!"{n}: patched text: {(owedExsText d id).length} lines; with the clause read for {fnName}:"
        for l in owedExsText d' id do IO.println l
        IO.println s!"  matchObligationsL {d'.sem.matchObligationsL.map fun (f, j) => (d'.sem.symName f, j)}"
    | .ok _, es => IO.println s!"{n} {fnName}: {es.length} equations"

/-! ## e3-eq-exists-int -/

namespace Int

open Faithful.UndefRhsWitness (cellSorts cellCtors cellSubsorts)

/-- `h(X) => Z` with `exs = [Z]` and `post := (Z *Int 2 ==Int X) = true`, X and Z of Int. -/
def clZ : Clause :=
  { vars := [Srt.int, Srt.int], pats := [.var 0], req := none, rhs := .var 1, ens := none, exs := [1],
    post := .equals Srt.bool (.app intEq [.app intMul [.var 1, .dv Srt.int (.int 2)], .var 0])
      (.dv Srt.bool (.bool true)) }

/-- A semantics with the cell sorts only: Int is not confined. -/
def c : Semantics :=
  { lib := {}
    sortNames := ["KCell", "KCellOpt"]
    symNames := ["LblisKCell", "LblisKCellOpt", "Lbl'-LT-'k'-GT-'", "LblnoKCell"]
    userSorts := cellSorts
    ctors := cellCtors
    fns := []
    userSubsorts := cellSubsorts
    pgmSort := Srt.k
    rules := [] }

/-- Z is neither of a confined sort nor fixed by the predicate. -/
theorem clZ_no : c.clausePlainEx clZ = false ∧ c.confined Srt.int = false ∧
    clZ.fixedExs c.confined (fun _ => false) = [] ∧ clZ.fixedExs (fun _ => true) (fun _ => true) = [] := by
  decide +kernel

end Int

/--
info: e3-eq-exists-int: kompile exit: 113
e3-eq-exists-int-ml: kompile exit: 0
e3-eq-exists-int-ml Lblh: vars [X:Int, Z:Int] exs [1]
  sorts [Int]; confined [false]; fixedExs []; clausePlainEx false
  read is the hand-built clause
e3-eq-exists-int-ml: today refused KCore.Parse.RefusalReason.manyValuedRightSide (\exists)
-/
#guard_msgs in
#eval show IO Unit from do
  IO.println s!"e3-eq-exists-int: kompile {← kompileExit "e3-eq-exists-int"}"
  IO.println s!"e3-eq-exists-int-ml: kompile {← kompileExit "e3-eq-exists-int-ml"}"
  run "e3-eq-exists-int-ml" "Lblh" Int.clZ
  today "e3-eq-exists-int-ml"

/-! ## The account's lines -/

/--
info: e3-eq-exists-partial-ml: patched text: 0 lines; with the clause read for Lblf:
clauses holding existential variables, each a match obligation (the package's match_named, Semantics.matchObligationsL; not a condition of wf: owed of each is MatchIndependent, that its instances are decided and give one result at each match where it decides): 1
      function Lblf, clause 0 at e3-eq-exists-partial-ml.k:4: MatchIndependent open, existential VarB:Bool
sound_hyp and complete_hyp (the package's sound_defn and complete_defn) are stated of this text only under these facts as hypotheses, each named with its function and clause (FnHyp's fourth conjunct; match_named of FnObligations)
  matchObligationsL [(Lblf, 0)]
e3-eq-exists-noens-ml: patched text: 0 lines; with the clause read for Lblf:
clauses holding existential variables, each a match obligation (the package's match_named, Semantics.matchObligationsL; not a condition of wf: owed of each is MatchIndependent, that its instances are decided and give one result at each match where it decides): 1
      function Lblf, clause 0 at e3-eq-exists-noens-ml.k:4: MatchIndependent open, existential VarB:Bool
sound_hyp and complete_hyp (the package's sound_defn and complete_defn) are stated of this text only under these facts as hypotheses, each named with its function and clause (FnHyp's fourth conjunct; match_named of FnObligations)
  matchObligationsL [(Lblf, 0)]
-/
#guard_msgs in
#eval show IO Unit from do
  owed "e3-eq-exists-partial-ml" "Lblf"
  owed "e3-eq-exists-noens-ml" "Lblf"

end ExClauseFixtures

/-- info: 'ExClauseFixtures.Int.clZ_no' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ExClauseFixtures.Int.clZ_no
