/-
  Three readings of library symbols and data, on edits of `f2-examples/colls.kore` made inside the
  test. Run from the package root: `lake env lean test/LibraryReading.lean`.
  - A library sort's projection applied by a rule is a function with the text's equation and the
    clause read from its selector-domain axiom (`ReadingNote.projectionDomainAsClause`), which
    krust's text holds: `bump`'s right side with `<bal>(B +Int 1)` made
    `<bal>(project:Int(kseq(inj{Int,KItem}(B +Int 1), dotk)))` is read, and `project:Int` is a
    function with two clauses.
  - The library's data states only what the text states (`Parse.libraryUnstated`): nothing on
    `colls.kore`; with its `[subsort{SortInt{}, SortKItem{}}()]` axiom deleted, that subsort, which
    the library's data gives, is reported.
  - A symbol-overload axiom between functions is an equation of the overloading one
    (`Parse.overloadEqn?`): `f_Gas(inj{Int,Gas}(K0)) = inj{Int,Gas}(f_Int(K0))` is the equation of
    `f_Gas` with the pattern `inj{Int,Gas}(VarK0)` and that right side; the sentence is read.
-/
import KcoreSpec

open KCore

/-- The user module's sentences mapped by `f`. -/
def onUser (f : Kore.Sentence → List Kore.Sentence) (k : Kore.Definition) : Kore.Definition :=
  { k with modules := k.modules.dropLast ++
      (k.modules.getLast?.map fun m => [{ m with sentences := m.sentences.flatMap f }]).getD [] }

partial def projBal : Kore.Pattern → Kore.Pattern
  | .app h ss [t] =>
    if h.ident.name == "Lbl'-LT-'bal'-GT-'" then match t with
      | .app g _ _ =>
        if g.ident.name == "Lbl'UndsPlus'Int'Unds'" then
          .app h ss [.app ⟨⟨"Lblproject'Coln'Int"⟩⟩ [] [.app ⟨⟨"kseq"⟩⟩ []
            [.app ⟨⟨"inj"⟩⟩ [KoreAML.srt "Int", KoreAML.srt "KItem"] [t], .app ⟨⟨"dotk"⟩⟩ [] []]]]
        else .app h ss [projBal t]
      | _ => .app h ss [projBal t]
    else .app h ss [projBal t]
  | .app h ss ps => .app h ss (ps.map projBal)
  | .and s ps => .and s (ps.map projBal)
  | .rewrites s p q => .rewrites s (projBal p) (projBal q)
  | p => p

def projectRules : Kore.Definition → Kore.Definition := onUser fun s => match s with
  | .axiom a => match a.pattern with
    | .rewrites .. => [.axiom { a with pattern := projBal a.pattern }]
    | _ => [s]
  | s => [s]

def dropIntSubsort : Kore.Definition → Kore.Definition := onUser fun s => match s with
  | .axiom a => match a.attributes with
    | [⟨⟨⟨"subsort"⟩⟩, [A, B], []⟩] =>
      if KoreAML.Parse.sortName? A == some "Int" && KoreAML.Parse.sortName? B == some "KItem" then [] else [s]
    | _ => [s]
  | s => [s]

def read (path : String) (edit : Kore.Definition → Kore.Definition) : IO (Kore.Definition × Except Parse.Refusal Definition) := do
  match Kore.parseDefinition (← IO.FS.readFile path) with
  | .error e => throw (IO.userError e)
  | .ok k => let k := edit k; return (k, Parse.parse k)

def overloadAx : Kore.Axiom :=
  let gas := KoreAML.srt "Gas"
  let int := KoreAML.srt "Int"
  let k0 : Kore.Pattern := .var (.evar ⟨⟨⟨"K0"⟩⟩, int⟩)
  { sortVars := [⟨⟨⟨"R"⟩⟩⟩], attributes := [⟨⟨⟨"symbol-overload"⟩⟩, [], [.app ⟨⟨"Lblf'Unds'Gas"⟩⟩ [] [], .app ⟨⟨"Lblf'Unds'Int"⟩⟩ [] []]⟩]
    pattern := .equals gas (KoreAML.srt "R")
      (.app ⟨⟨"Lblf'Unds'Gas"⟩⟩ [] [.app ⟨⟨"inj"⟩⟩ [int, gas] [k0]])
      (.app ⟨⟨"inj"⟩⟩ [int, gas] [.app ⟨⟨"Lblf'Unds'Int"⟩⟩ [] [k0]]) }

/--
info: projection: read, project:Int a function with 2 clause, wf true
library data on colls: 0
without Int < KItem: 1
overload: read; equation of Lblf'Unds'Gas, patterns [inj{SortInt{}, SortGas{}}(VarK0:SortInt{})]
-/
#guard_msgs in
#eval show IO Unit from do
  let (_, r) ← read "f2-examples/colls.kore" projectRules
  match r with
  | .error e => IO.println s!"projection: refused {e.toText}"
  | .ok d =>
    let fs := d.sem.fns.filter fun f => d.sem.symName f.label == "Lblproject'Coln'Int"
    IO.println s!"projection: read, project:Int a function with {(fs.map (·.clauses.length)).sum} clause, wf {wf d}"
  let (k, r) ← read "f2-examples/colls.kore" id
  match r with
  | .ok d => IO.println s!"library data on colls: {(Parse.libraryUnstated k d).length}"
  | .error e => IO.println s!"colls refused {e.toText}"
  let (k, _) ← read "f2-examples/colls.kore" dropIntSubsort
  match k.modules.getLast? with
  | some m => match Parse.finish m (Parse.scan m.sentences) with
    | .ok d => IO.println s!"without Int < KItem: {(Parse.libraryUnstated k d).length}"
    | .error _ => IO.println "without Int < KItem: finish fails"
  | none => pure ()
  match Parse.overloadEqn? overloadAx, Parse.classifyShape (.axiom overloadAx) with
  | some e, .read => IO.println s!"overload: read; equation of {e.fn}, patterns {e.pats.map Kore.Printer.pattern}"
  | _, c => IO.println s!"overload: not read ({c.name})"
