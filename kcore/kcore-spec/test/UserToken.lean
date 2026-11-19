/-
  Token sorts of the definition, read from K 7.1.337 kompile's own KORE (`f2-examples/usertok.k`,
  `usertok.kompile.kore`). Run from the package root: `lake env lean test/UserToken.lean`.
  - `Name` is declared `syntax Name [token]`: kompile writes `sort SortName{} [hasDomainValues{}(),
    Location, Source, token{}()]`. `Tag` has only a token production: kompile writes `sort SortTag{}
    [hasDomainValues{}()]`, without a place. Both are sorts of the definition (`userSorts`) and token
    sorts of the semantics (`lib.tokenSorts`, after the library's): their values are their literals.
    Their no-junk axioms `\or(\top, \bottom)` are the induced ones; nothing is unaccounted.
  - with `hasDomainValues` dropped from `Name`'s declaration, `Name` is a sort of constructor terms,
    and its no-junk axiom `\or(\top, \bottom)` is not induced (one `inertMismatch`, of a no-junk
    axiom).
  - In the kernel: `Name < Ident`, a subsort from a token sort into a sort with a constructor
    (`anon`), is a declared pair; a literal of `Name` injected into `Ident` is a value of `Ident`;
    `coreOK` holds; and the rule `go(N:Name) => done(N)` steps from `go(inj{Name,Ident}("abc"))` to
    `done("abc")`. Every fact is a kernel decision; the step goes through `Exec.step_iff_of_ok`.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

open KCore

/-- The declaration of `SortName` without its `hasDomainValues` attribute. -/
def dropDomainValues (k : Kore.Definition) : Kore.Definition :=
  let sent := fun (s : Kore.Sentence) => match s with
    | .sort x => if x.sort.ident.name == "SortName" then
        .sort { x with attributes := x.attributes.filter (·.head.ident.name != "hasDomainValues") }
      else .sort x
    | s => s
  { k with modules := k.modules.dropLast ++
      (k.modules.getLast?.map fun m => [{ m with sentences := m.sentences.map sent }]).getD [] }

/-- The reader's verdict on the text at `path` (edited by `edit`): the sentences unaccounted and
the inert constructor axioms not induced. -/
def verdict (path : String) (edit : Kore.Definition → Kore.Definition := id) : IO String := do
  match Kore.parseDefinition (← IO.FS.readFile path) with
  | .error e => return s!"KORE read error {e}"
  | .ok k =>
    let k := edit k
    return match Parse.parse k with
      | .ok d => s!"read; unaccounted {(Parse.unconsumed k d).map (·.detail)}; not induced {(Parse.uninduced k d).map fun r => s!"{r.reason.name} {r.detail}"}"
      | .error r => r.reason.name

/--
info: read; unaccounted []; not induced []
read; unaccounted []; not induced [inertMismatch noJunk]
-/
#guard_msgs in
#eval show IO Unit from do
  IO.println (← verdict "f2-examples/usertok.kompile.kore")
  IO.println (← verdict "f2-examples/usertok.kompile.kore" dropDomainValues)

namespace UserTok

definition_of defn from "f2-examples/usertok.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem

/-- The symbols and sorts the facts name, by number (the definition's own: `sortNames` from
`nRegSorts`, `symNames` from `nRegSyms`). -/
def tagS : Srt := 32
def identS : Srt := 33
def cmdS : Srt := 34
def nameS : Srt := 35
def kCell : Sym := 386
def done : Sym := 389
def go : Sym := 390

theorem names_ok : c.sortName tagS = "Tag" ∧ c.sortName identS = "Ident" ∧ c.sortName cmdS = "Cmd" ∧
    c.sortName nameS = "Name" ∧ c.symName kCell = "Lbl'-LT-'k'-GT-'" ∧ c.symName done = "Lbldone" ∧
    c.symName go = "Lblgo" := by
  decide +kernel

/-- Both token sorts are sorts of the definition and the semantics' token sorts. -/
theorem token_sorts : c.lib.tokenSorts = [tagS, nameS] ∧ c.userSorts.contains tagS = true ∧
    c.userSorts.contains nameS = true := by
  decide +kernel

theorem name_ident : c.userSubsorts.contains (nameS, identS) = true := by decide +kernel

tables_of T from "f2-examples/usertok.kompile.kore"

theorem T_eq : T = tables c := by decide +kernel

-- `faithCoreOK` by `decide_cheap`: each conjunct apart, the names on their codes
set_option maxHeartbeats 1000000 in
open Faithful Faithful.Model in
/-- `coreOK`, conjunct by conjunct, the sort checks from the tables. -/
theorem coreOK : c.coreOK = true :=
  Semantics.coreOK_of_T T_eq (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide_cheap)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- The literal `abc` of `Name`, and it injected into `Ident`. -/
def abc : GroundTerm := .dv nameS (.tok "abc")
def abcI : GroundTerm := .inj nameS identS abc

theorem abc_sort : c.sortOf abc = some nameS := sortOf_of_T T_eq (by decide +kernel)
theorem abcI_sort : c.sortOf abcI = some identS := sortOf_of_T T_eq (by decide +kernel)

/-- The configuration with `st` of sort `Cmd` in the k cell and the counter at 0. -/
def cfg (st : GroundTerm) : GroundTerm :=
  .ctor topLabel [.ctor kCell [.ctor kseq [.inj cmdS Srt.kitem st, .ctor dotk []]],
    .ctor counterLabel [.dv Srt.int (.int 0)]]

def x : GroundTerm := cfg (.ctor go [abcI])
def y : GroundTerm := cfg (.ctor done [abc])

def X : Config c := ⟨x, sortOf_of_T T_eq (by decide +kernel)⟩
def Y : Config c := ⟨y, sortOf_of_T T_eq (by decide +kernel)⟩

theorem ok : c.ok = true := ok_of_T T_eq (by decide +kernel)
theorem srReady : c.srReady = true := srReady_of_T T_eq (by decide +kernel)
theorem matchReady : c.matchReady = true := matchReady_of_T T_eq (by decide +kernel)
theorem coherent : CoherentAll c :=
  Det.coherentAll_of_nil ok srReady matchReady (by decide +kernel) (agreeObligations_of_T T_eq (by decide +kernel))

/-- **The step**: the rule matches the literal through `inj{Name,Ident}` and moves it out. -/
theorem step : Step c X Y :=
  (Exec.step_iff_of_ok c ok srReady matchReady coherent X Y).mpr ⟨100, by decide +kernel⟩

end UserTok

#print axioms UserTok.step
#print axioms UserTok.coreOK
