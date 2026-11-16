/-
  A definition without a configuration declaration, read from K 7.1.337 kompile's own KORE. Run
  from the package root: `lake env lean test/DefaultConfig.lean`.
  - `f2-examples/defcfg.kompile.kore` (`defcfg.k`): K gives the definition `kast.md`'s default
    configuration `configuration <k> $PGM:K </k>`; kompile declares its cell `<k>` with that file's
    `Source`. The reader reads it as the definition's configuration cell (`Parse.isDefaultConfig`,
    the declaration up to its place): read, `$PGM` of sort KItem (`project:KItem`), and the rule
    `inc(N) => val(N +Int 1)` steps from `inc(1)` to `val(2)`.
  - the same text with the cell's declaration not `defaultConfigCell` up to its place (its
    `injective` attribute dropped): a sentence of a K installation's file that is no library
    sentence, refused (`builtinText`).
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

open KCore

/-- The declaration of `<k>` without its `injective` attribute. -/
def dropInjective (k : Kore.Definition) : Kore.Definition :=
  let sent := fun (s : Kore.Sentence) => match s with
    | .symbol x => if x.symbol.ident.ident.name == "Lbl'-LT-'k'-GT-'" then
        .symbol { x with attributes := x.attributes.filter (·.head.ident.name != "injective") } else .symbol x
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
builtinText
-/
#guard_msgs in
#eval show IO Unit from do
  IO.println (← verdict "f2-examples/defcfg.kompile.kore")
  IO.println (← verdict "f2-examples/defcfg.kompile.kore" dropInjective)

namespace DefCfg

definition_of defn from "f2-examples/defcfg.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem

def kCell : Sym := 378
def inc : Sym := 380
def val : Sym := 381

theorem names_ok : c.symName kCell = "Lbl'-LT-'k'-GT-'" ∧ c.symName inc = "Lblinc" ∧
    c.symName val = "Lblval" := by decide +kernel

/-- `$PGM` is of sort KItem: the default configuration's `$PGM:K` is projected to KItem. -/
theorem pgm : c.pgmSort = Srt.kitem := by decide +kernel

theorem ok : c.ok = true := by decide +kernel
theorem srReady : c.srReady = true := by decide +kernel
theorem matchReady : c.matchReady = true := by decide +kernel
theorem coherent : CoherentAll c :=
  Det.coherentAll_of_nil ok srReady matchReady (by decide +kernel) (by decide +kernel)

/-- The configuration with `it` in the k cell and the counter at 0. -/
def cfg (it : GroundTerm) : GroundTerm :=
  .ctor topLabel [.ctor kCell [.ctor kseq [it, .ctor dotk []]], .ctor counterLabel [.dv Srt.int (.int 0)]]

def X : Config c := ⟨cfg (.ctor inc [.dv Srt.int (.int 1)]), by decide +kernel⟩
def Y : Config c := ⟨cfg (.ctor val [.dv Srt.int (.int 2)]), by decide +kernel⟩

/-- **The step** of the rule `inc(N) => val(N +Int 1)` in the default configuration. -/
theorem step : Step c X Y :=
  (Exec.step_iff_of_ok c ok srReady matchReady coherent X Y).mpr ⟨100, by decide +kernel⟩

end DefCfg

#print axioms DefCfg.step
