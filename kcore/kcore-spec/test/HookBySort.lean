/-
  A symbol the text declares with a library symbol hook has that hook's meaning only where its
  sorts carry the matching sort hooks (`Parse.hookImplAt`, read by the reader and checked by
  `Definition.paramsOK`). Run from the package root: `lake env lean -j1 test/HookBySort.lean`.

  The basis: the builtin text describes a hooked sort and its symbols together (MAP's prose is
  about the sort declared `hook(MAP.Map)` and the symbols declared on it), so a sort declared with
  that sort hook is that domain by the same description, and a symbol on it with one of the
  domain's symbol hooks is that symbol. No text says what `hook(MAP.concat)` means on a sort that
  is no map: such a symbol is a parameter without a registry hook, whose value is the
  interpretation's (`Semantics.paramVal`, `impl = none`), so the theory asserts nothing of it.

  - Decided: `hookImplAt` at `MAP.concat`, `MAP.lookup`, `MAP.in_keys`, `MAP.unit`, `SET.concat`,
    `LIST.get`, `INT.add` and `KEQUAL.ite` (keyed on its Bool argument alone), on the library's sorts, on a sort of the definition listed with the
    sort hook, and on one that is not; a wrong number of arguments; a hook the registry does not
    interpret.
  - Read, hand-built: `f2-examples/owisene.kompile.kore` with one declaration added to its main
    module, `hooked-symbol Lblcat{}(SortExp{}, SortExp{}) : SortExp{} [function{}(),
    hook{}("MAP.concat")]`, `SortExp` a sort declared without a hook: `cat` is read as a parameter
    without a registry hook, and the definition is well formed. With `SortMap` in place of
    `SortExp` (the library's sort, declared `hook{}("MAP.Map")`), `cat` has `_Map_`'s hook. With
    the declaration and no sort changed but the hook `MAP.lookup` (two arguments in the library,
    the first a Map): no registry hook.
  - Read, a kompiled text with cell collections (`f2-examples/colls.kore`): every symbol declared
    with a registry hook on a cell collection sort (`hooked-sort … hook{}("MAP.Map")`, `SET.Set`,
    `LIST.List`) keeps it: no declared hook that the registry interprets is left without its hook.
-/
import KcoreSpec

set_option autoImplicit false

namespace KCore.HookBySortTest

open KCore Parse

/-! ## Decided -/

/-- A sort of a definition (the first number after the registry's) and a symbol number. -/
abbrev own : Srt := nRegSorts
abbrev sym : Sym := nRegSyms

/-- On the library's own sorts the hook is the registry's. -/
theorem lib_sorts :
    hookImplAt [] "MAP.concat" ⟨sym, [Srt.map, Srt.map], Srt.map⟩ = some mapConcat ∧
    hookImplAt [] "MAP.lookup" ⟨sym, [Srt.map, Srt.kitem], Srt.kitem⟩ = some mapLookup ∧
    hookImplAt [] "INT.add" ⟨sym, [Srt.int, Srt.int], Srt.int⟩ = some intAdd ∧
    hookImplAt [] "LIST.get" ⟨sym, [Srt.list, Srt.int], Srt.kitem⟩ = some listGet := by
  decide +kernel

/-- On a sort declared with the sort hook (listed with the library sort it stands for), the hook is
the registry's: a cell map's concatenation, unit, element (at a key and a value sort of the
definition: KItem's positions carry no sort hook) and `in_keys`; a set's concatenation; a sort
hooked to Int under `INT.add`. -/
theorem hooked_sorts :
    hookImplAt [(own, Srt.map)] "MAP.concat" ⟨sym, [own, own], own⟩ = some mapConcat ∧
    hookImplAt [(own, Srt.map)] "MAP.unit" ⟨sym, [], own⟩ = some mapUnit ∧
    hookImplAt [(own, Srt.map)] "MAP.element" ⟨sym, [own + 1, own + 2], own⟩ = some mapElem ∧
    hookImplAt [(own, Srt.map)] "MAP.in_keys" ⟨sym, [own + 1, own], Srt.bool⟩ = some mapInKeys ∧
    hookImplAt [(own, Srt.set)] "SET.concat" ⟨sym, [own, own], own⟩ = some setConcat ∧
    hookImplAt [(own, Srt.int)] "INT.add" ⟨sym, [own, Srt.int], own⟩ = some intAdd := by
  decide +kernel

/-- **On a sort without the sort hook there is no registry hook**: `MAP.concat` on a sort that is
not listed, on a sort declared with another sort hook (a set, Int), on Int itself; `MAP.lookup`
whose first argument is no map; `INT.add` with a result sort that is not Int's. -/
theorem unhooked_sorts :
    hookImplAt [] "MAP.concat" ⟨sym, [own, own], own⟩ = none ∧
    hookImplAt [(own, Srt.set)] "MAP.concat" ⟨sym, [own, own], own⟩ = none ∧
    hookImplAt [(own, Srt.int)] "MAP.concat" ⟨sym, [own, own], own⟩ = none ∧
    hookImplAt [] "MAP.concat" ⟨sym, [Srt.int, Srt.int], Srt.int⟩ = none ∧
    hookImplAt [(own, Srt.map)] "MAP.concat" ⟨sym, [own, own + 1], own⟩ = none ∧
    hookImplAt [] "MAP.lookup" ⟨sym, [own, Srt.kitem], Srt.kitem⟩ = none ∧
    hookImplAt [] "INT.add" ⟨sym, [Srt.int, Srt.int], own⟩ = none := by
  decide +kernel

/-- Another number of arguments than the hook's, and a hook the registry does not interpret. -/
theorem arity_and_unregistered :
    hookImplAt [] "MAP.concat" ⟨sym, [Srt.map], Srt.map⟩ = none ∧
    hookImplAt [] "MAP.concat" ⟨sym, [Srt.map, Srt.map, Srt.map], Srt.map⟩ = none ∧
    hookImplAt [] "INT.rand" ⟨sym, [Srt.int], Srt.int⟩ = none := by
  decide +kernel

/-- `KEQUAL.ite` is keyed on its Bool argument alone: the sort of its branches and result is a
variable of the library's declaration, which carries no sort hook, so every sort stands there; a
first argument that is not Bool's has no registry hook. -/
theorem ite_keyed :
    hookImplAt [] "KEQUAL.ite" ⟨sym, [Srt.bool, own, own], own⟩ = some kIte ∧
    hookImplAt [] "KEQUAL.ite" ⟨sym, [Srt.bool, Srt.int, Srt.int], Srt.int⟩ = some kIte ∧
    hookImplAt [] "KEQUAL.ite" ⟨sym, [own, own, own], own⟩ = none := by
  decide +kernel

/-- Where it gives a hook, it is `regHookOf`'s. -/
theorem hookImplAt_reg {stands : List (Srt × Srt)} {hk : String} {k : CtorSig} {g : Sym}
    (h : hookImplAt stands hk k = some g) : regHookOf hk = some g := by
  unfold hookImplAt at h
  exact (Option.filter_eq_some_iff.mp h).1

/-! ## Read -/

/-- The text at `path` with the sentence `decl` added after the line `anchor` of its main module. -/
def withDecl (path anchor decl : String) : IO String := do
  let t ← IO.FS.readFile path
  if (t.splitOn anchor).length != 2 then throw (IO.userError s!"anchor not once: {anchor}")
  return t.replace anchor (anchor ++ decl)

/-- The parameter symbols of the definition's own (not the library's) whose presentation carries a
hook: name, hook attribute, the registry hook read. -/
def hookedParams (d : Definition) : List (String × String × Option Sym) :=
  let own := d.sem.params.filter fun k => decide (nRegSyms ≤ k.sig.name)
  (own.zip d.pres.params).filterMap fun (k, pp) =>
    if pp.hook == "" then none else some (d.sem.symName k.sig.name, pp.hook, k.impl)

def verdict (text : String) (only : String → Bool) : String :=
  match Kore.parseDefinition text with
  | .error e => s!"KORE read error {e}"
  | .ok k => match Parse.parse k with
    | .error r => s!"refused: {r.toText}"
    | .ok d =>
      s!"{(hookedParams d).filter (only ·.1)}; wf {KCore.wf d}; paramsOK {d.paramsOK}; " ++
        s!"account {(Parse.accountRefusals k d).length}; failing {(d.report.filter (!·.2)).map (·.1)}"

def anchor : String := "  sort SortExp{} []\n"

#eval show IO Unit from do
  let p := "f2-examples/owisene.kompile.kore"
  let isCat := fun (n : String) => n == "Lblcat"
  IO.println (verdict (← withDecl p anchor
    "  hooked-symbol Lblcat{}(SortExp{}, SortExp{}) : SortExp{} [function{}(), hook{}(\"MAP.concat\")]\n") isCat)
  IO.println (verdict (← withDecl p anchor
    "  hooked-symbol Lblcat{}(SortMap{}, SortMap{}) : SortMap{} [function{}(), hook{}(\"MAP.concat\")]\n") isCat)
  IO.println (verdict (← withDecl p anchor
    "  hooked-symbol Lblcat{}(SortExp{}, SortExp{}) : SortExp{} [function{}(), hook{}(\"MAP.lookup\")]\n") isCat)
  IO.println (verdict (← IO.FS.readFile p) isCat)

/-- Of the definition's hooked parameter symbols: how many, how many with a hook the registry
interprets by name, and those among them read without it. -/
def collsLine (text : String) : String :=
  match Kore.parseDefinition text with
  | .error e => s!"KORE read error {e}"
  | .ok k => match Parse.parse k with
    | .error r => s!"refused: {r.toText}"
    | .ok d =>
      let hp := hookedParams d
      let reg := hp.filter fun (_, hk, _) => (regHookOf hk).isSome
      s!"hooked {hp.length}; registry hooks {reg.length}; " ++
        s!"without it {(reg.filter fun (_, hk, g) => g != regHookOf hk).map (·.1)}; " ++
        s!"MAP.concat {(reg.filter fun (_, hk, _) => hk == "MAP.concat").map fun (n, _, g) => (n, g)}; " ++
        s!"wf {KCore.wf d}; paramsOK {d.paramsOK}"

#eval show IO Unit from do
  IO.println (collsLine (← IO.FS.readFile "f2-examples/colls.kore"))

#print axioms lib_sorts
#print axioms hooked_sorts
#print axioms unhooked_sorts
#print axioms arity_and_unregistered
#print axioms ite_keyed
#print axioms hookImplAt_reg

end KCore.HookBySortTest
