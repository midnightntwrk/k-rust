/-
  The import sentences of `f2-examples/base.kompile.kore`, the kompiled text of construct fixture
  base (`test/constructs/fixtures/base`), on its literal `kore`. Nothing here reads `Parse.parse` or
  `emit`. Run from the package root: `lake env lean -j1 test/ImportsBase.lean`.

  An import states no pattern: `Theory.ofDefinition` takes the declarations and axioms of every
  module of the text, and an import is neither. Its meaning is scope (kore-syntax.md:320): a
  declaration is in scope in a module if it appears there or is in scope, transitively, in a module
  it imports; the imported module appears earlier in the definition (kore-syntax.md:317).
  So the theory of every module is the theory in scope in the user module (the last) exactly when
  the modules its imports reach are the modules before it. On base:
  - `imports_earlier`: every import of every module names a module earlier in the text;
  - `imports_cover`: the modules reached from the user module through imports, transitively, are
    exactly the modules before it (BASE imports K; K imports KSEQ and INJ; KSEQ imports BASIC-K).
  Both are `Bool` checks on any `Kore.Definition`, decided on the literal. The tests of the checks:
  with the user module's import replaced by one of INJ, the cover check is false
  (`importsBase_inj_not_cover`; every import is still earlier); with one of a module the text does
  not hold, both are false; with the import removed, the cover check is false.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.ImportsBase

kore_term kore from "f2-examples/base.kompile.kore"

/-- The modules a module's import sentences name, in text order. -/
def importsOf (m : Kore.Module) : List Kore.ModuleName :=
  m.sentences.filterMap fun
    | .import i => some i.module
    | _ => none

/-- The modules the modules of name `n` import. -/
def importsOfName (d : Kore.Definition) (n : Kore.ModuleName) : List Kore.ModuleName :=
  (d.modules.filter (·.name == n)).flatMap importsOf

/-- `k` rounds of following imports from the names `s`: each round adds the names the modules of
    the current names import. Every name it returns is `s`'s or reached from `s` through imports. -/
def reachImports (d : Kore.Definition) : Nat → List Kore.ModuleName → List Kore.ModuleName
  | 0, s => s
  | k + 1, s => reachImports d k (s ++ ((s.flatMap (importsOfName d)).filter (!s.contains ·)).eraseDups)

/-- The names reached from the user module (the last) through its imports, followed as many rounds
    as the text has modules. -/
def userImportClosure (d : Kore.Definition) : List Kore.ModuleName :=
  match d.modules.getLast? with
  | none => []
  | some u => reachImports d d.modules.length (importsOf u)

/-- Every import of every module names a module earlier in the text (kore-syntax.md:317). -/
def importsEarlierB (d : Kore.Definition) : Bool :=
  d.modules.zipIdx.all fun (m, i) =>
    (importsOf m).all fun n => (d.modules.take i).any (·.name == n)

/-- The modules reached from the user module through imports are exactly the modules before it.
    `R := userImportClosure d` holds only names reached (`reachImports`); `R` closed under imports
    makes it every name reached, whatever the number of rounds; then `R` and the names of the
    modules before the last are equal as sets. -/
def importsCoverB (d : Kore.Definition) : Bool :=
  let L := d.modules.dropLast.map (·.name)
  let R := userImportClosure d
  (R.all fun n => (importsOfName d n).all R.contains) && R.all L.contains && L.all R.contains

/-- The definition with every import of the user module (the last) naming module `n`. -/
def withUserImport (d : Kore.Definition) (n : String) : Kore.Definition :=
  { d with modules := d.modules.dropLast ++ (d.modules.getLast?.map fun u =>
      { u with sentences := u.sentences.map fun
          | .import i => .import ⟨⟨⟨n⟩⟩, i.attributes⟩
          | s => s }).toList }

/-- The definition without the user module's import sentences. -/
def withoutUserImports (d : Kore.Definition) : Kore.Definition :=
  { d with modules := d.modules.dropLast ++ (d.modules.getLast?.map fun u =>
      { u with sentences := u.sentences.filter fun
          | .import _ => false
          | _ => true }).toList }

/-- Every import sentence of base names a module earlier in the text. -/
theorem imports_earlier : importsEarlierB kore = true := by decide +kernel

/-- The import closure of base's user module is exactly the modules before it. -/
theorem imports_cover : importsCoverB kore = true := by decide +kernel

/-- The closure itself, in the order the rounds reach it. -/
theorem importsBase_closure :
    userImportClosure kore = [⟨⟨"K"⟩⟩, ⟨⟨"KSEQ"⟩⟩, ⟨⟨"INJ"⟩⟩, ⟨⟨"BASIC-K"⟩⟩] := by decide +kernel

/-- With the user module importing INJ, every import is earlier, and the closure misses K, KSEQ
    and BASIC-K. -/
theorem importsBase_inj_earlier : importsEarlierB (withUserImport kore "INJ") = true := by
  decide +kernel
theorem importsBase_inj_not_cover : importsCoverB (withUserImport kore "INJ") = false := by
  decide +kernel

/-- With the user module importing a module the text does not hold, neither check holds. -/
theorem importsBase_nosuch_not_earlier : importsEarlierB (withUserImport kore "NOSUCH") = false := by
  decide +kernel
theorem importsBase_nosuch_not_cover : importsCoverB (withUserImport kore "NOSUCH") = false := by
  decide +kernel

/-- Without the user module's import, the closure is empty and misses every module before it. -/
theorem importsBase_noimport_not_cover : importsCoverB (withoutUserImports kore) = false := by
  decide +kernel

end KCore.ImportsBase

#print axioms KCore.ImportsBase.imports_earlier
#print axioms KCore.ImportsBase.imports_cover
#print axioms KCore.ImportsBase.importsBase_closure
#print axioms KCore.ImportsBase.importsBase_inj_earlier
#print axioms KCore.ImportsBase.importsBase_inj_not_cover
#print axioms KCore.ImportsBase.importsBase_nosuch_not_earlier
#print axioms KCore.ImportsBase.importsBase_nosuch_not_cover
#print axioms KCore.ImportsBase.importsBase_noimport_not_cover
