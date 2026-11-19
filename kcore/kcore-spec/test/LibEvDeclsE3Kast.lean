/-
  ID-COMMON's `freshId` and `String2Id` on the text of the fixture e3-kast
  (`f2-examples/e3-kast.kompile.kore`: INT and ID imported): the text declares both, and neither
  names a symbol of Γ. Nothing here reads `Parse.parse` or `emit`. Run from the package root:
  `lake env lean -j1 test/LibEvDeclsE3Kast.lean`.

  Each is a parameter symbol of the library's module ID-COMMON (a function of the library no hook
  of the registry interprets: `library`'s `params`, not in `hookSigs`): `freshId` the registry
  symbol 322, `String2Id` 321. The reading has no parameter symbol (`c.params = []`: no rule and
  no function of the reading applies either), so Γ has no symbol under either name.
  - `freshId_absent`: `freshId` is declared once, without sort parameters, and Γ has no symbol of
    its name. The sentences of the text that apply it are two: its `functional` axiom (110), whose
    one head it is, and its equation (268, domains.md 2299), whose heads Γ lacks are `freshId` and
    `String2Id`.
  - `string2Id_absent`: the same of `String2Id`, with its `functional` axiom (48).
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.LibEvDeclsE3Kast

open KCore ML Faithful KoreAML

kore_term kore from "f2-examples/e3-kast.kompile.kore"
definition_of defn from "f2-examples/e3-kast.kompile.kore"
user_axioms U from "f2-examples/e3-kast.kompile.kore" module "E3-KAST"

noncomputable abbrev c : Semantics := defn.sem

/-- Γ has a symbol under the name `n`. -/
noncomputable def hasSym (n : String) : Bool := (kernelSyms c).any fun k => c.symName k.name == n

/-- The names of the heads a sentence applies, each with its sort arguments (`appHeadsOf`), that are
not Γ's (`gammaHeads`). -/
noncomputable def absentOf (ad : AxiomDecl) : List String :=
  ((appHeadsOf ad.ax.pattern).filter fun h => !gammaHasHead c h).map (·.1)

def freshIdName : String := "LblfreshId'LParUndsRParUnds'ID-COMMON'Unds'Id'Unds'Int"
def string2IdName : String := "LblString2Id'LParUndsRParUnds'ID-COMMON'Unds'Id'Unds'String"

/-- A library module's parameter symbols hold the registry symbol `f`, and no hook of the registry
interprets it. -/
def libParamOf (m : String) (f : Sym) : Bool :=
  (library.find? (·.name == m)).any (·.params.any (·.name == f)) && hookSigs.all (·.name != f)

/-- The sentences of the user module that apply the head named `n`. -/
noncomputable def appliers (n : String) : List Nat :=
  (U.all.filter fun ad => (appHeadsOf ad.ax.pattern).any (·.1 == n)).map (·.index)

/-- **`freshId` is declared and Γ lacks it**: the text declares it once, without sort parameters;
it is ID-COMMON's parameter symbol 322, which no hook interprets; the reading has no parameter
symbol, so Γ has no symbol under its name. Its `functional` axiom (110) and its equation (268)
are the sentences applying it; the heads of 268 that Γ lacks are `freshId` and `String2Id`. -/
theorem freshId_absent :
    (kore.symbolDecls.filter (·.name == freshIdName)).map (·.params.isEmpty) = [true] ∧
    c.symName 322 = freshIdName ∧ libParamOf "ID-COMMON" 322 = true ∧
    c.params = [] ∧ hasSym freshIdName = false ∧ appliers freshIdName = [110, 268] ∧
    absentOf U.ax110 = [freshIdName] ∧ absentOf U.ax268 = [freshIdName, string2IdName] := by
  decide +kernel

/-- **`String2Id` is declared and Γ lacks it**: declared once, without sort parameters; ID-COMMON's
parameter symbol 321, which no hook interprets; Γ has no symbol under its name. Its `functional`
axiom (48) and `freshId`'s equation (268) are the sentences applying it. -/
theorem string2Id_absent :
    (kore.symbolDecls.filter (·.name == string2IdName)).map (·.params.isEmpty) = [true] ∧
    c.symName 321 = string2IdName ∧ libParamOf "ID-COMMON" 321 = true ∧
    hasSym string2IdName = false ∧ appliers string2IdName = [48, 268] ∧
    absentOf U.ax48 = [string2IdName] := by
  decide +kernel

end KCore.LibEvDeclsE3Kast

#check @KCore.LibEvDeclsE3Kast.freshId_absent
#check @KCore.LibEvDeclsE3Kast.string2Id_absent
/-- info: 'KCore.LibEvDeclsE3Kast.freshId_absent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvDeclsE3Kast.freshId_absent
/-- info: 'KCore.LibEvDeclsE3Kast.string2Id_absent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvDeclsE3Kast.string2Id_absent
