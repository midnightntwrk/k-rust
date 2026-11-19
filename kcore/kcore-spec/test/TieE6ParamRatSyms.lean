/-
  The four symbol declarations of module RAT (rat.md:163, :164, :176, :196) in
  `f2-examples/e6-param-rat.kompile.kore` that carry no `hook` attribute: `makeRat/2`, `makeRat/3`,
  `gcdInt` and `powRat`, functions RAT defines by its own equations. Each is a declaration of the
  text without sort parameters (`ratUnhookedDecls_declared`) and names a symbol of Γ
  (`ratUnhookedDecls_has`, `hasSym` as the ties state it: a symbol of `kernelSyms c` of that name).

  Γ of this text has no model, for every H (`KCore.TieE6ParamRatNoModel.no_model_text`), so an
  entailment from it is vacuous; this file states what does not rest on that: that the reading
  holds each of the four as a symbol of Γ.

  Run from the package root: `lake env lean -j1 test/TieE6ParamRatSyms.lean`.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.TieE6ParamRatSyms

open KCore ML Faithful KoreAML

kore_term kore from "f2-examples/e6-param-rat.kompile.kore"
definition_of defn from "f2-examples/e6-param-rat.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem

/-- A symbol of Γ by its name in the text. -/
noncomputable def hasSym (n : String) : Bool := (kernelSyms c).any fun k => c.symName k.name == n

/-- RAT's symbol declarations without a `hook` attribute, by name. -/
def ratUnhookedDecls : List String :=
  ["LblgcdInt'LParUndsCommUndsRParUnds'RAT'Unds'Int'Unds'Int'Unds'Int",
   "LblmakeRat'LParUndsCommUndsRParUnds'RAT'Unds'Rat'Unds'Int'Unds'Int",
   "LblmakeRat'LParUndsCommUndsCommUndsRParUnds'RAT'Unds'Rat'Unds'Int'Unds'Int'Unds'Int",
   "LblpowRat'LParUndsCommUndsRParUnds'RAT'Unds'Rat'Unds'Rat'Unds'Int"]

/-- Each is a symbol declaration of the text (a `symbol`, not a `hooked-symbol`), without sort
parameters. -/
theorem ratUnhookedDecls_declared :
    ratUnhookedDecls.all (fun n => kore.symbolDecls.any fun sd =>
      sd.name == n && sd.params.isEmpty && !sd.hooked) = true := by
  decide +kernel

/-- **Each names a symbol of Γ.** -/
theorem ratUnhookedDecls_has : ratUnhookedDecls.all hasSym = true := by decide +kernel

end KCore.TieE6ParamRatSyms

#check @KCore.TieE6ParamRatSyms.ratUnhookedDecls_declared
#check @KCore.TieE6ParamRatSyms.ratUnhookedDecls_has
#print axioms KCore.TieE6ParamRatSyms.ratUnhookedDecls_declared
#print axioms KCore.TieE6ParamRatSyms.ratUnhookedDecls_has
