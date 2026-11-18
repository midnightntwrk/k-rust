/-
  The tie's statement definitions on `f2-examples/rulecool.kompile.kore` (fixture e2-rule):
  `surplusItem` at two sort constants, `attrsAgree` at the whole text (`attrs_agree`), with the
  pairing of the function sentences' priorities (`fn_prios`). The rest of the tie is
  test/TieRuleCoolText.lean's. Run from the package root: `lake env lean -j1 test/TieRuleCoolAttrs.lean`.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.TieRuleCoolAttrs

open KCore ML Faithful KoreAML

kore_term kore from "f2-examples/rulecool.kompile.kore"
definition_of defn from "f2-examples/rulecool.kompile.kore"
user_axioms U from "f2-examples/rulecool.kompile.kore" module "E2-RULE"

noncomputable abbrev c : Semantics := defn.sem


/-- The function sentences, in the order of Γ's equations (test/TieRuleCoolText.lean's `fnText`). -/
noncomputable def fnText : List AxiomDecl := TiePair.fnTextOf c U.all

/-! ## The tie's statement definitions on this text

`surplusItem` at two sort constants, `attrsAgree` at the whole text, with the pairing of the
function sentences' priorities. -/

/-- The text declares no sort `Float`, so Γ's sort constant of Float is surplus; it declares `Int`,
whose sort constant is not. -/
theorem surplus_float : surplusItem kore (KoreAML.sortConstantItem (sortDeclOf c Srt.float)) = true ∧
    surplusItem kore (KoreAML.sortConstantItem (sortDeclOf c Srt.int)) = false := by decide +kernel

/-- **The attributes of the text agree with `defn`** (`attrsAgree`): constructors, functions,
hooks, collection symbols, priorities. -/
theorem attrs_agree : attrsAgree kore defn = true := by decide +kernel

/-- The priority each function sentence's attributes state is the priority of the clause whose
item is the sentence's translation (test/TieRuleCoolText.lean's `shape`), item by item in `fnItems`'s order: `attrsAgree`
compares a function's priorities up to order, this pairs them. -/
theorem fn_prios : fnText.map (fun ad => AttrsAgree.prioOf ad.ax.attributes) =
    c.allFns.flatMap (fun f => f.clauses.map (·.prio)) := by decide +kernel

end KCore.TieRuleCoolAttrs

#print axioms KCore.TieRuleCoolAttrs.surplus_float
#print axioms KCore.TieRuleCoolAttrs.attrs_agree
#print axioms KCore.TieRuleCoolAttrs.fn_prios
