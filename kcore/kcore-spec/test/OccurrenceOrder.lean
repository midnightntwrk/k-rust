/-
  `KoreAML.tr_occurrence_order` at a condition with a binder. Run from the package root, after the
  library: `lake env lean -j1 test/OccurrenceOrder.lean`.

  `Cond.kore` writes a condition over the canonical names: the rule's variables `V0`, `V1`, … and
  each binder the next one (`Cond.binder`), whatever the text spells them. A text spells the same
  predicate with its own names, the binder among them. The two patterns differ in the spelling of
  their variables only, with one order of occurrence, so under their own tables (`tableOf`) they
  translate to one KoreAML pattern: the tie of a sentence whose rule holds a binder is this
  equation, on patterns that hold no names. No print-back check (the emitted text against the
  text's, `KoreAML.Reordered`) is stated for such a sentence: `Emit.rulePattern` writes a rule's
  predicates with `Cond.kore`, whose binder's name is not the text's.

  - `pre`: over four variables, `∃ y:Exp. y ∈ b ∧ ¬ (y ∈ G)`, G the fourth variable.
  - `text`: the predicate as a text spells it, the binder `VarY`, the free variable `VarG`.
  - `text_eq`: `text` is `Cond.kore`'s pattern with `V4` spelled `VarY` and `V3` spelled `VarG`.
  - `tie`: the two patterns have one translation, each under its own table.
  - `clash`: a renaming that spells the free variable as the binder (`V3` as `VarV4`) is not
    one-to-one, and the two translations differ: the free variable would be the bound one.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

open KCore KCore.Faithful

namespace OccurrenceOrder

definition_of defn from "f2-examples/symrule.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem

example : c.symName 386 = "Lblb" ∧ c.sortName 32 = "Exp" := by decide +kernel

def vars : List Srt := [0, 0, 32, 32]

/-- `∃ y:Exp. y ∈ b ∧ ¬ (y ∈ G)`, y the variable after the four of `vars`, G the fourth. -/
def pre : Cond := .ex 32 (.and (.mem 32 (.var 4) (.app 386 [])) (.not (.mem 32 (.var 4) (.var 3))))

/-- `Cond.kore`'s pattern for `pre`, over the canonical names. -/
noncomputable def canon : Kore.Pattern := Cond.kore c (canonVars c vars) (srtOf c topCellSort) pre

def C : Kore.KSort := KoreAML.srt "GeneratedTopCell"
def E : Kore.KSort := KoreAML.srt "Exp"
def Y : Kore.EVar := KoreAML.evar "VarY" E
def G : Kore.EVar := KoreAML.evar "VarG" E

/-- The predicate as a text spells it. -/
def text : Kore.Pattern :=
  .exist C Y (.and C [.in E C (.var (.evar Y)) (KoreAML.ap "Lblb" []),
    .not C (.in E C (.var (.evar Y)) (.var (.evar G)))])

/-- The text's spelling of the canonical names: the binder `VarY`, the fourth variable `VarG`. -/
def spell (n : String) (_ : Kore.KSort) : String :=
  if n == "VarV4" then "VarY" else if n == "VarV3" then "VarG" else n

theorem text_eq : KoreAML.renVars spell (fun n _ => n) canon = text := by decide +kernel

theorem spell_inj : KoreAML.RenInjOn spell (fun n _ => n) (([] : List Kore.SortVar).map KoreAML.sortVarKey ++
    KoreAML.varsOf canon) := by decide +kernel

/-- **The tie of the predicate with a binder**: the text's pattern and `Cond.kore`'s translate to
one pattern, each under its own table. -/
theorem tie : KoreAML.tr ⟨KoreAML.tableOf [] text, []⟩ text = KoreAML.tr ⟨KoreAML.tableOf [] canon, []⟩ canon := by
  rw [← text_eq]
  exact KoreAML.tr_occurrence_order spell (fun n _ => n) [] [] canon spell_inj

/-- The free variable spelled as the binder's canonical name. -/
def spellClash (n : String) (_ : Kore.KSort) : String := if n == "VarV3" then "VarV4" else n

/-- A spelling that gives the free variable the binder's name is not one-to-one on the pattern's
variables, and the pattern so spelled has another translation. -/
theorem clash :
    ¬ KoreAML.RenInjOn spellClash (fun n _ => n) (([] : List Kore.SortVar).map KoreAML.sortVarKey ++
        KoreAML.varsOf canon) ∧
    KoreAML.tr ⟨KoreAML.tableOf [] (KoreAML.renVars spellClash (fun n _ => n) canon), []⟩
        (KoreAML.renVars spellClash (fun n _ => n) canon) ≠
      KoreAML.tr ⟨KoreAML.tableOf [] canon, []⟩ canon := by
  refine ⟨by decide +kernel, by decide +kernel⟩

end OccurrenceOrder
