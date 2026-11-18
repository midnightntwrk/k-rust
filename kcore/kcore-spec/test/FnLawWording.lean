/-
  The account's entry for each law under `FnLaws` (`Parse.fnLawEntry`, from `Parse.lawReads`), on
  the kompiled text of fixture e2-fn-assoc-unit (`f2-examples/e2-fn-assoc-unit.kompile.kore`, as
  test/FnUnitKompiled.lean reads it: `pu(A, B) => A +Int B`, `zero => 0`, and the three laws of
  `pu`) and on two semantics made from it by hand (not kompiled texts):
  - the text: `pu` and `zero` each have one clause with no condition over distinct variables, so
    their clauses apply at every argument list, and `+Int` has no point its text leaves open. No
    term of the three laws reads the interpretation: each entry is "FnLaws owed, open"
    (`text_entries`), never "false" and never a claim that the law holds.
  - `cRest`: `pu`'s clause is `pu(0, B) => B` alone, so at `pu(1, B)` every clause fails and the
    value is `pu`'s rest, the interpretation's. Each law reads it, and each entry is "a condition
    on the interpretation", "not discharged at HookParams.none" (`rest_entries`).
  - `cParam`: `pu` is a parameter symbol no hook implements, as the clause-less `pk` of fixture
    e2-fn-assoc-rest is read: each law reads the parameter (`param_reads`).

  Run from the package root: `lake env lean -j1 test/FnLawWording.lean`.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.FnLawWording

definition_of defn from "f2-examples/e2-fn-assoc-unit.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem

def pu : Sym := 384

theorem names : c.symName pu = "Lblpu" := by decide +kernel

theorem three_laws : defn.laws.length = 3 := by decide +kernel

def openEntry : String :=
  "FnLaws owed, open: no term of the law reads the interpretation, so it is one fact at every interpretation, not decided here"

/-- On the text, every law is owed and open. -/
theorem text_entries : defn.laws.map (Parse.fnLawEntry c) = [openEntry, openEntry, openEntry] := by
  decide +kernel

/-- `pu(0, B) => B`: a clause that does not apply at every argument list. -/
def clPu0 : Clause :=
  ⟨[Srt.int], [.dv Srt.int (.int 0), .var 0], none, .var 0, none, 50, false, [], .top, .top⟩

noncomputable def cRest : Semantics :=
  { c with fns := c.fns.map fun f => if f.label == pu then { f with clauses := [clPu0] } else f }

def restEntry : String :=
  "FnLaws owed: a condition on the interpretation (the law reads the rest of Lblpu: its value where its clauses are not shown to apply is the interpretation's); not discharged at HookParams.none"

/-- Where `pu`'s clauses leave arguments to its rest, every law of `pu` is a condition on the
interpretation, not discharged at `HookParams.none`. -/
theorem rest_entries : defn.laws.map (Parse.fnLawEntry cRest) = [restEntry, restEntry, restEntry] := by
  decide +kernel

noncomputable def cParam : Semantics :=
  { c with fns := c.fns.filter (·.label != pu),
           params := c.params ++ [{ sig := ⟨pu, [Srt.int, Srt.int], Srt.int⟩ }] }

/-- Where `pu` is a parameter no hook implements, every law of `pu` reads it. -/
theorem param_reads : defn.laws.map (Parse.lawReads cParam) =
    List.replicate 3 (some "the parameter Lblpu: its value is the interpretation's") := by
  decide +kernel

end KCore.FnLawWording
