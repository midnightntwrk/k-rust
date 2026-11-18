/-
  The three law axioms of `_RangeMap_` in the fixture `e6-rangemap` (its kompiled text
  `f2-examples/e6rm.kompile.kore`) are classified as the laws of a collection's concatenation, and
  the laws they state hold at range-map values. Run from the package root:
  `lake env lean test/RangeMapLawClass.lean`.
  - The reader: sentences 245, 246 and 247 (file lines 304-306: associativity, right unit, left unit) are
    `inert collectionLaw` with the head `Lbl'Unds'RangeMap'Unds'`, and the account refuses no law
    axiom (`lawUnmatched`), the head being the concatenation of a collection of the definition.
  - The kernel: that head is the concatenation of the range-map collection of `allColls`, whose unit
    is `.RangeMap` (`rangeMapColl_named`); at that collection's symbols the hook table gives the
    laws at values (`rangeMapLaws_hook`, from `rmConcat_assoc` and `rmConcat_unit`): associativity
    as an equality of patterns (both sides undefined, or one value) and the unit on either side.
    Instances: associativity at three range maps of which the concatenation is defined on both
    sides, and at three where both sides are undefined (an overlap); the unit at `M`.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.RangeMapLawClassTest

open KCore

/-! ## The reader's classification -/

/-- The user module's sentences classified `inert collectionLaw` with the head `h`, each with its
place in the file and its law attributes; and the account's law refusals. -/
def lawsOf (path h : String) : IO (List (Nat × List String) × List String) := do
  match Kore.parseDefinition (← IO.FS.readFile path) with
  | .error e => return ([], [s!"KORE read error {e}"])
  | .ok k => match k.modules.getLast?, Parse.parse k with
    | some m, .ok d =>
      let off := Parse.preludeLength k
      let ls := m.sentences.zipIdx.filterMap fun (s, i) => match s with
        | .axiom a =>
          if Parse.classifyShape s == .inert .collectionLaw && Parse.lawHead? a == some h then
            some (off + i, Parse.lawKeys a)
          else none
        | _ => none
      return (ls, (Parse.lawUnmatched k d).map Parse.Refusal.toText)
    | _, .error r => return ([], [s!"refused: {r.toText}"])
    | none, _ => return ([], ["no module"])

/--
info: ([(245, [assoc]), (246, [unit]), (247, [unit])], [])
-/
#guard_msgs in
#eval show IO Unit from do
  IO.println (← lawsOf "f2-examples/e6rm.kompile.kore" "Lbl'Unds'RangeMap'Unds'")

/-! ## The head is the range-map collection's concatenation -/

definition_of defn from "f2-examples/e6rm.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem

/-- The collection `lawUnmatched` finds for the head: the range-map row of `allColls`, its
concatenation named `Lbl'Unds'RangeMap'Unds'` and its unit `Lbl'Stop'RangeMap` in the text. -/
theorem rangeMapColl_named :
    builtinColl .rangeMap ∈ c.allColls ∧ (builtinColl .rangeMap).kind = .rangeMap ∧
      c.symName (builtinColl .rangeMap).concat = "Lbl'Unds'RangeMap'Unds'" ∧
      c.symName (builtinColl .rangeMap).unit = "Lbl'Stop'RangeMap" := by
  decide +kernel

/-! ## The laws at values, at the collection's symbols -/

/-- **The three laws hold at range-map values**, at the concatenation and unit of the range-map
collection, through the hook table: associativity as an equality of patterns, and the unit on
either side. -/
theorem rangeMapLaws_hook {es fs gs : Entries} (he : rangesOK es = true) (hf : rangesOK fs = true)
    (hg : rangesOK gs = true) :
    ((hook (builtinColl .rangeMap).concat [rmV es, rmV fs]).join.bind fun x =>
        (hook (builtinColl .rangeMap).concat [x, rmV gs]).join) =
      ((hook (builtinColl .rangeMap).concat [rmV fs, rmV gs]).join.bind fun y =>
        (hook (builtinColl .rangeMap).concat [rmV es, y]).join) ∧
    hook (builtinColl .rangeMap).unit [] = some (some (rmV [])) ∧
    hook (builtinColl .rangeMap).concat [rmV [], rmV es] = some (some (rmV es)) ∧
    hook (builtinColl .rangeMap).concat [rmV es, rmV []] = some (some (rmV es)) :=
  ⟨rmConcat_assoc he hf hg, rmConcat_unit he⟩

/-! ## Instances -/

/-- Two KItem values of the text (`a`, `b`). -/
def a : GroundTerm := .ctor 384 []
def b : GroundTerm := .ctor 385 []

theorem ab_named : c.symName 384 = "Lbla" ∧ c.symName 385 = "Lblb" := by decide +kernel

def M : Entries := [(rangeT 0 3, a), (rangeT 5 7, b)]
def N : Entries := [(rangeT 7 9, a)]
def P : Entries := [(rangeT 2 4, a)]

theorem M_ok : rangesOK M = true := by decide +kernel
theorem N_ok : rangesOK N = true := by decide +kernel
theorem P_ok : rangesOK P = true := by decide +kernel
theorem nil_ok : rangesOK [] = true := by decide +kernel

/-- Associativity where both sides are one value. -/
theorem assoc_defined :
    ((hook (builtinColl .rangeMap).concat [rmV M, rmV []]).join.bind fun x =>
        (hook (builtinColl .rangeMap).concat [x, rmV N]).join) =
      ((hook (builtinColl .rangeMap).concat [rmV [], rmV N]).join.bind fun y =>
        (hook (builtinColl .rangeMap).concat [rmV M, y]).join) :=
  (rangeMapLaws_hook M_ok nil_ok N_ok).1

theorem assoc_defined_value :
    ((hook (builtinColl .rangeMap).concat [rmV M, rmV []]).join.bind fun x =>
        (hook (builtinColl .rangeMap).concat [x, rmV N]).join) =
      some (rmV [(rangeT 0 3, a), (rangeT 5 7, b), (rangeT 7 9, a)]) := by
  decide +kernel

/-- Associativity where both sides are undefined: `[2,4)` overlaps `[0,3)`. -/
theorem assoc_overlap :
    ((hook (builtinColl .rangeMap).concat [rmV M, rmV N]).join.bind fun x =>
        (hook (builtinColl .rangeMap).concat [x, rmV P]).join) =
      ((hook (builtinColl .rangeMap).concat [rmV N, rmV P]).join.bind fun y =>
        (hook (builtinColl .rangeMap).concat [rmV M, y]).join) :=
  (rangeMapLaws_hook M_ok N_ok P_ok).1

theorem assoc_overlap_none :
    ((hook (builtinColl .rangeMap).concat [rmV M, rmV N]).join.bind fun x =>
        (hook (builtinColl .rangeMap).concat [x, rmV P]).join) = none := by
  decide +kernel

/-- The unit on either side of `M`. -/
theorem unit_M :
    hook (builtinColl .rangeMap).unit [] = some (some (rmV [])) ∧
    hook (builtinColl .rangeMap).concat [rmV [], rmV M] = some (some (rmV M)) ∧
    hook (builtinColl .rangeMap).concat [rmV M, rmV []] = some (some (rmV M)) :=
  (rangeMapLaws_hook M_ok nil_ok nil_ok).2

end KCore.RangeMapLawClassTest
