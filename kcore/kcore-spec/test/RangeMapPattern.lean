/-
  A range-map symbol binding a variable in a left side is refused (`rangeMapPattern`), and a rule of
  that shape is not sorted. Run from the package root: `lake env lean test/RangeMapPattern.lean`.
  kompile 7.1.337 rejects the shape in a K text (fixture e6-rangemap-pattern: exit 113, "Illegal
  function symbol _RangeMap_ on LHS of rule"), so the text read here is hand-written: the fixture
  hw-rangemap-pattern, `f2-examples/e6rm.kompile.kore` with one rewrite axiom added,
  `<k> res(I, X, Y, B1, B2, J, R, K, L, (RangeMap:Range(A, B) r|-> V) Rest) => V </k>`.
  - The reader: the account refuses that rule, `_RangeMap_` and `_r|->_` named, and nothing else;
    `functionInPattern` names neither (they are collection symbols); the definition is read and
    not well formed, its rules not sorted. e6-rangemap's own text has no such refusal.
  - The kernel, at e6-rangemap's semantics: no range-map symbol is in `patternHooks`,
    `collPatternHooks` or the heads of `patCtxAll` (the decided condition of the row); the rule
    built by hand, the one the reader reads from the added axiom (`rmRule_read`), has a left side
    `patCtxAll` does not sort, at its range-map subterm, so `ruleSorted` is false; the same rule
    with a variable of sort RangeMap in place of that subterm is sorted.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.RangeMapPatternTest

open KCore

/-! ## The reader -/

/-- The account's `rangeMapPattern` and `functionInPattern` refusals of the text at `path`, and
whether it is well formed with its failing parts; or its first refusal. -/
def verdict (path : String) : IO String := do
  match Kore.parseDefinition (← IO.FS.readFile path) with
  | .error e => return s!"KORE read error {e}"
  | .ok k => return match Parse.parse k with
    | .error r => s!"refused: {r.toText}"
    | .ok d =>
      let rp := (Parse.accountRefusals k d).filter (·.reason == .rangeMapPattern)
      s!"rangeMapPattern {rp.map Parse.Refusal.toText}; functionInPattern {(Parse.functionInPattern k d).length}; " ++
        s!"account {(Parse.accountRefusals k d).length}; wf {KCore.wf d}; failing {(d.report.filter (!·.2)).map (·.1)}"

/--
info: rangeMapPattern [sentence 475 (Lbl'-LT-'generatedTop'-GT-'): rangeMapPattern (Lbl'Unds'RangeMap'Unds'), sentence 475 (Lbl'-LT-'generatedTop'-GT-'): rangeMapPattern (Lbl'Unds'r'Pipe'-'-GT-Unds')]; functionInPattern 0; account 2; wf false; failing [rules: well-sorted over the configuration sort]
rangeMapPattern []; functionInPattern 0; account 0; wf true; failing []
-/
#guard_msgs in
#eval show IO Unit from do
  IO.println (← verdict "test/constructs/fixtures/hw-rangemap-pattern/hw-rangemap-pattern.kore")
  IO.println (← verdict "f2-examples/e6rm.kompile.kore")

/-! ## The kernel -/

definition_of defn from "f2-examples/e6rm.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem

/-- The range-map symbols: `.RangeMap`, `_r|->_`, `_RangeMap_`. -/
def rmSyms : List Sym := [rmUnit, rmElem, rmConcat]

/-- The decided condition of the row: no list of pattern symbols holds a range-map symbol. -/
theorem rm_not_patternHooks :
    rmSyms.all (fun g => !patternHooks.contains g && !collPatternHooks.contains g) = true := by
  decide

/-- So the left sides' context of e6-rangemap has no range-map symbol among its heads. -/
theorem patCtxAll_no_rm : (c.patCtxAll.heads.map (·.name)).all (fun g => !rmSyms.contains g) = true := by
  decide +kernel

/-- The symbols the rule applies, by their names in the text. -/
theorem syms_named :
    c.symName topLabel = "Lbl'-LT-'generatedTop'-GT-'" ∧ c.symName 382 = "Lbl'-LT-'k'-GT-'" ∧
      c.symName 388 = "Lblres" ∧ c.symName rmConcat = "Lbl'Unds'RangeMap'Unds'" ∧
      c.symName rmElem = "Lbl'Unds'r'Pipe'-'-GT-Unds'" ∧ c.symName rangeCtor = "LblRangeMap'Coln'Range" := by
  decide +kernel

/-- `<generatedTop> <k> res(V0, …, V8, t) </k> V13 </generatedTop>`. -/
def lhsWith (t : Term) (cnt : Nat) : Term :=
  .app topLabel [.app 382 [.app kseq [.app 388 [.var 0, .var 1, .var 2, .var 3, .var 4, .var 5, .var 6,
    .var 7, .var 8, t], .app dotk []]], .var cnt]

/-- `([A, B) r|-> V) Rest`, A, B, V, Rest the variables 9 to 12. -/
def rmPat : Term := .app rmConcat [.app rmElem [.app rangeCtor [.var 9, .var 10], .var 11], .var 12]

/-- The rule: Int, KItem, KItem, Bool, Bool, Int, Range, Int, Int, then A, B, V of KItem, Rest of
RangeMap, the generated counter cell. -/
def rmRule : Rule :=
  { vars := [3, 1, 1, 2, 2, 3, 28, 3, 3, 1, 1, 1, 29, 19], lhs := lhsWith rmPat 13, req := none,
    rhs := .app topLabel [.app 382 [.app kseq [.var 11, .app dotk []]], .var 13], ens := none, prio := 50 }

/-- The same rule with Rest, of sort RangeMap, in place of the range-map pattern. -/
def ctlRule : Rule :=
  { vars := [3, 1, 1, 2, 2, 3, 28, 3, 3, 29, 19], lhs := lhsWith (.var 9) 10, req := none,
    rhs := .app topLabel [.app 382 [.app kseq [.var 1, .app dotk []]], .var 10], ens := none, prio := 50 }

theorem rmPat_unsorted : sortOfTerm c.patCtxAll rmRule.vars rmPat = none := by decide +kernel

theorem rmRule_unsorted : c.ruleSorted rmRule = false := by decide +kernel

theorem ctlRule_sorted : c.ruleSorted ctlRule = true := by decide +kernel

-- `rmRule_read`: the rule the reader reads from the added axiom is `rmRule` (compared by `repr`;
-- the text's other rule is `go`'s).
/--
info: true
-/
#guard_msgs in
#eval show IO Unit from do
  match Kore.parseDefinition (← IO.FS.readFile "test/constructs/fixtures/hw-rangemap-pattern/hw-rangemap-pattern.kore") with
  | .error e => IO.println s!"KORE read error {e}"
  | .ok k => match Parse.parse k with
    | .error r => IO.println s!"refused: {r.toText}"
    | .ok d => IO.println ((d.sem.rules.map fun r => reprStr r).contains (reprStr rmRule))

end KCore.RangeMapPatternTest
