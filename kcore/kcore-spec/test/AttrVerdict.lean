/-
  The reader's attribute verdicts against the construct table (DONE-0 C4 part 2).

  `rowsE2` is E2's rows of a class other than `frontend`, written out: class, key and the row's
  status. Each verdict of `Parse.attrVerdict` at a row is the row's status (`read` for supported,
  `inert` for inert, `refused` for refused and for erased), checked by the kernel. The file prints
  one line per row (`row CLASS NAME STATUS`) and one per key (`key NAME KORE-SPELLING`), which
  test/constructs.sh compares with test/constructs/rows.toml: the rows written here are the
  table's, and the keys of `AttrKeyE2` are the names of those rows.
-/
import KcoreSpec.Parse

open KCore.Parse

/-- A row's status. -/
inductive StatusE2 where
  | supported | inert | refused | erased
  deriving Repr, DecidableEq

def StatusE2.name : StatusE2 → String
  | .supported => "supported" | .inert => "inert" | .refused => "refused" | .erased => "erased"

/-- The status a verdict stands for: an erased row's key is refused. -/
def StatusE2.is : StatusE2 → AttrVerdict → Bool
  | .supported, .read => true
  | .inert, .inert _ => true
  | .refused, .refused _ _ => true
  | .erased, .refused _ _ => true
  | _, _ => false

/-- E2's rows of a class other than `frontend`. -/
def rowsE2 : List (AttrClassE2 × AttrKeyE2 × StatusE2) := [
  (.symbol, .alias, .inert),
  (.symbol, .aliasRec, .inert),
  (.rule, .anywhere, .refused),
  (.equation, .anywhere, .refused),
  (.simplification, .anywhere, .refused),
  (.symbol, .assoc, .refused),
  (.symbol, .binder, .inert),
  (.symbol, .bracket, .erased),
  (.symbol, .cell, .supported),
  (.claim, .circularity, .inert),
  (.symbol, .colors, .erased),
  (.symbol, .comm, .refused),
  (.rule, .comm, .inert),
  (.equation, .comm, .inert),
  (.simplification, .comm, .inert),
  (.module, .concrete, .erased),
  (.symbol, .concrete, .inert),
  (.rule, .concrete, .inert),
  (.equation, .concrete, .inert),
  (.simplification, .concrete, .inert),
  (.symbol, .constructor, .supported),
  (.rule, .cool, .inert),
  (.equation, .cool, .supported),
  (.simplification, .cool, .inert),
  (.claim, .depends, .inert),
  (.symbol, .deprecated, .inert),
  (.symbol, .element, .supported),
  (.symbol, .format, .erased),
  (.symbol, .freshGenerator, .inert),
  (.symbol, .function, .supported),
  (.symbol, .functional, .supported),
  (.symbol, .hook, .supported),
  (.sort, .hook, .supported),
  (.symbol, .idem, .supported),
  (.symbol, .impure, .inert),
  (.symbol, .injective, .inert),
  (.symbol, .klabel, .inert),
  (.sort, .label, .inert),
  (.symbol, .label, .inert),
  (.rule, .label, .supported),
  (.equation, .label, .supported),
  (.simplification, .label, .supported),
  (.claim, .label, .inert),
  (.symbol, .macroKey, .inert),
  (.symbol, .macroRec, .inert),
  (.symbol, .memo, .inert),
  (.rule, .nonExecutable, .refused),
  (.equation, .nonExecutable, .supported),
  (.simplification, .nonExecutable, .inert),
  (.symbol, .noEvaluators, .inert),
  (.rule, .owise, .supported),
  (.equation, .owise, .supported),
  (.simplification, .owise, .refused),
  (.rule, .preservesDefinedness, .inert),
  (.equation, .preservesDefinedness, .inert),
  (.simplification, .preservesDefinedness, .inert),
  (.rule, .priority, .supported),
  (.symbol, .priority, .inert),
  (.equation, .priority, .supported),
  (.simplification, .priority, .refused),
  (.rule, .simplification, .refused),
  (.equation, .simplification, .inert),
  (.simplification, .simplification, .inert),
  (.symbol, .smtlib, .inert),
  (.symbol, .smtHook, .inert),
  (.rule, .smtLemma, .refused),
  (.equation, .smtLemma, .inert),
  (.simplification, .smtLemma, .inert),
  (.symbol, .symbol, .inert),
  (.module, .symbolic, .erased),
  (.symbol, .symbolic, .inert),
  (.rule, .symbolic, .inert),
  (.equation, .symbolic, .inert),
  (.simplification, .symbolic, .inert),
  (.rule, .syntactic, .refused),
  (.equation, .syntactic, .refused),
  (.simplification, .syntactic, .inert),
  (.sort, .token, .supported),
  (.symbol, .token, .supported),
  (.symbol, .total, .supported),
  (.claim, .trusted, .inert),
  (.symbol, .unit, .supported),
  (.symbol, .update, .inert),
  (.any, .concat, .supported),
  (.any, .coolLike, .inert),
  (.any, .hasDomainValues, .supported),
  (.any, .left, .erased),
  (.any, .location, .supported),
  (.any, .nat, .refused),
  (.any, .priorities, .erased),
  (.any, .right, .erased),
  (.any, .source, .supported),
  (.any, .symbolOverload, .supported),
  (.any, .terminals, .erased),
  (.any, .uniqueId, .supported)]

/-- Every row's verdict is its status. -/
theorem attrVerdict_rows : rowsE2.all (fun (c, k, s) => s.is (attrVerdict c k)) = true := by decide +kernel

/-- No row is written twice. -/
theorem rowsE2_nodup : (rowsE2.map fun (c, k, _) => (c, k)).Nodup := by decide +kernel

/-- Every key is the key of a row, and is found by its KORE spelling. -/
theorem attrKeys_rows : AttrKeyE2.all.all (fun k => rowsE2.any (·.2.1 == k)) = true := by decide +kernel
theorem attrKeys_ofName : AttrKeyE2.all.all (fun k => AttrKeyE2.ofName? k.kore == some k) = true := by
  decide +kernel

/-- A refused verdict's reason is a constructor of `RefusalReason`. -/
example : AttrRefusalE2.ruleAttribute.reason = .ruleAttribute ∧ AttrRefusalE2.outsideE2.reason = .attrOutsideE2 :=
  ⟨rfl, rfl⟩

-- the three spellings that differ from K's name, and a name that is no key
example : AttrKeyE2.ofName? "org'Stop'kframework'Stop'attributes'Stop'Location" = some .location := by decide +kernel
example : AttrKeyE2.ofName? "UNIQUE'Unds'ID" = some .uniqueId := by decide +kernel
example : AttrKeyE2.ofName? "symbol'Kywd'" = some .symbol := by decide +kernel
example : AttrKeyE2.ofName? "symbol" = none := by decide +kernel
example : AttrKeyE2.ofName? "subsort" = none := by decide +kernel

-- a key at a class with no row: the row at class `any`, else refused
example : attrVerdict .rule .uniqueId = .read := rfl
example : attrVerdict .rule .format = .refused .ruleAttribute unwritten := rfl
example : attrVerdict .symbol .bracket = .refused .outsideE2 (erased "BRACKET(bracket)@symbol") := rfl

#eval do
  for (c, k, s) in rowsE2 do IO.println s!"row {c.name} {k.name} {s.name}"
  for k in AttrKeyE2.all do IO.println s!"key {k.name} {k.kore}"

#print axioms attrVerdict_rows
