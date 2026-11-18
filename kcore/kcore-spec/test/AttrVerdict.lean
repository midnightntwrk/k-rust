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
  (.symbol, .alias, .supported),
  (.symbol, .aliasRec, .supported),
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
  (.symbol, .macroKey, .supported),
  (.symbol, .macroRec, .supported),
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
example : attrVerdict .rule .format = .inert printedForm := rfl
example : attrVerdict .rule .uniqueId = .read ∧ attrVerdict .equation .symbolOverload = .read := ⟨rfl, rfl⟩

/-! The verdicts the readers of a rewrite axiom and of a function equation apply (`ruleAttrFault?`,
`eqnAttrFault?`): every refusal at class `rule` is `ruleAttribute` and at class `equation`
`equationAttribute`; the keys read at a rule are those `Parse.ruleBody` reads (its id, label,
priority, place, `owise`), and the inert ones the presentation keeps (`inertRuleAttrs` and
`inertArgAttrs` of DefinitionWf, written out). -/

def verdictKeys (c : AttrClassE2) (p : AttrVerdict → Bool) : List String :=
  (AttrKeyE2.all.filter fun k => p (attrVerdict c k)).map (·.kore)

def isRefusedBy (r : AttrRefusalE2) : AttrVerdict → Bool
  | .refused r' _ => r' == r
  | _ => false

def isRead : AttrVerdict → Bool
  | .read => true
  | _ => false

def isInert : AttrVerdict → Bool
  | .inert _ => true
  | _ => false

def isRefused : AttrVerdict → Bool
  | .refused _ _ => true
  | _ => false

theorem rule_refusals : AttrKeyE2.all.all (fun k => !isRefused (attrVerdict .rule k) || isRefusedBy .ruleAttribute (attrVerdict .rule k)) = true := by decide +kernel
theorem equation_refusals : AttrKeyE2.all.all (fun k => !isRefused (attrVerdict .equation k) || isRefusedBy .equationAttribute (attrVerdict .equation k)) = true := by decide +kernel

theorem rule_read : verdictKeys .rule isRead =
    ["label", "org'Stop'kframework'Stop'attributes'Stop'Location", "org'Stop'kframework'Stop'attributes'Stop'Source",
     "owise", "priority", "UNIQUE'Unds'ID"] := by decide +kernel
theorem rule_inert : verdictKeys .rule isInert =
    ["colors", "comm", "concrete", "cool", "cool-like", "format", "preserves-definedness", "symbol'Kywd'", "symbolic"] := by
  decide +kernel
theorem equation_read : verdictKeys .equation isRead =
    ["cool", "label", "non-executable", "org'Stop'kframework'Stop'attributes'Stop'Location",
     "org'Stop'kframework'Stop'attributes'Stop'Source", "owise", "priority", "symbol-overload", "UNIQUE'Unds'ID"] := by
  decide +kernel
theorem equation_inert : verdictKeys .equation isInert =
    ["comm", "concrete", "cool-like", "preserves-definedness", "simplification", "smt-lemma", "symbolic"] := by
  decide +kernel

-- the readers: an attribute is refused with its name and why, a name that is no key as well
example : ruleAttrFault? [KoreAML.attr "format"] = none ∧ ruleAttrFault? [KoreAML.attr "symbol'Kywd'"] = none ∧
    ruleAttrFault? [KoreAML.attr "cool-like"] = none := by decide +kernel
example : (ruleAttrFault? [KoreAML.attr "owise", KoreAML.attr "concat"]).isSome ∧
    (ruleAttrFault? [KoreAML.attr "heat"]).isSome ∧ (ruleAttrFault? [KoreAML.attr "anywhere"]).isSome := by decide +kernel
example : eqnAttrFault? [KoreAML.attr "concrete", KoreAML.attr "preserves-definedness"] = none ∧
    (eqnAttrFault? [KoreAML.attr "anywhere"]).isSome ∧ (eqnAttrFault? [KoreAML.attr "syntactic"]).isSome ∧
    (eqnAttrFault? [KoreAML.attr "functional"]).isSome ∧ (eqnAttrFault? [KoreAML.attr "heat"]).isSome := by
  decide +kernel
example : attrVerdict .symbol .bracket = .refused .outsideE2 (erased "BRACKET(bracket)@symbol") := rfl

#eval do
  for (c, k, s) in rowsE2 do IO.println s!"row {c.name} {k.name} {s.name}"
  for k in AttrKeyE2.all do IO.println s!"key {k.name} {k.kore}"

#print axioms attrVerdict_rows

/-! The verdicts the readers of a declaration, a claim and the module apply (`attrFault?`,
`sortAttrOK`). No key that a kompiled text's symbol or hooked-symbol declaration carries is refused
(the keys of the corpus's and the fixtures' kompiled texts, written out); the keys the readers of a
symbol declaration read (`symProdBody`, `cellSym?`, `hookFnSym`, `isOpenGenerator`) are read, and
its name (`symbol`) inert, kept in the presentation. -/

theorem symbol_kompiled : [AttrKeyE2.alias, .aliasRec, .anywhere, .binder, .cell, .concrete, .constructor,
    .deprecated, .element, .freshGenerator, .function, .functional, .hook, .idem, .impure, .injective,
    .klabel, .label, .macroKey, .macroRec, .memo, .noEvaluators, .location, .source, .priority,
    .smtHook, .smtlib, .symbol, .symbolic, .total, .unit, .update].all
      (fun k => !isRefused (attrVerdict .symbol k)) = true := by decide +kernel
theorem symbol_readers : [AttrKeyE2.cell, .constructor, .total, .functional, .hook, .function, .anywhere].all
      (fun k => isRead (attrVerdict .symbol k)) = true ∧ isInert (attrVerdict .symbol .symbol) = true ∧
    attrVerdict .equation .symbolOverload = .read := by decide +kernel

example : attrFault? .symbol .symbolAttribute [KoreAML.attr "constructor", KoreAML.attr "anywhere",
    KoreAML.attrStr "symbol'Kywd'" "a"] = none := by decide +kernel
example : (attrFault? .symbol .symbolAttribute [KoreAML.attr "sortInjection"]).map (·.1) = some .symbolAttrUnkeyed ∧
    (attrFault? .symbol .symbolAttribute [KoreAML.attr "assoc"]).map (·.1) = some .openGenerator ∧
    (attrFault? .symbol .symbolAttribute [KoreAML.attr "bracket"]).map (·.1) = some .attrOutsideE2 ∧
    (attrFault? .claim .outsideE2 [KoreAML.attr "owise"]).map (·.1) = some .attrOutsideE2 ∧
    attrFault? .claim .outsideE2 [KoreAML.attr "trusted"] = none ∧
    attrFault? .module .outsideE2 [KoreAML.attrStr "org'Stop'kframework'Stop'attributes'Stop'Source" "Source(x)"] = none ∧
    (attrFault? .module .outsideE2 [KoreAML.attr "concrete"]).map (·.1) = some .attrOutsideE2 := by decide +kernel

-- a sort declaration: its place, token, hasDomainValues, label, cool-like; not nat, a hooked sort's
-- key or a name that is no key
example : sortAttrOK (KoreAML.attr "token") ∧ sortAttrOK (KoreAML.attr "hasDomainValues") ∧
    sortAttrOK (KoreAML.attrStr "label" "x") ∧ sortAttrOK (KoreAML.attr "cool-like") ∧
    sortAttrOK (KoreAML.attrStr "org'Stop'kframework'Stop'attributes'Stop'Location" "Location(1,1,1,1)") ∧
    !sortAttrOK (KoreAML.attr "nat") ∧ !sortAttrOK (KoreAML.attrStr "hook" "INT.Int") ∧
    !sortAttrOK (KoreAML.attr "concat") ∧ !sortAttrOK (KoreAML.attr "subsort") := by decide +kernel

-- a claim: refused where the verdict at class claim refuses one of its attributes, inert otherwise
example : classify (.claim ⟨[], .string "p", [KoreAML.attr "owise"]⟩) = .refused .attrOutsideE2 ∧
    classify (.claim ⟨[], .string "p", [KoreAML.attr "trusted", KoreAML.attrStr "label" "c"]⟩) = .inert .claim ∧
    classify (.claim ⟨[], .string "p", [KoreAML.attr "foo"]⟩) = .refused .attrOutsideE2 := by decide +kernel

-- a symbol declaration (`symAttrFault?`): `assoc` and `comm` on a function's declaration are
-- refused attrOutsideE2 (kompile writes neither there), on another symbol's openGenerator as the
-- verdict gives; the other keys as `attrFault?` at class symbol
example : (symAttrFault? [KoreAML.attr "function", KoreAML.attr "assoc"]).map (·.1) = some .attrOutsideE2 ∧
    (symAttrFault? [KoreAML.attr "comm", KoreAML.attr "function"]).map (·.1) = some .attrOutsideE2 ∧
    (symAttrFault? [KoreAML.attr "function", KoreAML.attr "bracket"]).map (·.1) = some .attrOutsideE2 ∧
    (symAttrFault? [KoreAML.attr "function", KoreAML.attr "foo"]).map (·.1) = some .symbolAttrUnkeyed ∧
    symAttrFault? [KoreAML.attr "function", KoreAML.attr "total"] = none ∧
    (symAttrFault? [KoreAML.attr "constructor", KoreAML.attr "assoc"]).map (·.1) = some .openGenerator ∧
    (symAttrFault? [KoreAML.attr "functional", KoreAML.attr "comm"]).map (·.1) = some .openGenerator := by
  decide +kernel

-- `symbol-overload` gives an equation priority 0 and `aside` only as the one attribute of a
-- symbol-overload axiom (`overloadSyms?`, which `ClausePres.overload` records); beside another
-- attribute the equation is read as any other
example :
    let ovl : Kore.AppPattern := ⟨⟨⟨"symbol-overload"⟩⟩, [], [.app ⟨⟨"Lblf"⟩⟩ [] [], .app ⟨⟨"Lblg"⟩⟩ [] []]⟩
    let e := fun (as : List Kore.AppPattern) => (⟨"Lblf", [], none, none, .top KoreAML.R, as, none, false⟩ : RawEqn)
    (eqnPrio (e [ovl]), nonExec (e [ovl]), (overloadSyms? [ovl]).isSome) = ((none, 0), true, true) ∧
    (eqnPrio (e [ovl, KoreAML.attrStr "UNIQUE'Unds'ID" "x"]), nonExec (e [ovl, KoreAML.attrStr "UNIQUE'Unds'ID" "x"]),
      (overloadSyms? [ovl, KoreAML.attrStr "UNIQUE'Unds'ID" "x"]).isSome) = ((none, 50), false, false) := by
  decide +kernel
