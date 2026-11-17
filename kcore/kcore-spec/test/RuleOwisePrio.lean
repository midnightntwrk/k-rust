/-
  A rewrite axiom carrying `owise{}()` beside `priority{}("n")` states two priorities: `owise` sets
  the rule's priority to 200 and `priority` sets it to n, and no sentence of the text says which
  holds when both are written. Where n is not 200 the two readings give different steps (a rule of
  priority p between n and 200 that matches the same configuration is tried before the rule under
  one and after it under the other), so the reader refuses the axiom by name (`ruleAttribute`, the
  reason naming both keys); where n is 200 both marks state 200 and the rule is read with
  priority 200. Run from the package root: `lake env lean test/RuleOwisePrio.lean`.

  The text: `f2-examples/ens.kompile.kore` (K 7.1.337's), whose one rewrite axiom `ENS.go` carries
  no priority mark, given in memory:
  - `owise{}()` and `priority{}("40")`: refused, `ruleAttribute`, naming both keys;
  - `owise{}()` and `priority{}("200")`: read, priority 200;
  - controls: `priority{}("40")` alone (40), `owise{}()` alone (200), neither (50).
  For each text read, the emitted rewrite axiom's priority marks (`Definition.emit`): a rule read
  from `priority{}` is written with `priority{}` alone, so `owise{}()` beside `priority{}("200")` is
  emitted as `priority{}("200")` (the same priority, the `owise` mark not written).
-/
import KcoreSpec.Account

open KCore

/-- The user module's rewrite axioms with `extra` appended to their attributes. -/
def withRuleAttrsROP (extra : List Kore.AppPattern) (k : Kore.Definition) : Kore.Definition :=
  let sent := fun (s : Kore.Sentence) => match s with
    | .axiom a => match a.pattern with
      | .rewrites .. => .axiom { a with attributes := a.attributes ++ extra }
      | _ => s
    | s => s
  { k with modules := k.modules.dropLast ++
      (k.modules.getLast?.map fun m => [{ m with sentences := m.sentences.map sent }]).getD [] }

/-- The priority marks among attributes: `owise` and `priority n`, or `none`. -/
def prioMarksROP (as : List Kore.AppPattern) : String :=
  let ms := as.filterMap fun ap => match ap.head.ident.name, ap.args with
    | "owise", [] => some "owise"
    | "priority", [.string v] => some s!"priority {v}"
    | _, _ => none
  if ms.isEmpty then "none" else ", ".intercalate ms

/-- The reader's verdict on `ens.kompile.kore` with `extra` on its rewrite axiom: its refusal, or
the rules' priorities and the emitted rewrite axioms' priority marks. -/
def verdictROP (extra : List Kore.AppPattern) : IO String := do
  match Kore.parseDefinition (← IO.FS.readFile "f2-examples/ens.kompile.kore") with
  | .error e => return s!"KORE read error {e}"
  | .ok k => return match Parse.parse (withRuleAttrsROP extra k) with
    | .error r => s!"refused {r.reason.name}: {r.detail}"
    | .ok d =>
      let rws := ((d.emit.modules.getLast?.map (·.sentences)).getD []).filterMap fun s => match s with
        | .axiom a => match a.pattern with
          | .rewrites .. => some (prioMarksROP a.attributes)
          | _ => none
        | _ => none
      s!"read, prio {d.sem.rules.map (·.prio)}, emitted [{"; ".intercalate rws}]"

/--
info: owise, priority 40: refused ruleAttribute: owise and priority{}("40") on a \rewrites axiom: owise sets the rule's priority to 200 and priority to 40, two priorities that order the rule differently against a rule of a priority between them matching the same configuration, and no sentence of the text chooses between them
priority 40, owise: refused ruleAttribute: owise and priority{}("40") on a \rewrites axiom: owise sets the rule's priority to 200 and priority to 40, two priorities that order the rule differently against a rule of a priority between them matching the same configuration, and no sentence of the text chooses between them
owise, priority 200: read, prio [200], emitted [priority 200]
priority 40: read, prio [40], emitted [priority 40]
owise: read, prio [200], emitted [owise]
neither: read, prio [50], emitted [none]
-/
#guard_msgs in
#eval show IO Unit from do
  IO.println s!"owise, priority 40: {← verdictROP [KoreAML.attr "owise", KoreAML.attrStr "priority" "40"]}"
  IO.println s!"priority 40, owise: {← verdictROP [KoreAML.attrStr "priority" "40", KoreAML.attr "owise"]}"
  IO.println s!"owise, priority 200: {← verdictROP [KoreAML.attr "owise", KoreAML.attrStr "priority" "200"]}"
  IO.println s!"priority 40: {← verdictROP [KoreAML.attrStr "priority" "40"]}"
  IO.println s!"owise: {← verdictROP [KoreAML.attr "owise"]}"
  IO.println s!"neither: {← verdictROP []}"
