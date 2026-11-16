/-
  The hooked equalities the reader writes for what a text states (`_==Int_`, `_==K_`), read from
  K 7.1.337 kompile's KORE. Run from the package root: `lake env lean test/HookEqSentence.lean`.
  The read `requires` `Key0 ==Int idx(B, I)` of a map key's rule (`keyCut`) is the text's left side
  under `_==Int_`'s `functional` axiom and its sentence `((K1 ==Int K2) = true) = (K1 = K2)`
  (`INT-KORE.eq-int-true-left`); `_==K_`'s, of one-item sequences, under `_==K_`'s two.
  - `f2-examples/keyfn.kompile.kore` as kompile writes it: read, the rule's `requires` an `_==Int_`.
  - the same text without the sentence labelled `INT-KORE.eq-int-true-left`, `_==Int_` still
    declared: refused `hookEqualityUnstated`, naming `_==Int_` and the sentence.
  - `f2-examples/keyfn-partial.kompile.kore` without `_==K_`'s sentence (its `UNIQUE_ID` 4f1df0fc…,
    it has no label): refused `hookEqualityUnstated`, naming `_==K_`.
-/
import KcoreSpec

set_option autoImplicit false

open KCore

/-- The text at `path` without the axioms `drop` names: read, or the refusal. -/
def verdict (path : String) (drop : Kore.Axiom → Bool := fun _ => false) : IO String := do
  match Kore.parseDefinition (← IO.FS.readFile path) with
  | .error e => return s!"KORE read error {e}"
  | .ok k =>
    let k := { k with modules := k.modules.map fun m => { m with sentences := m.sentences.filter fun s =>
      match s with | .axiom a => !drop a | _ => true } }
    return match Parse.parse k with
    | .ok d => s!"read; keys {(Parse.keysAsRequires k).map (·.2)}; coreOK {d.sem.coreOK}"
    | .error r => s!"{r.reason.name} {r.detail}"

/-- An axiom whose attribute `n` is `v`. -/
def attrIs (n v : String) (a : Kore.Axiom) : Bool := KoreAML.Parse.attrStr? a.attributes n == some v

/--
info: read; keys [[Lblidx]]; coreOK true
hookEqualityUnstated Lbl'UndsEqlsEqls'Int'Unds': declared without ((K1 Lbl'UndsEqlsEqls'Int'Unds' K2) = true) = (K1 = K2)
hookEqualityUnstated Lbl'UndsEqlsEqls'K'Unds': declared without ((K1 Lbl'UndsEqlsEqls'K'Unds' K2) = true) = (K1 = K2)
-/
#guard_msgs in
#eval show IO Unit from do
  IO.println (← verdict "f2-examples/keyfn.kompile.kore")
  IO.println (← verdict "f2-examples/keyfn.kompile.kore" (attrIs "label" "INT-KORE.eq-int-true-left"))
  IO.println (← verdict "f2-examples/keyfn-partial.kompile.kore"
    (attrIs "UNIQUE'Unds'ID" "4f1df0fcbe5672da3e37bad79f0a8a2e8ac5474f49364d679a98e61b384a27ab"))
