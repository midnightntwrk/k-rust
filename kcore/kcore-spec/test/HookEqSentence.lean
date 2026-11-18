/-
  The hooked equalities the reader writes for what a text states (`_==Int_`, `_==K_`), read from
  K 7.1.337 kompile's KORE. Run from the package root: `lake env lean test/HookEqSentence.lean`.
  A strict conjunction of an equation's `ensures` (`conjTerms`) is read as `_==K_` of the sequences
  of the conjuncts' values and of as many `true`, which is the text's under `_==K_`'s `functional`
  axiom and its sentence `((K1 ==K K2) = true) = (K1 = K2)`; a map key's cut (`keyCut`) writes no
  hooked equality (the key's membership in the application is a conjunct of `pre`), so it reads no
  such sentence.
  - `f2-examples/ens.kompile.kore` with `half`'s `ensures` edited to `(N >=Int 0) #And (N >=Int 0)`:
    read; the same text without `_==K_`'s sentence (its `UNIQUE_ID` 4f1df0fc…, it has no label):
    refused `hookEqualityUnstated`, naming `_==K_`.
  - `f2-examples/keyfn.kompile.kore` as kompile writes it, and without the sentence labelled
    `INT-KORE.eq-int-true-left` (`_==Int_`'s): read, the key's rule in both.
  - `f2-examples/keyfn-partial.kompile.kore` without `_==K_`'s sentence: read, its three key rules
    (one with a written `requires`, one with a key of the sort `Key`) in it.
-/
import KcoreSpec

set_option autoImplicit false

open KCore

/-- The text at `path`, edited by `edit`, without the axioms `drop` names: read, or the refusal. -/
def verdict (path : String) (drop : Kore.Axiom → Bool := fun _ => false) (edit : String → String := id) :
    IO String := do
  match Kore.parseDefinition (edit (← IO.FS.readFile path)) with
  | .error e => return s!"KORE read error {e}"
  | .ok k =>
    let k := { k with modules := k.modules.map fun m => { m with sentences := m.sentences.filter fun s =>
      match s with | .axiom a => !drop a | _ => true } }
    return match Parse.parse k with
    | .ok d => s!"read; keys {(Parse.keysAsMember k).map (·.2)}; coreOK {d.sem.coreOK}"
    | .error r => s!"{r.reason.name} {r.detail}"

/-- An axiom whose attribute `n` is `v`. -/
def attrIs (n v : String) (a : Kore.Axiom) : Bool := KoreAML.Parse.attrStr? a.attributes n == some v

/-- `_==K_`'s sentence `((K1 ==K K2) = true) = (K1 = K2)`. -/
def kEqSentence : Kore.Axiom → Bool :=
  attrIs "UNIQUE'Unds'ID" "4f1df0fcbe5672da3e37bad79f0a8a2e8ac5474f49364d679a98e61b384a27ab"

/-- `half`'s `ensures` `N >=Int 0` conjoined with itself (`#And`). -/
def ensConj (s : String) : String :=
  s.replace "        Lbl'Unds-GT-Eqls'Int'Unds'{}(VarN:SortInt{},\\dv{SortInt{}}(\"0\")),\n"
    "        \\and{SortBool{}}(Lbl'Unds-GT-Eqls'Int'Unds'{}(VarN:SortInt{},\\dv{SortInt{}}(\"0\")), Lbl'Unds-GT-Eqls'Int'Unds'{}(VarN:SortInt{},\\dv{SortInt{}}(\"0\"))),\n"

/--
info: read; keys []; coreOK true
hookEqualityUnstated Lbl'UndsEqlsEqls'K'Unds': declared without ((K1 Lbl'UndsEqlsEqls'K'Unds' K2) = true) = (K1 = K2)
read; keys [[Lblidx]]; coreOK true
read; keys [[Lblidx]]; coreOK true
read; keys [[Lblpidx], [Lblkf], [Lblpidx]]; coreOK true
-/
#guard_msgs in
#eval show IO Unit from do
  IO.println (← verdict "f2-examples/ens.kompile.kore" (edit := ensConj))
  IO.println (← verdict "f2-examples/ens.kompile.kore" kEqSentence ensConj)
  IO.println (← verdict "f2-examples/keyfn.kompile.kore")
  IO.println (← verdict "f2-examples/keyfn.kompile.kore" (attrIs "label" "INT-KORE.eq-int-true-left"))
  IO.println (← verdict "f2-examples/keyfn-partial.kompile.kore" kEqSentence)
