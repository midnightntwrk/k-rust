/-
  A variable held on a right side under a collection's symbols (CN-4b §2, HO-1), read from
  K 7.1.337 kompile's KORE of the fixtures e3-vars-* (copied to f2-examples as `held*.kompile.kore`;
  e3-vars-list's is `exvarslist.kompile.kore`).
  Run from the package root: `lake env lean -j1 test/HeldFixtures.lean`.

  ## openRefusal
  The reader's `Parse.openRefusal` reads the variables the right side holds under constructors,
  injections and the unit, element and concatenation symbols of a map, list or set collection
  (`heldOccs`), as `rulesPlain`'s conjunct for one rule does (`Semantics.rulePlainHO1`). For each
  text: the reader's verdict, and on its reading before the rules are checked (`Parse.coreBase`)
  each rule's `openRefusal` and `rulePlainHO1`, which agree (`agree true`):
  - e3-vars-map (`<m> .Map => K |-> ?V:Int </m>`), e3-vars-set (`SetItem(?V:Int)`), e3-vars-list
    (`ListItem(?V:Int)`): V is held under the collection's element symbol; read, no refusal.
  - e3-vars-update (`M [ 0 <- ?V:Int ] [ 0 <- 1 ]`): `_[_<-_]` is a hooked function, no collection
    pattern symbol, and the successor does not hold V: refused `openRight` at Int.
  - e3-vars-rangemap (`[0, 1) r|-> ?V:Int`): a range map's symbols hold nothing: refused `openRight`
    at Int.
-/
import KcoreSpec.Parse
import KcoreSpec.PredPlain

set_option autoImplicit false
set_option maxRecDepth 1000000

open KCore

namespace HeldFixtures

/-- The reader's semantics of a text before its rules are checked (`Parse.coreBase`, the stage
after which `Parse.coreOf` refuses a rule), and the names of each rule's variables. -/
def heldBaseOf (k : Kore.Definition) : Except String (Semantics × List (List String)) :=
  match k.modules.getLast? with
  | none => .error "no module"
  | some m =>
    let S := Parse.scan m.sentences
    let r : Parse.Rd (Semantics × List (List String)) := do
      let E ← Parse.envOf m S
      let sp ← (Parse.prodSyms S E).mapM (Parse.symProd E S.eqs)
      let rules ← S.rewrites.mapM (Parse.ruleOf E.N E.src)
      let c ← Parse.coreBase S E (Parse.prodsOf S E sp) rules
      pure (c, rules.map (·.2.names))
    match r with
    | .ok x => .ok x
    | .error f => .error s!"{repr f.reason} {f.detail}"

/-- The reader's verdict on the text, and each rule of its reading before the rules are checked
whose `openRefusal` or `rulePlainHO1` is not that of a plain rule: the two, and whether they agree. -/
def heldVerdict (name path : String) : IO Unit := do
  match Kore.parseDefinition (← IO.FS.readFile path) with
  | .error e => IO.println s!"{name}: KORE read error {e}"
  | .ok k =>
    match Parse.parse k with
    | .error r => IO.println s!"{name}: parse refused {repr r.reason} {r.detail}"
    | .ok _ => IO.println s!"{name}: parse read"
    match heldBaseOf k with
    | .error e => IO.println s!"{name}: base {e}"
    | .ok (c, ns) =>
      for (r, names) in c.rules.zip ns do
        if !r.opens.isEmpty then
          let ref := Parse.openRefusal c r names
          let shown := match ref with
            | none => "none"
            | some (why, detail) => s!"{repr why} {detail}"
          IO.println s!"{name}: opens {r.opens} held {c.rulePlainHO1 r} agree {ref.isNone == c.rulePlainHO1 r} refusal {shown}"

def run : IO Unit := do
  heldVerdict "map" "f2-examples/heldmap.kompile.kore"
  heldVerdict "set" "f2-examples/heldset.kompile.kore"
  heldVerdict "list" "f2-examples/exvarslist.kompile.kore"
  heldVerdict "update" "f2-examples/heldupdate.kompile.kore"
  heldVerdict "rangemap" "f2-examples/heldrangemap.kompile.kore"

/--
info: map: parse read
map: opens [3] held true agree true refusal none
set: parse read
set: opens [3] held true agree true refusal none
list: parse read
list: opens [3] held true agree true refusal none
update: parse refused KCore.Parse.RefusalReason.openRight Var'Ques'V:Int: bound by \exists on the right side, held there or in the ensures under no constructor, of a sort the text leaves unconfined: the successor is a value through an element that is no value's
update: opens [3] held false agree true refusal KCore.Parse.RefusalReason.openRight Var'Ques'V:Int: bound by \exists on the right side, held there or in the ensures under no constructor, of a sort the text leaves unconfined: the successor is a value through an element that is no value's
rangemap: parse refused KCore.Parse.RefusalReason.openRight Var'Ques'V:Int: bound by \exists on the right side, held there or in the ensures under no constructor, of a sort the text leaves unconfined: the successor is a value through an element that is no value's
rangemap: opens [3] held false agree true refusal KCore.Parse.RefusalReason.openRight Var'Ques'V:Int: bound by \exists on the right side, held there or in the ensures under no constructor, of a sort the text leaves unconfined: the successor is a value through an element that is no value's
-/
#guard_msgs in
#eval run

end HeldFixtures
