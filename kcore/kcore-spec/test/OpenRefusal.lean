/-
  The reader's `Parse.openRefusal` against `Semantics.rulePlainOpen` (OpenStep.lean), the
  conjunct of `rulesPlain` for one rule. Run from the package root:
  `lake env lean -j1 test/OpenRefusal.lean`.

  On rules over the semantics of `f2-examples/symrule.kompile.kore` (those of
  test/RulesPlainArmC.lean, with no existential variable and `pre`, `post` true, where
  `rulePlainOpen` is its arms and its competition conjunct), `openRefusal` is `none` exactly where
  `rulePlainOpen` holds (`agree true` on every row), and otherwise gives:
  - `bad1` (`a() => b(X) requires X ==Int 2 *Int H`), `bad2`
    (`a() => a() requires B ==Bool (2 *Int H ==Int 1) ensures B`): `openRequires`, H in a closed
    condition that holds a variable the rest of the rule holds (X, B), named in the detail;
  - `right` (`a() => b(X +Int 1)`): `openRight`, X under no constructor;
  - `bound` (`b(X) => b(X) requires H ==Int X`): `openRequires`, H in a condition with a variable
    the left side binds;
  - `held` (`b(X) => b(H) requires H ==Int X`): read alone (H by arm A); beside a rule of a larger
    priority, `openRequires` by the competition conjunct;
  - `ok1` to `ok4`, `ok2` beside a larger rule: read.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

open KCore

namespace OpenRefusalTest

def i (n : Int) : Term := .dv Srt.int (.int n)
/-- `<generatedTop>(<k>(kseq(inj{Exp,KItem}(b), V0)), cnt)`. -/
def cfg (cnt : Term) : Term :=
  .app 71 [.app 383 [.app 0 [.inj 32 1 (.app 386 []), .var 0]], cnt]

def run : IO Unit := do
  match Kore.parseDefinition (← IO.FS.readFile "f2-examples/symrule.kompile.kore") with
  | .error e => IO.println s!"KORE read error {e}"
  | .ok k =>
    match Parse.parse k with
    | .error r => IO.println s!"refused {repr r.reason} {r.detail}"
    | .ok d =>
      let c := d.sem
      let vs0 := (c.rules.map (·.vars)).getD 0 []
      let sK := vs0.getD 1 0
      let sC := vs0.getD 2 0
      let mk := fun (vars : List Srt) (lhs rhs : Term) (req ens : Option Term) (prio : Nat) =>
        ({ vars := vars, lhs := lhs, req := req, rhs := rhs, ens := ens, prio := prio } : Rule)
      let mkA := fun (vars : List Srt) (rhs : Term) (req ens : Option Term) =>
        mk vars (cfg (.var 1)) rhs req ens 50
      let bad1 := mkA [sK, sC, Srt.int, Srt.int] (cfg (.app 73 [.var 2]))
        (some (.app intEq [.var 2, .app intMul [i 2, .var 3]])) none
      let bad2 := mkA [sK, sC, Srt.bool, Srt.int] (cfg (.var 1))
        (some (.app boolEq [.var 2, .app intEq [.app intMul [i 2, .var 3], i 1]])) (some (.var 2))
      let ok1 := mkA [sK, sC, Srt.int] (cfg (.app 73 [.var 2])) none none
      let ok2 := mkA [sK, sC, Srt.int] (cfg (.var 1)) (some (.app intEq [.var 2, i 0])) none
      let ok3 := mkA [sK, sC, Srt.int] (cfg (.app 73 [.var 2])) (some (.app intEq [.var 2, i 0])) none
      let ok4 := mkA [sK, sC, Srt.int, Srt.int] (cfg (.app 73 [.var 2])) (some (.app intEq [.var 3, i 0])) none
      -- a() => b(X +Int 1)
      let right := mkA [sK, sC, Srt.int] (cfg (.app 73 [.app intAdd [.var 2, i 1]])) none none
      -- b(X) => b(X) requires H ==Int X, X the variable 1, H the variable 2
      let bound := mk [sK, Srt.int, Srt.int] (cfg (.app 73 [.var 1])) (cfg (.app 73 [.var 1]))
        (some (.app intEq [.var 2, .var 1])) none 50
      -- b(X) => b(H) requires H ==Int X
      let held := mk [sK, Srt.int, Srt.int] (cfg (.app 73 [.var 1])) (cfg (.app 73 [.var 2]))
        (some (.app intEq [.var 2, .var 1])) none 50
      let plain := mk [sK, sC] (cfg (.var 1)) (cfg (.var 1)) none none 200
      let row := fun (n : String) (rs : List Rule) (names : List String) =>
        let c' := { c with rules := rs }
        let r := rs.headD plain
        let ref := Parse.openRefusal c' r names
        let shown := match ref with
          | none => "none"
          | some (why, detail) => s!"{repr why} {detail}"
        IO.println s!"{n}: sorted {rs.all c'.ruleSorted} plain {c'.rulePlainOpen r} agree {ref.isNone == c'.rulePlainOpen r} refusal {shown}"
      let nA := ["V0", "V1", "X", "H"]
      row "bad1" [bad1] nA
      row "bad2" [bad2] ["V0", "V1", "B", "H"]
      row "ok1" [ok1] nA
      row "ok2" [ok2] ["V0", "V1", "H"]
      row "ok3" [ok3] nA
      row "ok4" [ok4] nA
      row "right" [right] nA
      row "bound" [bound] ["V0", "X", "H"]
      row "held" [held] ["V0", "X", "H"]
      row "held+larger" [held, plain] ["V0", "X", "H"]
      row "ok2+larger" [ok2, plain] ["V0", "V1", "H"]
      row "bad1+larger" [bad1, plain] nA

/--
info: bad1: sorted true plain false agree true refusal KCore.Parse.RefusalReason.openRequires VarH:Int: in a closed condition that holds VarX:Int, which the right side, the ensures or post holds; of a sort the text leaves unconfined
bad2: sorted true plain false agree true refusal KCore.Parse.RefusalReason.openRequires VarH:Int: in a closed condition that holds VarB:Bool, which the right side, the ensures or post holds; of a sort the text leaves unconfined
ok1: sorted true plain true agree true refusal none
ok2: sorted true plain true agree true refusal none
ok3: sorted true plain true agree true refusal none
ok4: sorted true plain true agree true refusal none
right: sorted true plain false agree true refusal KCore.Parse.RefusalReason.openRight VarX:Int: in the right side or the ensures under no constructor, not bound by the left side, of a sort the text leaves unconfined: the successor is a value through an element that is no value's
bound: sorted true plain false agree true refusal KCore.Parse.RefusalReason.openRequires VarH:Int: in a condition with a variable the left side binds, of a sort the text leaves unconfined
held: sorted true plain true agree true refusal none
held+larger: sorted true plain false agree true refusal KCore.Parse.RefusalReason.openRequires VarH:Int: in a condition with a variable the left side binds, of a sort the text leaves unconfined, in a rule of a priority below another's
ok2+larger: sorted true plain true agree true refusal none
bad1+larger: sorted true plain false agree true refusal KCore.Parse.RefusalReason.openRequires VarH:Int: in a closed condition that holds VarX:Int, which the right side, the ensures or post holds; of a sort the text leaves unconfined
-/
#guard_msgs in
#eval run

end OpenRefusalTest
