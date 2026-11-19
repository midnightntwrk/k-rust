/-
  A cut variable held on a right side under K's `append` (`Semantics.appendHeldX`), read from
  K 7.1.337 kompile's KORE of the construct fixture e3-ml-rule-rhs-top (copied to f2-examples as
  `heldrhstop.kompile.kore`). Run from the package root: `lake env lean -j1 test/HeldAppend.lean`.

  kompile writes `rule <k> go => #Top ... </k>` with the right side `append(\top{SortK{}}(), _DotVar1)`;
  the cut reads `\top` there as a variable `Z : K` bound by `\exists` on the right side, under no
  constructor and under `append`. The definition's `append` has the prelude's two clauses, K is a
  constructor sort whose generators are `kseq` and `dotk` alone, so `appendHeldX` accepts it and
  `heldOccs` holds Z:
  - the reader reads the text: `Parse.parse` refuses nothing, the one rule has an existential
    variable, and `openRefusal` is `none` on it (`held true`, `refusal none`);
  - on the same rule, with a third constructor of result K added to the semantics (`third`), K's
    generators are no longer `kseq` and `dotk` alone, `append` is not held, and `openRefusal` is
    `openRight`.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

open KCore

namespace HeldAppendTest

def run : IO Unit := do
  match Kore.parseDefinition (← IO.FS.readFile "f2-examples/heldrhstop.kompile.kore") with
  | .error e => IO.println s!"KORE read error {e}"
  | .ok k =>
    match Parse.parse k with
    | .error r => IO.println s!"refused {repr r.reason} {r.detail}"
    | .ok d =>
      let c := d.sem
      let shown := fun (ref : Option (Parse.RefusalReason × String)) => match ref with
        | none => "none"
        | some (why, _) => s!"{repr why}"
      match (c.fns.find? fun fn => c.symName fn.label == "append"), c.rules with
      | some fn, [r] =>
        IO.println s!"read: rules 1, exs {r.exs.length}, held {c.holds fn.label}, refusal {shown (Parse.openRefusal c r [])}"
        let fresh : Sym := nRegSyms + c.symNames.length
        let c3 := { c with ctors := c.ctors ++ [⟨fresh, [], Srt.k⟩] }
        IO.println s!"third: gens of K {(c3.gens Srt.k).length}, held {c3.holds fn.label}, refusal {shown (Parse.openRefusal c3 r [])}"
      | _, _ => IO.println "unexpected: no append or not one rule"

/--
info: read: rules 1, exs 1, held true, refusal none
third: gens of K 3, held false, refusal KCore.Parse.RefusalReason.openRight
-/
#guard_msgs in
#eval run

end HeldAppendTest
