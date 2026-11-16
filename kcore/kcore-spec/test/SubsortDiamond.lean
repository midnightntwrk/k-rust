/-
  A no-junk axiom over a subsort reached by two paths, read from K 7.1.337 kompile's KORE. Run from
  the package root: `lake env lean test/SubsortDiamond.lean`.
  - `f2-examples/subsort-diamond.kompile.kore` (`subsort-diamond.k`): `E < A < T` and `E < B < T`,
    no subsort `E < T` stated. kompile's no-junk axiom of `T` lists `inj{E, T}` once; `emit`'s,
    written from the subsort closure, which holds the pair once per path, lists it twice.
    `\or(P, P, Q)` and `\or(P, Q)` denote one set (a disjunction's argument repeated changes nothing
    it states), and the account's normal form (`canon`) drops an argument printed as the one before
    it: the axiom is induced, nothing uninduced.
  - with `inj{E, T}` dropped from the text's axiom: no longer the induced one (`inertMismatch`).
  - with `inj{A, T}`'s disjunct written twice in the text: induced.
-/
import KcoreSpec

set_option autoImplicit false

open KCore

/-- The disjunct of `T`'s no-junk axiom for `E`, as kompile writes it. -/
def eDisjunct : String := ", \\exists{SortT{}} (Val:SortE{}, inj{SortE{}, SortT{}} (Val:SortE{}))"

/-- The disjunct of `T`'s no-junk axiom for `A`, as kompile writes it. -/
def aDisjunct : String := "\\exists{SortT{}} (Val:SortA{}, inj{SortA{}, SortT{}} (Val:SortA{}))"

/-- The reader's verdict on the text at `path` (its text edited by `edit`): the uninduced
constructor axioms' classes and `coreOK`, or the refusal. -/
def verdict (path : String) (edit : String → String := id) : IO String := do
  match Kore.parseDefinition (edit (← IO.FS.readFile path)) with
  | .error e => return s!"KORE read error {e}"
  | .ok k =>
    return match Parse.parse k with
      | .ok d => s!"read; uninduced {(Parse.uninduced k d).map (·.detail)}; coreOK {d.sem.coreOK}"
      | .error r => s!"{r.reason.name} {r.detail}"

/--
info: read; uninduced []; coreOK true
read; uninduced [noJunk]; coreOK true
read; uninduced []; coreOK true
-/
#guard_msgs in
#eval show IO Unit from do
  IO.println (← verdict "f2-examples/subsort-diamond.kompile.kore")
  IO.println (← verdict "f2-examples/subsort-diamond.kompile.kore" (·.replace eDisjunct ""))
  IO.println (← verdict "f2-examples/subsort-diamond.kompile.kore" (·.replace aDisjunct (aDisjunct ++ ", " ++ aDisjunct)))
