/-
  A function symbol in a rule's left side, read from K 7.1.337 kompile's KORE. Run from the package
  root: `lake env lean test/FunctionInPattern.lean`.
  - `f2-examples/lset.kompile.kore` (`lset.k`): the rule `<k> l(I, J) => done() </k> <list> _ [ I <- J ]
    </list>` applies LIST's update `List:set` (a hooked function of the registry) in its left side.
    The reader reads the application through the cut (`Parse.ovlCut`, `Parse.regCutSyms`): the list
    cell's content a fresh variable V with `V ∈ List:set(_Gen0, I, J)` a conjunct of the rule's `pre`.
    `_Gen0` is held by nothing else in the rule and List is not confined, so the rule is refused
    `openRequires`, the variable and the symbol named: at an element of List that is no value's the
    registry states nothing of `List:set`, and whether some such element gives the list cell's list
    differs between models of the text.
  - the same text with the rule's left side `List:set(_, I, J)` replaced by its first argument
    (`_Gen0:List`): no refusal.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

open KCore

mutual
  /-- `p` with each application of `f` replaced by its first argument. -/
  def unwrap (f : String) : Kore.Pattern → Kore.Pattern
    | .app h ss ps => if h.ident.name == f then (match ps with
        | p :: _ => unwrap f p
        | [] => .app h ss [])
      else .app h ss (unwrapList f ps)
    | .and s ps => .and s (unwrapList f ps)
    | .rewrites s p q => .rewrites s (unwrap f p) (unwrap f q)
    | p => p
  def unwrapList (f : String) : List Kore.Pattern → List Kore.Pattern
    | [] => []
    | p :: ps => unwrap f p :: unwrapList f ps
end

/-- The rewrite axioms with each application of `f` replaced by its first argument. -/
def unwrapRules (f : String) (k : Kore.Definition) : Kore.Definition :=
  let sent := fun (s : Kore.Sentence) => match s with
    | .axiom a => match a.pattern with
      | .rewrites .. => .axiom { a with pattern := unwrap f a.pattern }
      | _ => s
    | s => s
  { k with modules := k.modules.dropLast ++
      (k.modules.getLast?.map fun m => [{ m with sentences := m.sentences.map sent }]).getD [] }

/-- The reader's verdict on the text at `path` (edited by `edit`): the refusal, or the sentences
unaccounted and the account's `functionInPattern` refusals (the rule's label, the function). -/
def verdict (path : String) (edit : Kore.Definition → Kore.Definition := id) : IO String := do
  match Kore.parseDefinition (← IO.FS.readFile path) with
  | .error e => return s!"KORE read error {e}"
  | .ok k =>
    let k := edit k
    return match Parse.parse k with
      | .ok d => s!"read; unaccounted {(Parse.unconsumed k d).map (·.detail)}; {(Parse.functionInPattern k d).map fun r => s!"{r.head}: {r.reason.name} {r.detail}"}"
      | .error r => s!"{r.reason.name} {r.detail}"

/--
info: openRequires Var'Unds'Gen0:List: in a condition with a variable the left side binds (V ∈ LblList'Coln'set(…)), under LblList'Coln'set, of a sort the text leaves unconfined
read; unaccounted []; []
-/
#guard_msgs in
#eval show IO Unit from do
  IO.println (← verdict "f2-examples/lset.kompile.kore")
  IO.println (← verdict "f2-examples/lset.kompile.kore" (unwrapRules "LblList'Coln'set"))
