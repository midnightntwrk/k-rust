/-
  The reader on rules whose right side is under `\exists` (`\rewrites(\and(lhs, req), \exists(x̄,
  \and(rhs, ens)))`), read from K 7.1.337 kompile's KORE (test/constructs/fixtures, the kompiled
  texts copied to f2-examples). Run from the package root: `lake env lean -j1 test/ExReader.lean`.

  The rule's existential variables are its `exs`, in the text's order of nesting. A rule
  `rulePlainEx` admits is read (`Parse.openRefusal` gives none); an existential variable the right
  side holds under no constructor, of an unconfined sort, is refused `openRight`.
  - `exrhs` (e3-vars): `c(_, _Y) => d(?Z:Int)`: read, `exs` the one variable `?Z`, under the
    constructor d (arm A).
  - `exvarstwo` (e3-vars-two): `c() => d(?Y:Int, ?Z:Int)`, written `\exists(?Y, \exists(?Z, …))`:
    read, `exs` `?Y` then `?Z`; with the binders swapped in the text (`swapped`), `?Z` then `?Y`.
  - `exvarsbool` (e3-vars-bool): `c() => d(?Z:Bool)`: read (arm A, and Bool is confined).
  - `exvarslist` (e3-vars-list): `L => ListItem(?V:Int) L`: read, `?V` held under the list's
    element and concatenation symbols (`heldOccs`, HO-1), which `rulePlainEx`'s constructor arm
    does not read (`rulePlainEx false`).
  `rulesPlain` asks `rulePlainHO1` of each rule (`Semantics.rulesPlain_iff_held`), so the four read
  texts are well formed and have `coreOK` (`Vars.rule2` for e3-vars, by the kernel).

  The binders are read by the sentence's scoping (C3.reader-exists-binders; section "Hand-written
  binders"): a variable is a name and a sort, and a binder's scope is its body. On e3-vars' text
  with its third rewrite axiom `c(_Gen0, _Y) => \exists ?Z:Int. d(?Z)` changed by hand, and on
  e3-ml-lhs-empty-sort's with its left sides without Empty:
  - `shadow` (site a), the binder and its occurrence spelled `_Y`, the name of the left side's
    second variable: read with the binder renamed apart (`_Y'`, `existsRenamedApart`), `exs` the
    one variable; the Semantics is the unchanged text's.
  - `sort` (site b), the binder at Bool and the body's `?Z` at Int: the binder binds nothing and is
    dropped (`existsDropped`), `?Z:Int` is a variable of the rule the left side does not bind; the
    Semantics is that of the text without the binder. `shadow-sort`: the binder `_Y:Bool`, the body
    `d(_Y:Int)`: renamed apart and dropped, the body's `_Y` the left side's.
  - `unused` (site c), the body `d(_Y)`: the binder `?Z:Int` dropped; `empty`, a binder
    `Z:Empty` (a sort without a constructor) around both right sides of e3-ml-lhs-empty-sort:
    dropped, no premise on the sort; `bottom`, the right side `d(?Z) ∧ ⊥`: the right side is empty
    and not read, the binder dropped, the `ensures` false. Each has the Semantics of its text
    without the binder.
  - `twice` (site d), `\exists ?Z. \exists ?Z. d(?Z)`: `exs` of one index, the unchanged text's
    Semantics.
  - `bare` (site e), the binder over the right side's term alone, no `\and(rhs, ens)`: `ruleShape`,
    as without a binder; `alias`, the binder over `weakAlwaysFinally{C}(\and(rhs, ens))`: read
    through the alias (`identityAlias`), the unchanged text's Semantics; `alias-two`, the alias at
    two arguments under the binder: `aliasApplication`.
  - `left-alias` (site f), the left side an application of a symbol the text does not have:
    `aliasApplication`, as without a binder.
  No text is refused for a binder. Kernel: `exApart_shadow` (the renaming), `exKept_drop` (the
  binders that bind something, and their indices).
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

open KCore

namespace ExReader

/-- The reader on a text: its first refusal, or each rule with existential variables (their names
in the order of `exs`, `rulePlainEx`, whether `openRefusal` gives none) and the definition's
failing `wf` conjuncts, `rulesPlain` and `coreOK`. -/
def show1 (n : String) : IO Unit := do
  match Kore.parseDefinition (← IO.FS.readFile s!"f2-examples/{n}.kompile.kore") with
  | .error e => IO.println s!"{n}: KORE read error {e}"
  | .ok k =>
    match (Parse.refusals k).find? (·.reason != .aliasDeclaration) with
    | some r => IO.println s!"{n}: {repr r.reason} {r.detail}"
    | none => match Parse.parse k with
      | .error r => IO.println s!"{n}: refused {repr r.reason} {r.detail}"
      | .ok d =>
        for ((r, p), i) in (d.sem.rules.zip d.pres.rules).zipIdx do
          if !r.exs.isEmpty then
            IO.println s!"{n} rule {i}: exs {r.exs} {r.exs.map fun j => p.names.getD j ""}; rulePlainEx {d.sem.rulePlainEx r}; openRefusal none {(Parse.openRefusal d.sem r p.names).isNone}"
        IO.println s!"{n}: wf failing {(d.report.filter (!·.2)).map (·.1)}; rulesPlain {d.sem.rulesPlain}; coreOK {d.sem.coreOK}"

/--
info: exrhs rule 2: exs [5] ['Ques'Z]; rulePlainEx true; openRefusal none true
exrhs: wf failing []; rulesPlain true; coreOK true
exvarstwo rule 0: exs [2, 3] ['Ques'Y, 'Ques'Z]; rulePlainEx true; openRefusal none true
exvarstwo: wf failing []; rulesPlain true; coreOK true
exvarsbool rule 0: exs [1] ['Ques'Z]; rulePlainEx true; openRefusal none true
exvarsbool: wf failing []; rulesPlain true; coreOK true
exvarslist rule 0: exs [3] ['Ques'V]; rulePlainEx false; openRefusal none true
exvarslist: wf failing []; rulesPlain true; coreOK true
-/
#guard_msgs in
#eval show IO Unit from do
  for n in ["exrhs", "exvarstwo", "exvarsbool", "exvarslist"] do show1 n

/-- The binders of exvarstwo's rule swapped, `\exists(?Z, \exists(?Y, …))`, the body unchanged:
`exs` follows the nesting (`?Z` then `?Y`), not the order in which the body first holds them. -/
def swapped : IO Unit := do
  let t ← IO.FS.readFile "f2-examples/exvarstwo.kompile.kore"
  let a := "(Var'Ques'Y:SortInt{},  \\exists{SortGeneratedTopCell{}} (Var'Ques'Z:SortInt{},"
  let b := "(Var'Ques'Z:SortInt{},  \\exists{SortGeneratedTopCell{}} (Var'Ques'Y:SortInt{},"
  match Kore.parseDefinition (t.replace a b) with
  | .error e => IO.println s!"KORE read error {e}"
  | .ok k => match Parse.parse k with
    | .error r => IO.println s!"refused {repr r.reason} {r.detail}"
    | .ok d =>
      let p := d.pres.rules.getD 0 default
      match d.sem.rules with
      | r :: _ => IO.println s!"swapped: changed {decide (t.replace a b ≠ t)}; exs {r.exs} {r.exs.map fun j => p.names.getD j ""}"
      | [] => IO.println "swapped: no rule"

/-- info: swapped: changed true; exs [3, 2] ['Ques'Z, 'Ques'Y] -/
#guard_msgs in
#eval swapped

/-! ## Hand-written binders

A rewrite axiom's right-side binders by the sentence's scoping: the cases of the header. -/

/-- `t` with each `(a, b)` of `eds` applied in turn (every occurrence of a replaced by b); `none`
where one of them changes nothing. -/
def edited (t : String) : List (String × String) → Option String
  | [] => some t
  | (a, b) :: eds => if t.replace a b == t then none else edited (t.replace a b) eds

/-- The user module's rewrite axioms with their pattern edited by `ed`. -/
def editRw (ed : Kore.Pattern → Kore.Pattern) (k : Kore.Definition) : Kore.Definition :=
  let sent := fun (s : Kore.Sentence) => match s with
    | .axiom a => match a.pattern with
      | .rewrites .. => .axiom { a with pattern := ed a.pattern }
      | _ => s
    | s => s
  { k with modules := k.modules.dropLast ++
      (k.modules.getLast?.map fun m => [{ m with sentences := m.sentences.map sent }]).getD [] }

/-- The text of `file` edited by `eds`, then its rewrite axioms by `ed`. -/
def hw (file : String) (eds : List (String × String)) (ed : Kore.Pattern → Kore.Pattern := id) :
    IO (Option Kore.Definition) := do
  let some t := edited (← IO.FS.readFile s!"f2-examples/{file}.kompile.kore") eds | return none
  match Kore.parseDefinition t with
  | .error _ => return none
  | .ok k => return some (editRw ed k)

/-- The reader on a hand-written text: its refusal, or the rules `is` (variables, `exs`, whether
the `ensures` is `false`, `ruleSorted`, `rulePlainEx`, `openRefusal`), the notes of the sentences
read through one, the definition's verdicts, and whether its Semantics is that of `twin`. -/
def showHw (n : String) (k? twin? : Option Kore.Definition) (is : List Nat) : IO Unit := do
  let some k := k? | IO.println s!"{n}: no text (an edit changed nothing, or KORE read error)"
  match Parse.parse k with
  | .error r => IO.println s!"{n}: refused {r.reason.name}{if r.detail.isEmpty then "" else " " ++ r.detail}"
  | .ok d =>
    for i in is do
      match d.sem.rules[i]?, d.pres.rules[i]? with
      | some r, some p =>
        let vars := (p.names.zip r.vars).map fun (x, s) => s!"{x}:{d.sem.sortName s}"
        let open? := match Parse.openRefusal d.sem r p.names with
          | some (reason, detail) => s!"{reason.name} {detail}"
          | none => "none"
        IO.println s!"{n} rule {i}: vars {vars}; exs {r.exs}; ens false {reprStr r.ens == reprStr (some (Term.dv Srt.bool (.bool false)))}; ruleSorted {d.sem.ruleSorted r}; rulePlainEx {d.sem.rulePlainEx r}; openRefusal {open?}"
      | _, _ => IO.println s!"{n} rule {i}: no rule"
    let notes := (Parse.connReadings k).map fun (_, ns) => ns.map Parse.ReadingNote.name
    let same := match twin? with
      | some k' => match Parse.parse k' with
        | .ok d' => s!"{reprStr d.sem == reprStr d'.sem}"
        | .error _ => "twin refused"
      | none => "no twin"
    IO.println s!"{n}: notes {notes}; wf failing {(d.report.filter (!·.2)).map (·.1)}; rulesPlain {d.sem.rulesPlain}; coreOK {d.sem.coreOK}; Semantics of its twin {same}"

def topCell : Kore.KSort := KoreAML.srt "GeneratedTopCell"

/-- The binder of e3-vars' third rewrite axiom, its occurrence in the body, the axiom's end, and
the same without the binder. -/
def exB : String := "\\exists{SortGeneratedTopCell{}} (Var'Ques'Z:SortInt{}, "
def exD : String := "Lbld{}(Var'Ques'Z:SortInt{})"
def exEnd : String := "Var'Unds'Gen2:SortGeneratedCounterCell{}), \\top{SortGeneratedTopCell{}}())))"
def noBinder : List (String × String) :=
  [(exB, ""), (exEnd, "Var'Unds'Gen2:SortGeneratedCounterCell{}), \\top{SortGeneratedTopCell{}}()))")]

/-- e3-ml-lhs-empty-sort's two left sides without Empty. -/
def noEmpty : List (String × String) :=
  [("\\or{SortExp{}}(Lble{}(Var'Unds'Gen0:SortEmpty{}),Lbld{}())", "Lbld{}()"),
   ("Lblc{}(\\exists{SortExp{}}(VarY:SortEmpty{},Lbla{}()))", "Lblc{}(Lbla{}())")]

/--
info: base rule 2: vars ['Unds'Gen0:Int, 'Unds'Y:Int, 'Unds'DotVar1:K, 'Unds'Gen1:NCell, 'Unds'Gen2:GeneratedCounterCell, 'Ques'Z:Int]; exs [5]; ens false false; ruleSorted true; rulePlainEx true; openRefusal none
base: notes []; wf failing []; rulesPlain true; coreOK true; Semantics of its twin no twin
shadow rule 2: vars ['Unds'Gen0:Int, 'Unds'Y:Int, 'Unds'DotVar1:K, 'Unds'Gen1:NCell, 'Unds'Gen2:GeneratedCounterCell, 'Unds'Y':Int]; exs [5]; ens false false; ruleSorted true; rulePlainEx true; openRefusal none
shadow: notes [[existsRenamedApart]]; wf failing []; rulesPlain true; coreOK true; Semantics of its twin true
sort rule 2: vars ['Unds'Gen0:Int, 'Unds'Y:Int, 'Unds'DotVar1:K, 'Unds'Gen1:NCell, 'Unds'Gen2:GeneratedCounterCell, 'Ques'Z:Int]; exs []; ens false false; ruleSorted true; rulePlainEx true; openRefusal none
sort: notes [[existsDropped]]; wf failing []; rulesPlain true; coreOK true; Semantics of its twin true
shadow-sort rule 2: vars ['Unds'Gen0:Int, 'Unds'Y:Int, 'Unds'DotVar1:K, 'Unds'Gen1:NCell, 'Unds'Gen2:GeneratedCounterCell]; exs []; ens false false; ruleSorted true; rulePlainEx true; openRefusal none
shadow-sort: notes [[existsRenamedApart, existsDropped]]; wf failing []; rulesPlain true; coreOK true; Semantics of its twin true
unused rule 2: vars ['Unds'Gen0:Int, 'Unds'Y:Int, 'Unds'DotVar1:K, 'Unds'Gen1:NCell, 'Unds'Gen2:GeneratedCounterCell]; exs []; ens false false; ruleSorted true; rulePlainEx true; openRefusal none
unused: notes [[existsDropped]]; wf failing []; rulesPlain true; coreOK true; Semantics of its twin true
empty rule 0: vars ['Unds'DotVar1:K, 'Unds'DotVar0:GeneratedCounterCell]; exs []; ens false false; ruleSorted true; rulePlainEx true; openRefusal none
empty rule 1: vars ['Unds'DotVar1:K, 'Unds'DotVar0:GeneratedCounterCell]; exs []; ens false false; ruleSorted true; rulePlainEx true; openRefusal none
empty: notes [[existsDropped], [existsDropped]]; wf failing []; rulesPlain true; coreOK true; Semantics of its twin true
bottom rule 2: vars ['Unds'Gen0:Int, 'Unds'Y:Int, 'Unds'DotVar1:K, 'Unds'Gen1:NCell, 'Unds'Gen2:GeneratedCounterCell]; exs []; ens false true; ruleSorted true; rulePlainEx true; openRefusal none
bottom: notes [[existsDropped]]; wf failing []; rulesPlain true; coreOK true; Semantics of its twin true
twice rule 2: vars ['Unds'Gen0:Int, 'Unds'Y:Int, 'Unds'DotVar1:K, 'Unds'Gen1:NCell, 'Unds'Gen2:GeneratedCounterCell, 'Ques'Z:Int]; exs [5]; ens false false; ruleSorted true; rulePlainEx true; openRefusal none
twice: notes [[existsDropped]]; wf failing []; rulesPlain true; coreOK true; Semantics of its twin true
bare: refused ruleShape
alias rule 2: vars ['Unds'Gen0:Int, 'Unds'Y:Int, 'Unds'DotVar1:K, 'Unds'Gen1:NCell, 'Unds'Gen2:GeneratedCounterCell, 'Ques'Z:Int]; exs [5]; ens false false; ruleSorted true; rulePlainEx true; openRefusal none
alias: notes [[identityAlias]]; wf failing []; rulesPlain true; coreOK true; Semantics of its twin true
alias-two: refused aliasApplication weakAlwaysFinally: an alias of K's prelude heading the right side of the rewrite axiom (the form kompile writes for a rule of a module carrying all-path or one-path), not at one sort and one argument or not defined by the text as the identity on its argument (aliasIsIdentity); not read as its argument
left-alias: refused aliasApplication rule2LHS
-/
#guard_msgs in
#eval show IO Unit from do
  let base ← hw "exrhs" []
  showHw "base" base none [2]
  -- site a
  showHw "shadow" (← hw "exrhs" [("Var'Ques'Z:SortInt{}", "Var'Unds'Y:SortInt{}")]) base [2]
  -- site b
  showHw "sort" (← hw "exrhs" [(exB, "\\exists{SortGeneratedTopCell{}} (Var'Ques'Z:SortBool{}, ")])
    (← hw "exrhs" noBinder) [2]
  showHw "shadow-sort"
    (← hw "exrhs" [(exB, "\\exists{SortGeneratedTopCell{}} (Var'Unds'Y:SortBool{}, "), (exD, "Lbld{}(Var'Unds'Y:SortInt{})")])
    (← hw "exrhs" (noBinder ++ [(exD, "Lbld{}(Var'Unds'Y:SortInt{})")])) [2]
  -- site c
  showHw "unused" (← hw "exrhs" [(exD, "Lbld{}(Var'Unds'Y:SortInt{})")])
    (← hw "exrhs" (noBinder ++ [(exD, "Lbld{}(Var'Unds'Y:SortInt{})")])) [2]
  showHw "empty"
    (← hw "mlempty" noEmpty fun
      | .rewrites s l r => .rewrites s l (.exist topCell (KoreAML.evar "VarZ" (KoreAML.srt "Empty")) r)
      | p => p)
    (← hw "mlempty" noEmpty) [0, 1]
  showHw "bottom" (← hw "exrhs" [(exD, "\\and{SortExp{}}(Lbld{}(Var'Ques'Z:SortInt{}),\\bottom{SortExp{}}())")])
    (← hw "exrhs" (noBinder ++ [(exD, "\\and{SortExp{}}(Lbld{}(Var'Ques'Z:SortInt{}),\\bottom{SortExp{}}())")])) [2]
  -- site d
  showHw "twice" (← hw "exrhs" [(exB, exB ++ exB), (exEnd, exEnd ++ ")")]) base [2]
  -- site e
  showHw "bare" (← hw "exrhs" [] fun
    | .rewrites s l (.exist s' x (.and _ [r, _])) => .rewrites s l (.exist s' x r)
    | p => p) none [2]
  showHw "alias" (← hw "exrhs" [] fun
    | .rewrites s l (.exist s' x b) => .rewrites s l (.exist s' x (.app ⟨⟨"weakAlwaysFinally"⟩⟩ [topCell] [b]))
    | p => p) base [2]
  showHw "alias-two" (← hw "exrhs" [] fun
    | .rewrites s l (.exist s' x b) => .rewrites s l (.exist s' x (.app ⟨⟨"weakAlwaysFinally"⟩⟩ [topCell] [b, b]))
    | p => p) none [2]
  -- site f
  showHw "left-alias" (← hw "exrhs" [] fun
    | .rewrites s _ (.exist s' x b) => .rewrites s (.app ⟨⟨"rule2LHS"⟩⟩ [] []) (.exist s' x b)
    | p => p) none [2]

/-! ### Kernel-checked: the two devices -/

namespace Hand

open Parse

def int : Kore.KSort := KoreAML.srt "Int"
def bool : Kore.KSort := KoreAML.srt "Bool"
def top : Kore.Pattern := .top topCell
def Z (s : Kore.KSort) : Kore.EVar := KoreAML.evar "VarZ" s
def Y : Kore.EVar := KoreAML.evar "VarY" int
/-- `c(Z:Int)`, `\top`: the left side holds the name Z. -/
def l : Kore.Pattern := KoreAML.ap "Lblc" [KoreAML.ev "VarZ" int]
def d (x : Kore.EVar) : Kore.Pattern := KoreAML.ap "Lbld" [.var (.evar x)]
def body (x : Kore.EVar) : Kore.Pattern := .and topCell [d x, top]
def ax (rx : Kore.Pattern) : Kore.Pattern := .rewrites topCell (.and topCell [l, top]) rx

/-- **The renaming (`existsRenamedApart`), in the kernel**: `c(Z) => ∃Z. d(Z)` is read as
`c(Z) => ∃Z'. d(Z')`; of two binders of the variable, `∃Z. ∃Z. d(Z)`, the inner one keeps the
occurrence, `∃Z''. ∃Z'. d(Z')`; a binder at Bool around a body holding Z at Int is renamed and the
body's Z, the left side's variable, is not; a binder of another name is left as it is. -/
theorem exApart_shadow :
    rhsApart (ax (.exist topCell (Z int) (body (Z int)))) l top (.exist topCell (Z int) (body (Z int))) =
      .exist topCell (KoreAML.evar "VarZ'" int) (body (KoreAML.evar "VarZ'" int)) ∧
    rhsApart (ax (.exist topCell (Z int) (.exist topCell (Z int) (body (Z int))))) l top
        (.exist topCell (Z int) (.exist topCell (Z int) (body (Z int)))) =
      .exist topCell (KoreAML.evar "VarZ''" int) (.exist topCell (KoreAML.evar "VarZ'" int)
        (body (KoreAML.evar "VarZ'" int))) ∧
    rhsApart (ax (.exist topCell (Z bool) (body (Z int)))) l top (.exist topCell (Z bool) (body (Z int))) =
      .exist topCell (KoreAML.evar "VarZ'" bool) (body (Z int)) ∧
    rhsApart (ax (.exist topCell Y (body Y))) l top (.exist topCell Y (body Y)) = .exist topCell Y (body Y) ∧
    exRenamed l top (.exist topCell (Z int) (body (Z int))) = true ∧
    exRenamed l top (.exist topCell Y (body Y)) = false := by
  decide +kernel

/-- **The binders that bind something (`existsDropped`), in the kernel**: of `∃Z. ∃Y. ∃Z` around
`d(Z) ∧ d(Y)` the binders kept are Y and the inner Z, in the order of nesting; a binder at Bool
around `d(Z:Int)` binds nothing; nor does a binder absent from the body, or one over a right side
holding `\bottom`; and a kept binder's index is looked up by name and sort after the first `n0`
variables: of Z:Int, X:Int (a variable of the left side), W:Int (absent), Z:Bool (another sort) and
Key0:Int (no variable at the lookup), the one index is Z:Int's. -/
theorem exKept_drop :
    exKept [Z int, Y, Z int] (.and topCell [d (Z int), d Y]) top = [Y, Z int] ∧
    exKept [Z bool] (d (Z int)) top = [] ∧
    exKept [Y] (d (Z int)) top = [] ∧
    exKept [Z int] (.and topCell [d (Z int), .bottom topCell]) top = [] ∧
    exKept [Z int] (d (Z int)) top = [Z int] ∧
    exIndices [⟨"X", "Int"⟩, ⟨"Z", "Int"⟩] 1
      [Z int, KoreAML.evar "VarX" int, KoreAML.evar "VarW" int, Z bool, KoreAML.evar "VarKey0" int] = [1] := by
  decide +kernel

end Hand

/-- info: 'ExReader.Hand.exApart_shadow' depends on axioms: [propext] -/
#guard_msgs in #print axioms Hand.exApart_shadow
/-- info: 'ExReader.Hand.exKept_drop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Hand.exKept_drop

/-! ## Kernel-checked: the read rules and their existential variables -/

namespace Vars

definition_of defn from "f2-examples/exrhs.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem

/-- **`c(_, _Y) => d(?Z:Int)`**: the rule 2 has the one existential variable 5, `?Z`, which the
left side and the `requires` do not hold; it is well sorted, `rulePlainEx` admits it (arm A: under
the constructor d) and `openRefusal` gives none; `rulesPlain` and `coreOK` hold of the text. -/
theorem rule2 :
    (c.rules[2]'(by decide +kernel)).exs = [5] ∧
    (defn.pres.rules.getD 2 default).names.getD 5 "" = "'Ques'Z" ∧
    c.ruleSorted (c.rules[2]'(by decide +kernel)) = true ∧
    c.rulePlainEx (c.rules[2]'(by decide +kernel)) = true ∧
    (Parse.openRefusal c (c.rules[2]'(by decide +kernel)) []).isNone = true ∧
    c.rulesPlain = true ∧ c.coreOK = true := by
  decide_cheap

end Vars

namespace Two

definition_of defn from "f2-examples/exvarstwo.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem

/-- **`\exists(?Y, \exists(?Z, …))`**: `exs` is `?Y` then `?Z`, the text's order of nesting. -/
theorem rule0 :
    (c.rules[0]'(by decide +kernel)).exs = [2, 3] ∧
    ((defn.pres.rules.getD 0 default).names.getD 2 "", (defn.pres.rules.getD 0 default).names.getD 3 "") =
      ("'Ques'Y", "'Ques'Z") ∧
    c.ruleSorted (c.rules[0]'(by decide +kernel)) = true ∧
    c.rulePlainEx (c.rules[0]'(by decide +kernel)) = true := by
  decide +kernel

end Two

/-- info: 'ExReader.Vars.rule2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Vars.rule2
/-- info: 'ExReader.Two.rule0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Two.rule0

end ExReader
