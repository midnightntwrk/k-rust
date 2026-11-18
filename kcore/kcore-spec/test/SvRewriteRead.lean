/-
  A set variable in a rewrite axiom, read through its instances at one element per occurrence
  (`Parse.svRewrite?`, `Parse.ruleBody`), on K 7.1.337 kompile's KORE of three fixtures
  (test/constructs/fixtures/NAME; the kompiled texts in f2-examples with their paths restored). Run
  from the package root: `lake env lean test/SvRewriteRead.lean`.

  - `e3-setvar-rewrite`: `rule <k> c(@S, @S) => d(@S) ... </k>`: read with the left side
    `c(S#L0, S#L1)`, the right side `d(S#R0)`, `S#R0` existential (`exs`) and
    `post := S#R0 ∈ S#L0 ∨ S#R0 ∈ S#L1`.
  - `e3-setvar-rewrite-fn`: `rule <k> c(@S, @S) => d(g(@S)) ... </k>`, g a function: read so, the
    existential variable under g, under no constructor: refused `openRight`.
  - `e3-setvar-rewrite-req`: `rule <k> c(@S) => d() ... </k> requires p(@S)`: refused
    `setVariable`, the detail naming the requires.
  - hand-written variants of `e3-setvar-rewrite`'s axiom: the set variable only on the left
    (`=> d(a())`: read, `post` top), only on the right (`c(a(), a())` on the left: refused), under
    `\not` on the left, in the ensures, and beside a second set variable (refused).
  - The emitted rule (`rulePattern`) carries `post` beside the `ensures`, under the existential
    variables' binders: `∃Z. \and(rhs, \and(ens, Z ∈ A₀ ∨ Z ∈ A₁))`, for any rule of that form
    (kernel-checked), and on the rule read from `e3-setvar-rewrite` (printed).
-/
import KcoreSpec

set_option autoImplicit false

open KCore

/-- A term, variables by name. -/
partial def svrTermStr (c : Semantics) (ns : List String) : Term → String
  | .var i => ns.getD i s!"?{i}"
  | .app f as => s!"{c.symName f}(" ++ ", ".intercalate (as.map (svrTermStr c ns)) ++ ")"
  | .inj a b t => s!"inj[{c.sortName a},{c.sortName b}](" ++ svrTermStr c ns t ++ ")"
  | .as t i => "(" ++ svrTermStr c ns t ++ s!" as {ns.getD i s!"?{i}"})"
  | .dv s l => s!"dv[{c.sortName s}]({reprStr l})"

/-- A condition, terms as `svrTermStr` prints them. -/
partial def svrCondStr (c : Semantics) (ns : List String) : Cond → String
  | .top => "top"
  | .bot => "bot"
  | .and p q => "and(" ++ svrCondStr c ns p ++ ", " ++ svrCondStr c ns q ++ ")"
  | .or p q => "or(" ++ svrCondStr c ns p ++ ", " ++ svrCondStr c ns q ++ ")"
  | .mem s t u => s!"in[{c.sortName s}](" ++ svrTermStr c ns t ++ ", " ++ svrTermStr c ns u ++ ")"
  | _ => "other"

/-- The user module's rewrite axiom's pattern edited by `edit`. -/
def svrEdit (edit : Kore.Pattern → Kore.Pattern) (k : Kore.Definition) : Kore.Definition :=
  let sent := fun (s : Kore.Sentence) => match s with
    | .axiom a => match a.pattern with
      | .rewrites .. => .axiom { a with pattern := edit a.pattern }
      | _ => s
    | s => s
  { k with modules := k.modules.dropLast ++
      (k.modules.getLast?.map fun m => [{ m with sentences := m.sentences.map sent }]).getD [] }

/-- The reader's verdict on the text at `path` (its rewrite axiom edited by `edit`): the refusal,
or each rule's variables, left side, right side, `exs` and `post`. -/
def svrVerdict (path : String) (edit : Kore.Pattern → Kore.Pattern := id) : IO String := do
  let .ok k := Kore.parseDefinition (← IO.FS.readFile path) | return "KORE read error"
  return match Parse.parse (svrEdit edit k) with
    | .error r => s!"{r.reason.name} ({r.detail})"
    | .ok d =>
      let c := d.sem
      let rules := (c.rules.zip d.pres.rules).map fun (r, p) =>
        s!"[{p.names}] {svrTermStr c p.names r.lhs} => {svrTermStr c p.names r.rhs} exs {r.exs.map (p.names.getD · "?")} post {svrCondStr c p.names r.post}"
      s!"read; {rules}"

/-- `c(@S, @S)`'s set variable occurrences, the user rule's left side's, replaced by `a()` (`left`)
or the right side's `d(@S)` by `d(a())`. -/
partial def svrSubst (left : Bool) : Kore.Pattern → Kore.Pattern
  | .rewrites s l r => if left then .rewrites s (svrSubst left l) r else .rewrites s l (svrSubst left r)
  | .and s ps => .and s (ps.map (svrSubst left))
  | .app h ss ps => .app h ss (ps.map (svrSubst left))
  | .var (.svar _) => .app ⟨⟨"Lbla"⟩⟩ [] []
  | p => p

/-- The user rule's left side's first set variable occurrence under `\not`. -/
partial def svrNot : Kore.Pattern → Kore.Pattern
  | .rewrites s l r => .rewrites s (svrNot l) r
  | .and s ps => .and s (ps.map svrNot)
  | .app h ss ps => .app h ss (ps.map svrNot)
  | .var (.svar x) => .not x.sort (.var (.svar x))
  | p => p

/-- The first set variable of a pattern. -/
partial def svrFirst : Kore.Pattern → Option Kore.SVar
  | .var (.svar x) => some x
  | .app _ _ ps | .and _ ps => ps.findSome? svrFirst
  | _ => none

/-- The right side's `\top` ensures replaced by `\ceil(@S)`. -/
def svrEns : Kore.Pattern → Kore.Pattern
  | .rewrites s l (.and s' [r, .top t]) => match svrFirst l with
    | some x => .rewrites s l (.and s' [r, .ceil x.sort t (.var (.svar x))])
    | none => .rewrites s l (.and s' [r, .top t])
  | p => p

/-- The right side's set variable renamed `@VarT`. -/
partial def svrTwo : Kore.Pattern → Kore.Pattern
  | .rewrites s l r => .rewrites s l (svrTwo r)
  | .and s ps => .and s (ps.map svrTwo)
  | .app h ss ps => .app h ss (ps.map svrTwo)
  | .var (.svar x) => .var (.svar { x with var := ⟨⟨"VarT"⟩⟩ })
  | p => p

/--
info: read; [[[S'Hash'L0, S'Hash'L1, 'Unds'DotVar1, 'Unds'DotVar0, S'Hash'R0]] Lbl'-LT-'generatedTop'-GT-'(Lbl'-LT-'k'-GT-'(kseq(inj[Exp,KItem](Lblc(S'Hash'L0, S'Hash'L1)), 'Unds'DotVar1)), 'Unds'DotVar0) => Lbl'-LT-'generatedTop'-GT-'(Lbl'-LT-'k'-GT-'(kseq(inj[Exp,KItem](Lbld(S'Hash'R0)), 'Unds'DotVar1)), 'Unds'DotVar0) exs [S'Hash'R0] post or(in[Exp](S'Hash'R0, S'Hash'L0), in[Exp](S'Hash'R0, S'Hash'L1))]
openRight (VarS'Hash'R0:Exp: bound by \exists on the right side, held there or in the ensures under no constructor, of a sort the text leaves unconfined: the successor is a value through an element that is no value's)
setVariable (VarS: in the requires: its truth at a larger set is not entailed by its truth at a smaller one, so the sentence reads every subset of the sort)
read; [[[S'Hash'L0, S'Hash'L1, 'Unds'DotVar1, 'Unds'DotVar0]] Lbl'-LT-'generatedTop'-GT-'(Lbl'-LT-'k'-GT-'(kseq(inj[Exp,KItem](Lblc(S'Hash'L0, S'Hash'L1)), 'Unds'DotVar1)), 'Unds'DotVar0) => Lbl'-LT-'generatedTop'-GT-'(Lbl'-LT-'k'-GT-'(kseq(inj[Exp,KItem](Lbld(Lbla())), 'Unds'DotVar1)), 'Unds'DotVar0) exs [] post top]
setVariable (VarS: in the right side and not in the left: the right side at the empty set is empty, so the axiom states that its left side matches nothing)
setVariable (VarS: under \not in the left side: the axiom is read through its instances at one element per occurrence only where every occurrence stands under applications)
setVariable (VarS: in the ensures: its truth at a larger set is not entailed by its truth at a smaller one, so the sentence reads every subset of the sort)
setVariable (VarS: one of two set variables or more: the reading is stated for one)
-/
#guard_msgs in
#eval show IO Unit from do
  IO.println (← svrVerdict "f2-examples/e3-setvar-rewrite.kompile.kore")
  IO.println (← svrVerdict "f2-examples/e3-setvar-rewrite-fn.kompile.kore")
  IO.println (← svrVerdict "f2-examples/e3-setvar-rewrite-req.kompile.kore")
  IO.println (← svrVerdict "f2-examples/e3-setvar-rewrite.kompile.kore" (svrSubst false))
  IO.println (← svrVerdict "f2-examples/e3-setvar-rewrite.kompile.kore" (svrSubst true))
  IO.println (← svrVerdict "f2-examples/e3-setvar-rewrite.kompile.kore" svrNot)
  IO.println (← svrVerdict "f2-examples/e3-setvar-rewrite.kompile.kore" svrEns)
  IO.println (← svrVerdict "f2-examples/e3-setvar-rewrite.kompile.kore" svrTwo)

/-- A rule with one existential variable Z (index 0) whose `post` is `Z ∈ A₀ ∨ Z ∈ A₁` and whose
`pre` is `\top` is emitted with the disjunction beside its `ensures`, under `\exists Z`. -/
example (c : Semantics) (z a0 a1 : KoreAML.Var) (r : Rule) (s : Srt) (hex : r.exs = [0])
    (hpre : r.pre = .top) (hpost : r.post = .or (.mem s (.var 0) (.var 1)) (.mem s (.var 0) (.var 2))) :
    rulePattern c [z, a0, a1] r =
      .rewrites (srtOf c topCellSort)
        (.and (srtOf c topCellSort) [Term.kore c [z, a0, a1] r.lhs, reqPat (srtOf c topCellSort) (r.req.map (Term.kore c [z, a0, a1]))])
        (.exist (srtOf c topCellSort) z.kore
          (.and (srtOf c topCellSort) [Term.kore c [z, a0, a1] r.rhs,
            .and (srtOf c topCellSort) [reqPat (srtOf c topCellSort) (r.ens.map (Term.kore c [z, a0, a1])),
              .or (srtOf c topCellSort)
                [.in (srtOf c s) (srtOf c topCellSort) (.var (.evar z.kore)) (.var (.evar a0.kore)),
                 .in (srtOf c s) (srtOf c topCellSort) (.var (.evar z.kore)) (.var (.evar a1.kore))]]])) := by
  simp only [rulePattern, rulePredPat_top hpre, hex, hpost]; rfl

/-- Each rule of the text at `path`, emitted (`rulePattern`, under the presentation's names). -/
def svrEmitted (path : String) : IO String := do
  let .ok k := Kore.parseDefinition (← IO.FS.readFile path) | return "KORE read error"
  return match Parse.parse k with
    | .error r => s!"{r.reason.name} ({r.detail})"
    | .ok d => "\n".intercalate ((d.sem.rules.zip d.pres.rules).map fun (r, p) =>
        Kore.Printer.pattern (rulePattern d.sem (KoreAML.varList (r.vars.map d.sem.sortName) p.names) r))

/--
info: \rewrites{SortGeneratedTopCell{}}(\and{SortGeneratedTopCell{}}(Lbl'-LT-'generatedTop'-GT-'{}(Lbl'-LT-'k'-GT-'{}(kseq{}(inj{SortExp{}, SortKItem{}}(Lblc{}(VarS'Hash'L0:SortExp{}, VarS'Hash'L1:SortExp{})), Var'Unds'DotVar1:SortK{})), Var'Unds'DotVar0:SortGeneratedCounterCell{}), \top{SortGeneratedTopCell{}}()), \exists{SortGeneratedTopCell{}}(VarS'Hash'R0:SortExp{}, \and{SortGeneratedTopCell{}}(Lbl'-LT-'generatedTop'-GT-'{}(Lbl'-LT-'k'-GT-'{}(kseq{}(inj{SortExp{}, SortKItem{}}(Lbld{}(VarS'Hash'R0:SortExp{})), Var'Unds'DotVar1:SortK{})), Var'Unds'DotVar0:SortGeneratedCounterCell{}), \and{SortGeneratedTopCell{}}(\top{SortGeneratedTopCell{}}(), \or{SortGeneratedTopCell{}}(\in{SortExp{}, SortGeneratedTopCell{}}(VarS'Hash'R0:SortExp{}, VarS'Hash'L0:SortExp{}), \in{SortExp{}, SortGeneratedTopCell{}}(VarS'Hash'R0:SortExp{}, VarS'Hash'L1:SortExp{}))))))
-/
#guard_msgs in
#eval show IO Unit from do
  IO.println (← svrEmitted "f2-examples/e3-setvar-rewrite.kompile.kore")
