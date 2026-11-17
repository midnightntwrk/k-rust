/-
  Reading functions that give a rule a predicate (`pre`, `post`), on kompiled texts. Run from the
  package root, after the library: `lake env lean -j1 test/PredReader.lean`.

  `Parse.connRuleOf` (KcoreSpec/ReadRuleConn.lean; `ruleBody` does not call it) reads a rewrite
  axiom that holds a connective at a term position under applications with the position cut.
  `show1` prints, for a text, the landed reader's answer, then the definition `parseWith
  connRuleOf` builds: each rule with a predicate (its names, sorts, `exs`, `opens`, `pre`, `post`,
  `ruleSorted`, `rulePlainPP`, `openRefusal`), and the failing `wf` conjuncts with `rulesPlain`
  and `coreOK` (`rulesPlain` asks `\top` predicates of every rule, so it fails where a rule has
  one).

  ## rhs-connective
  - `mlror` (e3-ml-rule-rhs-or, `go => a() #Or b()`): the landed reader refuses `\or`; read as
    `go => ?Z` with `post := or (mem Z a) (mem Z b)`, Z:Exp in `exs`, under the constructors of the
    configuration (arm A): `rulePlainPP` true, `openRefusal` none.
  - hand-written on the same text, the right side's `\or{Exp}(a, b)` replaced: `\not{Exp}(a)`:
    `post := not (mem Z a)`; `\top{Exp}()`: no `post`, Z an existential variable of the rule;
    `c(\or{Exp}(a, \not{Exp}(b)))`: the cut under the constructor c, `post := or (mem Z a) (not
    (mem Z b))`.
  ## lhs-not
  - `mlnot` (e3-ml-rule-lhs-not, kompiled to `c(\not{Exp}(\and{Exp}(a, _Gen5))) => _Gen5`): the
    landed reader refuses `\not`; read as `c(Z) => G` with `pre := not (and (mem Z a) (mem Z G))`, Z
    bound by the left side, G open and held by the right side under constructors (arm A):
    `rulePlainPP` true, `openRefusal` none. `larger`: beside a rule of a larger priority, G is open
    in a condition (`pre`) with a variable the left side binds: `openRequires` at Exp.
  A text the landed reader reads is read by it (`mlor`, e7-guardors: the same rules).
  Kernel: `cut_right`, `cut_left` (the cut of a pattern), `parseWith_ruleOf`.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

open KCore

namespace PredReader

def load (n : String) : IO (Option Kore.Definition) := do
  match Kore.parseDefinition (← IO.FS.readFile s!"f2-examples/{n}.kompile.kore") with
  | .error e => IO.println s!"{n}: KORE read error {e}"; pure none
  | .ok k => pure (some k)

/-- The rule's predicates and what `rulesPlain`'s conjunct and `openRefusal` answer. -/
def showRule (c : Semantics) (tag : String) (r : Rule) (names : List String) : IO Unit := do
  IO.println s!"{tag}: names {names} vars {r.vars.map c.sortName} exs {r.exs} opens {r.opens}"
  IO.println s!"  pre {repr r.pre}"
  IO.println s!"  post {repr r.post}"
  IO.println s!"  ruleSorted {c.ruleSorted r}; rulePlainPP {c.rulePlainPP r}; openRefusal {(Parse.openRefusal c r names).map fun x => (repr x.1, x.2)}"

def showDef (n : String) (k : Kore.Definition) : IO Unit := do
  match Parse.parse k with
  | .ok d => IO.println s!"{n}: landed reader: read, {d.sem.rules.length} rules"
  | .error r => IO.println s!"{n}: landed reader: {repr r.reason} {r.detail}"
  match Parse.parseWith Parse.connRuleOf k with
  | .error r => IO.println s!"{n}: connRuleOf: refused {repr r.reason} {r.detail}"
  | .ok d =>
    let same := match Parse.parse k with
      | .ok d' => s!"; rules as the landed reader's {d.sem.rules.length == d'.sem.rules.length && (d.sem.rules.zip d'.sem.rules).all fun (a, b) => a.pre.isTop && a.post.isTop && a.exs == b.exs && a.vars == b.vars}"
      | .error _ => ""
    for ((r, p), i) in (d.sem.rules.zip d.pres.rules).zipIdx do
      if !(r.pre.isTop && r.post.isTop) || !r.exs.isEmpty then showRule d.sem s!"{n} rule {i}" r p.names
    IO.println s!"{n}: connRuleOf: wf failing {(d.report.filter (!·.2)).map (·.1)}; rulesPlain {d.sem.rulesPlain}; coreOK {d.sem.coreOK}{same}"

/-- The text with the right argument of each rewrite axiom whose right side holds `old` changed
by `ed`. -/
def editRhs (ed : Kore.Pattern → Kore.Pattern) (k : Kore.Definition) : Kore.Definition :=
  { k with modules := k.modules.map fun m => { m with sentences := m.sentences.map fun s => match s with
      | .axiom a => (match a.pattern with
        | .rewrites s l r => .axiom { a with pattern := .rewrites s l (ed r) }
        | _ => .axiom a)
      | s => s } }

def expS : Kore.KSort := KoreAML.srt "Exp"
def aP : Kore.Pattern := KoreAML.ap "Lbla" []
def bP : Kore.Pattern := KoreAML.ap "Lblb" []

mutual
  /-- p with each `\or{Exp}(a, b)` replaced by q. -/
  def replOr (q : Kore.Pattern) : Kore.Pattern → Kore.Pattern
    | .app h ss ps => .app h ss (replOrList q ps)
    | .and s ps => .and s (replOrList q ps)
    | .or s ps => if decide (Kore.Pattern.or s ps = .or expS [aP, bP]) then q else .or s ps
    | p => p
  def replOrList (q : Kore.Pattern) : List Kore.Pattern → List Kore.Pattern
    | [] => []
    | p :: ps => replOr q p :: replOrList q ps
end

/--
info: ## rhs-connective
mlror: landed reader: KCore.Parse.RefusalReason.patternConnective \or
mlror rule 0: names ['Unds'DotVar1, 'Unds'DotVar0, 'Hash'Cut0] vars [K, GeneratedCounterCell, Exp] exs [2] opens [2]
  pre KCore.Cond.top
  post KCore.Cond.or
  (KCore.Cond.mem 32 (KCore.Term.var 2) (KCore.Term.app 385 []))
  (KCore.Cond.mem 32 (KCore.Term.var 2) (KCore.Term.app 386 []))
  ruleSorted true; rulePlainPP true; openRefusal none
mlror: connRuleOf: wf failing [rules plain (rulesPlain): \top predicates, open and existential variables held, open condition variables confined or closed conditions apart]; rulesPlain false; coreOK false
mlror \not: landed reader: KCore.Parse.RefusalReason.patternConnective \not
mlror \not rule 0: names ['Unds'DotVar1, 'Unds'DotVar0, 'Hash'Cut0] vars [K, GeneratedCounterCell, Exp] exs [2] opens [2]
  pre KCore.Cond.top
  post KCore.Cond.not (KCore.Cond.mem 32 (KCore.Term.var 2) (KCore.Term.app 385 []))
  ruleSorted true; rulePlainPP true; openRefusal none
mlror \not: connRuleOf: wf failing [rules plain (rulesPlain): \top predicates, open and existential variables held, open condition variables confined or closed conditions apart]; rulesPlain false; coreOK false
mlror \top: landed reader: KCore.Parse.RefusalReason.patternConnective \top
mlror \top rule 0: names ['Unds'DotVar1, 'Unds'DotVar0, 'Hash'Cut0] vars [K, GeneratedCounterCell, Exp] exs [2] opens [2]
  pre KCore.Cond.top
  post KCore.Cond.top
  ruleSorted true; rulePlainPP true; openRefusal none
mlror \top: connRuleOf: wf failing []; rulesPlain true; coreOK true
mlror c(or-not): landed reader: KCore.Parse.RefusalReason.patternConnective \or
mlror c(or-not) rule 0: names ['Unds'DotVar1, 'Unds'DotVar0, 'Hash'Cut0] vars [K, GeneratedCounterCell, Exp] exs [2] opens [2]
  pre KCore.Cond.top
  post KCore.Cond.or
  (KCore.Cond.mem 32 (KCore.Term.var 2) (KCore.Term.app 385 []))
  (KCore.Cond.not (KCore.Cond.mem 32 (KCore.Term.var 2) (KCore.Term.app 386 [])))
  ruleSorted true; rulePlainPP true; openRefusal none
mlror c(or-not): connRuleOf: wf failing [rules plain (rulesPlain): \top predicates, open and existential variables held, open condition variables confined or closed conditions apart]; rulesPlain false; coreOK false
mlor: landed reader: read, 2 rules
mlor: connRuleOf: wf failing []; rulesPlain true; coreOK true; rules as the landed reader's true
## lhs-not
mlnot: landed reader: KCore.Parse.RefusalReason.patternConnective \not
mlnot rule 0: names ['Hash'Cut0, 'Unds'DotVar1, 'Unds'DotVar0, 'Unds'Gen5] vars [Exp, K, GeneratedCounterCell, Exp] exs [] opens [3]
  pre KCore.Cond.not
  (KCore.Cond.and
    (KCore.Cond.mem 32 (KCore.Term.var 0) (KCore.Term.app 385 []))
    (KCore.Cond.mem 32 (KCore.Term.var 0) (KCore.Term.var 3)))
  post KCore.Cond.top
  ruleSorted true; rulePlainPP true; openRefusal none
mlnot: connRuleOf: wf failing [rules plain (rulesPlain): \top predicates, open and existential variables held, open condition variables confined or closed conditions apart]; rulesPlain false; coreOK false
mlnot larger: names ['Hash'Cut0, 'Unds'DotVar1, 'Unds'DotVar0, 'Unds'Gen5] vars [Exp, K, GeneratedCounterCell, Exp] exs [] opens [3]
  pre KCore.Cond.not
  (KCore.Cond.and
    (KCore.Cond.mem 32 (KCore.Term.var 0) (KCore.Term.app 385 []))
    (KCore.Cond.mem 32 (KCore.Term.var 0) (KCore.Term.var 3)))
  post KCore.Cond.top
  ruleSorted true; rulePlainPP false; openRefusal (some (KCore.Parse.RefusalReason.openRequires, Var'Unds'Gen5:Exp: in a condition with a variable the left side binds, of a sort the text leaves unconfined, in a rule of a priority below another's))
-/
#guard_msgs (whitespace := lax) in
#eval show IO Unit from do
  IO.println "## rhs-connective"
  if let some k ← load "mlror" then
    showDef "mlror" k
    showDef "mlror \\not" (editRhs (replOr (.not expS aP)) k)
    showDef "mlror \\top" (editRhs (replOr (.top expS)) k)
    showDef "mlror c(or-not)" (editRhs (replOr (KoreAML.ap "Lblc" [.or expS [aP, .not expS bP]])) k)
  if let some k ← load "mlor" then showDef "mlor" k
  IO.println "## lhs-not"
  if let some k ← load "mlnot" then
    showDef "mlnot" k
    match Parse.parseWith Parse.connRuleOf k with
    | .error _ => pure ()
    | .ok d =>
      match d.sem.rules.zip d.pres.rules with
      | (r, p) :: _ =>
        let c' : Semantics := { d.sem with rules := d.sem.rules ++ [{ r with pre := .top, prio := 200 }] }
        showRule c' "mlnot larger" r p.names
      | [] => pure ()

/-! ## Kernel-checked: the cut -/

def Z0 : Kore.EVar := KoreAML.evar "Var'Hash'Cut0" expS

/-- On a right side `\or` is cut, under the constructor that holds it. -/
theorem cut_right : Parse.connCut false [] 0 (KoreAML.ap "Lblc" [.or expS [aP, bP]]) =
    (KoreAML.ap "Lblc" [.var (.evar Z0)], 1, [(Z0, expS, .or expS [aP, bP])]) := by decide +kernel

/-- On a left side `\not` is cut, and `\or` and `\top` are not. -/
theorem cut_left : Parse.connCut true [] 0 (KoreAML.ap "Lbld" [.not expS aP, .or expS [aP, bP], .top expS]) =
    (KoreAML.ap "Lbld" [.var (.evar Z0), .or expS [aP, bP], .top expS], 1, [(Z0, expS, .not expS aP)]) := by
  decide +kernel

example (k : Kore.Definition) : Parse.parseWith Parse.ruleOf k = Parse.parse k := Parse.parseWith_ruleOf k

end PredReader
