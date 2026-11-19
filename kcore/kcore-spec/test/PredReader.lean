/-
  Reading functions that give a rule a predicate (`pre`, `post`), on kompiled texts. Run from the
  package root, after the library: `lake env lean -j1 test/PredReader.lean`.

  `Parse.parse` reads a rewrite axiom that holds a connective at a term position under
  applications with the position cut (`Parse.connRuleBody`, `ReadingNote.connectiveCut`).
  `showDef` prints, for a text, the definition `parse` builds: each rule with a predicate (its
  names, sorts, `exs`, `opens`, `pre`, `post`, `ruleSorted`, `rulePlainPP`, `openRefusal`), and the
  failing `wf` conjuncts with `rulesPlain` and `coreOK` (`rulesPlain` asks `rulePlainPP` of every
  rule, so a rule with a predicate does not fail it: each definition here has `wf`, `rulesPlain`
  and `coreOK`), or the refusal.

  ## rhs-connective
  - `mlror` (e3-ml-rule-rhs-or, `go => a() #Or b()`): read as
    `go => ?Z` with `post := or (mem Z a) (mem Z b)`, Z:Exp in `exs`, under the constructors of the
    configuration (arm A): `rulePlainPP` true, `openRefusal` none.
  - hand-written on the same text, the right side's `\or{Exp}(a, b)` replaced: `\not{Exp}(a)`:
    `post := not (mem Z a)`; `\top{Exp}()`: no `post`, Z an existential variable of the rule;
    `c(\or{Exp}(a, \not{Exp}(b)))`: the cut under the constructor c, `post := or (mem Z a) (not
    (mem Z b))`. With a `requires true andBool true` added, the rule read with the cut variable
    has a conjunct of `pre` of its own (`andAtBool`), and the cut is not taken: refused
    `patternConnective` (`\or`), the refusal without the cut.
  ## lhs-not
  - `mlnot` (e3-ml-rule-lhs-not, kompiled to `c(\not{Exp}(\and{Exp}(a, _Gen5))) => _Gen5`): read
    as `c(Z) => G` with `pre := not (and (mem Z a) (mem Z G))`, Z bound by the left side, G open
    and held by the right side under constructors (arm A): `rulePlainPP` true, `openRefusal` none. `larger`: beside a rule of a larger priority, G is open
    in a condition (`pre`) with a variable the left side binds: `openRequires` at Exp.
  A text read without the cut is read so (`mlor`, e7-guardors: no rule with a predicate).
  Kernel: `cut_right`, `cut_left` (the cut of a pattern), `parseWith_ruleOf`.

  ## lhs-implies
  - `mlimpl` (e3-ml-rule-lhs-implies, `c(a() #Implies b()) => b()`, kompiled to
    `c(\implies{Exp}(a(), \and{Exp}(b(), _Gen6))) => _Gen6`): read as `c(Z) => G` with
    `pre := implies (mem Z a) (and (mem Z b) (mem Z G))`. Kernel: `cut_implies`.

  ## lhs-and
  `Parse.lhsAndRuleBody` reads a left side's conjunction at a position under applications through
  the cut (`Parse.lhsAndCut`, `ReadingNote.lhsAndCut`), where the axiom is not read without it.
  - `mllhsceil` (e3-ml-rule-lhs-ceil-ctor, `go(X) #And #Ceil(go(X)) => done`): `pre := ceil go(X)`;
    `mllhseq` (e3-ml-rule-lhs-equals, `go(X) #And {X #Equals 1} => done`): `pre := X = 1`.
  - `mllhsandv` (e3-ml-rule-lhs-and, `c(X #And d(_, b())) => X`): `c(d(G, b) #as X) => X`, no
    `pre`.
  - `mllhsandp` (e3-ml-rule-lhs-and-pats, `c(d(X, _) #And d(_, b())) => X`): `c(d(X, G) #as Z) => X`
    with `pre := exMatch [Exp] Exp d(Y, b) Z top`, Y (the second wildcard, held by nothing else)
    bound by the match, held under the constructor d, so `Cond.bound` admits it.
  - hand-written on `mlimpl`'s text, the left side's `c(…)` conjoined with `{_Gen6 #Equals b()}` at
    KItem: both cuts, `pre` the connective's membership and then the predicate; the notes are
    `connectiveCut` and `lhsAndCut`.
  Kernel: `lhsAnd_pred`, `lhsAnd_var`, `lhsAnd_terms` (the cut of a left side).

  ## rhs-and
  `Parse.andRuleOf` (which `ruleBody` takes where `Parse.andCutOK` holds) reads a right side's
  conjunction of terms at a
  position under applications with the position cut (`Parse.andCut`). `showAnd` prints the rules
  `parseWith andRuleOf` builds, as `showDef` does, with whether the rule has an `ensures`.
  - `mlandt` (e3-ml-rule-rhs-and-term, `go(X) => f(X) #And g(X)` at Int): no conjunct is a
    variable, so the fresh form: `go(X) => ?Z` with `post := and (mem Z f(X)) (mem Z g(X))`.
  - `mlandc` (e3-ml-rule-rhs-and-ctor, `c(X) => X #And a()`), `mlandv` (e3-ml-rule-rhs-and-var,
    `c(X) => a() #And X`), `mlorand` (e3-ml-rule-lhs-or-rhs-and, `c(X) #Or d(X) => X #And a()`,
    two rules): the variable form, `c(X) => X` with `post := mem X a()`, no new variable.
  - hand-written on `mlandt`'s text: V1 `go(X) => f(f(X) #And g(X))`, the conjunction under the
    function f: the fresh form, refused `openRight` on the cut variable (held under no
    constructor). V2 `done => go(X) #And go(g(X))`, X not bound by the left side: the fresh form,
    refused `openRight` on X. V3 `done => X #And g(X)`: the variable form, `rulePlainPP` true.
  Each rule so read has no `ensures` (the text's rule has none) and `ruleSorted` true, and each
  definition has `wf`, `rulesPlain` and `coreOK` (`rulesPlain` asks `rulePlainPP` of every rule).
  Kernel: `and_fresh`, `and_var` (the cut of a pattern in each form).
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
  | .error r => IO.println s!"{n}: refused {repr r.reason} {r.detail}"
  | .ok d =>
    for ((r, p), i) in (d.sem.rules.zip d.pres.rules).zipIdx do
      if !(r.pre.isTop && r.post.isTop) || !r.exs.isEmpty then showRule d.sem s!"{n} rule {i}" r p.names
    IO.println s!"{n}: wf failing {(d.report.filter (!·.2)).map (·.1)}; rulesPlain {d.sem.rulesPlain}; coreOK {d.sem.coreOK}"

/-- The text with each rewrite axiom's `requires` replaced by `true andBool true`. -/
def editReq (k : Kore.Definition) : Kore.Definition :=
  let boolS := KoreAML.srt "Bool"
  let tt : Kore.Pattern := .dv boolS "true"
  { k with modules := k.modules.map fun m => { m with sentences := m.sentences.map fun s => match s with
      | .axiom a => (match a.pattern with
        | .rewrites s (.and s' [l, _]) r =>
          .axiom { a with pattern := .rewrites s (.and s' [l, .equals boolS s' (.and boolS [tt, tt]) tt]) r }
        | _ => .axiom a)
      | s => s } }

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
mlror rule 0: names ['Unds'DotVar1, 'Unds'DotVar0, 'Hash'Cut0] vars [K, GeneratedCounterCell, Exp] exs [2] opens [2]
  pre KCore.Cond.top
  post KCore.Cond.or
  (KCore.Cond.mem 32 (KCore.Term.var 2) (KCore.Term.app 385 []))
  (KCore.Cond.mem 32 (KCore.Term.var 2) (KCore.Term.app 386 []))
  ruleSorted true; rulePlainPP true; openRefusal none
mlror: wf failing []; rulesPlain true; coreOK true
mlror \not rule 0: names ['Unds'DotVar1, 'Unds'DotVar0, 'Hash'Cut0] vars [K, GeneratedCounterCell, Exp] exs [2] opens [2]
  pre KCore.Cond.top
  post KCore.Cond.not (KCore.Cond.mem 32 (KCore.Term.var 2) (KCore.Term.app 385 []))
  ruleSorted true; rulePlainPP true; openRefusal none
mlror \not: wf failing []; rulesPlain true; coreOK true
mlror \top rule 0: names ['Unds'DotVar1, 'Unds'DotVar0, 'Hash'Cut0] vars [K, GeneratedCounterCell, Exp] exs [2] opens [2]
  pre KCore.Cond.top
  post KCore.Cond.top
  ruleSorted true; rulePlainPP true; openRefusal none
mlror \top: wf failing []; rulesPlain true; coreOK true
mlror c(or-not) rule 0: names ['Unds'DotVar1, 'Unds'DotVar0, 'Hash'Cut0] vars [K, GeneratedCounterCell, Exp] exs [2] opens [2]
  pre KCore.Cond.top
  post KCore.Cond.or
  (KCore.Cond.mem 32 (KCore.Term.var 2) (KCore.Term.app 385 []))
  (KCore.Cond.not (KCore.Cond.mem 32 (KCore.Term.var 2) (KCore.Term.app 386 [])))
  ruleSorted true; rulePlainPP true; openRefusal none
mlror c(or-not): wf failing []; rulesPlain true; coreOK true
mlror requires: refused KCore.Parse.RefusalReason.patternConnective \or
mlor: wf failing []; rulesPlain true; coreOK true
## lhs-not
mlnot rule 0: names ['Hash'Cut0, 'Unds'DotVar1, 'Unds'DotVar0, 'Unds'Gen5] vars [Exp, K, GeneratedCounterCell, Exp] exs [] opens [3]
  pre KCore.Cond.not
  (KCore.Cond.and
    (KCore.Cond.mem 32 (KCore.Term.var 0) (KCore.Term.app 385 []))
    (KCore.Cond.mem 32 (KCore.Term.var 0) (KCore.Term.var 3)))
  post KCore.Cond.top
  ruleSorted true; rulePlainPP true; openRefusal none
mlnot: wf failing []; rulesPlain true; coreOK true
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
    showDef "mlror requires" (editReq k)
  if let some k ← load "mlor" then showDef "mlor" k
  IO.println "## lhs-not"
  if let some k ← load "mlnot" then
    showDef "mlnot" k
    match Parse.parse k with
    | .error _ => pure ()
    | .ok d =>
      match d.sem.rules.zip d.pres.rules with
      | (r, p) :: _ =>
        let c' : Semantics := { d.sem with rules := d.sem.rules ++ [{ r with pre := .top, prio := 200 }] }
        showRule c' "mlnot larger" r p.names
      | [] => pure ()

/-! ## rhs-and -/

def showAnd (n : String) (k : Kore.Definition) : IO Unit := do
  match Parse.parseWith Parse.andRuleOf k with
  | .error r => IO.println s!"{n}: andRuleOf: refused {repr r.reason} {r.detail}"
  | .ok d =>
    for ((r, p), i) in (d.sem.rules.zip d.pres.rules).zipIdx do
      if !(r.pre.isTop && r.post.isTop) || !r.exs.isEmpty then
        showRule d.sem s!"{n} rule {i}" r p.names
        IO.println s!"  ensures {r.ens.isSome}"
    IO.println s!"{n}: andRuleOf: wf failing {(d.report.filter (!·.2)).map (·.1)}; rulesPlain {d.sem.rulesPlain}; coreOK {d.sem.coreOK}"

mutual
  /-- p with each occurrence of `old` replaced by `new`. -/
  def repl (old new : Kore.Pattern) : Kore.Pattern → Kore.Pattern
    | .app h ss ps => if decide (Kore.Pattern.app h ss ps = old) then new else .app h ss (replList old new ps)
    | .and s ps => if decide (Kore.Pattern.and s ps = old) then new else .and s (replList old new ps)
    | p => if decide (p = old) then new else p
  def replList (old new : Kore.Pattern) : List Kore.Pattern → List Kore.Pattern
    | [] => []
    | p :: ps => repl old new p :: replList old new ps
end

/-- The text with each rewrite axiom's two sides changed by `edL` and `edR`. -/
def editRule (edL edR : Kore.Pattern → Kore.Pattern) (k : Kore.Definition) : Kore.Definition :=
  { k with modules := k.modules.map fun m => { m with sentences := m.sentences.map fun s => match s with
      | .axiom a => (match a.pattern with
        | .rewrites s l r => .axiom { a with pattern := .rewrites s (edL l) (edR r) }
        | _ => .axiom a)
      | s => s } }

def intS : Kore.KSort := KoreAML.srt "Int"
def kitemS : Kore.KSort := KoreAML.srt "KItem"
def xI : Kore.Pattern := .var (.evar (KoreAML.evar "VarX" intS))
def fX : Kore.Pattern := KoreAML.ap "Lblf" [xI]
def gX : Kore.Pattern := KoreAML.ap "Lblg" [xI]
def goX : Kore.Pattern := KoreAML.ap "Lblgo" [xI]
def injI (p : Kore.Pattern) : Kore.Pattern := .app ⟨⟨"inj"⟩⟩ [intS, kitemS] [p]
def injE (p : Kore.Pattern) : Kore.Pattern := .app ⟨⟨"inj"⟩⟩ [expS, kitemS] [p]

/--
info: ## rhs-and
mlandt rule 0: names [X, 'Unds'DotVar1, 'Unds'DotVar0, 'Hash'Cut0] vars [Int, K, GeneratedCounterCell, Int] exs [3] opens [3]
  pre KCore.Cond.top
  post KCore.Cond.and
  (KCore.Cond.mem 3 (KCore.Term.var 3) (KCore.Term.app 388 [KCore.Term.var 0]))
  (KCore.Cond.mem 3 (KCore.Term.var 3) (KCore.Term.app 389 [KCore.Term.var 0]))
  ruleSorted true; rulePlainPP true; openRefusal none
  ensures false
mlandt: andRuleOf: wf failing []; rulesPlain true; coreOK true
mlandc rule 0: names [X, 'Unds'DotVar1, 'Unds'DotVar0] vars [Exp, K, GeneratedCounterCell] exs [] opens []
  pre KCore.Cond.top
  post KCore.Cond.mem 32 (KCore.Term.var 0) (KCore.Term.app 385 [])
  ruleSorted true; rulePlainPP true; openRefusal none
  ensures false
mlandc: andRuleOf: wf failing []; rulesPlain true; coreOK true
mlandv rule 0: names [X, 'Unds'DotVar1, 'Unds'DotVar0] vars [Exp, K, GeneratedCounterCell] exs [] opens []
  pre KCore.Cond.top
  post KCore.Cond.mem 32 (KCore.Term.var 0) (KCore.Term.app 385 [])
  ruleSorted true; rulePlainPP true; openRefusal none
  ensures false
mlandv: andRuleOf: wf failing []; rulesPlain true; coreOK true
mlorand rule 0: names [X, 'Unds'DotVar1, 'Unds'DotVar0] vars [Exp, K, GeneratedCounterCell] exs [] opens []
  pre KCore.Cond.top
  post KCore.Cond.mem 32 (KCore.Term.var 0) (KCore.Term.app 385 [])
  ruleSorted true; rulePlainPP true; openRefusal none
  ensures false
mlorand rule 1: names [X, 'Unds'DotVar1, 'Unds'DotVar0] vars [Exp, K, GeneratedCounterCell] exs [] opens []
  pre KCore.Cond.top
  post KCore.Cond.mem 32 (KCore.Term.var 0) (KCore.Term.app 385 [])
  ruleSorted true; rulePlainPP true; openRefusal none
  ensures false
mlorand: andRuleOf: wf failing []; rulesPlain true; coreOK true
mlandt V1: andRuleOf: refused KCore.Parse.RefusalReason.openRight Var'Hash'Cut0:Int: bound by \exists on the right side, held there or in the ensures under no constructor, of a sort the text leaves unconfined: the successor is a value through an element that is no value's
mlandt V2: andRuleOf: refused KCore.Parse.RefusalReason.openRight VarX:Int: in the right side or the ensures under no constructor, not bound by the left side, of a sort the text leaves unconfined: the successor is a value through an element that is no value's
mlandt V3 rule 0: names ['Unds'DotVar1, 'Unds'DotVar0, X] vars [K, GeneratedCounterCell, Int] exs [] opens [2]
  pre KCore.Cond.top
  post KCore.Cond.mem 3 (KCore.Term.var 2) (KCore.Term.app 389 [KCore.Term.var 2])
  ruleSorted true; rulePlainPP true; openRefusal none
  ensures false
mlandt V3: andRuleOf: wf failing []; rulesPlain true; coreOK true
-/
#guard_msgs (whitespace := lax) in
#eval show IO Unit from do
  IO.println "## rhs-and"
  for n in ["mlandt", "mlandc", "mlandv", "mlorand"] do
    if let some k ← load n then showAnd n k
  if let some k ← load "mlandt" then
    let lhsDone := repl goX (KoreAML.ap "Lbldone" [])
    showAnd "mlandt V1" (editRule id (repl (.and intS [fX, gX]) (KoreAML.ap "Lblf" [.and intS [fX, gX]])) k)
    showAnd "mlandt V2" (editRule lhsDone
      (repl (injI (.and intS [fX, gX])) (injE (.and expS [goX, KoreAML.ap "Lblgo" [gX]]))) k)
    showAnd "mlandt V3" (editRule lhsDone (repl (.and intS [fX, gX]) (.and intS [xI, gX])) k)

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

def ZI : Kore.EVar := KoreAML.evar "Var'Hash'Cut0" intS

/-- A conjunction of two terms, neither a variable: a fresh variable at its place, in both. -/
theorem and_fresh : Parse.andCut [] 0 (injI (.and intS [fX, gX])) =
    (injI (.var (.evar ZI)), 1, [⟨ZI, intS, true, [fX, gX]⟩]) := by decide +kernel

/-- A conjunction with a variable among its conjuncts: the variable at its place, in the others;
no number is used. -/
theorem and_var : Parse.andCut [] 0 (injI (.and intS [gX, xI])) =
    (injI xI, 0, [⟨KoreAML.evar "VarX" intS, intS, false, [gX]⟩]) := by decide +kernel

/-! ## lhs-implies and lhs-and -/

/-- On a left side `\implies` is cut, as `\not` is. -/
theorem cut_implies : Parse.connCut true [] 0 (KoreAML.ap "Lblc" [.implies expS aP bP]) =
    (KoreAML.ap "Lblc" [.var (.evar Z0)], 1, [(Z0, expS, .implies expS aP bP)]) := by decide +kernel

def xE : Kore.Pattern := .var (.evar (KoreAML.evar "VarX" expS))
def yE : Kore.Pattern := .var (.evar (KoreAML.evar "VarY" expS))
def dP (p q : Kore.Pattern) : Kore.Pattern := KoreAML.ap "Lbld" [p, q]
def eqXa : Kore.Pattern := .equals expS expS xE aP

/-- A predicate operand of a left side's conjunction is taken out, the other at its place. -/
theorem lhsAnd_pred : Parse.lhsAndCut [] 0 (KoreAML.ap "Lblc" [.and expS [dP xE bP, eqXa]]) =
    (KoreAML.ap "Lblc" [dP xE bP], 0, [eqXa], []) := by decide +kernel

/-- A variable operand binds the other: `\and(X, p)` is `\and(p, X)`, which `term` reads as
`p #as X`. -/
theorem lhsAnd_var : Parse.lhsAndCut [] 0 (KoreAML.ap "Lblc" [.and expS [xE, dP yE bP]]) =
    (KoreAML.ap "Lblc" [.and expS [dP yE bP, xE]], 0, [], []) := by decide +kernel

/-- Two terms: the second's place holds a fresh variable, with the cut. -/
theorem lhsAnd_terms : Parse.lhsAndCut [] 0 (KoreAML.ap "Lblc" [.and expS [dP xE yE, dP yE bP]]) =
    (KoreAML.ap "Lblc" [.and expS [dP xE yE, .var (.evar Z0)]], 1, [], [(Z0, expS, dP yE bP)]) := by
  decide +kernel

/-- The notes of each rewrite axiom of the user's source in the last module of `k`. -/
def showNotes (n : String) (k : Kore.Definition) : IO Unit := do
  let N := Parse.namesOf k
  match k.modules.getLast? with
  | none => pure ()
  | some m =>
    for s in m.sentences do
      if let .axiom a := s then
        if (Parse.scanRewrite s).isSome && Parse.isUserSource a.attributes then
          IO.println s!"{n}: notes {(Parse.connNotes N a).map (·.name)}"

def gen6 : Kore.Pattern := .var (.evar (KoreAML.evar "Var'Unds'Gen6" expS))
def cImpl : Kore.Pattern := KoreAML.ap "Lblc" [.implies expS aP (.and expS [bP, gen6])]

/--
info: ## lhs-implies
mlimpl rule 0: names ['Hash'Cut0, 'Unds'DotVar1, 'Unds'DotVar0, 'Unds'Gen6] vars [Exp, K, GeneratedCounterCell, Exp] exs [] opens [3]
  pre KCore.Cond.implies
  (KCore.Cond.mem 32 (KCore.Term.var 0) (KCore.Term.app 385 []))
  (KCore.Cond.and
    (KCore.Cond.mem 32 (KCore.Term.var 0) (KCore.Term.app 386 []))
    (KCore.Cond.mem 32 (KCore.Term.var 0) (KCore.Term.var 3)))
  post KCore.Cond.top
  ruleSorted true; rulePlainPP true; openRefusal none
mlimpl: wf failing []; rulesPlain true; coreOK true
mlimpl: notes [connectiveCut]
-/
#guard_msgs (whitespace := lax) in
#eval show IO Unit from do
  IO.println "## lhs-implies"
  if let some k ← load "mlimpl" then
    showDef "mlimpl" k
    showNotes "mlimpl" k

/-- `mlimpl`'s text with the left side's `c(…)` conjoined with `{_Gen6 #Equals b()}` at KItem. -/
def editImplEq (k : Kore.Definition) : Kore.Definition :=
  editRule (repl (injE cImpl) (.and kitemS [injE cImpl, .equals expS kitemS gen6 bP])) id k

/--
info: ## lhs-and
mllhsceil rule 0: names [X, 'Unds'DotVar1, 'Unds'DotVar0] vars [Int, K, GeneratedCounterCell] exs [] opens []
  pre KCore.Cond.ceil 32 (KCore.Term.app 386 [KCore.Term.var 0])
  post KCore.Cond.top
  ruleSorted true; rulePlainPP true; openRefusal none
mllhsceil: wf failing []; rulesPlain true; coreOK true
mllhsceil: notes [lhsAndCut]
mllhseq rule 0: names [X, 'Unds'DotVar1, 'Unds'DotVar0] vars [Int, K, GeneratedCounterCell] exs [] opens []
  pre KCore.Cond.equals 3 (KCore.Term.var 0) (KCore.Term.dv 3 (KCore.Lit.int 1))
  post KCore.Cond.top
  ruleSorted true; rulePlainPP true; openRefusal none
mllhseq: wf failing []; rulesPlain true; coreOK true
mllhseq: notes [lhsAndCut]
mllhsandv: wf failing []; rulesPlain true; coreOK true
mllhsandv: notes [lhsAndCut]
mllhsandp rule 0: names [X, 'Unds'Gen0, 'Hash'Cut0, 'Unds'DotVar1, 'Unds'DotVar0] vars [Exp, Exp, Exp, K, GeneratedCounterCell] exs [] opens []
  pre KCore.Cond.exMatch
  [32]
  32
  (KCore.Term.app 388 [KCore.Term.var 5, KCore.Term.app 386 []])
  (KCore.Term.var 2)
  (KCore.Cond.top)
  post KCore.Cond.top
  ruleSorted true; rulePlainPP true; openRefusal none
mllhsandp: wf failing []; rulesPlain true; coreOK true
mllhsandp: notes [lhsAndCut]
mlimpl and-eq rule 0: names ['Hash'Cut0, 'Unds'DotVar1, 'Unds'DotVar0, 'Unds'Gen6] vars [Exp, K, GeneratedCounterCell, Exp] exs [] opens [3]
  pre KCore.Cond.and
  (KCore.Cond.implies
    (KCore.Cond.mem 32 (KCore.Term.var 0) (KCore.Term.app 385 []))
    (KCore.Cond.and
      (KCore.Cond.mem 32 (KCore.Term.var 0) (KCore.Term.app 386 []))
      (KCore.Cond.mem 32 (KCore.Term.var 0) (KCore.Term.var 3))))
  (KCore.Cond.equals 32 (KCore.Term.var 3) (KCore.Term.app 386 []))
  post KCore.Cond.top
  ruleSorted true; rulePlainPP true; openRefusal none
mlimpl and-eq: wf failing []; rulesPlain true; coreOK true
mlimpl and-eq: notes [connectiveCut, lhsAndCut]
-/
#guard_msgs (whitespace := lax) in
#eval show IO Unit from do
  IO.println "## lhs-and"
  for n in ["mllhsceil", "mllhseq", "mllhsandv", "mllhsandp"] do
    if let some k ← load n then
      showDef n k
      showNotes n k
  if let some k ← load "mlimpl" then
    showDef "mlimpl and-eq" (editImplEq k)
    showNotes "mlimpl and-eq" (editImplEq k)

end PredReader
