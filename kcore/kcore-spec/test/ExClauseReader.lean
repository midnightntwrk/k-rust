/-
  `Parse.ceRead` (KcoreSpec/ReadFns.lean): an equation whose right side is under `\exists`, read as
  one clause with existential variables (`Clause.exs`) and a right-side predicate (`Clause.post`).
  Run on the kompiled texts of the fixtures (test/constructs/fixtures; K 7.1.337 kompile's KORE,
  from the cache `kfix.py` keeps, as test/RhsReader.lean reads it) and on hand-written equations.
  Run from the package root: `lake env lean -j1 test/ExClauseReader.lean`.

  `Parse.clauseBody` does not call `ceRead`: the reader refuses each of these texts as before
  (their accounts are unchanged). Each clause is put in the definition the landed reader builds
  from the text with that equation's right side replaced by a plain term, and printed with
  - the landed `clauseSorted` and `condOK` of `post`;
  - `sortedCE`, the conjuncts CN-4b §1.3 adds to `clauseSorted` (the existential variables are
    variables of the clause, distinct, held by neither the patterns nor the conditions; `post`
    well sorted);
  - `Clause.fixedExs` and whether each existential variable's sort is confined;
  - `clauseCE`, written here: `Semantics.clausePlainEx` (which the section or prints beside it)
    and the landed conjunct on open condition variables: `(!exs.isEmpty || post.isTop) &&
    exs.all (confined or among fixedExs c.confined c.hasValue) && (the landed conjunct on
    open condition variables)`. `clausesPlain` is `clausePlainEx` with `clauseExOK` (the conjuncts
    `sortedCE` prints) and the conjuncts on the premise and the open condition variables, so it is
    true of a text exactly where every clause has `clauseCE` and `sortedCE` (their premises being
    `\top`).

  ## exists

  | Fixture | Clause | `fixedExs`, confined | `clauseCE` |
  |---|---|---|---|
  | `e3-eq-exists-partial-ml` | `[X:Bool, B:Bool]`, `exs [1]`, `rhs B`, `post B = notBool(X)` | `[1]`, true | true |
  | `e3-eq-exists-ctor-ml` | `[X:Col, C:Col]`, `exs [1]`, `rhs C`, `post (C =/=K X) = true` | `[]`, true | true |
  | `e3-eq-exists-noens-ml` | `[_Gen0:Bool, B:Bool]`, `exs [1]`, `rhs B`, `post ⊤` | `[]`, true | true |
  | `e3-eq-exists-int-ml` | `[X:Int, Z:Int]`, `exs [1]`, `rhs Z`, `post (Z *Int 2 ==Int X) = true` | `[]`, false | false: Z is neither confined nor fixed, the clause is to be refused `existentialEquation Int` on the built definition |
  | `e3-eq-exists-ml-supersort` f | `[X:Int, B:Bool]`, `exs [1]`, `rhs inj{Bool,KItem}(B)`, `post B = (X >Int 0)` | `[1]`, true | true |
  | `e3-eq-exists-ml-supersort` h | `[K:KItem, Z:Int]`, `exs [1]`, `rhs Z`, `post inj{Int,KItem}(Z) = K` | `[1]`, false | true |

  Hand-written (`Hand`, over the names `N1`, f : Bool → Bool):
  - `eqTwoB`, `#Exists B. #Exists C. (C #And {C #Equals B} #And {B #Equals notBool X})`: `exs` is B
    then C, the order of nesting, though the body holds C first.
  - `eqUnheld`, `#Exists B. X`: refused `unheldVariable`, the body does not hold B.
  - `eqArg`, `#Exists X. X`: refused `patternConnective`, the arguments hold X.
  - `eqTwice`, `#Exists B. #Exists B. B`: refused `patternConnective`; `eqTwiceAB`,
    `#Exists A. #Exists B. #Exists B. B`: the detail names B, the variable bound twice.
  - `eqNoTerm`, `#Exists B. {B #Equals notBool X}`: refused `manyValuedRightSide` (`\top`).
  - `eqInner`, `#Exists B. (B #And #Exists C. {C #Equals B})`: refused `manyValuedRightSide`.
  - `eqAnd`, `#Exists B. (B #And notBool X)`, two term conjuncts, one of them B: see and-terms.
  - `eqPlain`, `f(X) => notBool X #And {X #Equals true}`, no binder: `exs = []`, the predicate in
    `post`.
  - `eqPredAnd`, a conjunction of two terms in a predicate's operand (`{(notBool X #And B) #Equals
    X}`): refused `patternConnective` (`ceRead_refused`); `cutAnd` does not reach an operand, and
    `term` would read it as the left-side pattern `notBool X #as B`.
  Kernel-checked (`kernel_rfl`, `decide +kernel`): `ceRead` on the equation of
  `e3-eq-exists-partial-ml` written by hand (`Hand.eqB`; `tie` checks that it is the scanned
  text's), on `eqTwoB`, and the refusals' reasons.

  ## and-terms-eq: a conjunction of terms at a term position (`Parse.cutAnd`)

  - `e3-ml-eq-rhs-and-term`, `h(X) => f(X) #And g(X)`: one clause over `[X:Int, #Cut0:Int]`,
    `exs [1]`, `rhs #Cut0`, `post (#Cut0 ∈ f(X)) ∧ (#Cut0 ∈ g(X))`; `fixedExs [1]` (both
    memberships are over X), so `clauseCE` is true at the unconfined Int.
  Hand-written (`HandAnd`, over the names `N2`, f, g, h : Int → Int):
  - `eqVar`, `h(X) => X #And g(X)`, a conjunct that is a variable of the clause: `post (Z ∈ X) ∧
    (Z ∈ g(X))`.
  - `eqUnder`, `h(X) => f(f(X) #And g(X))`, the conjunction under an application: `rhs f(Z)`.
  - `eqPred`, `h(X) => f(g(X) #And {X >Int 0 #Equals true})`: no cut, the predicate lifted out of
    the application into `post`.
  - `eqNested`, `h(X) => f(X) #And (g(X) #And X)`: one cut, three memberships.
  - `eqInner`, `h(X) => f(X) #And g(X #And f(X))`: two cuts, the inner one first in `exs`.
  - `eqOr`, `h(X) => f(X) #And (g(X) #Or X)`, a conjunct that is a disjunction: one cut, `post
    (Z ∈ f(X)) ∧ ((Z ∈ g(X)) ∨ (Z ∈ X))`, no variable for the disjunction (section or).
  A conjunct that applies a function whose equation has a `requires` is read as any application
  (the reading function does not look at g's equations); what the clause gives where g has no
  value is a fact of `Eval`, the fixture tests' after the wiring.
  Kernel-checked: `cutAnd` on the fixture's right side (the fresh variable's name among them),
  `ceRead` on the fixture's equation written by hand (`HandAnd.eqH`, tied to the text) and on
  `eqInner`.

  ## ceil-and: a conjunction of terms in the operand of a `\ceil` conjunct

  - `e3-ml-eq-rhs-ceil-and`, `h(X) => X #And #Ceil(f(X) #And g(X))`: `[X:Int, #Cut0:Int]`,
    `exs [1]`, `rhs X`, `post ⌈#Cut0⌉ ∧ #Cut0 ∈ f(X) ∧ #Cut0 ∈ g(X)`, `fixedExs [1]`.
  - `e3-ml-eq-rhs-equals-and` (the conjunction in an operand of `\equals`) and
    `e3-ml-eq-rhs-not-ceil-and` (the `\ceil` under `\not`): refused `patternConnective`.
  Hand-written (`HandAnd`): `eqCeilUnder`, `h(X) => X #And #Ceil(f(X #And g(X)))`: the operand is
  `f(#Cut0)`; `eqCeilBoth`, `h(X) => (f(X) #And g(X)) #And #Ceil(g(X #And f(X)))`: the body's
  variable before the `\ceil`'s in `exs`.
  Kernel-checked: `ceRead` on the fixture's equation written by hand (`HandAnd.eqCeil`, tied to the
  text).

  ## left: right sides `Parse.frRead` and `Parse.exRead` give `none` on (test/RhsReader.lean)

  Each put in the text's equation and read in the text's definition:
  - `g(#Bottom) #Or X` after `Parse.dropEmptyAlts`, in h's equation of `e3-ml-eq-rhs-or-total` (h
    with its `functional` sentence) and of `e3-ml-eq-rhs-or` (h without): `rhs X`, `exs []`.
  - `#Exists B:Bool. notBool(notBool(B) #And X)` in f's equation of `e3-eq-exists-bool-ml`: `exs`
    is B and the conjunction's fresh variable, `post` its two memberships.

  ## and-terms: a conjunction of terms one of which is an `\exists` variable

  - `e3-eq-exists-ml-and-terms` f, `f(X) => #Exists B:Bool. (B #And (notBool X))`: `[X:Bool,
    B:Bool]`, `exs [1]`, `rhs B`, `post B ∈ notBool(X)`, `fixedExs [1]`.
  - `e3-eq-exists-ml-and-terms` k, `k(X) => #Exists Z:Int. (Z #And (X +Int 1))`: `[X:Int, Z:Int]`,
    `exs [1]`, `rhs Z`, `post Z ∈ X +Int 1`, `fixedExs [1]`, so `clauseCE` is true at the
    unconfined Int.
  Hand-written (`HandTerms`, over `HandAnd.N2`):
  - `eqThree`, `h(X) => #Exists Z. (f(X) #And Z #And g(X))`: the variable is not the first
    conjunct: `rhs Z`, `post (Z ∈ f(X)) ∧ (Z ∈ g(X))`, no fresh variable.
  - `eqTwoVars`, `h(X) => #Exists Y. #Exists Z. (Z #And Y #And f(X))`: the first conjunct that
    is a bound variable, Z, stands in the position: `post (Z ∈ Y) ∧ (Z ∈ f(X))`.
  - `eqOther`, `h(X) => #Exists Z. (f(Z) #And g(X))`: no conjunct is the variable: a fresh
    `#Cut0` after Z in `exs`, `post (#Cut0 ∈ f(Z)) ∧ (#Cut0 ∈ g(X))`.
  - `eqArgVar`, `h(X) => #Exists Z. (f(Z) #And X)`: X is no `\exists` variable: a fresh variable.
  Kernel-checked: `cutAnd` and `ceRead` on the equation of k written by hand (`HandTerms.eqK`,
  tied to the text), and `ceRead` on `eqOther`.

  ## or: a disjunction of terms at a term position (`Parse.orCut`)

  `C[t₁ ∨ … ∨ tₙ]` under applications is `∃Z. C[Z] ∧ (Z ∈ t₁ ∨ … ∨ Z ∈ tₙ)`: one fresh variable
  `#Or0` of the disjunction's sort in `exs`, the disjunction of its memberships in `post`. Each
  clause is printed with `Semantics.clausePlainEx` in the definition built from the patched text.
  - `e3-ml-eq-rhs-or`, `h(X) => f(X) #Or g(X)`, h without its `functional` sentence: one clause
    over `[X:Int, #Or0:Int]`, `exs [1]`, `rhs #Or0`, `post (#Or0 ∈ f(X)) ∨ (#Or0 ∈ g(X))`;
    `fixedExs [1]` (each alternative fixes it by a term over X), so `clausePlainEx` is true at the
    unconfined Int.
  - `e3-ml-eq-rhs-or-many`, `k(_) => 1 #Or … #Or 9`: one clause, one variable, nine memberships
    (the text nests the disjunctions, and the memberships nest as they do);
    `clausePlainEx` true.
  `Parse.clauseBody` does not call `ceRead`, so today the reader refuses both texts
  `manyValuedRightSide` (`today`; their accounts are unchanged). Once `clauseBody` calls it where
  `frRead` does not read the equation (h has no `functional` sentence; k has nine alternatives),
  each text is read as the clause printed here, `clausesPlain` permitting.
  Hand-written (`HandOr`, over `HandAnd.N2`):
  - `eqUnder`, `h(X) => f(g(X) #Or X)`, under an application: `rhs f(#Or0)`.
  - `eqNested`, `h(X) => (f(X) #Or g(X)) #Or X`: one variable, three memberships.
  - `HandAnd.eqOr`: above.
  - `eqBoth`, `h(X) => f((f(X) #Or X) #And g(g(X) #Or X))`, a conjunction with a disjunction as a
    conjunct and one under an application of the other conjunct: `exs` is the conjunction's
    variable then the disjunction's, distinct.
  - `eqPredOr`, `h(X) => f(X) #And ({…} #Or {…})`, a disjunction of predicates: no cut, the
    predicate in `post` (`condOf`).
  - `eqInner`, `h(X) => f(g(X) #Or X) #Or X`, a disjunction under an application of an
    alternative: refused `manyValuedRightSide` (`\or`). An alternative is no position under
    applications of the right side: `C[g(a ∨ b) ∨ t]` is `C[t]` where a and b have no element,
    and a variable Z' cut beside the outer disjunction, `post (Z' ∈ a ∨ Z' ∈ b) ∧ (Z ∈ g(Z') ∨
    Z ∈ t)`, leaves no element there; the reader does not tell which inner disjunctions have an
    element.
  - `eqAndAlt`, `h(X) => (f(X) #And g(X) #And {…}) #Or X`, an alternative that is a conjunction:
    no variable for it, `post ((Z ∈ f(X)) ∧ (Z ∈ g(X)) ∧ {…}) ∨ (Z ∈ X)` (the one element Z is in
    a conjunction where it is in each conjunct; a predicate conjunct is itself).
  - `eqAndUnder`, `h(X) => f(f(X) #And g(X)) #Or X`, a conjunction under an application of an
    alternative: refused `patternConnective` (`\and`), for the reason of `eqInner`.
  - `eqPredAlt`, `eqTopAlt`, `eqNotAlt`, an alternative that is a predicate, `\top` under an
    application of an alternative and `\not` as an alternative: refused `manyValuedRightSide`.
  - `eqOrCeil`, `h(X) => f(f(X) #And g(g(X) #Or X)) #And #Ceil(f(X) #And g(X))`, a disjunction
    and a conjunction at term positions and a conjunction in a `\ceil`: `exs` is the body's
    conjunction's variable, the disjunction's, then the `\ceil`'s, and `post` the `\ceil`, then
    the memberships in that order.
  - `eqCeilOr`, `h(X) => X #And #Ceil(f(X) #And (g(X) #Or X))`, a disjunction that is a conjunct
    of a conjunction in a `\ceil`: read as in a conjunction at a term position,
    `(Z ∈ g(X)) ∨ (Z ∈ X)`. `eqCeilOrUnder`, `h(X) => X #And #Ceil(f(X) #And g(g(X) #Or X))`, a
    disjunction under an application in a `\ceil`'s conjunct: no variable is cut there, refused
    `patternConnective` (`\or`).
  Kernel-checked: `orCut` on the fixture's right side, `ceRead` on the fixture's equation written
  by hand (`HandOr.eqH`, tied to the text) and on `eqBoth`, and the refusals' reasons.

  ## hoist: `\exists` moved to the top of a right side (`Parse.hoistExists`)

  Hand-written (`HandHoist`, over `HandAnd.N2`), each right side compared with the expected one
  and then read by `ceRead`:
  - `eqApp`, `h(X) => f(#Exists Z. (Z #And {Z #Equals g(X)}))`: the binder under an application
    moves to the top; no test of a value is read.
  - `eqConj`, `h(X) => f(X) #And #Exists Z. (…)`: the binder in a conjunct; likewise.
  - `eqAlt`, `h(X) => X #Or #Exists Z. (…)`: the binder in an alternative moves where the test
    accepts Int, and the equation is refused `existentialEquation` where it accepts no sort.
    `ceRead` then reads the `\or` by `orCut` (section or): `exs` Z then `#Or0`, `post (#Or0 ∈ X)
    ∨ ((#Or0 ∈ Z) ∧ {Z = g(X)})`.
  - `eqTwo`, two binders named Z in two arguments: the second is `Z'`.
  - `eqArg`, a binder named as the argument X: renamed `X'` with the occurrences it binds.
  - `eqShadow`, a binder inside a binder of the same name: the inner one is renamed.
  - `eqNot`, `eqPredConj`: a binder under `\not` and one in a predicate conjunct stay.
  On fixtures, with `Semantics.valued` on the built definition as the test (`valuedSort`):
  `e3-eq-exists-ml-in-or-int` and `e3-eq-exists-ml-in-or` (the binder leaves the alternative;
  `ceRead` reads the `\or` as `eqAlt`'s), `e3-eq-exists-ml-under-app` and
  `e3-eq-exists-ml-and-right` (one clause each).
  Kernel-checked (`decide +kernel`): each hand-written case (`HandHoist.hoist_steps`).

  ## ex-after-hoist: EX's test after the binders are moved to the top (`Parse.exEqn?`)

  `exCases` and `clausesBody` test EX's shape on the equation `exEqn?` gives: `hoistExists` with no
  sort accepted as having a value, so the binders under applications and `\and` conjuncts move to
  the top (N1, N2: equalities in every interpretation, nothing asked of the sort) and a binder in an
  alternative of `\or` does not (the equation is not EX's; the stages after it read it as before).
  Hand-written (`HandExHoist`, over `NB`: f, g : Bool → Bool, f with its `functional` sentence):
  `eqUA`, `f(X) => g(#Exists B:Bool. (B #And {B #Equals X}))` (the equation of
  `e3-eq-exists-ml-under-app`, `tie`), and `eqAR`, `f(X) => notBool X #And #Exists B. (…)`, are moved
  to `eqUA'` and `eqAR'`; `eqOr`, `f(X) => X #Or #Exists B. (…)`, is not (`exEqn_steps`); `exCases`
  holds of the first two (`exCases_steps`); the reader's clauses of each are `exRead`'s of the moved
  equation (`wire_ua`, `wire_ar`). On the fixtures (`runExHoist`): `e3-eq-exists-ml-under-app` (f
  `total`) is read by EX, three clauses, `existsAsCases`; `e3-eq-exists-ml-and-right` (f not `total`)
  and `e3-eq-exists-ml-in-or` (the binder in an alternative of `\or`) are refused as before.
  The results of the reading (`HoistEval`): with the reader's clauses of `eqUA` (`reader_fCls`) and
  g's clause `g(B) => notBool B`, `f(true)` is `false` and `f(false)` is `true`, and nothing else
  (`eval_after_hoist`).
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

open KCore KCore.Parse

namespace ExClauseReader

/-! ## The harness -/

/-- `Semantics.clausePlainEx` with the conjunct of `clausesPlain` on open condition variables, written
out for one clause. -/
def clauseCE (c : Semantics) (cl : Clause) : Bool :=
  let conf := fun i => (cl.vars[i]?.map c.confined).getD false
  (!cl.exs.isEmpty || cl.post.isTop) &&
  cl.exs.all (fun i => conf i || (cl.fixedExs c.confined c.hasValue).contains i) &&
  (!cl.reqOpen || cl.reqClosed || cl.openCondVars.all fun i => conf i || memHeld c (varOccsList cl.pats) cl.pre i)

/-- CN-4b §1.3's additions to `clauseSorted`. -/
def sortedCE (c : Semantics) (cl : Clause) : Bool :=
  cl.exs.all (· < cl.vars.length) && nodup cl.exs && cl.exs.all (fun i => !cl.leftVars.contains i) &&
  c.condOK cl.vars cl.post

/-- The cache of kompiled fixture texts, as test/constructs/kfix.py names it. -/
def cacheDir : IO String := do
  let get := fun (n : String) => do
    match ← IO.getEnv n with
    | some d => pure (if d.isEmpty then none else some d)
    | none => pure none
  if let some d ← get "KCORE_KFIX_CACHE" then return d
  if let some d ← get "XDG_CACHE_HOME" then return s!"{d}/kcore-kfix"
  let home := (← get "HOME").getD "."
  return s!"{home}/.cache/kcore-kfix"

/-- The kompiled text of fixture `n`, its `BUILTIN/` and `FIXTURE/` paths restored to made-up
directories (as `kfix.py accounts` restores them before reading). -/
def load (n : String) : IO Kore.Definition := do
  let t ← IO.FS.readFile s!"test/constructs/fixtures/{n}/kompile.txt"
  let some l := (t.splitOn "\n").find? (·.startsWith "definition.kore sha256: ")
    | throw (IO.userError s!"{n}: kompile.txt names no sha256")
  let sha := (l.splitOn ": ").getD 1 ""
  let raw ← IO.FS.readFile s!"{← cacheDir}/{sha}.kore"
  let raw := ((raw.replace "BUILTIN/" "/made-up-k/include/kframework/builtin/").replace "FIXTURE/" "/made-up-fx/").replace
    "FIXTURE" "/made-up-fx"
  match Kore.parseDefinition raw with
  | .ok k => pure k
  | .error e => throw (IO.userError s!"{n}: KORE read error {e}")

/-- The text with the right side of each equation of the functions `fns` replaced by a pattern the
landed reader reads (the first argument's variable where the sorts agree, else a literal or its
injection), so that the definition is built and the clauses read here can be put in it. -/
def patch (fns : List String) (k : Kore.Definition) : Kore.Definition :=
  let fix := fun (s : Kore.Sentence) => match s with
    | .axiom a => match rawEqn? a, a.pattern with
      | some e, .implies r prem (.equals s1 s2 l (.and s3 [_, en])) =>
        if fns.contains e.fn then
          let rs := (KoreAML.Parse.sortName? s1).getD ""
          let arg := e.pats.findSome? fun p => match p with | .var (.evar x) => some x | _ => none
          let rhs : Kore.Pattern := match arg with
            | some x => if KoreAML.Parse.sortName? x.sort == some rs then .var (.evar x)
                        else if rs == "KItem" then .app ⟨⟨"inj"⟩⟩ [x.sort, s1] [.var (.evar x)]
                        else if rs == "Int" then .dv s1 "0" else .dv s1 "true"
            | none => if rs == "Int" then .dv s1 "0" else .dv s1 "true"
          Kore.Sentence.axiom { a with pattern := .implies r prem (.equals s1 s2 l (.and s3 [rhs, en])) }
        else s
      | _, _ => s
    | s => s
  match k.modules.reverse with
  | m :: rest => { k with modules := (({ m with sentences := m.sentences.map fix }) :: rest).reverse }
  | [] => k

def showT (sym : Sym → String) (srt : Srt → String) (names : List String) : Term → String
  | .var i => names.getD i s!"#{i}"
  | .app f ts => sym f ++ "(" ++ ", ".intercalate (ts.attach.map fun ⟨t, _⟩ => showT sym srt names t) ++ ")"
  | .inj a b t => s!"inj[{srt a},{srt b}](" ++ showT sym srt names t ++ ")"
  | .as t i => showT sym srt names t ++ " #as " ++ names.getD i s!"#{i}"
  | .dv _ (.bool b) => s!"{b}"
  | .dv _ (.int i) => s!"{i}"
  | .dv _ l => s!"{repr l}"

def showC (sym : Sym → String) (srt : Srt → String) (names : List String) : Cond → String
  | .top => "⊤" | .bot => "⊥"
  | .not p => "¬" ++ showC sym srt names p
  | .and p q => "(" ++ showC sym srt names p ++ " ∧ " ++ showC sym srt names q ++ ")"
  | .or p q => "(" ++ showC sym srt names p ++ " ∨ " ++ showC sym srt names q ++ ")"
  | .implies p q => "(" ++ showC sym srt names p ++ " → " ++ showC sym srt names q ++ ")"
  | .ceil s t => s!"⌈{showT sym srt names t}⌉:{srt s}"
  | .equals s t u => s!"({showT sym srt names t} =[{srt s}] {showT sym srt names u})"
  | .mem s t u => s!"({showT sym srt names t} ∈[{srt s}] {showT sym srt names u})"
  | .exMatch .. => "exMatch…"
  | .ex _ b => "∃." ++ showC sym srt names b
  | .all _ b => "∀." ++ showC sym srt names b

/-- A clause's fields. -/
def showFields (sym : Sym → String) (srt : Srt → String) (i : Nat) (cl : Clause) (vs : List KoreAML.Var) : IO Unit := do
  let names := vs.map (·.name)
  let T := showT sym srt names
  let C := showC sym srt names
  IO.println s!"  [{i}] vars {vs.map fun v => v.name ++ ":" ++ v.sort} pats {cl.pats.map T} req {cl.req.map T} prio {cl.prio} aside {cl.aside}"
  IO.println s!"      pre {C cl.pre}"
  IO.println s!"      rhs {T cl.rhs} ens {cl.ens.map T} exs {cl.exs} post {C cl.post}"

/-- `ceRead` on the equations of the functions `fns` of fixture `n` (each as `edit` gives it: a
hand-written right side in the text's equation): a refusal, or the clause, put in the definition
built from the patched text; with `plainEx`, `Semantics.clausePlainEx` of the clause there as
well. -/
def run (n : String) (fns : List String) (edit : RawEqn → RawEqn := id) (plainEx : Bool := false) : IO Unit := do
  let k ← load n
  let some m := k.modules.getLast? | IO.println s!"{n}: no module"
  let S := scan m.sentences
  match envOf m S with
  | .error f => IO.println s!"{n}: envOf fails {repr f.reason}"
  | .ok E =>
    match Parse.parse (patch fns k) with
    | .error r => IO.println s!"{n}: patched text refused {repr r.reason} {r.detail}"
    | .ok d =>
      let c0 := d.sem
      for fnName in fns do
        let mut cls : List (Clause × List KoreAML.Var) := []
        let mut stop := false
        for e in S.eqs.filter (·.fn == fnName) do
          match ceRead E.N (edit e) with
          | .error f => stop := true; IO.println s!"{n} {fnName}: refused {repr f.reason} ({f.detail})"
          | .ok x => cls := cls ++ [x]
        if stop then continue
        let some f := c0.fns.find? (c0.symName ·.label == fnName) | IO.println s!"{n}: no function {fnName}"
        let f' := { f with clauses := cls.map (·.1) }
        let c := { c0 with fns := c0.fns.map fun g => if g.label == f.label then f' else g }
        IO.println s!"{n} {fnName}: functional sentence {eqnFnl E.N ⟨fnName, [], none, none, .top (KoreAML.srt "K"), [], none, false⟩}; clauses {cls.length}"
        for ((cl, vs), i) in cls.zipIdx do
          showFields c.symName c.sortName i cl vs
          IO.println <| s!"      clauseSorted {c.clauseSorted f' (c.fns.map Fn.sig) cl}; condOK post {c.condOK cl.vars cl.post}; sortedCE {sortedCE c cl}; fixedExs {cl.fixedExs c.confined c.hasValue}; confined {cl.exs.map fun i => (cl.vars[i]?.map c.confined).getD false}; clauseCE {clauseCE c cl}" ++
            (if plainEx then s!"; clausePlainEx {c.clausePlainEx cl}" else "")
        let rest := c.subsortsOK && c.fns.all (fun f => f.clauses.all (c.clauseSorted f (c.fns.map Fn.sig))) &&
          c.rules.all c.ruleSorted && c.rulesPlain && c.paramsPlain
        IO.println s!"  sortedOK but clausesPlain {rest}; clausesPlain {c.clausesPlain}; every clause clauseCE {c.fns.all fun f => f.clauses.all (clauseCE c)}; readsConfined {c.readsConfined}"

/-- What the reader does with the text of fixture `n` as it is. -/
def today (n : String) : IO Unit := do
  match Parse.parse (← load n) with
  | .error r => IO.println s!"{n}: today refused {repr r.reason} ({r.detail})"
  | .ok _ => IO.println s!"{n}: today read"

/-- `ceRead` on a hand-written equation, a symbol and a sort the registry does not name printed
by number. -/
def showHand (what : String) (r : Rd (Clause × List KoreAML.Var)) : IO Unit :=
  match r with
  | .error f => IO.println s!"{what}: refused {repr f.reason} ({f.detail})"
  | .ok (cl, vs) => do
    IO.println s!"{what}:"
    showFields (fun f => regSymNames.getD f s!"sym{f - nRegSyms}") (fun s => regSortNames.getD s s!"sort{s - nRegSorts}") 0 cl vs

/-- The one equation of `fn` in the scanned text of fixture `n` is `e0` (its attributes apart). -/
def tie (n fn : String) (e0 : RawEqn) : IO Unit := do
  let k ← load n
  let some m := k.modules.getLast? | IO.println s!"{n}: no module"
  match (scan m.sentences).eqs.filter (·.fn == fn) with
  | [e] => IO.println s!"{n} {fn}: the hand-written equation is the text's: {e.pats == e0.pats && e.req == e0.req && e.competitors == e0.competitors && e.rhs == e0.rhs && e.ens == e0.ens && e.dom == e0.dom}"
  | es => IO.println s!"{n} {fn}: {es.length} equations"


/-! ## exists -/

/--
info: e3-eq-exists-partial-ml Lblf: functional sentence false; clauses 1
  [0] vars [X:Bool, B:Bool] pats [X] req none prio 50 aside false
      pre ⊤
      rhs B ens none exs [1] post (B =[Bool] LblnotBool'Unds'(X))
      clauseSorted true; condOK post true; sortedCE true; fixedExs [1]; confined [true]; clauseCE true
  sortedOK but clausesPlain true; clausesPlain true; every clause clauseCE true; readsConfined true
e3-eq-exists-ctor-ml Lblpick: functional sentence false; clauses 1
  [0] vars [X:Col, C:Col] pats [X] req none prio 50 aside false
      pre ⊤
      rhs C ens none exs [1] post (Lbl'UndsEqlsSlshEqls'K'Unds'(kseq(inj[Col,KItem](C), dotk()), kseq(inj[Col,KItem](X), dotk())) =[Bool] true)
      clauseSorted true; condOK post true; sortedCE true; fixedExs []; confined [true]; clauseCE true
  sortedOK but clausesPlain true; clausesPlain true; every clause clauseCE true; readsConfined true
e3-eq-exists-noens-ml Lblf: functional sentence false; clauses 1
  [0] vars ['Unds'Gen0:Bool, B:Bool] pats ['Unds'Gen0] req none prio 50 aside false
      pre ⊤
      rhs B ens none exs [1] post ⊤
      clauseSorted true; condOK post true; sortedCE true; fixedExs []; confined [true]; clauseCE true
  sortedOK but clausesPlain true; clausesPlain true; every clause clauseCE true; readsConfined true
e3-eq-exists-int-ml Lblh: functional sentence false; clauses 1
  [0] vars [X:Int, Z:Int] pats [X] req none prio 50 aside false
      pre ⊤
      rhs Z ens none exs [1] post (Lbl'UndsEqlsEqls'Int'Unds'(Lbl'UndsStar'Int'Unds'(Z, 2), X) =[Bool] true)
      clauseSorted true; condOK post true; sortedCE true; fixedExs []; confined [false]; clauseCE false
  sortedOK but clausesPlain true; clausesPlain false; every clause clauseCE false; readsConfined true
e3-eq-exists-ml-supersort Lblf: functional sentence false; clauses 1
  [0] vars [X:Int, B:Bool] pats [X] req none prio 50 aside false
      pre ⊤
      rhs inj[Bool,KItem](B) ens none exs [1] post (B =[Bool] Lbl'Unds-GT-'Int'Unds'(X, 0))
      clauseSorted true; condOK post true; sortedCE true; fixedExs [1]; confined [true]; clauseCE true
  sortedOK but clausesPlain true; clausesPlain true; every clause clauseCE true; readsConfined true
e3-eq-exists-ml-supersort Lblh: functional sentence false; clauses 1
  [0] vars [K:KItem, Z:Int] pats [K] req none prio 50 aside false
      pre ⊤
      rhs Z ens none exs [1] post (inj[Int,KItem](Z) =[KItem] K)
      clauseSorted true; condOK post true; sortedCE true; fixedExs [1]; confined [false]; clauseCE true
  sortedOK but clausesPlain true; clausesPlain true; every clause clauseCE true; readsConfined true
-/
#guard_msgs in
#eval show IO Unit from do
  run "e3-eq-exists-partial-ml" ["Lblf"]
  run "e3-eq-exists-ctor-ml" ["Lblpick"]
  run "e3-eq-exists-noens-ml" ["Lblf"]
  run "e3-eq-exists-int-ml" ["Lblh"]
  run "e3-eq-exists-ml-supersort" ["Lblf", "Lblh"]

namespace Hand

open KoreAML (ev ap srt evar)

/-- f : Bool → Bool, the symbol `nRegSyms`, without a `functional` sentence. -/
def N1 : Names := { sorts := [], syms := ["Lblf"], keyFns := [(nRegSyms, "Bool")] }

def bool : Kore.KSort := srt "Bool"
def X : Kore.Pattern := ev "VarX" bool
def B : Kore.Pattern := ev "VarB" bool
def C : Kore.Pattern := ev "VarC" bool
def notB (p : Kore.Pattern) : Kore.Pattern := ap "LblnotBool'Unds'" [p]
def eqP (p q : Kore.Pattern) : Kore.Pattern := .equals bool bool p q
/-- `#Exists V:Bool. body`. -/
def ex (v : String) (body : Kore.Pattern) : Kore.Pattern := .exist bool (evar v bool) body

def eqn (rhs : Kore.Pattern) : RawEqn := ⟨"Lblf", [X], none, none, rhs, [], none, false⟩

/-- `f(X) => #Exists B:Bool. (B #And {B #Equals notBool X})`: the equation of
`e3-eq-exists-partial-ml` (`tie`). -/
def eqB : RawEqn := eqn (ex "VarB" (.and bool [B, eqP B (notB X)]))
def eqTwoB : RawEqn := eqn (ex "VarB" (ex "VarC" (.and bool [C, .and bool [eqP C B, eqP B (notB X)]])))
def eqUnheld : RawEqn := eqn (ex "VarB" X)
def eqArg : RawEqn := eqn (ex "VarX" X)
def eqTwice : RawEqn := eqn (ex "VarB" (ex "VarB" B))
def eqTwiceAB : RawEqn := eqn (ex "VarA" (ex "VarB" (ex "VarB" B)))
def eqNoTerm : RawEqn := eqn (ex "VarB" (eqP B (notB X)))
def eqInner : RawEqn := eqn (ex "VarB" (.and bool [B, ex "VarC" (eqP C B)]))
def eqAnd : RawEqn := eqn (ex "VarB" (.and bool [B, notB X]))
def eqPlain : RawEqn := eqn (.and bool [notB X, eqP X (.dv bool "true")])
/-- `#Exists B. (B #And {(notBool X #And B) #Equals X})`: a conjunction in a predicate's operand. -/
def eqPredAnd : RawEqn := eqn (ex "VarB" (.and bool [B, eqP (.and bool [notB X, B]) X]))

end Hand

/--
info: e3-eq-exists-partial-ml Lblf: the hand-written equation is the text's: true
-/
#guard_msgs in
#eval tie "e3-eq-exists-partial-ml" "Lblf" Hand.eqB

/--
info: eqB:
  [0] vars [X:Bool, B:Bool] pats [X] req none prio 50 aside false
      pre ⊤
      rhs B ens none exs [1] post (B =[Bool] LblnotBool'Unds'(X))
eqTwoB:
  [0] vars [X:Bool, B:Bool, C:Bool] pats [X] req none prio 50 aside false
      pre ⊤
      rhs C ens none exs [1, 2] post ((C =[Bool] B) ∧ (B =[Bool] LblnotBool'Unds'(X)))
eqUnheld: refused KCore.Parse.RefusalReason.unheldVariable (VarB: bound by \exists, not held by its body)
eqArg: refused KCore.Parse.RefusalReason.patternConnective (VarX)
eqTwice: refused KCore.Parse.RefusalReason.patternConnective (VarB: bound twice)
eqTwiceAB: refused KCore.Parse.RefusalReason.patternConnective (VarB: bound twice)
eqNoTerm: refused KCore.Parse.RefusalReason.manyValuedRightSide (\top)
eqInner: refused KCore.Parse.RefusalReason.manyValuedRightSide (\exists)
eqAnd:
  [0] vars [X:Bool, B:Bool] pats [X] req none prio 50 aside false
      pre ⊤
      rhs B ens none exs [1] post (B ∈[Bool] LblnotBool'Unds'(X))
eqPlain:
  [0] vars [X:Bool] pats [X] req none prio 50 aside false
      pre ⊤
      rhs LblnotBool'Unds'(X) ens none exs [] post (X =[Bool] true)
-/
#guard_msgs in
open Hand in
#eval show IO Unit from do
  showHand "eqB" (ceRead N1 eqB)
  showHand "eqTwoB" (ceRead N1 eqTwoB)
  showHand "eqUnheld" (ceRead N1 eqUnheld)
  showHand "eqArg" (ceRead N1 eqArg)
  showHand "eqTwice" (ceRead N1 eqTwice)
  showHand "eqTwiceAB" (ceRead N1 eqTwiceAB)
  showHand "eqNoTerm" (ceRead N1 eqNoTerm)
  showHand "eqInner" (ceRead N1 eqInner)
  showHand "eqAnd" (ceRead N1 eqAnd)
  showHand "eqPlain" (ceRead N1 eqPlain)

/-! ## Kernel-checked -/

namespace Hand

def notX : Term := .app (regSymNames.idxOf "LblnotBool'Unds'") [.var 0]

/-- **`ceRead` on the fixture's equation, in the kernel**: one clause over `[X:Bool, B:Bool]`, B
existential, `rhs B`, `post B = notBool(X)`. -/
theorem ceRead_eqB : ceRead N1 eqB = .ok
    ({ vars := [Srt.bool, Srt.bool], pats := [.var 0], req := none, rhs := .var 1, ens := none, prio := 50,
       aside := false, exs := [1], post := .equals Srt.bool (.var 1) notX },
     [⟨"X", "Bool"⟩, ⟨"B", "Bool"⟩]) := by
  kernel_rfl

/-- `exs` follows the nesting of the binders, B then C, where the body holds C first. -/
theorem ceRead_eqTwoB : ceRead N1 eqTwoB = .ok
    ({ vars := [Srt.bool, Srt.bool, Srt.bool], pats := [.var 0], req := none, rhs := .var 2, ens := none,
       prio := 50, aside := false, exs := [1, 2],
       post := .and (.equals Srt.bool (.var 2) (.var 1)) (.equals Srt.bool (.var 1) notX) },
     [⟨"X", "Bool"⟩, ⟨"B", "Bool"⟩, ⟨"C", "Bool"⟩]) := by
  kernel_rfl

/-- The refusals' reasons. -/
theorem ceRead_refused :
    let reason := fun (e : RawEqn) => match ceRead N1 e with | .error f => some f.reason | .ok _ => none
    reason eqUnheld = some .unheldVariable ∧ reason eqArg = some .patternConnective ∧
    reason eqTwice = some .patternConnective ∧ reason eqTwiceAB = some .patternConnective ∧ reason eqNoTerm = some .manyValuedRightSide ∧
    reason eqInner = some .manyValuedRightSide ∧ reason eqPredAnd = some .patternConnective := by
  decide +kernel

end Hand

/-- info: 'ExClauseReader.Hand.ceRead_eqB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Hand.ceRead_eqB
/-- info: 'ExClauseReader.Hand.ceRead_eqTwoB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Hand.ceRead_eqTwoB
/-- info: 'ExClauseReader.Hand.ceRead_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Hand.ceRead_refused

/-! ## and-terms-eq -/

/--
info: e3-ml-eq-rhs-and-term Lblh: functional sentence false; clauses 1
  [0] vars [X:Int, 'Hash'Cut0:Int] pats [X] req none prio 50 aside false
      pre ⊤
      rhs 'Hash'Cut0 ens none exs [1] post (('Hash'Cut0 ∈[Int] Lblf(X)) ∧ ('Hash'Cut0 ∈[Int] Lblg(X)))
      clauseSorted true; condOK post true; sortedCE true; fixedExs [1]; confined [false]; clauseCE true
  sortedOK but clausesPlain true; clausesPlain true; every clause clauseCE true; readsConfined true
-/
#guard_msgs in
#eval show IO Unit from do
  run "e3-ml-eq-rhs-and-term" ["Lblh"]

namespace HandAnd

open KoreAML (ev ap srt evar)

/-- f, g, h : Int → Int, the symbols `nRegSyms` to `nRegSyms + 2`. -/
def N2 : Names :=
  { sorts := [], syms := ["Lblf", "Lblg", "Lblh"]
    keyFns := [(nRegSyms, "Int"), (nRegSyms + 1, "Int"), (nRegSyms + 2, "Int")] }

def int : Kore.KSort := srt "Int"
def X : Kore.Pattern := ev "VarX" int
def f (p : Kore.Pattern) : Kore.Pattern := ap "Lblf" [p]
def g (p : Kore.Pattern) : Kore.Pattern := ap "Lblg" [p]
def gt0 : Kore.Pattern :=
  .equals (srt "Bool") int (ap "Lbl'Unds-GT-'Int'Unds'" [X, .dv int "0"]) (.dv (srt "Bool") "true")

def eqn (rhs : Kore.Pattern) : RawEqn := ⟨"Lblh", [X], none, none, rhs, [], none, false⟩

/-- `h(X) => f(X) #And g(X)`: the equation of `e3-ml-eq-rhs-and-term` (`tie`). -/
def eqH : RawEqn := eqn (.and int [f X, g X])
def eqVar : RawEqn := eqn (.and int [X, g X])
def eqUnder : RawEqn := eqn (f (.and int [f X, g X]))
def eqPred : RawEqn := eqn (f (.and int [g X, gt0]))
def eqNested : RawEqn := eqn (.and int [f X, .and int [g X, X]])
def eqInner : RawEqn := eqn (.and int [f X, g (.and int [X, f X])])
def eqOr : RawEqn := eqn (.and int [f X, .or int [g X, X]])

end HandAnd

/--
info: e3-ml-eq-rhs-and-term Lblh: the hand-written equation is the text's: true
-/
#guard_msgs in
#eval tie "e3-ml-eq-rhs-and-term" "Lblh" HandAnd.eqH

/--
info: eqH:
  [0] vars [X:Int, 'Hash'Cut0:Int] pats [X] req none prio 50 aside false
      pre ⊤
      rhs 'Hash'Cut0 ens none exs [1] post (('Hash'Cut0 ∈[Int] sym0(X)) ∧ ('Hash'Cut0 ∈[Int] sym1(X)))
eqVar:
  [0] vars [X:Int, 'Hash'Cut0:Int] pats [X] req none prio 50 aside false
      pre ⊤
      rhs 'Hash'Cut0 ens none exs [1] post (('Hash'Cut0 ∈[Int] X) ∧ ('Hash'Cut0 ∈[Int] sym1(X)))
eqUnder:
  [0] vars [X:Int, 'Hash'Cut0:Int] pats [X] req none prio 50 aside false
      pre ⊤
      rhs sym0('Hash'Cut0) ens none exs [1] post (('Hash'Cut0 ∈[Int] sym0(X)) ∧ ('Hash'Cut0 ∈[Int] sym1(X)))
eqPred:
  [0] vars [X:Int] pats [X] req none prio 50 aside false
      pre ⊤
      rhs sym0(sym1(X)) ens none exs [] post (Lbl'Unds-GT-'Int'Unds'(X, 0) =[Bool] true)
eqNested:
  [0] vars [X:Int, 'Hash'Cut0:Int] pats [X] req none prio 50 aside false
      pre ⊤
      rhs 'Hash'Cut0 ens none exs [1] post (('Hash'Cut0 ∈[Int] sym0(X)) ∧ (('Hash'Cut0 ∈[Int] sym1(X)) ∧ ('Hash'Cut0 ∈[Int] X)))
eqInner:
  [0] vars [X:Int, 'Hash'Cut0:Int, 'Hash'Cut1:Int] pats [X] req none prio 50 aside false
      pre ⊤
      rhs 'Hash'Cut1 ens none exs [1, 2] post (('Hash'Cut0 ∈[Int] X) ∧ (('Hash'Cut0 ∈[Int] sym0(X)) ∧ (('Hash'Cut1 ∈[Int] sym0(X)) ∧ ('Hash'Cut1 ∈[Int] sym1('Hash'Cut0)))))
eqOr:
  [0] vars [X:Int, 'Hash'Cut0:Int] pats [X] req none prio 50 aside false
      pre ⊤
      rhs 'Hash'Cut0 ens none exs [1] post (('Hash'Cut0 ∈[Int] sym0(X)) ∧ (('Hash'Cut0 ∈[Int] sym1(X)) ∨ ('Hash'Cut0 ∈[Int] X)))
-/
#guard_msgs in
open HandAnd in
#eval show IO Unit from do
  showHand "eqH" (ceRead N2 eqH)
  showHand "eqVar" (ceRead N2 eqVar)
  showHand "eqUnder" (ceRead N2 eqUnder)
  showHand "eqPred" (ceRead N2 eqPred)
  showHand "eqNested" (ceRead N2 eqNested)
  showHand "eqInner" (ceRead N2 eqInner)
  showHand "eqOr" (ceRead N2 eqOr)

namespace HandAnd

def F : Sym := nRegSyms
def G : Sym := nRegSyms + 1
def x : Term := .var 0

/-- `cutAnd` on the fixture's right side, in the kernel: the fresh variable `Var'Hash'Cut0` of the
conjunction's sort in the position, the next number, the one cut, no predicate. -/
theorem cutAnd_eqH : cutAnd ["VarX"] [] 0 eqH.rhs =
    (KoreAML.ev "Var'Hash'Cut0" int, 1, [(KoreAML.evar "Var'Hash'Cut0" int, int, [f X, g X])], []) := by
  kernel_rfl

/-- A name of the text's is not taken: the fresh variable is primed. -/
theorem cutAnd_primed : (cutAnd ["VarX", "Var'Hash'Cut0"] [] 0 eqH.rhs).1 = KoreAML.ev "Var'Hash'Cut0'" int := by
  kernel_rfl

/-- **`ceRead` on the fixture's equation, in the kernel**: one clause over `[X:Int, #Cut0:Int]`,
the fresh variable existential and in the position, the two memberships in `post`. -/
theorem ceRead_eqH : ceRead N2 eqH = .ok
    ({ vars := [Srt.int, Srt.int], pats := [.var 0], req := none, rhs := .var 1, ens := none, prio := 50,
       aside := false, exs := [1],
       post := .and (.mem Srt.int (.var 1) (.app F [x])) (.mem Srt.int (.var 1) (.app G [x])) },
     [⟨"X", "Int"⟩, ⟨"'Hash'Cut0", "Int"⟩]) := by
  kernel_rfl

/-- Two cuts: the inner conjunction's variable first. -/
theorem ceRead_eqInner : ceRead N2 eqInner = .ok
    ({ vars := [Srt.int, Srt.int, Srt.int], pats := [.var 0], req := none, rhs := .var 2, ens := none,
       prio := 50, aside := false, exs := [1, 2],
       post := .and (.mem Srt.int (.var 1) x) (.and (.mem Srt.int (.var 1) (.app F [x]))
         (.and (.mem Srt.int (.var 2) (.app F [x])) (.mem Srt.int (.var 2) (.app G [.var 1])))) },
     [⟨"X", "Int"⟩, ⟨"'Hash'Cut0", "Int"⟩, ⟨"'Hash'Cut1", "Int"⟩]) := by
  kernel_rfl

end HandAnd

/-- info: 'ExClauseReader.HandAnd.cutAnd_eqH' depends on axioms: [propext] -/
#guard_msgs in #print axioms HandAnd.cutAnd_eqH
/-- info: 'ExClauseReader.HandAnd.cutAnd_primed' depends on axioms: [propext] -/
#guard_msgs in #print axioms HandAnd.cutAnd_primed
/-- info: 'ExClauseReader.HandAnd.ceRead_eqH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms HandAnd.ceRead_eqH
/-- info: 'ExClauseReader.HandAnd.ceRead_eqInner' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms HandAnd.ceRead_eqInner

/-! ## and-terms -/

/--
info: e3-eq-exists-ml-and-terms Lblf: functional sentence false; clauses 1
  [0] vars [X:Bool, B:Bool] pats [X] req none prio 50 aside false
      pre ⊤
      rhs B ens none exs [1] post (B ∈[Bool] LblnotBool'Unds'(X))
      clauseSorted true; condOK post true; sortedCE true; fixedExs [1]; confined [true]; clauseCE true
  sortedOK but clausesPlain true; clausesPlain true; every clause clauseCE true; readsConfined true
e3-eq-exists-ml-and-terms Lblk: functional sentence false; clauses 1
  [0] vars [X:Int, Z:Int] pats [X] req none prio 50 aside false
      pre ⊤
      rhs Z ens none exs [1] post (Z ∈[Int] Lbl'UndsPlus'Int'Unds'(X, 1))
      clauseSorted true; condOK post true; sortedCE true; fixedExs [1]; confined [false]; clauseCE true
  sortedOK but clausesPlain true; clausesPlain true; every clause clauseCE true; readsConfined true
-/
#guard_msgs in
#eval show IO Unit from do
  run "e3-eq-exists-ml-and-terms" ["Lblf", "Lblk"]

namespace HandTerms

open KoreAML (ev ap evar)
open HandAnd (N2 int X f g F G x)

def Y : Kore.Pattern := ev "VarY" int
def Z : Kore.Pattern := ev "VarZ" int
/-- `#Exists V:Int. body`. -/
def ex (v : String) (body : Kore.Pattern) : Kore.Pattern := .exist int (evar v int) body

def eqn (fn : String) (rhs : Kore.Pattern) : RawEqn := ⟨fn, [X], none, none, rhs, [], none, false⟩

/-- k : Int → Int, the symbol `nRegSyms`. -/
def N3 : Names := { sorts := [], syms := ["Lblk"], keyFns := [(nRegSyms, "Int")] }

/-- `k(X) => #Exists Z:Int. (Z #And (X +Int 1))`: the equation of k in
`e3-eq-exists-ml-and-terms` (`tie`). -/
def eqK : RawEqn := eqn "Lblk" (ex "VarZ" (.and int [Z, ap "Lbl'UndsPlus'Int'Unds'" [X, .dv int "1"]]))
def eqThree : RawEqn := eqn "Lblh" (ex "VarZ" (.and int [f X, .and int [Z, g X]]))
def eqTwoVars : RawEqn := eqn "Lblh" (ex "VarY" (ex "VarZ" (.and int [Z, .and int [Y, f X]])))
def eqOther : RawEqn := eqn "Lblh" (ex "VarZ" (.and int [f Z, g X]))
def eqArgVar : RawEqn := eqn "Lblh" (ex "VarZ" (.and int [f Z, X]))

end HandTerms

/--
info: e3-eq-exists-ml-and-terms Lblk: the hand-written equation is the text's: true
-/
#guard_msgs in
#eval tie "e3-eq-exists-ml-and-terms" "Lblk" HandTerms.eqK

/--
info: eqK:
  [0] vars [X:Int, Z:Int] pats [X] req none prio 50 aside false
      pre ⊤
      rhs Z ens none exs [1] post (Z ∈[Int] Lbl'UndsPlus'Int'Unds'(X, 1))
eqThree:
  [0] vars [X:Int, Z:Int] pats [X] req none prio 50 aside false
      pre ⊤
      rhs Z ens none exs [1] post ((Z ∈[Int] sym0(X)) ∧ (Z ∈[Int] sym1(X)))
eqTwoVars:
  [0] vars [X:Int, Y:Int, Z:Int] pats [X] req none prio 50 aside false
      pre ⊤
      rhs Z ens none exs [1, 2] post ((Z ∈[Int] Y) ∧ (Z ∈[Int] sym0(X)))
eqOther:
  [0] vars [X:Int, Z:Int, 'Hash'Cut0:Int] pats [X] req none prio 50 aside false
      pre ⊤
      rhs 'Hash'Cut0 ens none exs [1, 2] post (('Hash'Cut0 ∈[Int] sym0(Z)) ∧ ('Hash'Cut0 ∈[Int] sym1(X)))
eqArgVar:
  [0] vars [X:Int, Z:Int, 'Hash'Cut0:Int] pats [X] req none prio 50 aside false
      pre ⊤
      rhs 'Hash'Cut0 ens none exs [1, 2] post (('Hash'Cut0 ∈[Int] sym0(Z)) ∧ ('Hash'Cut0 ∈[Int] X))
-/
#guard_msgs in
open HandTerms HandAnd in
#eval show IO Unit from do
  showHand "eqK" (ceRead N3 eqK)
  showHand "eqThree" (ceRead N2 eqThree)
  showHand "eqTwoVars" (ceRead N2 eqTwoVars)
  showHand "eqOther" (ceRead N2 eqOther)
  showHand "eqArgVar" (ceRead N2 eqArgVar)

namespace HandTerms

open KoreAML (ap evar)
open HandAnd (N2 int X F G x)

def plus1 : Term := .app (regSymNames.idxOf "Lbl'UndsPlus'Int'Unds'") [.var 0, .dv Srt.int (.int 1)]

/-- `cutAnd` with Z bound, on the body of k's right side, in the kernel: Z in the position, no
number used, the one cut with the other conjunct. -/
theorem cutAnd_eqK : cutAnd ["VarX", "VarZ"] ["VarZ"] 0 (.and HandAnd.int [Z, ap "Lbl'UndsPlus'Int'Unds'" [X, .dv HandAnd.int "1"]]) =
    (Z, 0, [(evar "VarZ" HandAnd.int, HandAnd.int, [ap "Lbl'UndsPlus'Int'Unds'" [X, .dv HandAnd.int "1"]])], []) := by
  kernel_rfl

/-- **`ceRead` on the fixture's equation of k, in the kernel**: one clause over `[X:Int, Z:Int]`,
Z existential and in the position, `post Z ∈ X +Int 1`. -/
theorem ceRead_eqK : ceRead N3 eqK = .ok
    ({ vars := [Srt.int, Srt.int], pats := [.var 0], req := none, rhs := .var 1, ens := none, prio := 50,
       aside := false, exs := [1], post := .mem Srt.int (.var 1) plus1 },
     [⟨"X", "Int"⟩, ⟨"Z", "Int"⟩]) := by
  kernel_rfl

/-- No conjunct is the bound variable: the fresh variable, after Z in `exs`. -/
theorem ceRead_eqOther : ceRead N2 eqOther = .ok
    ({ vars := [Srt.int, Srt.int, Srt.int], pats := [.var 0], req := none, rhs := .var 2, ens := none,
       prio := 50, aside := false, exs := [1, 2],
       post := .and (.mem Srt.int (.var 2) (.app F [.var 1])) (.mem Srt.int (.var 2) (.app G [x])) },
     [⟨"X", "Int"⟩, ⟨"Z", "Int"⟩, ⟨"'Hash'Cut0", "Int"⟩]) := by
  kernel_rfl

end HandTerms

/-- info: 'ExClauseReader.HandTerms.cutAnd_eqK' depends on axioms: [propext] -/
#guard_msgs in #print axioms HandTerms.cutAnd_eqK
/-- info: 'ExClauseReader.HandTerms.ceRead_eqK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms HandTerms.ceRead_eqK
/-- info: 'ExClauseReader.HandTerms.ceRead_eqOther' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms HandTerms.ceRead_eqOther

/-! ## ceil-and -/

namespace HandAnd

/-- `h(X) => X #And #Ceil(f(X) #And g(X))`: the equation of `e3-ml-eq-rhs-ceil-and` (`tie`). -/
def eqCeil : RawEqn := eqn (.and int [X, .ceil int int (.and int [f X, g X])])
def eqCeilUnder : RawEqn := eqn (.and int [X, .ceil int int (f (.and int [X, g X]))])
def eqCeilBoth : RawEqn := eqn (.and int [.and int [f X, g X], .ceil int int (g (.and int [X, f X]))])

/-- **`ceRead` on the fixture's equation, in the kernel**: one clause over `[X:Int, #Cut0:Int]`,
`rhs X`, the fresh variable existential, `post` the `\ceil` of it and its two memberships. -/
theorem ceRead_eqCeil : ceRead N2 eqCeil = .ok
    ({ vars := [Srt.int, Srt.int], pats := [.var 0], req := none, rhs := .var 0, ens := none, prio := 50,
       aside := false, exs := [1],
       post := .and (.ceil Srt.int (.var 1))
         (.and (.mem Srt.int (.var 1) (.app F [x])) (.mem Srt.int (.var 1) (.app G [x]))) },
     [⟨"X", "Int"⟩, ⟨"'Hash'Cut0", "Int"⟩]) := by
  kernel_rfl

end HandAnd

/-- info: 'ExClauseReader.HandAnd.ceRead_eqCeil' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms HandAnd.ceRead_eqCeil

/--
info: e3-ml-eq-rhs-ceil-and Lblh: the hand-written equation is the text's: true
e3-ml-eq-rhs-ceil-and Lblh: functional sentence false; clauses 1
  [0] vars [X:Int, 'Hash'Cut0:Int] pats [X] req none prio 50 aside false
      pre ⊤
      rhs X ens none exs [1] post (⌈'Hash'Cut0⌉:Int ∧ (('Hash'Cut0 ∈[Int] Lblf(X)) ∧ ('Hash'Cut0 ∈[Int] Lblg(X))))
      clauseSorted true; condOK post true; sortedCE true; fixedExs [1]; confined [false]; clauseCE true
  sortedOK but clausesPlain true; clausesPlain true; every clause clauseCE true; readsConfined true
e3-ml-eq-rhs-equals-and Lblh: refused KCore.Parse.RefusalReason.patternConnective (\and)
e3-ml-eq-rhs-not-ceil-and Lblh: refused KCore.Parse.RefusalReason.patternConnective (\and)
eqCeilUnder:
  [0] vars [X:Int, 'Hash'Cut0:Int] pats [X] req none prio 50 aside false
      pre ⊤
      rhs X ens none exs [1] post (⌈sym0('Hash'Cut0)⌉:Int ∧ (('Hash'Cut0 ∈[Int] X) ∧ ('Hash'Cut0 ∈[Int] sym1(X))))
eqCeilBoth:
  [0] vars [X:Int, 'Hash'Cut0:Int, 'Hash'Cut1:Int] pats [X] req none prio 50 aside false
      pre ⊤
      rhs 'Hash'Cut0 ens none exs [1, 2] post (⌈sym1('Hash'Cut1)⌉:Int ∧ (('Hash'Cut0 ∈[Int] sym0(X)) ∧ (('Hash'Cut0 ∈[Int] sym1(X)) ∧ (('Hash'Cut1 ∈[Int] X) ∧ ('Hash'Cut1 ∈[Int] sym0(X))))))
-/
#guard_msgs in
open HandAnd in
#eval show IO Unit from do
  tie "e3-ml-eq-rhs-ceil-and" "Lblh" eqCeil
  run "e3-ml-eq-rhs-ceil-and" ["Lblh"]
  run "e3-ml-eq-rhs-equals-and" ["Lblh"]
  run "e3-ml-eq-rhs-not-ceil-and" ["Lblh"]
  showHand "eqCeilUnder" (ceRead N2 eqCeilUnder)
  showHand "eqCeilBoth" (ceRead N2 eqCeilBoth)

/-! ## left -/

/--
info: e3-ml-eq-rhs-or-total Lblh: functional sentence true; clauses 1
  [0] vars [X:Int] pats [X] req none prio 50 aside false
      pre ⊤
      rhs X ens none exs [] post ⊤
      clauseSorted true; condOK post true; sortedCE true; fixedExs []; confined []; clauseCE true
  sortedOK but clausesPlain true; clausesPlain true; every clause clauseCE true; readsConfined false
e3-ml-eq-rhs-or Lblh: functional sentence false; clauses 1
  [0] vars [X:Int] pats [X] req none prio 50 aside false
      pre ⊤
      rhs X ens none exs [] post ⊤
      clauseSorted true; condOK post true; sortedCE true; fixedExs []; confined []; clauseCE true
  sortedOK but clausesPlain true; clausesPlain true; every clause clauseCE true; readsConfined false
e3-eq-exists-bool-ml Lblf: functional sentence true; clauses 1
  [0] vars [X:Bool, B:Bool, 'Hash'Cut0:Bool] pats [X] req none prio 50 aside false
      pre ⊤
      rhs LblnotBool'Unds'('Hash'Cut0) ens none exs [1, 2] post (('Hash'Cut0 ∈[Bool] LblnotBool'Unds'(B)) ∧ ('Hash'Cut0 ∈[Bool] X))
      clauseSorted true; condOK post true; sortedCE true; fixedExs [2]; confined [true, true]; clauseCE true
  sortedOK but clausesPlain true; clausesPlain true; every clause clauseCE true; readsConfined true
-/
#guard_msgs in
open KoreAML (ev ap srt evar) in
#eval show IO Unit from do
  let int := srt "Int"
  let side := dropEmptyAlts (.or int [ap "Lblg" [.bottom int], ev "VarX" int])
  run "e3-ml-eq-rhs-or-total" ["Lblh"] (fun e => { e with rhs := side })
  run "e3-ml-eq-rhs-or" ["Lblh"] (fun e => { e with rhs := side })
  let bool := srt "Bool"
  let notB := fun (p : Kore.Pattern) => ap "LblnotBool'Unds'" [p]
  run "e3-eq-exists-bool-ml" ["Lblf"]
    (fun e => { e with rhs := .exist bool (evar "VarB" bool) (notB (.and bool [notB (ev "VarB" bool), ev "VarX" bool])) })

/-! ## or -/

/--
info: e3-ml-eq-rhs-or Lblh: functional sentence false; clauses 1
  [0] vars [X:Int, 'Hash'Or0:Int] pats [X] req none prio 50 aside false
      pre ⊤
      rhs 'Hash'Or0 ens none exs [1] post (('Hash'Or0 ∈[Int] Lblf(X)) ∨ ('Hash'Or0 ∈[Int] Lblg(X)))
      clauseSorted true; condOK post true; sortedCE true; fixedExs [1]; confined [false]; clauseCE true; clausePlainEx true
  sortedOK but clausesPlain true; clausesPlain true; every clause clauseCE true; readsConfined true
e3-ml-eq-rhs-or-many Lblk: functional sentence true; clauses 1
  [0] vars ['Unds'Gen0:Int, 'Hash'Or0:Int] pats ['Unds'Gen0] req none prio 50 aside false
      pre ⊤
      rhs 'Hash'Or0 ens none exs [1] post ((((((((('Hash'Or0 ∈[Int] 1) ∨ ('Hash'Or0 ∈[Int] 2)) ∨ ('Hash'Or0 ∈[Int] 3)) ∨ ('Hash'Or0 ∈[Int] 4)) ∨ ('Hash'Or0 ∈[Int] 5)) ∨ ('Hash'Or0 ∈[Int] 6)) ∨ ('Hash'Or0 ∈[Int] 7)) ∨ ('Hash'Or0 ∈[Int] 8)) ∨ ('Hash'Or0 ∈[Int] 9))
      clauseSorted true; condOK post true; sortedCE true; fixedExs [1]; confined [false]; clauseCE true; clausePlainEx true
  sortedOK but clausesPlain true; clausesPlain true; every clause clauseCE true; readsConfined true
e3-ml-eq-rhs-or: today refused KCore.Parse.RefusalReason.manyValuedRightSide (\or: the sentence gives the function every element of each side; the text holds no functional sentence of the function, so where the sides differ that is more than one element, which no clause states)
e3-ml-eq-rhs-or-many: today refused KCore.Parse.RefusalReason.manyValuedRightSide (\or: 9 alternatives, more than 8)
-/
#guard_msgs in
#eval show IO Unit from do
  run "e3-ml-eq-rhs-or" ["Lblh"] (plainEx := true)
  run "e3-ml-eq-rhs-or-many" ["Lblk"] (plainEx := true)
  today "e3-ml-eq-rhs-or"
  today "e3-ml-eq-rhs-or-many"

namespace HandOr

open HandAnd (N2 int X f g F G x eqn gt0)

/-- `h(X) => f(X) #Or g(X)`: the equation of `e3-ml-eq-rhs-or` (`tie`). -/
def eqH : RawEqn := eqn (.or int [f X, g X])
def eqUnder : RawEqn := eqn (f (.or int [g X, X]))
def eqNested : RawEqn := eqn (.or int [.or int [f X, g X], X])
def eqBoth : RawEqn := eqn (f (.and int [.or int [f X, X], g (.or int [g X, X])]))
def eqPredOr : RawEqn := eqn (.and int [f X, .or int [gt0, .not int gt0]])
def eqInner : RawEqn := eqn (.or int [f (.or int [g X, X]), X])
def eqAndAlt : RawEqn := eqn (.or int [.and int [f X, .and int [g X, gt0]], X])
def eqAndUnder : RawEqn := eqn (.or int [f (.and int [f X, g X]), X])
def eqPredAlt : RawEqn := eqn (.or int [gt0, X])
def eqTopAlt : RawEqn := eqn (.or int [f (.top int), X])
def eqNotAlt : RawEqn := eqn (.or int [.not int (f X), X])
def eqOrCeil : RawEqn :=
  eqn (.and int [f (.and int [f X, g (.or int [g X, X])]), .ceil int int (.and int [f X, g X])])
def eqCeilOr : RawEqn := eqn (.and int [X, .ceil int int (.and int [f X, .or int [g X, X]])])
def eqCeilOrUnder : RawEqn := eqn (.and int [X, .ceil int int (.and int [f X, g (.or int [g X, X])])])

end HandOr

/--
info: e3-ml-eq-rhs-or Lblh: the hand-written equation is the text's: true
-/
#guard_msgs in
#eval tie "e3-ml-eq-rhs-or" "Lblh" HandOr.eqH

/--
info: eqH:
  [0] vars [X:Int, 'Hash'Or0:Int] pats [X] req none prio 50 aside false
      pre ⊤
      rhs 'Hash'Or0 ens none exs [1] post (('Hash'Or0 ∈[Int] sym0(X)) ∨ ('Hash'Or0 ∈[Int] sym1(X)))
eqUnder:
  [0] vars [X:Int, 'Hash'Or0:Int] pats [X] req none prio 50 aside false
      pre ⊤
      rhs sym0('Hash'Or0) ens none exs [1] post (('Hash'Or0 ∈[Int] sym1(X)) ∨ ('Hash'Or0 ∈[Int] X))
eqNested:
  [0] vars [X:Int, 'Hash'Or0:Int] pats [X] req none prio 50 aside false
      pre ⊤
      rhs 'Hash'Or0 ens none exs [1] post ((('Hash'Or0 ∈[Int] sym0(X)) ∨ ('Hash'Or0 ∈[Int] sym1(X))) ∨ ('Hash'Or0 ∈[Int] X))
eqOr:
  [0] vars [X:Int, 'Hash'Cut0:Int] pats [X] req none prio 50 aside false
      pre ⊤
      rhs 'Hash'Cut0 ens none exs [1] post (('Hash'Cut0 ∈[Int] sym0(X)) ∧ (('Hash'Cut0 ∈[Int] sym1(X)) ∨ ('Hash'Cut0 ∈[Int] X)))
eqBoth:
  [0] vars [X:Int, 'Hash'Cut0:Int, 'Hash'Or0:Int] pats [X] req none prio 50 aside false
      pre ⊤
      rhs sym0('Hash'Cut0) ens none exs [1, 2] post ((('Hash'Cut0 ∈[Int] sym0(X)) ∨ ('Hash'Cut0 ∈[Int] X)) ∧ (('Hash'Cut0 ∈[Int] sym1('Hash'Or0)) ∧ (('Hash'Or0 ∈[Int] sym1(X)) ∨ ('Hash'Or0 ∈[Int] X))))
eqPredOr:
  [0] vars [X:Int] pats [X] req none prio 50 aside false
      pre ⊤
      rhs sym0(X) ens none exs [] post ((Lbl'Unds-GT-'Int'Unds'(X, 0) =[Bool] true) ∨ ¬(Lbl'Unds-GT-'Int'Unds'(X, 0) =[Bool] true))
eqInner: refused KCore.Parse.RefusalReason.manyValuedRightSide (\or)
eqAndAlt:
  [0] vars [X:Int, 'Hash'Or0:Int] pats [X] req none prio 50 aside false
      pre ⊤
      rhs 'Hash'Or0 ens none exs [1] post ((('Hash'Or0 ∈[Int] sym0(X)) ∧ (('Hash'Or0 ∈[Int] sym1(X)) ∧ (Lbl'Unds-GT-'Int'Unds'(X, 0) =[Bool] true))) ∨ ('Hash'Or0 ∈[Int] X))
eqAndUnder: refused KCore.Parse.RefusalReason.patternConnective (\and)
eqPredAlt: refused KCore.Parse.RefusalReason.manyValuedRightSide (\top)
eqTopAlt: refused KCore.Parse.RefusalReason.manyValuedRightSide (\top)
eqNotAlt: refused KCore.Parse.RefusalReason.manyValuedRightSide (\not)
eqOrCeil:
  [0] vars [X:Int, 'Hash'Cut0:Int, 'Hash'Or0:Int, 'Hash'Cut1:Int] pats [X] req none prio 50 aside false
      pre ⊤
      rhs sym0('Hash'Cut0) ens none exs [1, 2, 3] post (⌈'Hash'Cut1⌉:Int ∧ (('Hash'Cut0 ∈[Int] sym0(X)) ∧ (('Hash'Cut0 ∈[Int] sym1('Hash'Or0)) ∧ ((('Hash'Or0 ∈[Int] sym1(X)) ∨ ('Hash'Or0 ∈[Int] X)) ∧ (('Hash'Cut1 ∈[Int] sym0(X)) ∧ ('Hash'Cut1 ∈[Int] sym1(X)))))))
eqCeilOr:
  [0] vars [X:Int, 'Hash'Cut0:Int] pats [X] req none prio 50 aside false
      pre ⊤
      rhs X ens none exs [1] post (⌈'Hash'Cut0⌉:Int ∧ (('Hash'Cut0 ∈[Int] sym0(X)) ∧ (('Hash'Cut0 ∈[Int] sym1(X)) ∨ ('Hash'Cut0 ∈[Int] X))))
eqCeilOrUnder: refused KCore.Parse.RefusalReason.patternConnective (\or)
-/
#guard_msgs in
open HandOr HandAnd in
#eval show IO Unit from do
  showHand "eqH" (ceRead N2 HandOr.eqH)
  showHand "eqUnder" (ceRead N2 HandOr.eqUnder)
  showHand "eqNested" (ceRead N2 HandOr.eqNested)
  showHand "eqOr" (ceRead N2 eqOr)
  showHand "eqBoth" (ceRead N2 eqBoth)
  showHand "eqPredOr" (ceRead N2 eqPredOr)
  showHand "eqInner" (ceRead N2 HandOr.eqInner)
  showHand "eqAndAlt" (ceRead N2 eqAndAlt)
  showHand "eqAndUnder" (ceRead N2 eqAndUnder)
  showHand "eqPredAlt" (ceRead N2 eqPredAlt)
  showHand "eqTopAlt" (ceRead N2 eqTopAlt)
  showHand "eqNotAlt" (ceRead N2 eqNotAlt)
  showHand "eqOrCeil" (ceRead N2 eqOrCeil)
  showHand "eqCeilOr" (ceRead N2 eqCeilOr)
  showHand "eqCeilOrUnder" (ceRead N2 eqCeilOrUnder)

namespace HandOr

open HandAnd (N2 int X f g F G x)

/-- `orCut` on the fixture's right side, in the kernel: the fresh variable `Var'Hash'Or0` of the
disjunction's sort in the position, the next number, the one cut, its conjunct the disjunction. -/
theorem orCut_eqH : orCut ["VarX"] 0 eqH.rhs =
    (KoreAML.ev "Var'Hash'Or0" HandAnd.int, 1,
      [(KoreAML.evar "Var'Hash'Or0" HandAnd.int, HandAnd.int, [.or HandAnd.int [f X, g X]])]) := by
  kernel_rfl

/-- **`ceRead` on the fixture's equation, in the kernel**: one clause over `[X:Int, #Or0:Int]`,
the fresh variable existential and in the position, the disjunction of its memberships in `post`. -/
theorem ceRead_eqH : ceRead N2 eqH = .ok
    ({ vars := [Srt.int, Srt.int], pats := [.var 0], req := none, rhs := .var 1, ens := none, prio := 50,
       aside := false, exs := [1],
       post := .or (.mem Srt.int (.var 1) (.app F [x])) (.mem Srt.int (.var 1) (.app G [x])) },
     [⟨"X", "Int"⟩, ⟨"'Hash'Or0", "Int"⟩]) := by
  kernel_rfl

/-- A conjunction and two disjunctions: the conjunction's variable, then the variable of the
disjunction under an application; the disjunction that is a conjunct has none. -/
theorem ceRead_eqBoth : ceRead N2 eqBoth = .ok
    ({ vars := [Srt.int, Srt.int, Srt.int], pats := [.var 0], req := none, rhs := .app F [.var 1], ens := none,
       prio := 50, aside := false, exs := [1, 2],
       post := .and (.or (.mem Srt.int (.var 1) (.app F [x])) (.mem Srt.int (.var 1) x))
         (.and (.mem Srt.int (.var 1) (.app G [.var 2]))
           (.or (.mem Srt.int (.var 2) (.app G [x])) (.mem Srt.int (.var 2) x))) },
     [⟨"X", "Int"⟩, ⟨"'Hash'Cut0", "Int"⟩, ⟨"'Hash'Or0", "Int"⟩]) := by
  kernel_rfl

/-- The refusals' reasons. -/
theorem ceRead_refused :
    let reason := fun (e : RawEqn) => match ceRead N2 e with | .error f => some f.reason | .ok _ => none
    reason eqInner = some .manyValuedRightSide ∧ reason eqAndUnder = some .patternConnective ∧
    reason eqPredAlt = some .manyValuedRightSide ∧
    reason eqTopAlt = some .manyValuedRightSide ∧ reason eqNotAlt = some .manyValuedRightSide := by
  decide +kernel

end HandOr

/-- info: 'ExClauseReader.HandOr.orCut_eqH' depends on axioms: [propext] -/
#guard_msgs in #print axioms HandOr.orCut_eqH
/-- info: 'ExClauseReader.HandOr.ceRead_eqH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms HandOr.ceRead_eqH
/-- info: 'ExClauseReader.HandOr.ceRead_eqBoth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms HandOr.ceRead_eqBoth
/-- info: 'ExClauseReader.HandOr.ceRead_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms HandOr.ceRead_refused

/-! Opaque constants `ceRead`, `cutAnd` and `orCut` reach (test/OpaqueAudit.lean's walk):
`String.Internal.append`, through the details of refusals only. -/

open Lean in
def opaqueReach (roots : List Name) : MetaM (List Name) := do
  let env ← getEnv
  let mut seen : NameSet := {}
  let mut todo : List Name := roots
  let mut out : List Name := []
  while !todo.isEmpty do
    let n := todo.head!
    todo := todo.tail!
    if seen.contains n then continue
    seen := seen.insert n
    match env.find? n with
    | some (.opaqueInfo _) => out := n :: out
    | some (.defnInfo d) =>
      for c in d.value.getUsedConstants ++ d.type.getUsedConstants do
        unless seen.contains c do todo := c :: todo
    | _ => pure ()
  return out.mergeSort (·.toString < ·.toString)

/--
info: KCore.Parse.ceRead: [String.Internal.append]
KCore.Parse.cutAnd: []
KCore.Parse.orCut: []
-/
#guard_msgs in
#eval show Lean.MetaM Unit from do
  for root in [``ceRead, ``cutAnd, ``orCut] do IO.println s!"{root}: {← opaqueReach [root]}"

/-! ## hoist: `\exists` moved to the top of a right side (`Parse.hoistExists`) -/

namespace HandHoist

open KoreAML (ev ap srt evar)
open HandAnd (N2 int X f g eqn)

def Z : Kore.Pattern := ev "VarZ" int
def Z' : Kore.Pattern := ev "VarZ'" int
def X' : Kore.Pattern := ev "VarX'" int
def eqI (p q : Kore.Pattern) : Kore.Pattern := .equals int int p q
/-- `#Exists V:Int. body`. -/
def ex (v : String) (body : Kore.Pattern) : Kore.Pattern := .exist int (evar v int) body

/-- A test of a value that accepts Int only. -/
def valInt (s : Kore.KSort) : Bool := KoreAML.Parse.sortName? s == some "Int"

/-- N1, `h(X) => f(#Exists Z. (Z #And {Z #Equals g(X)}))`: the binder under an application. -/
def eqApp : RawEqn := eqn (f (ex "VarZ" (.and int [Z, eqI Z (g X)])))
def eqApp' : RawEqn := eqn (ex "VarZ" (f (.and int [Z, eqI Z (g X)])))
/-- N2, `h(X) => f(X) #And #Exists Z. (Z #And {Z #Equals g(X)})`: the binder in a conjunct. -/
def eqConj : RawEqn := eqn (.and int [f X, ex "VarZ" (.and int [Z, eqI Z (g X)])])
def eqConj' : RawEqn := eqn (ex "VarZ" (.and int [f X, .and int [Z, eqI Z (g X)]]))
/-- N3, `h(X) => X #Or #Exists Z. (Z #And {Z #Equals f(X)})`: the binder in an alternative. -/
def eqAlt : RawEqn := eqn (.or int [X, ex "VarZ" (.and int [Z, eqI Z (f X)])])
def eqAlt' : RawEqn := eqn (ex "VarZ" (.or int [X, .and int [Z, eqI Z (f X)]]))
/-- Two binders of one name in two conjuncts: the second is renamed. -/
def eqTwo : RawEqn := eqn (.and int [f (ex "VarZ" (.and int [Z, eqI Z X])), g (ex "VarZ" (.and int [Z, eqI Z (f X)]))])
def eqTwo' : RawEqn :=
  eqn (ex "VarZ" (ex "VarZ'" (.and int [f (.and int [Z, eqI Z X]), g (.and int [Z', eqI Z' (f X)])])))
/-- A binder of the argument's name: renamed, with the occurrences it binds. -/
def eqArg : RawEqn := eqn (f (ex "VarX" (.and int [X, eqI X (.dv int "0")])))
def eqArg' : RawEqn := eqn (ex "VarX'" (f (.and int [X', eqI X' (.dv int "0")])))
/-- A binder inside a binder of the same name: the inner one is renamed. -/
def eqShadow : RawEqn := eqn (ex "VarZ" (.and int [Z, f (ex "VarZ" (.and int [Z, eqI Z X]))]))
def eqShadow' : RawEqn := eqn (ex "VarZ" (ex "VarZ'" (.and int [Z, f (.and int [Z', eqI Z' X])])))
/-- A binder under `\not` and a binder in a predicate conjunct stay where they are. -/
def eqNot : RawEqn := eqn (f (.not int (ex "VarZ" Z)))
def eqPredConj : RawEqn := eqn (.and int [f X, ex "VarZ" (eqI Z X)])
/-- No binder. -/
def eqNone : RawEqn := eqn (.and int [f X, g X])

/-- Whether `hoistExists` gives the right side of `e'`, or the refusal. -/
def showHoist (what : String) (val : Kore.KSort → Bool) (e e' : RawEqn) : IO Unit :=
  match hoistExists val int e with
  | .error f => IO.println s!"{what}: refused {repr f.reason} ({f.detail})"
  | .ok r => IO.println s!"{what}: the expected right side {r.rhs == e'.rhs}"

end HandHoist

/--
info: eqApp: the expected right side true
eqConj: the expected right side true
eqAlt: the expected right side true
eqAlt, no sort accepted: refused KCore.Parse.RefusalReason.existentialEquation (VarZ: bound in an alternative of \or at the sort Int, which the test of a value does not accept)
eqTwo: the expected right side true
eqArg: the expected right side true
eqShadow: the expected right side true
eqNot: the expected right side true
eqPredConj: the expected right side true
eqNone: the expected right side true
eqApp:
  [0] vars [X:Int, Z:Int] pats [X] req none prio 50 aside false
      pre ⊤
      rhs sym0(Z) ens none exs [1] post (Z =[Int] sym1(X))
eqConj:
  [0] vars [X:Int, Z:Int] pats [X] req none prio 50 aside false
      pre ⊤
      rhs Z ens none exs [1] post ((Z =[Int] sym1(X)) ∧ (Z ∈[Int] sym0(X)))
eqAlt:
  [0] vars [X:Int, Z:Int, 'Hash'Or0:Int] pats [X] req none prio 50 aside false
      pre ⊤
      rhs 'Hash'Or0 ens none exs [1, 2] post (('Hash'Or0 ∈[Int] X) ∨ (('Hash'Or0 ∈[Int] Z) ∧ (Z =[Int] sym0(X))))
eqTwo:
  [0] vars [X:Int, Z:Int, Z':Int, 'Hash'Cut0:Int] pats [X] req none prio 50 aside false
      pre ⊤
      rhs 'Hash'Cut0 ens none exs [1, 2, 3] post ((Z =[Int] X) ∧ ((Z' =[Int] sym0(X)) ∧ (('Hash'Cut0 ∈[Int] sym0(Z)) ∧ ('Hash'Cut0 ∈[Int] sym1(Z')))))
eqArg:
  [0] vars [X:Int, X':Int] pats [X] req none prio 50 aside false
      pre ⊤
      rhs sym0(X') ens none exs [1] post (X' =[Int] 0)
eqShadow:
  [0] vars [X:Int, Z:Int, Z':Int] pats [X] req none prio 50 aside false
      pre ⊤
      rhs Z ens none exs [1, 2] post ((Z' =[Int] X) ∧ (Z ∈[Int] sym0(Z')))
eqNot: refused KCore.Parse.RefusalReason.manyValuedRightSide (\exists)
eqPredConj: refused KCore.Parse.RefusalReason.manyValuedRightSide (\exists)
-/
#guard_msgs in
open HandHoist HandAnd in
#eval show IO Unit from do
  let all := fun (_ : Kore.KSort) => true
  showHoist "eqApp" (fun _ => false) eqApp eqApp'
  showHoist "eqConj" (fun _ => false) eqConj eqConj'
  showHoist "eqAlt" valInt eqAlt eqAlt'
  showHoist "eqAlt, no sort accepted" (fun _ => false) eqAlt eqAlt'
  showHoist "eqTwo" all eqTwo eqTwo'
  showHoist "eqArg" all eqArg eqArg'
  showHoist "eqShadow" all eqShadow eqShadow'
  showHoist "eqNot" all eqNot eqNot
  showHoist "eqPredConj" all eqPredConj eqPredConj
  showHoist "eqNone" all eqNone eqNone
  let rd := fun (e : RawEqn) => hoistExists valInt int e >>= ceRead N2
  showHand "eqApp" (rd eqApp)
  showHand "eqConj" (rd eqConj)
  showHand "eqAlt" (rd eqAlt)
  showHand "eqTwo" (rd eqTwo)
  showHand "eqArg" (rd eqArg)
  showHand "eqShadow" (rd eqShadow)
  showHand "eqNot" (rd eqNot)
  showHand "eqPredConj" (rd eqPredConj)

/-- `hoistExists` on the equation of `fn` of fixture `n`, with `Semantics.valued` on the definition
built from the patched text as the test of a value (`valuedSort`), then `ceRead`. -/
def runHoist (n fn rs : String) (others : List String := []) : IO Unit := do
  let k ← load n
  let some m := k.modules.getLast? | IO.println s!"{n}: no module"
  let S := scan m.sentences
  match envOf m S with
  | .error f => IO.println s!"{n}: envOf fails {repr f.reason}"
  | .ok E =>
    match Parse.parse (patch (fn :: others) k) with
    | .error r => IO.println s!"{n}: patched text refused {repr r.reason} {r.detail}"
    | .ok d =>
      for e in S.eqs.filter (·.fn == fn) do
        let (bs, _) := peelExists e.rhs
        IO.println s!"{n} {fn}: binders at the top {bs.map (·.var.ident.name)}; an \\exists below {hasExists (peelExists e.rhs).2}"
        match hoistExists (valuedSort E.N d.sem) (KoreAML.srt rs) e with
        | .error f => IO.println s!"  hoistExists: refused {repr f.reason} ({f.detail})"
        | .ok e' =>
          let (bs', body) := peelExists e'.rhs
          IO.println s!"  hoistExists: binders at the top {bs'.map (·.var.ident.name)}; an \\exists below {hasExists body}"
          showHand "  ceRead" (ceRead E.N e')

/--
info: e3-eq-exists-ml-in-or-int Lblf: binders at the top []; an \exists below true
  hoistExists: binders at the top [VarB]; an \exists below false
  ceRead:
  [0] vars [X:Int, B:Int, 'Hash'Or0:Int] pats [X] req none prio 50 aside false
      pre ⊤
      rhs 'Hash'Or0 ens none exs [1, 2] post (('Hash'Or0 ∈[Int] X) ∨ (('Hash'Or0 ∈[Int] B) ∧ (B =[Int] Lbl'UndsPlus'Int'Unds'(X, 1))))
e3-eq-exists-ml-in-or Lblf: binders at the top []; an \exists below true
  hoistExists: binders at the top [VarB]; an \exists below false
  ceRead:
  [0] vars [X:Bool, B:Bool, 'Hash'Or0:Bool] pats [X] req none prio 50 aside false
      pre ⊤
      rhs 'Hash'Or0 ens none exs [1, 2] post (('Hash'Or0 ∈[Bool] X) ∨ (('Hash'Or0 ∈[Bool] B) ∧ (B =[Bool] LblnotBool'Unds'(X))))
e3-eq-exists-ml-under-app Lblf: binders at the top []; an \exists below true
  hoistExists: binders at the top [VarB]; an \exists below false
  ceRead:
  [0] vars [X:Bool, B:Bool] pats [X] req none prio 50 aside false
      pre ⊤
      rhs sym5(B) ens none exs [1] post (B =[Bool] X)
e3-eq-exists-ml-and-right Lblf: binders at the top []; an \exists below true
  hoistExists: binders at the top [VarB]; an \exists below false
  ceRead:
  [0] vars [X:Bool, B:Bool] pats [X] req none prio 50 aside false
      pre ⊤
      rhs B ens none exs [1] post ((B =[Bool] X) ∧ (B ∈[Bool] LblnotBool'Unds'(X)))
-/
#guard_msgs in
#eval show IO Unit from do
  runHoist "e3-eq-exists-ml-in-or-int" "Lblf" "Int"
  runHoist "e3-eq-exists-ml-in-or" "Lblf" "Bool" ["Lblfx"]
  runHoist "e3-eq-exists-ml-under-app" "Lblf" "Bool"
  runHoist "e3-eq-exists-ml-and-right" "Lblf" "Bool"

namespace HandHoist

open HandAnd (int)

/-- **`hoistExists` in the kernel**: each step on a hand-written right side, the renamings, the
binders that stay, and the refusal's reason. -/
theorem hoist_steps :
    let rhs := fun (val : Kore.KSort → Bool) (e : RawEqn) => match hoistExists val int e with
      | .ok r => some r.rhs | .error _ => none
    let reason := fun (val : Kore.KSort → Bool) (e : RawEqn) => match hoistExists val int e with
      | .error f => some f.reason | .ok _ => none
    rhs (fun _ => false) eqApp = some eqApp'.rhs ∧ rhs (fun _ => false) eqConj = some eqConj'.rhs ∧
    rhs valInt eqAlt = some eqAlt'.rhs ∧ reason (fun _ => false) eqAlt = some .existentialEquation ∧
    rhs valInt eqTwo = some eqTwo'.rhs ∧ rhs valInt eqArg = some eqArg'.rhs ∧
    rhs valInt eqShadow = some eqShadow'.rhs ∧ rhs valInt eqNot = some eqNot.rhs ∧
    rhs valInt eqPredConj = some eqPredConj.rhs ∧ rhs valInt eqNone = some eqNone.rhs := by
  decide +kernel

end HandHoist

/-- info: 'ExClauseReader.HandHoist.hoist_steps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms HandHoist.hoist_steps


/-! ## ex-after-hoist: EX's test after the binders are moved to the top (`Parse.exEqn?`)

`exCases` and `clausesBody` test EX's shape on the equation `exEqn?` gives: the binders under
applications and `\and` conjuncts moved to the top (N1, N2; no sort is accepted as having a value,
so a binder in an alternative of `\or` stays and the equation is not EX's). -/

namespace HandExHoist

open KoreAML (ev ap srt evar)

/-- f, g : Bool → Bool, the symbols `nRegSyms + 4` and `nRegSyms + 5` (after the four cell
symbols of `mk`'s semantics); f has its `functional` sentence; Bool has its literals only. -/
def NB : Names :=
  { sorts := []
    syms := ["LblisKCell", "LblisKCellOpt", "Lbl'-LT-'k'-GT-'", "LblnoKCell", "Lblf", "Lblg"]
    keyFns := [(nRegSyms + 4, "Bool"), (nRegSyms + 5, "Bool")]
    fnlSyms := [("Lblf", false)]
    boolLits := true }

def bS : Kore.KSort := srt "Bool"
def Xp : Kore.Pattern := ev "VarX" bS
def Bp : Kore.Pattern := ev "VarB" bS
def exB (body : Kore.Pattern) : Kore.Pattern := .exist bS (evar "VarB" bS) body
def bodyP : Kore.Pattern := .and bS [Bp, .equals bS bS Bp Xp]
def uid : List Kore.AppPattern := [KoreAML.attrStr "UNIQUE'Unds'ID" "u"]
def eqn (rhs : Kore.Pattern) : RawEqn := ⟨"Lblf", [Xp], none, none, rhs, uid, none, false⟩

/-- N1, `f(X) => g(#Exists B:Bool. (B #And {B #Equals X}))` (`e3-eq-exists-ml-under-app`). -/
def eqUA : RawEqn := eqn (ap "Lblg" [exB bodyP])
def eqUA' : RawEqn := eqn (exB (ap "Lblg" [bodyP]))
/-- N2, `f(X) => notBool X #And #Exists B:Bool. (B #And {B #Equals X})`
(`e3-eq-exists-ml-and-right`). -/
def eqAR : RawEqn := eqn (.and bS [ap "LblnotBool'Unds'" [Xp], exB bodyP])
def eqAR' : RawEqn := eqn (exB (.and bS [ap "LblnotBool'Unds'" [Xp], bodyP]))
/-- N3, `f(X) => X #Or #Exists B:Bool. (B #And {B #Equals X})`: the binder in an alternative. -/
def eqOr : RawEqn := eqn (.or bS [Xp, exB bodyP])

/-- **The equation EX's test reads, in the kernel**: N1 and N2 move the binder to the top; a binder
in an alternative of `\or` is not moved (`none`); a binder at the top is the equation itself. -/
theorem exEqn_steps :
    exEqn? NB eqUA = some eqUA' ∧ exEqn? NB eqAR = some eqAR' ∧ exEqn? NB eqOr = none ∧
    exEqn? NB eqUA' = some eqUA' := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> kernel_rfl

/-- **`exCases` holds of N1's and N2's equations, not of N3's.** -/
theorem exCases_steps : exCases NB eqUA = true ∧ exCases NB eqAR = true ∧ exCases NB eqOr = false := by
  refine ⟨?_, ?_, ?_⟩ <;> kernel_rfl

/-- **The reader's clauses of N1's equation are `exRead`'s of the moved one, in the kernel.** -/
theorem wire_ua : (clausesBody NB "" eqUA none).map (·.map (·.1)) =
    (exRead NB eqUA').map (fun x => (x.map (·.1)).getD []) := by kernel_rfl

theorem wire_ar : (clausesBody NB "" eqAR none).map (·.map (·.1)) =
    (exRead NB eqAR').map (fun x => (x.map (·.1)).getD []) := by kernel_rfl

end HandExHoist

/-- The reader on the equation of `fn` in fixture `n`: whether `exEqn?` moves its binder, its
clauses and whether they are `exRead`'s of the moved equation, the sentence's notes, and the
definition built. -/
def runExHoist (n fn : String) : IO Unit := do
  let k ← load n
  let some m := k.modules.getLast? | IO.println s!"{n}: no module"
  let S := scan m.sentences
  match envOf m S with
  | .error f => IO.println s!"{n}: envOf fails {repr f.reason}"
  | .ok E =>
    for e in S.eqs.filter (·.fn == fn) do
      let e' : RawEqn := { e with rhs := dropEmptyAlts e.rhs }
      let moved := (exEqn? E.N e').map fun (x : RawEqn) => (peelExists x.rhs).1.map fun (b : Kore.EVar) => b.var.ident.name
      IO.println s!"{n} {fn}: binders at the top after exEqn? {moved}; exCases {exCases E.N e}"
      match clauses? E.N E.src e none with
      | .error f => IO.println s!"  refused {repr f.reason} ({f.detail})"
      | .ok xs =>
        let ex := match (exEqn? E.N e').map (exRead E.N) with
          | some (.ok (some (cs, _))) => reprStr (xs.map (fun (p : Clause × ClausePres) => p.1)) == reprStr cs
          | _ => false
        IO.println s!"  clauses {xs.length}; exRead's of the moved equation: {ex}"
  let notes := (connReadings k).map fun (_, ns) => ns.map ReadingNote.name
  match Parse.parse k with
  | .error r => IO.println s!"  notes {notes}; refused {repr r.reason} ({r.detail})"
  | .ok d => IO.println s!"  notes {notes}; read; coreOK {d.sem.coreOK}; readsConfined {d.sem.readsConfined}"

/--
info: e3-eq-exists-ml-under-app Lblf: the hand-written equation is the text's: true
-/
#guard_msgs in
#eval tie "e3-eq-exists-ml-under-app" "Lblf" HandExHoist.eqUA

/--
info: e3-eq-exists-ml-under-app Lblf: binders at the top after exEqn? (some [VarB]); exCases true
  clauses 3; exRead's of the moved equation: true
  notes [[existsAsCases]]; read; coreOK true; readsConfined true
e3-eq-exists-ml-and-right Lblf: binders at the top after exEqn? (some [VarB]); exCases false
  refused KCore.Parse.RefusalReason.patternConnective (\and)
  notes []; refused KCore.Parse.RefusalReason.patternConnective (\and)
e3-eq-exists-ml-in-or Lblf: binders at the top after exEqn? none; exCases false
  refused KCore.Parse.RefusalReason.manyValuedRightSide (\or: the sentence gives the function every element of each side; the text holds no functional sentence of the function, so where the sides differ that is more than one element, which no clause states)
  notes []; refused KCore.Parse.RefusalReason.manyValuedRightSide (\or: the sentence gives the function every element of each side; the text holds no functional sentence of the function, so where the sides differ that is more than one element, which no clause states)
-/
#guard_msgs in
#eval show IO Unit from do
  runExHoist "e3-eq-exists-ml-under-app" "Lblf"
  runExHoist "e3-eq-exists-ml-and-right" "Lblf"
  runExHoist "e3-eq-exists-ml-in-or" "Lblf"

/-! ### The results of N1's reading

f with the reader's clauses of `HandExHoist.eqUA` (`reader_fCls`) and g with the clause
`g(B) => notBool B`, the fixture's: `f(true)` is `false` and `f(false)` is `true`, and nothing else
(`eval_after_hoist`). The clause of the literal b applies where b is X (its premise
`⌈g(b)⌉ ∧ b = X`), and the binder clause's premise `¬∃B:Bool. (⌈g(B)⌉ ∧ B = X)` is false at both
arguments (B := X). -/

namespace HoistEval

open Faithful.UndefRhsWitness (cellSorts cellCtors cellSubsorts)

def Fs : Sym := nRegSyms + 4
def Gs : Sym := nRegSyms + 5
def litT (b : Bool) : Term := .dv Srt.bool (.bool b)
def gT (t : Term) : Term := .app Gs [t]
def clB (rhs : Term) (ens : Option Term) (pre : Cond) : Clause :=
  ⟨[Srt.bool], [.var 0], none, rhs, ens, 50, false, [], pre, .top⟩
def preB (b : Bool) : Cond := .and (.ceil Srt.bool (gT (litT b))) (.equals Srt.bool (litT b) (.var 0))
def bodyC : Cond := .and (.ceil Srt.bool (gT (.var 1))) (.equals Srt.bool (.var 1) (.var 0))
def lastPre : Cond := .not (.ex Srt.bool bodyC)
def fCls : List Clause :=
  [clB (gT (litT true)) none (preB true), clB (gT (litT false)) none (preB false),
   clB (gT (litT true)) (some (litT false)) lastPre]

/-- **The reader's clauses of N1's equation**, in the kernel. -/
theorem reader_fCls : (clausesBody HandExHoist.NB "" HandExHoist.eqUA none).map (·.map (·.1)) = .ok fCls := by
  kernel_rfl

def gFn : Fn := ⟨Gs, [Srt.bool], Srt.bool, [clB (.app boolNot [.var 0]) none .top], true⟩
def fFn : Fn := ⟨Fs, [Srt.bool], Srt.bool, fCls, true⟩

def c : Semantics :=
  { lib := {}
    sortNames := ["KCell", "KCellOpt"]
    symNames := ["LblisKCell", "LblisKCellOpt", "Lbl'-LT-'k'-GT-'", "LblnoKCell", "Lblf", "Lblg"]
    userSorts := cellSorts
    ctors := cellCtors
    fns := [fFn, gFn]
    userSubsorts := cellSubsorts
    pgmSort := Srt.k
    rules := [] }

theorem c_coreOK : c.coreOK = true := by decide +kernel
theorem c_lit : c.litSort Srt.bool = true := by decide +kernel

theorem lookupF : c.lookupFn Fs = some fFn := by rw [Semantics.lookupFn_eq]; rfl
theorem lookupG : c.lookupFn Gs = some gFn := by rw [Semantics.lookupFn_eq]; rfl
theorem kindsG : c.isCtor Gs = false ∧ isHook Gs = false ∧ c.isParam Gs = false ∧ c.isOvl Gs = false := by
  decide +kernel
theorem kindsNot : c.isCtor boolNot = false ∧ isHook boolNot = true ∧ c.isOvl boolNot = false := by
  decide +kernel

/-- The substitution that gives X the value v. -/
def sg (v : GroundTerm) : Subst := [(0, v)]

theorem sg_sorted (x : Bool) : c.WellSorted [Srt.bool] (sg (bool x)) := by
  intro i s hs
  cases i with
  | zero =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hs
    subst hs
    exact ⟨bool x, rfl, sortOf_bool x⟩
  | succ i => simp at hs

theorem sg_sortedAt (x : Bool) (is : List Nat) : c.WellSortedAt [Srt.bool] is (sg (bool x)) :=
  fun i _ s hs => sg_sorted x i s hs

theorem sg_match (v : GroundTerm) : PatVals c (sg v) [.var 0] [v] := .cons (.var rfl) .nil

theorem match0 {σ : Subst} {vs : List GroundTerm} (h : PatVals c σ [.var 0] vs) :
    ∃ v, vs = [v] ∧ σ.lookup 0 = some v := by
  obtain ⟨v, vs', rfl, hv, hs⟩ := PatVals.cons_inv h
  rw [PatVals.nil_inv hs]
  exact ⟨v, rfl, PatVal.var_inv hv⟩

/-- `notBool(X)` is `!y` where X is y, and nothing else. -/
theorem not_iff {σ : Subst} {y : Bool} (hl : σ.lookup 0 = some (bool y)) (w : Option GroundTerm) :
    EvalTerm c σ (.app boolNot [.var 0]) w ↔ w = some (bool !y) := by
  constructor
  · intro h
    cases h with
    | ctor hk _ => exact absurd (kindsNot.1.symm.trans hk) (by simp)
    | hook _ _ hts hh _ =>
      cases hts with
      | cons h1 hs =>
        cases hs; cases h1
        rw [hl] at hh
        exact Option.some.inj ((hh _ rfl).symm.trans (by cases y <;> rfl))
    | param _ hhk _ _ _ => exact absurd (kindsNot.2.1.symm.trans hhk) (by simp)
    | call _ hhk _ _ _ _ => exact absurd (kindsNot.2.1.symm.trans hhk) (by simp)
    | callUndef _ hhk _ _ _ => exact absurd (kindsNot.2.1.symm.trans hhk) (by simp)
    | ovl _ ho _ _ => exact absurd (kindsNot.2.2.symm.trans ho) (by simp)
    | ovlFn _ ho _ _ _ _ _ => exact absurd (kindsNot.2.2.symm.trans ho) (by simp)
  · rintro rfl
    exact .hook kindsNot.1 kindsNot.2.1 (.cons .var .nil)
      (fun vs hvs => by
        rw [hl] at hvs
        obtain rfl := Option.some.inj hvs.symm
        cases y <;> rfl)
      (fun hn => by rw [hl] at hn; exact nomatch hn)

theorem gCl_of {cl : Clause} (h : cl ∈ gFn.clauses) : cl = clB (.app boolNot [.var 0]) none .top := by
  simpa [gFn] using h

/-- **g(y) is `!y`**, and nothing else. -/
theorem evalG_iff (y : Bool) (r : Option GroundTerm) : Eval c Gs [bool y] r ↔ r = some (bool !y) := by
  have hmem : clB (.app boolNot [.var 0]) none .top ∈ gFn.clauses := by simp [gFn]
  constructor
  · intro h
    cases h with
    | clause hfn hcl _ hm _ _ _ _ hr _ _ =>
      obtain rfl := Option.some.inj (lookupG.symm.trans hfn)
      obtain rfl := gCl_of hcl
      obtain ⟨w, hw, hl⟩ := match0 hm
      cases hw
      exact (not_iff hl _).mp hr
    | rest hfn hn =>
      obtain rfl := Option.some.inj (lookupG.symm.trans hfn)
      cases hn _ hmem with
      | intro hf =>
        cases hf (sg (bool y)) (sg_sortedAt y _) (sg_match _) with
        | intro ht _ _ => exact nomatch ht
        | pre hp => cases hp
    | ensFails hfn hcl _ _ _ _ _ _ ht _ _ =>
      obtain rfl := Option.some.inj (lookupG.symm.trans hfn)
      obtain rfl := gCl_of hcl
      exact nomatch ht
    | clauseEx hfn hcl _ _ _ _ _ hne _ _ _ _ =>
      obtain rfl := Option.some.inj (lookupG.symm.trans hfn)
      obtain rfl := gCl_of hcl
      exact absurd rfl hne
    | exNone hfn hcl hne _ _ _ _ _ _ _ =>
      obtain rfl := Option.some.inj (lookupG.symm.trans hfn)
      obtain rfl := gCl_of hcl
      exact absurd rfl hne
  · rintro rfl
    exact .clause lookupG hmem (sg_sorted y) (sg_match _) (fun t ht => nomatch ht) .top
      (fun cl' h _ hlt => by rw [gCl_of h] at hlt; exact absurd hlt (Nat.lt_irrefl _)) rfl
      ((not_iff rfl _).mpr rfl) (fun t ht => nomatch ht) .top

/-- `g(t)`, where t has the one result y, has the one result `!y`. -/
theorem gT_iff {σ : Subst} {t : Term} {y : Bool} (ht : ∀ w, EvalTerm c σ t w ↔ w = some (bool y))
    (w : Option GroundTerm) : EvalTerm c σ (gT t) w ↔ w = some (bool !y) := by
  constructor
  · intro h
    cases h with
    | ctor hk _ => exact absurd (kindsG.1.symm.trans hk) (by simp)
    | hook _ hh _ _ _ => exact absurd (kindsG.2.1.symm.trans hh) (by simp)
    | param _ _ hp _ _ => exact absurd (kindsG.2.2.1.symm.trans hp) (by simp)
    | call _ _ hts hvs hf _ =>
      cases hts with
      | cons h1 hs =>
        cases hs
        rw [(ht _).mp h1] at hvs
        obtain rfl := Option.some.inj hvs.symm
        exact (evalG_iff y _).mp hf
    | callUndef _ _ hts hvs _ =>
      cases hts with
      | cons h1 hs =>
        cases hs
        rw [(ht _).mp h1] at hvs
        exact nomatch hvs
    | ovl _ ho _ _ => exact absurd (kindsG.2.2.2.symm.trans ho) (by simp)
    | ovlFn _ ho _ _ _ _ _ => exact absurd (kindsG.2.2.2.symm.trans ho) (by simp)
  · rintro rfl
    exact .call kindsG.1 kindsG.2.1 (.cons ((ht _).mpr rfl) .nil) rfl ((evalG_iff y _).mpr rfl) kindsG.2.2.1

theorem lit_iff {σ : Subst} (b : Bool) (w : Option GroundTerm) : EvalTerm c σ (litT b) w ↔ w = some (bool b) :=
  ⟨fun h => EvalTerm.dv_inv h, fun h => h ▸ .dv⟩

theorem var_iff {σ : Subst} {i : Nat} {y : Bool} (hl : σ.lookup i = some (bool y)) (w : Option GroundTerm) :
    EvalTerm c σ (.var i) w ↔ w = some (bool y) :=
  ⟨fun h => (EvalTerm.var_inv h).trans hl, fun h => h ▸ hl ▸ .var⟩

/-- Whether b is x. -/
def bEq (b x : Bool) : Bool := sameResult (some (bool b)) (some (bool x))

theorem bEq_iff (b x : Bool) : bEq b x = true ↔ b = x := by cases b <;> cases x <;> decide

/-- The premise of the literal b's clause has the truth value `b = x` where X is x. -/
theorem preB_mk {σ : Subst} {x : Bool} (hl : σ.lookup 0 = some (bool x)) (b : Bool) :
    Holds c 1 σ (preB b) (bEq b x) :=
  Holds.and (Holds.ceil ((gT_iff (lit_iff b) _).mpr rfl)) (Holds.equals ((lit_iff b _).mpr rfl) ((var_iff hl _).mpr rfl))

theorem preB_inv {σ : Subst} {x b r : Bool} (hl : σ.lookup 0 = some (bool x)) (h : Holds c 1 σ (preB b) r) :
    r = bEq b x := by
  cases h with
  | and h1 h2 =>
    cases h1 with
    | ceil e1 =>
      cases h2 with
      | equals e2 e3 =>
        rw [(gT_iff (lit_iff b) _).mp e1, (lit_iff b _).mp e2, (var_iff hl _).mp e3]
        rfl

/-- The binder's body under σ', B the index 1: whether B is x. -/
def gB (x : Bool) (σ' : Subst) : Bool := sameResult (σ'.lookup 1) (some (bool x))

theorem bodyC_mk {σ' : Subst} {x y : Bool} (hl0 : σ'.lookup 0 = some (bool x)) (hl1 : σ'.lookup 1 = some (bool y)) :
    Holds c 2 σ' bodyC (gB x σ') := by
  have h := Holds.and (n := 2) (Holds.ceil (s := Srt.bool) ((gT_iff (var_iff hl1) _).mpr rfl))
    (Holds.equals (s := Srt.bool) ((var_iff hl1 _).mpr rfl) ((var_iff hl0 _).mpr rfl))
  rw [show gB x σ' = sameResult (some (bool y)) (some (bool x)) by simp [gB, hl1]]
  exact h

theorem bodyC_inv {σ' : Subst} {x y r : Bool} (hl0 : σ'.lookup 0 = some (bool x)) (hl1 : σ'.lookup 1 = some (bool y))
    (h : Holds c 2 σ' bodyC r) : r = gB x σ' := by
  cases h with
  | and h1 h2 =>
    cases h1 with
    | ceil e1 =>
      cases h2 with
      | equals e2 e3 =>
        rw [(gT_iff (var_iff hl1) _).mp e1, (var_iff hl1 _).mp e2, (var_iff hl0 _).mp e3]
        simp [gB, hl1]

/-- An extension of σ by B: B is a literal. -/
theorem ext_lit {σ σ' : Subst} (he : Extends c 1 [Srt.bool] σ σ') : ∃ y, σ'.lookup 1 = some (bool y) := by
  obtain ⟨v, hv, hs⟩ := he.2 0 Srt.bool rfl
  obtain ⟨y, rfl⟩ := boolValues c_coreOK c_lit hs
  exact ⟨y, hv⟩

/-- The extension of σ by B := x. -/
def ext (x : Bool) (σ : Subst) : Subst := (1, bool x) :: σ

theorem ext_extends (x : Bool) (σ : Subst) : Extends c 1 [Srt.bool] σ (ext x σ) := by
  refine ⟨fun i hi => ?_, fun j s hs => ?_⟩
  · have : i = 0 := by omega
    subst this; rfl
  · cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hs
      subst hs
      exact ⟨bool x, rfl, sortOf_bool x⟩
    | succ j => simp at hs

theorem gB_ext (x : Bool) (σ : Subst) : gB x (ext x σ) = true := by
  cases x <;> rfl

/-- **The binder clause's premise is false where X is a literal**: B := X gives the body. -/
theorem last_mk {σ : Subst} {x : Bool} (hl : σ.lookup 0 = some (bool x)) : Holds c 1 σ lastPre false := by
  have hex : Holds c 1 σ (.ex Srt.bool bodyC) true := by
    refine Holds.ex (gB x) (fun σ' he => ?_) ?_
    · obtain ⟨y, hy⟩ := ext_lit he
      exact bodyC_mk ((he.1 0 (by omega)).trans hl) hy
    · exact ⟨fun _ => ⟨ext x σ, ext_extends x σ, gB_ext x σ⟩, fun _ => rfl⟩
  exact Holds.not hex

theorem last_inv {σ : Subst} {x r : Bool} (hl : σ.lookup 0 = some (bool x)) (h : Holds c 1 σ lastPre r) :
    r = false := by
  cases h with
  | not h =>
    cases h with
    | ex g hb hr =>
      have hg := bodyC_inv (σ' := ext x σ) (y := x) hl rfl (hb (ext x σ) (ext_extends x σ))
      have h1 : g (ext x σ) = true := by rw [hg]; exact gB_ext x σ
      have := hr.mpr ⟨_, ext_extends x σ, h1⟩
      subst this; rfl

theorem fCl_of {cl : Clause} (h : cl ∈ fFn.clauses) :
    cl = clB (gT (litT true)) none (preB true) ∨ cl = clB (gT (litT false)) none (preB false) ∨
      cl = clB (gT (litT true)) (some (litT false)) lastPre := by
  simpa [fFn, fCls] using h

theorem prio_none {vs : List GroundTerm} {cl : Clause} (hcl : cl ∈ fFn.clauses) :
    ∀ cl' ∈ fFn.clauses, cl'.aside = false → cl'.prio < cl.prio → Fails c vs cl' := by
  intro cl' hcl' _ hlt
  rcases fCl_of hcl with rfl | rfl | rfl <;> rcases fCl_of hcl' with rfl | rfl | rfl <;>
    exact absurd hlt (by decide)

theorem lit_mem (b : Bool) : clB (gT (litT b)) none (preB b) ∈ fFn.clauses := by
  cases b <;> simp [fFn, fCls]

/-- **`f(x)` is `!x`**, by the clause of the literal x: g(x). -/
theorem evalF_mk (x : Bool) : Eval c Fs [bool x] (some (bool !x)) := by
  have hp := preB_mk (σ := sg (bool x)) (x := x) rfl x
  rw [(bEq_iff x x).mpr rfl] at hp
  exact .clause (cl := clB (gT (litT x)) none (preB x)) lookupF (lit_mem _) (sg_sorted x) (sg_match _)
    (fun t ht => nomatch ht) hp (prio_none (lit_mem _)) rfl ((gT_iff (lit_iff x) _).mpr rfl)
    (fun t ht => nomatch ht) .top

/-- **`f(x)` has no other result**: the other literal's clause and the binder clause do not apply. -/
theorem evalF_inv {x : Bool} {r : Option GroundTerm} (h : Eval c Fs [bool x] r) : r = some (bool !x) := by
  cases h with
  | clause hfn hcl _ hm _ hpre _ _ hrhs _ _ =>
    obtain rfl := Option.some.inj (lookupF.symm.trans hfn)
    rcases fCl_of hcl with rfl | rfl | rfl <;> obtain ⟨w, hw, hl⟩ := match0 hm <;> cases hw
    · have hb := (bEq_iff true x).mp (preB_inv hl hpre).symm
      subst hb
      exact (gT_iff (lit_iff true) _).mp hrhs
    · have hb := (bEq_iff false x).mp (preB_inv hl hpre).symm
      subst hb
      exact (gT_iff (lit_iff false) _).mp hrhs
    · exact absurd (last_inv hl hpre) (by simp)
  | rest hfn hnone =>
    obtain rfl := Option.some.inj (lookupF.symm.trans hfn)
    cases hnone _ (lit_mem x) with
    | intro hf =>
      cases hf (sg (bool x)) (sg_sortedAt x _) (sg_match _) with
      | intro ht _ _ => cases ht
      | pre hp =>
        have := (bEq_iff x x).mpr rfl
        rw [← preB_inv (σ := sg (bool x)) rfl hp] at this
        exact absurd this (by simp)
  | ensFails hfn hcl _ hm _ hpre _ _ ht _ _ =>
    obtain rfl := Option.some.inj (lookupF.symm.trans hfn)
    rcases fCl_of hcl with rfl | rfl | rfl <;> obtain ⟨w, hw, hl⟩ := match0 hm <;> cases hw
    · cases ht
    · cases ht
    · exact absurd (last_inv hl hpre) (by simp)
  | clauseEx hfn hcl _ _ _ _ _ hne _ _ _ _ =>
    obtain rfl := Option.some.inj (lookupF.symm.trans hfn)
    rcases fCl_of hcl with rfl | rfl | rfl <;> exact absurd rfl hne
  | exNone hfn hcl hne _ _ _ _ _ _ _ =>
    obtain rfl := Option.some.inj (lookupF.symm.trans hfn)
    rcases fCl_of hcl with rfl | rfl | rfl <;> exact absurd rfl hne

/-- **N1's reading of `e3-eq-exists-ml-under-app`**: `f(true)` is `false` and `f(false)` is `true`,
nothing else, as the sentence gives (`f(x) = g({x}) = {notBool x}`). -/
theorem eval_after_hoist :
    (Eval c Fs [bool true] (some (bool false)) ∧ ∀ r, Eval c Fs [bool true] r → r = some (bool false)) ∧
    (Eval c Fs [bool false] (some (bool true)) ∧ ∀ r, Eval c Fs [bool false] r → r = some (bool true)) :=
  ⟨⟨evalF_mk true, fun _ h => evalF_inv h⟩, ⟨evalF_mk false, fun _ h => evalF_inv h⟩⟩

end HoistEval

/-- info: 'ExClauseReader.HandExHoist.exEqn_steps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms HandExHoist.exEqn_steps
/-- info: 'ExClauseReader.HoistEval.reader_fCls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms HoistEval.reader_fCls
/-- info: 'ExClauseReader.HoistEval.eval_after_hoist' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms HoistEval.eval_after_hoist

end ExClauseReader
