/-
  The reading functions of KcoreSpec/ReadFns.lean for an equation's right side that holds `\or`
  (`Parse.frRead`) or one `\exists` over a Bool variable (`Parse.exRead`), run on the kompiled texts of the fixtures (test/constructs/fixtures; K 7.1.337
  kompile's KORE, from the cache `kfix.py` keeps: `$KCORE_KFIX_CACHE`, else
  `$XDG_CACHE_HOME/kcore-kfix`, else `~/.cache/kcore-kfix`, the text named by the sha256 of the
  fixture's kompile.txt) and on hand-written equations. Run from the package root:
  `lake env lean -j1 test/RhsReader.lean`.

  `Parse.clauseBody` does not call these functions: the reader refuses each of these texts as
  before (their accounts are unchanged). Each clause a function gives is put in the definition the
  landed reader builds from the text with that equation's right side replaced by a plain term, and
  printed with `clauseSorted`, `condOK` of its predicates and `clauseE3`, the conjunct CN-4 §4.9
  gives `clausesPlain` for one clause (`clausesPlain` asks it, and admits a predicate other than
  `\top` only where the clause's conditions need no witness).

  ## fr: `\or` on an equation's right side

  - `e3-ml-eq-rhs-or-total`, `h(X) => f(X) #Or g(X)`, h `total`: three clauses over `[X:Int]`:
    `pre ⌈f(X)⌉`, `rhs f(X)`; `pre ⌈g(X)⌉`, `rhs g(X)`; `pre ¬⌈f(X)⌉ ∧ ¬⌈g(X)⌉`, `rhs f(X)`,
    `ens false`.
  - `e3-ml-eq-rhs-or`, the same with h not `total` (the text has no `functional` sentence of h):
    refused `manyValuedRightSide`.
  - `e3-ml-eq-rhs-or-many`, `k(_) => 1 #Or … #Or 9`, k `total`: refused `manyValuedRightSide`,
    nine alternatives.
  Hand-written (`Hand`, over the names `N0`):
  - `eqD`, `k(X) => (X -Int Z) #Or X`: refused `manyValuedRightSide` naming Z, which the arguments
    do not bind.
  - `eqA`, `h(X) => (f(X) #And {X >Int 0 #Equals true}) #Or g(X)`: the first clause's `pre` is
    `⌈f(X)⌉ ∧ (X >Int 0 = true)`.
  - `eqE`, `h(X) => f(X) #Or g(X) ensures X >Int 0`: each alternative's `pre` holds the `ensures`.
  - `eqOne`, `h(X) => f(X) #Or g(#Bottom)`: one alternative is left; `frRead` gives `none`.
  - `eqPlain`, `h(X) => f(X)`: no `\or`; `none`.
  Alternatives that are `\bottom` (`Parse.dropEmptyAlts`), each right side put in the equation of
  h of `e3-ml-eq-rhs-or-total` (h with its `functional` sentence) and of `e3-ml-eq-rhs-or` (h
  without):
  - `orEmpty`, `g(#Bottom) #Or X`: `dropEmptyAlts` gives `X`; `frRead` gives `none` in both texts
    (test/ExClauseReader.lean prints the clause `Parse.ceRead` gives for that side, `rhs X`).
  - `bothEmpty`, `(f(X) #And #Bottom) #Or (g(X) #And #Bottom)`: `\bottom`, the side is empty; `none`.
  - `orBot`, `f(X) #Or #Bottom`: `f(X)`, and `hoist` gives what it gives of the text; `none`.
  Kernel-checked (`kernel_rfl`, `decide +kernel`): `frRead` on the fixture's equation written by
  hand (`Hand.eqH`; `tie` checks that it is the scanned text's equation) and on the hand-written
  equations; `frClauses` with an `ensures`, and its length; `dropEmptyAlts` on the three right
  sides, and `frRead`'s `none` on the first for a function without its `functional` sentence.

  ## ex: `\exists` over one Bool variable (`existsAsCases`)

  - `e3-eq-exists-bool-ml`, `f(X) => #Exists B:Bool. (B #And {B #Equals notBool X})`, f `total`:
    three clauses over `[X:Bool]`: `pre ⌈true⌉ ∧ (true = notBool(X))`, `rhs true`; the same at
    `false`; the negations, `rhs true`, `ens false`.
  - `e3-eq-exists-bool-ml-loop`, `f() => #Exists B:Bool. pick(B)`, f `total`: `pre ⌈pick(true)⌉`,
    `rhs pick(true)`; the same at `false`; the negations.
  - `e3-eq-exists-partial-ml` (f not `total`) and `e3-eq-exists-ml-under-app` (the binder under an
    application): `none`.
  Hand-written (`HandEx`, over the names `N1`):
  - `eqY`, the predicate `{B #Equals notBool Y}`, Y in no pattern: refused `manyValuedRightSide`
    naming Y; `eqYreq`, the same with `requires Y`: refused likewise (the `requires` holds Y, the
    arguments do not bind it).
  - `eqEns`, with `ensures X`: each instance's `pre` holds the predicate, then the `ensures`.
  - `eqFloor`, a predicate `condOf` does not read (`\floor`): refused `patternConnective`.
  - `eqTwo`, `#Exists B. (B #And notBool X)`, a conjunction of two terms, B one of them: read as B
    with the predicate `B ∈ notBool(X)`, so each instance's `pre` holds `b ∈ notBool(X)`.
  - `eqUnderAnd`, `#Exists B. notBool(B #And X)`, the conjunction under an application: the
    alternative is `notBool(b)`, `pre` holds `b ∈ X`.
  - `eqFresh`, `#Exists B. notBool(notBool(B) #And X)`, a conjunction without B: `none` (B alone
    does not stand for it); `Parse.ceRead` reads it as one clause with a further variable.
  - `eqPredAnd`, a conjunction of two terms in a predicate's operand: refused `patternConnective`
    (`exRead_noAs`): `term` would read `\and(p, X)` as the left-side pattern `p #as X`.
  The three, each as the right side of f's equation in `e3-eq-exists-bool-ml`'s text, are printed
  in that definition.
  Kernel-checked: `exRead` on the fixture's equation written by hand (`HandEx.eqB`, tied to the
  text), on `eqTwo` and `eqUnderAnd`, `none` and the refusals' reasons; `condOf` on the fixture's
  predicate.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

open KCore KCore.Parse

namespace RhsReader

/-! ## The harness -/

/-- CN-4 §4.9's final text of what `clausesPlain` asks of one clause (test/EqRhsOr.lean). -/
def clauseE3 (c : Semantics) (cl : Clause) : Bool :=
  cl.exs.isEmpty && cl.post.isTop &&
  (!cl.reqOpen || cl.reqClosed || cl.openCondVars.all fun i => (cl.vars[i]?.map c.confined).getD false)

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

/-- One clause, in the semantics `c` where `f` has it. -/
def showClause (c : Semantics) (f : Fn) (i : Nat) (cl : Clause) (vs : List KoreAML.Var) : IO Unit := do
  showFields c.symName c.sortName i cl vs
  IO.println s!"      clauseSorted {c.clauseSorted f (c.fns.map Fn.sig) cl}; condOK pre {c.condOK cl.vars cl.pre}, post {c.condOK cl.vars cl.post}; clauseE3 {clauseE3 c cl}"

/-- `read` on the equations of the functions `fns` of fixture `n` (each as `edit` gives it: a
hand-written right side in the text's equation): a refusal, `none`, or the clauses, put in the
definition built from the patched text. -/
def run (n : String) (fns : List String) (read : Names → RawEqn → Rd (Option (List Clause × List KoreAML.Var)))
    (edit : RawEqn → RawEqn := id) : IO Unit := do
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
          match read E.N (edit e) with
          | .error f => stop := true; IO.println s!"{n} {fnName}: refused {repr f.reason} ({f.detail})"
          | .ok none => stop := true; IO.println s!"{n} {fnName}: none"
          | .ok (some (cs, vs)) => cls := cls ++ cs.map (·, vs)
        if stop then continue
        let some f := c0.fns.find? (c0.symName ·.label == fnName) | IO.println s!"{n}: no function {fnName}"
        let f' := { f with clauses := cls.map (·.1) }
        let c := { c0 with fns := c0.fns.map fun g => if g.label == f.label then f' else g }
        IO.println s!"{n} {fnName}: functional sentence {eqnFnl E.N ⟨fnName, [], none, none, .top (KoreAML.srt "K"), [], none, false⟩}; clauses {cls.length}"
        for ((cl, vs), i) in cls.zipIdx do showClause c f' i cl vs
        let rest := c.subsortsOK && c.fns.all (fun f => f.clauses.all (c.clauseSorted f (c.fns.map Fn.sig))) &&
          c.rules.all c.ruleSorted && c.rulesPlain && c.paramsPlain
        IO.println s!"  sortedOK but clausesPlain {rest}; clausesPlain {c.clausesPlain}; every clause clauseE3 {c.fns.all fun f => f.clauses.all (clauseE3 c)}; readsConfined {c.readsConfined}; litSort Bool {c.litSort Srt.bool}"

/-- The result of a reading function on a hand-written equation, a symbol and a sort printed by
number. -/
def showHand (what : String) (r : Rd (Option (List Clause × List KoreAML.Var))) : IO Unit :=
  match r with
  | .error f => IO.println s!"{what}: refused {repr f.reason} ({f.detail})"
  | .ok none => IO.println s!"{what}: none"
  | .ok (some (cs, vs)) => do
    IO.println s!"{what}: clauses {cs.length}"
    for (cl, i) in cs.zipIdx do showFields (fun f => regSymNames.getD f s!"sym{f - nRegSyms}") (fun s => regSortNames.getD s s!"sort{s - nRegSorts}") i cl vs

/-! ## fr -/

/--
info: e3-ml-eq-rhs-or-total Lblh: functional sentence true; clauses 3
  [0] vars [X:Int] pats [X] req none prio 50 aside false
      pre ⌈Lblf(X)⌉:Int
      rhs Lblf(X) ens none exs [] post ⊤
      clauseSorted true; condOK pre true, post true; clauseE3 true
  [1] vars [X:Int] pats [X] req none prio 50 aside false
      pre ⌈Lblg(X)⌉:Int
      rhs Lblg(X) ens none exs [] post ⊤
      clauseSorted true; condOK pre true, post true; clauseE3 true
  [2] vars [X:Int] pats [X] req none prio 50 aside false
      pre (¬⌈Lblf(X)⌉:Int ∧ ¬⌈Lblg(X)⌉:Int)
      rhs Lblf(X) ens (some false) exs [] post ⊤
      clauseSorted true; condOK pre true, post true; clauseE3 true
  sortedOK but clausesPlain true; clausesPlain true; every clause clauseE3 true; readsConfined false; litSort Bool true
e3-ml-eq-rhs-or Lblh: refused KCore.Parse.RefusalReason.manyValuedRightSide (\or: the sentence gives the function every element of each side; the text holds no functional sentence of the function, so where the sides differ that is more than one element, which no clause states)
e3-ml-eq-rhs-or-many Lblk: refused KCore.Parse.RefusalReason.manyValuedRightSide (\or: 9 alternatives, more than 8)
-/
#guard_msgs in
#eval show IO Unit from do
  run "e3-ml-eq-rhs-or-total" ["Lblh"] frRead
  run "e3-ml-eq-rhs-or" ["Lblh"] frRead
  run "e3-ml-eq-rhs-or-many" ["Lblk"] frRead

namespace Hand

open KoreAML (ev ap srt)

/-- The names of test/EqRhsOr.lean's semantics, with k: f, g, h, k are the symbols `nRegSyms + 4`
to `nRegSyms + 7`; h and k have their `functional` sentences. -/
def N0 : Names :=
  { sorts := ["KCell", "KCellOpt"]
    syms := ["LblisKCell", "LblisKCellOpt", "Lbl'-LT-'k'-GT-'", "LblnoKCell", "Lblf", "Lblg", "Lblh", "Lblk"]
    keyFns := [(nRegSyms + 4, "Int"), (nRegSyms + 5, "Int"), (nRegSyms + 6, "Int"), (nRegSyms + 7, "Int")]
    fnlSyms := [("Lblh", false), ("Lblk", false)] }

def F : Sym := nRegSyms + 4
def G : Sym := nRegSyms + 5

def X : Kore.Pattern := ev "VarX" (srt "Int")
def Z : Kore.Pattern := ev "VarZ" (srt "Int")
def fX : Kore.Pattern := ap "Lblf" [X]
def gX : Kore.Pattern := ap "Lblg" [X]
/-- `{B #Equals true}` at Int. -/
def isTrueP (b : Kore.Pattern) : Kore.Pattern := .equals (srt "Bool") (srt "Int") b (.dv (srt "Bool") "true")
def gt0 : Kore.Pattern := ap "Lbl'Unds-GT-'Int'Unds'" [X, .dv (srt "Int") "0"]

def eqn (fn : String) (rhs : Kore.Pattern) (ens : Option Kore.Pattern := none) : RawEqn :=
  ⟨fn, [X], none, none, rhs, [], ens, false⟩

/-- `h(X) => f(X) #Or g(X)`: the equation of `e3-ml-eq-rhs-or-total` (`tie`). -/
def eqH : RawEqn := eqn "Lblh" (.or (srt "Int") [fX, gX])
/-- `k(X) => (X -Int Z) #Or X`. -/
def eqD : RawEqn := eqn "Lblk" (.or (srt "Int") [ap "Lbl'Unds'-Int'Unds'" [X, Z], X])
/-- `h(X) => (f(X) #And {X >Int 0 #Equals true}) #Or g(X)`. -/
def eqA : RawEqn := eqn "Lblh" (.or (srt "Int") [.and (srt "Int") [fX, isTrueP gt0], gX])
/-- `h(X) => f(X) #Or g(X) ensures X >Int 0`. -/
def eqE : RawEqn := eqn "Lblh" (.or (srt "Int") [fX, gX]) (some gt0)
/-- `h(X) => f(X) #Or g(#Bottom)`. -/
def eqOne : RawEqn := eqn "Lblh" (.or (srt "Int") [fX, ap "Lblg" [.bottom (srt "Int")]])
/-- `h(X) => f(X)`. -/
def eqPlain : RawEqn := eqn "Lblh" fX
/-- `f(X) => f(X) #Or g(X)`: f has no `functional` sentence among `N0`'s. -/
def eqNF : RawEqn := eqn "Lblf" (.or (srt "Int") [fX, gX])
def bot : Kore.Pattern := .bottom (srt "Int")
/-- `g(#Bottom) #Or X`. -/
def orEmpty : Kore.Pattern := .or (srt "Int") [ap "Lblg" [bot], X]
/-- `(f(X) #And #Bottom) #Or (g(X) #And #Bottom)`. -/
def bothEmpty : Kore.Pattern := .or (srt "Int") [.and (srt "Int") [fX, bot], .and (srt "Int") [gX, bot]]
/-- `f(X) #Or #Bottom`. -/
def orBot : Kore.Pattern := .or (srt "Int") [fX, bot]
/-- `f(X) => g(#Bottom) #Or X`: f has no `functional` sentence among `N0`'s. -/
def eqOneNF : RawEqn := eqn "Lblf" orEmpty

end Hand

/-- The equation of h in the scanned text of `e3-ml-eq-rhs-or-total` is `Hand.eqH` (its
attributes apart). -/
def tie (n fn : String) (e0 : RawEqn) : IO Unit := do
  let k ← load n
  let some m := k.modules.getLast? | IO.println s!"{n}: no module"
  match (scan m.sentences).eqs.filter (·.fn == fn) with
  | [e] => IO.println s!"{n} {fn}: the hand-written equation is the text's: {e.pats == e0.pats && e.req == e0.req && e.competitors == e0.competitors && e.rhs == e0.rhs && e.ens == e0.ens && e.dom == e0.dom}"
  | es => IO.println s!"{n} {fn}: {es.length} equations"

/--
info: e3-ml-eq-rhs-or-total Lblh: the hand-written equation is the text's: true
-/
#guard_msgs in
#eval tie "e3-ml-eq-rhs-or-total" "Lblh" Hand.eqH

/--
info: eqH: clauses 3
  [0] vars [X:Int] pats [X] req none prio 50 aside false
      pre ⌈sym4(X)⌉:Int
      rhs sym4(X) ens none exs [] post ⊤
  [1] vars [X:Int] pats [X] req none prio 50 aside false
      pre ⌈sym5(X)⌉:Int
      rhs sym5(X) ens none exs [] post ⊤
  [2] vars [X:Int] pats [X] req none prio 50 aside false
      pre (¬⌈sym4(X)⌉:Int ∧ ¬⌈sym5(X)⌉:Int)
      rhs sym4(X) ens (some false) exs [] post ⊤
eqD: refused KCore.Parse.RefusalReason.manyValuedRightSide (\or: VarZ: in an alternative or the ensures, not bound by the arguments)
eqA: clauses 3
  [0] vars [X:Int] pats [X] req none prio 50 aside false
      pre (⌈sym4(X)⌉:Int ∧ (Lbl'Unds-GT-'Int'Unds'(X, 0) =[Bool] true))
      rhs sym4(X) ens none exs [] post ⊤
  [1] vars [X:Int] pats [X] req none prio 50 aside false
      pre ⌈sym5(X)⌉:Int
      rhs sym5(X) ens none exs [] post ⊤
  [2] vars [X:Int] pats [X] req none prio 50 aside false
      pre (¬(⌈sym4(X)⌉:Int ∧ (Lbl'Unds-GT-'Int'Unds'(X, 0) =[Bool] true)) ∧ ¬⌈sym5(X)⌉:Int)
      rhs sym4(X) ens (some false) exs [] post ⊤
eqE: clauses 3
  [0] vars [X:Int] pats [X] req none prio 50 aside false
      pre (⌈sym4(X)⌉:Int ∧ (Lbl'Unds-GT-'Int'Unds'(X, 0) =[Bool] true))
      rhs sym4(X) ens none exs [] post ⊤
  [1] vars [X:Int] pats [X] req none prio 50 aside false
      pre (⌈sym5(X)⌉:Int ∧ (Lbl'Unds-GT-'Int'Unds'(X, 0) =[Bool] true))
      rhs sym5(X) ens none exs [] post ⊤
  [2] vars [X:Int] pats [X] req none prio 50 aside false
      pre (¬(⌈sym4(X)⌉:Int ∧ (Lbl'Unds-GT-'Int'Unds'(X, 0) =[Bool] true)) ∧ ¬(⌈sym5(X)⌉:Int ∧ (Lbl'Unds-GT-'Int'Unds'(X, 0) =[Bool] true)))
      rhs sym4(X) ens (some false) exs [] post ⊤
eqOne: none
eqPlain: none
eqNF: refused KCore.Parse.RefusalReason.manyValuedRightSide (\or: the sentence gives the function every element of each side; the text holds no functional sentence of the function, so where the sides differ that is more than one element, which no clause states)
-/
#guard_msgs in
open Hand in
#eval show IO Unit from do
  showHand "eqH" (frRead N0 eqH)
  showHand "eqD" (frRead N0 eqD)
  showHand "eqA" (frRead N0 eqA)
  showHand "eqE" (frRead N0 eqE)
  showHand "eqOne" (frRead N0 eqOne)
  showHand "eqPlain" (frRead N0 eqPlain)
  showHand "eqNF" (frRead N0 eqNF)

/--
info: e3-ml-eq-rhs-or-total Lblh: none
e3-ml-eq-rhs-or-total Lblh: none
e3-ml-eq-rhs-or-total Lblh: none
e3-ml-eq-rhs-or Lblh: none
e3-ml-eq-rhs-or Lblh: none
e3-ml-eq-rhs-or Lblh: none
eqOneNF: none
-/
#guard_msgs in
open Hand in
#eval show IO Unit from do
  for n in ["e3-ml-eq-rhs-or-total", "e3-ml-eq-rhs-or"] do
    for r in [orEmpty, bothEmpty, orBot] do
      run n ["Lblh"] frRead (fun e => { e with rhs := r })
  showHand "eqOneNF" (frRead N0 eqOneNF)

/-! ## Kernel-checked -/

namespace Hand

def fT : Term := .app F [.var 0]
def gT : Term := .app G [.var 0]
def gt0T : Term := .app (regSymNames.idxOf "Lbl'Unds-GT-'Int'Unds'") [.var 0, .dv Srt.int (.int 0)]

/-- A clause of h over `[X:Int]`. -/
def cl (rhs : Term) (ens : Option Term) (pre : Cond) : Clause :=
  { vars := [Srt.int], pats := [.var 0], req := none, rhs, ens, prio := 50, aside := false, pre }

/-- **`frRead` on the fixture's equation, in the kernel**: the three clauses of
`h(X) => f(X) #Or g(X)` and the variables. -/
theorem frRead_eqH : frRead N0 eqH = .ok (some
    ([cl fT none (.ceil Srt.int fT), cl gT none (.ceil Srt.int gT),
      cl fT (some (boolT false)) (.and (.not (.ceil Srt.int fT)) (.not (.ceil Srt.int gT)))],
     [⟨"X", "Int"⟩])) := by
  kernel_rfl

/-- An alternative's own `{B #Equals true}` is a conjunct of its `pre`. -/
theorem frRead_eqA : frRead N0 eqA = .ok (some
    ([cl fT none (.and (.ceil Srt.int fT) (isTrueC gt0T)), cl gT none (.ceil Srt.int gT),
      cl fT (some (boolT false))
        (.and (.not (.and (.ceil Srt.int fT) (isTrueC gt0T))) (.not (.ceil Srt.int gT)))],
     [⟨"X", "Int"⟩])) := by
  kernel_rfl

/-- The equation's `ensures` is a conjunct of each alternative's `pre`. -/
theorem frRead_eqE : frRead N0 eqE = .ok (some
    ([cl fT none (.and (.ceil Srt.int fT) (isTrueC gt0T)), cl gT none (.and (.ceil Srt.int gT) (isTrueC gt0T)),
      cl fT (some (boolT false))
        (.and (.not (.and (.ceil Srt.int fT) (isTrueC gt0T))) (.not (.and (.ceil Srt.int gT) (isTrueC gt0T))))],
     [⟨"X", "Int"⟩])) := by
  kernel_rfl

/-- Fewer than two alternatives that are not empty, and no `\or`: not this function's. -/
theorem frRead_none : frRead N0 eqOne = .ok none ∧ frRead N0 eqPlain = .ok none := by
  constructor <;> kernel_rfl

/-- `dropEmptyAlts`: the alternative left; `\bottom` where none is, an empty side for `hoist`;
and of `t #Or #Bottom` the side `hoist` gives of the text. -/
theorem dropEmptyAlts_hand :
    dropEmptyAlts orEmpty = X ∧ dropEmptyAlts bothEmpty = bot ∧ (hoist (dropEmptyAlts bothEmpty)).2.2 = true ∧
    dropEmptyAlts orBot = fX ∧ (hoist (dropEmptyAlts orBot)).1 = (hoist orBot).1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> kernel_rfl

/-- One alternative left: not this function's, with the `functional` sentence (`eqOne`) or
without (`eqOneNF`). -/
theorem frRead_oneLeft : frRead N0 eqOneNF = .ok none ∧ frRead N0 (eqn "Lblh" orEmpty) = .ok none := by
  constructor <;> kernel_rfl

/-- The refusals' reasons: a variable the arguments do not bind, and no `functional` sentence. -/
theorem frRead_refused :
    (match frRead N0 eqD with | .error f => decide (f.reason = .manyValuedRightSide) | .ok _ => false) = true ∧
    (match frRead N0 eqNF with | .error f => decide (f.reason = .manyValuedRightSide) | .ok _ => false) = true := by
  decide +kernel

/-- `frClauses` with an `ensures` E: each alternative's `pre` is `⌈aₖ⌉ ∧ (E = true)`. -/
theorem frClauses_ens (E : Term) :
    (frClauses Srt.int [Srt.int] [.var 0] none 50 false [(fT, [isTrueC E]), (gT, [isTrueC E])]).map (·.pre) =
      [.and (.ceil Srt.int fT) (isTrueC E), .and (.ceil Srt.int gT) (isTrueC E),
       .and (.not (.and (.ceil Srt.int fT) (isTrueC E))) (.not (.and (.ceil Srt.int gT) (isTrueC E)))] := rfl

/-- n alternatives give n + 1 clauses. -/
theorem frClauses_length (s : Srt) (vars : List Srt) (pats : List Term) (req : Option Term) (prio : Nat)
    (aside : Bool) (alts : List (Term × List Cond)) :
    (frClauses s vars pats req prio aside alts).length = alts.length + 1 := by
  simp [frClauses]

end Hand

/-- info: 'RhsReader.Hand.frRead_eqH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Hand.frRead_eqH
/-- info: 'RhsReader.Hand.frRead_eqA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Hand.frRead_eqA
/-- info: 'RhsReader.Hand.frRead_eqE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Hand.frRead_eqE
/-- info: 'RhsReader.Hand.frRead_none' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Hand.frRead_none
/-- info: 'RhsReader.Hand.frRead_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Hand.frRead_refused
/-- info: 'RhsReader.Hand.dropEmptyAlts_hand' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Hand.dropEmptyAlts_hand
/-- info: 'RhsReader.Hand.frRead_oneLeft' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Hand.frRead_oneLeft

/-! Opaque constants the reading functions reach (test/OpaqueAudit.lean's walk): the kernel
cannot unfold one. `String.Internal.append` is reached through the details of refusals only, as
for `Parse.parse` (test/OpaqueAudit.lean). -/

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

/-- info: KCore.Parse.frRead: [String.Internal.append] -/
#guard_msgs in
#eval show Lean.MetaM Unit from do
  for root in [``frRead] do IO.println s!"{root}: {← opaqueReach [root]}"

/-! ## ex: `\exists` over one Bool variable, by cases -/

/--
info: e3-eq-exists-bool-ml Lblf: functional sentence true; clauses 3
  [0] vars [X:Bool] pats [X] req none prio 50 aside false
      pre (⌈true⌉:Bool ∧ (true =[Bool] LblnotBool'Unds'(X)))
      rhs true ens none exs [] post ⊤
      clauseSorted true; condOK pre true, post true; clauseE3 true
  [1] vars [X:Bool] pats [X] req none prio 50 aside false
      pre (⌈false⌉:Bool ∧ (false =[Bool] LblnotBool'Unds'(X)))
      rhs false ens none exs [] post ⊤
      clauseSorted true; condOK pre true, post true; clauseE3 true
  [2] vars [X:Bool] pats [X] req none prio 50 aside false
      pre (¬(⌈true⌉:Bool ∧ (true =[Bool] LblnotBool'Unds'(X))) ∧ ¬(⌈false⌉:Bool ∧ (false =[Bool] LblnotBool'Unds'(X))))
      rhs true ens (some false) exs [] post ⊤
      clauseSorted true; condOK pre true, post true; clauseE3 true
  sortedOK but clausesPlain true; clausesPlain true; every clause clauseE3 true; readsConfined false; litSort Bool true
e3-eq-exists-bool-ml-loop Lblf: functional sentence true; clauses 3
  [0] vars [] pats [] req none prio 50 aside false
      pre ⌈Lblpick(true)⌉:Int
      rhs Lblpick(true) ens none exs [] post ⊤
      clauseSorted true; condOK pre true, post true; clauseE3 true
  [1] vars [] pats [] req none prio 50 aside false
      pre ⌈Lblpick(false)⌉:Int
      rhs Lblpick(false) ens none exs [] post ⊤
      clauseSorted true; condOK pre true, post true; clauseE3 true
  [2] vars [] pats [] req none prio 50 aside false
      pre (¬⌈Lblpick(true)⌉:Int ∧ ¬⌈Lblpick(false)⌉:Int)
      rhs Lblpick(true) ens (some false) exs [] post ⊤
      clauseSorted true; condOK pre true, post true; clauseE3 true
  sortedOK but clausesPlain true; clausesPlain true; every clause clauseE3 true; readsConfined false; litSort Bool true
e3-eq-exists-partial-ml Lblf: none
e3-eq-exists-ml-under-app Lblf: none
-/
#guard_msgs in
#eval show IO Unit from do
  run "e3-eq-exists-bool-ml" ["Lblf"] exRead
  run "e3-eq-exists-bool-ml-loop" ["Lblf"] exRead
  run "e3-eq-exists-partial-ml" ["Lblf"] exRead
  run "e3-eq-exists-ml-under-app" ["Lblf"] exRead

namespace HandEx

open KoreAML (ev ap srt evar)

/-- f : Bool → Bool, the symbol `nRegSyms`, with its `functional` sentence. -/
def N1 : Names := { sorts := [], syms := ["Lblf"], keyFns := [(nRegSyms, "Bool")], fnlSyms := [("Lblf", false)] }

def bool : Kore.KSort := srt "Bool"
def X : Kore.Pattern := ev "VarX" bool
def Y : Kore.Pattern := ev "VarY" bool
def B : Kore.Pattern := ev "VarB" bool
def notB (p : Kore.Pattern) : Kore.Pattern := ap "LblnotBool'Unds'" [p]
/-- `#Exists B:Bool. body`. -/
def exB (body : Kore.Pattern) : Kore.Pattern := .exist bool (evar "VarB" bool) body

def eqn (rhs : Kore.Pattern) (req ens : Option Kore.Pattern := none) : RawEqn :=
  ⟨"Lblf", [X], req, none, rhs, [], ens, false⟩

/-- `f(X) => #Exists B:Bool. (B #And {B #Equals notBool X})`: the equation of
`e3-eq-exists-bool-ml` (`tie`). -/
def eqB : RawEqn := eqn (exB (.and bool [B, .equals bool bool B (notB X)]))
/-- The same with `notBool Y`, Y in no pattern. -/
def eqY : RawEqn := eqn (exB (.and bool [B, .equals bool bool B (notB Y)]))
/-- The same with `requires Y`: the `requires` holds Y, the arguments do not. -/
def eqYreq : RawEqn := eqn (exB (.and bool [B, .equals bool bool B (notB Y)])) (some Y)
/-- `f(X) => #Exists B:Bool. (B #And {B #Equals notBool X}) ensures X`. -/
def eqEns : RawEqn := eqn (exB (.and bool [B, .equals bool bool B (notB X)])) none (some X)
/-- A predicate `condOf` does not read: `#Floor(B)`. -/
def eqFloor : RawEqn := eqn (exB (.and bool [B, .floor bool bool B]))
/-- `#Exists B. (B #And notBool X)`: a conjunction of two terms, B one of them. -/
def eqTwo : RawEqn := eqn (exB (.and bool [B, notB X]))
/-- `#Exists B. notBool(B #And X)`: such a conjunction under an application. -/
def eqUnderAnd : RawEqn := eqn (exB (notB (.and bool [B, X])))
/-- `#Exists B. notBool(notBool(B) #And X)`: a conjunction of two terms, B none of them. -/
def eqFresh : RawEqn := eqn (exB (notB (.and bool [notB B, X])))
/-- `#Exists B. (B #And {(notBool X #And B) #Equals X})`: a conjunction in a predicate's operand. -/
def eqPredAnd : RawEqn := eqn (exB (.and bool [B, .equals bool bool (.and bool [notB X, B]) X]))

end HandEx

/--
info: e3-eq-exists-bool-ml Lblf: the hand-written equation is the text's: true
-/
#guard_msgs in
#eval tie "e3-eq-exists-bool-ml" "Lblf" HandEx.eqB

/--
info: eqB: clauses 3
  [0] vars [X:Bool] pats [X] req none prio 50 aside false
      pre (⌈true⌉:Bool ∧ (true =[Bool] LblnotBool'Unds'(X)))
      rhs true ens none exs [] post ⊤
  [1] vars [X:Bool] pats [X] req none prio 50 aside false
      pre (⌈false⌉:Bool ∧ (false =[Bool] LblnotBool'Unds'(X)))
      rhs false ens none exs [] post ⊤
  [2] vars [X:Bool] pats [X] req none prio 50 aside false
      pre (¬(⌈true⌉:Bool ∧ (true =[Bool] LblnotBool'Unds'(X))) ∧ ¬(⌈false⌉:Bool ∧ (false =[Bool] LblnotBool'Unds'(X))))
      rhs true ens (some false) exs [] post ⊤
eqY: refused KCore.Parse.RefusalReason.manyValuedRightSide (\exists: VarY: in an alternative or the ensures, not bound by the arguments)
eqYreq: refused KCore.Parse.RefusalReason.manyValuedRightSide (\exists: VarY: in an alternative or the ensures, not bound by the arguments)
eqEns: clauses 3
  [0] vars [X:Bool] pats [X] req none prio 50 aside false
      pre (⌈true⌉:Bool ∧ ((true =[Bool] LblnotBool'Unds'(X)) ∧ (X =[Bool] true)))
      rhs true ens none exs [] post ⊤
  [1] vars [X:Bool] pats [X] req none prio 50 aside false
      pre (⌈false⌉:Bool ∧ ((false =[Bool] LblnotBool'Unds'(X)) ∧ (X =[Bool] true)))
      rhs false ens none exs [] post ⊤
  [2] vars [X:Bool] pats [X] req none prio 50 aside false
      pre (¬(⌈true⌉:Bool ∧ ((true =[Bool] LblnotBool'Unds'(X)) ∧ (X =[Bool] true))) ∧ ¬(⌈false⌉:Bool ∧ ((false =[Bool] LblnotBool'Unds'(X)) ∧ (X =[Bool] true))))
      rhs true ens (some false) exs [] post ⊤
eqFloor: refused KCore.Parse.RefusalReason.patternConnective (\floor)
eqTwo: clauses 3
  [0] vars [X:Bool] pats [X] req none prio 50 aside false
      pre (⌈true⌉:Bool ∧ (true ∈[Bool] LblnotBool'Unds'(X)))
      rhs true ens none exs [] post ⊤
  [1] vars [X:Bool] pats [X] req none prio 50 aside false
      pre (⌈false⌉:Bool ∧ (false ∈[Bool] LblnotBool'Unds'(X)))
      rhs false ens none exs [] post ⊤
  [2] vars [X:Bool] pats [X] req none prio 50 aside false
      pre (¬(⌈true⌉:Bool ∧ (true ∈[Bool] LblnotBool'Unds'(X))) ∧ ¬(⌈false⌉:Bool ∧ (false ∈[Bool] LblnotBool'Unds'(X))))
      rhs true ens (some false) exs [] post ⊤
eqUnderAnd: clauses 3
  [0] vars [X:Bool] pats [X] req none prio 50 aside false
      pre (⌈LblnotBool'Unds'(true)⌉:Bool ∧ (true ∈[Bool] X))
      rhs LblnotBool'Unds'(true) ens none exs [] post ⊤
  [1] vars [X:Bool] pats [X] req none prio 50 aside false
      pre (⌈LblnotBool'Unds'(false)⌉:Bool ∧ (false ∈[Bool] X))
      rhs LblnotBool'Unds'(false) ens none exs [] post ⊤
  [2] vars [X:Bool] pats [X] req none prio 50 aside false
      pre (¬(⌈LblnotBool'Unds'(true)⌉:Bool ∧ (true ∈[Bool] X)) ∧ ¬(⌈LblnotBool'Unds'(false)⌉:Bool ∧ (false ∈[Bool] X)))
      rhs LblnotBool'Unds'(true) ens (some false) exs [] post ⊤
eqFresh: none
eqFresh by ceRead: clauses 1
  [0] vars [X:Bool, B:Bool, 'Hash'Cut0:Bool] pats [X] req none prio 50 aside false
      pre ⊤
      rhs LblnotBool'Unds'('Hash'Cut0) ens none exs [1, 2] post (('Hash'Cut0 ∈[Bool] LblnotBool'Unds'(B)) ∧ ('Hash'Cut0 ∈[Bool] X))
eqPredAnd: refused KCore.Parse.RefusalReason.patternConnective (\and)
-/
#guard_msgs in
open HandEx in
#eval show IO Unit from do
  showHand "eqB" (exRead N1 eqB)
  showHand "eqY" (exRead N1 eqY)
  showHand "eqYreq" (exRead N1 eqYreq)
  showHand "eqEns" (exRead N1 eqEns)
  showHand "eqFloor" (exRead N1 eqFloor)
  showHand "eqTwo" (exRead N1 eqTwo)
  showHand "eqUnderAnd" (exRead N1 eqUnderAnd)
  showHand "eqFresh" (exRead N1 eqFresh)
  showHand "eqFresh by ceRead" ((fun x => some ([x.1], x.2)) <$> ceRead N1 eqFresh)
  showHand "eqPredAnd" (exRead N1 eqPredAnd)

/--
info: e3-eq-exists-bool-ml Lblf: functional sentence true; clauses 3
  [0] vars [X:Bool] pats [X] req none prio 50 aside false
      pre (⌈true⌉:Bool ∧ (true ∈[Bool] LblnotBool'Unds'(X)))
      rhs true ens none exs [] post ⊤
      clauseSorted true; condOK pre true, post true; clauseE3 true
  [1] vars [X:Bool] pats [X] req none prio 50 aside false
      pre (⌈false⌉:Bool ∧ (false ∈[Bool] LblnotBool'Unds'(X)))
      rhs false ens none exs [] post ⊤
      clauseSorted true; condOK pre true, post true; clauseE3 true
  [2] vars [X:Bool] pats [X] req none prio 50 aside false
      pre (¬(⌈true⌉:Bool ∧ (true ∈[Bool] LblnotBool'Unds'(X))) ∧ ¬(⌈false⌉:Bool ∧ (false ∈[Bool] LblnotBool'Unds'(X))))
      rhs true ens (some false) exs [] post ⊤
      clauseSorted true; condOK pre true, post true; clauseE3 true
  sortedOK but clausesPlain true; clausesPlain true; every clause clauseE3 true; readsConfined false; litSort Bool true
e3-eq-exists-bool-ml Lblf: functional sentence true; clauses 3
  [0] vars [X:Bool] pats [X] req none prio 50 aside false
      pre (⌈LblnotBool'Unds'(true)⌉:Bool ∧ (true ∈[Bool] X))
      rhs LblnotBool'Unds'(true) ens none exs [] post ⊤
      clauseSorted true; condOK pre true, post true; clauseE3 true
  [1] vars [X:Bool] pats [X] req none prio 50 aside false
      pre (⌈LblnotBool'Unds'(false)⌉:Bool ∧ (false ∈[Bool] X))
      rhs LblnotBool'Unds'(false) ens none exs [] post ⊤
      clauseSorted true; condOK pre true, post true; clauseE3 true
  [2] vars [X:Bool] pats [X] req none prio 50 aside false
      pre (¬(⌈LblnotBool'Unds'(true)⌉:Bool ∧ (true ∈[Bool] X)) ∧ ¬(⌈LblnotBool'Unds'(false)⌉:Bool ∧ (false ∈[Bool] X)))
      rhs LblnotBool'Unds'(true) ens (some false) exs [] post ⊤
      clauseSorted true; condOK pre true, post true; clauseE3 true
  sortedOK but clausesPlain true; clausesPlain true; every clause clauseE3 true; readsConfined false; litSort Bool true
e3-eq-exists-bool-ml Lblf: none
-/
#guard_msgs in
open HandEx in
#eval show IO Unit from do
  for e in [eqTwo, eqUnderAnd, eqFresh] do
    run "e3-eq-exists-bool-ml" ["Lblf"] exRead (fun e0 => { e0 with rhs := e.rhs })

namespace HandEx

def notX : Term := .app (regSymNames.idxOf "LblnotBool'Unds'") [.var 0]
/-- `⌈b⌉ ∧ (b = notBool(X))`. -/
def preB (b : Bool) : Cond := .and (.ceil Srt.bool (boolT b)) (.equals Srt.bool (boolT b) notX)

/-- A clause of f over `[X:Bool]`. -/
def cl (rhs : Term) (ens : Option Term) (pre : Cond) : Clause :=
  { vars := [Srt.bool], pats := [.var 0], req := none, rhs, ens, prio := 50, aside := false, pre }

/-- **`exRead` on the fixture's equation, in the kernel**: the clauses of the instances `true`
and `false`, the clause of neither, and the variables. -/
theorem exRead_eqB : exRead N1 eqB = .ok (some
    ([cl (boolT true) none (preB true), cl (boolT false) none (preB false),
      cl (boolT true) (some (boolT false)) (.and (.not (preB true)) (.not (preB false)))],
     [⟨"X", "Bool"⟩])) := by
  kernel_rfl

/-- `true ∈ notBool(X)`, `false ∈ notBool(X)`. -/
def memB (b : Bool) : Cond := .mem Srt.bool (boolT b) notX
/-- `⌈b⌉ ∧ (b ∈ notBool(X))`. -/
def preM (b : Bool) : Cond := .and (.ceil Srt.bool (boolT b)) (memB b)

/-- A conjunction of B and a term is B where the term holds it: the instances' `pre` hold
`b ∈ notBool(X)`. -/
theorem exRead_eqTwo : exRead N1 eqTwo = .ok (some
    ([cl (boolT true) none (preM true), cl (boolT false) none (preM false),
      cl (boolT true) (some (boolT false)) (.and (.not (preM true)) (.not (preM false)))],
     [⟨"X", "Bool"⟩])) := by
  kernel_rfl

def notT (b : Bool) : Term := .app (regSymNames.idxOf "LblnotBool'Unds'") [boolT b]
/-- `⌈notBool(b)⌉ ∧ (b ∈ X)`. -/
def preU (b : Bool) : Cond := .and (.ceil Srt.bool (notT b)) (.mem Srt.bool (boolT b) (.var 0))

/-- The same under an application: the alternative is `notBool(b)`, `pre` holds `b ∈ X`. -/
theorem exRead_eqUnderAnd : exRead N1 eqUnderAnd = .ok (some
    ([cl (notT true) none (preU true), cl (notT false) none (preU false),
      cl (notT true) (some (boolT false)) (.and (.not (preU true)) (.not (preU false)))],
     [⟨"X", "Bool"⟩])) := by
  kernel_rfl

/-- A conjunction of two terms, B none of them: not this function's. -/
theorem exRead_none : exRead N1 eqFresh = .ok none := by kernel_rfl

/-- The refusals' reasons: a variable the arguments do not bind (in the `requires` or not), and a
predicate `condOf` does not read. -/
theorem exRead_refused :
    (match exRead N1 eqY with | .error f => decide (f.reason = .manyValuedRightSide) | .ok _ => false) = true ∧
    (match exRead N1 eqYreq with | .error f => decide (f.reason = .manyValuedRightSide) | .ok _ => false) = true ∧
    (match exRead N1 eqFloor with | .error f => decide (f.reason = .patternConnective) | .ok _ => false) = true := by
  decide +kernel

/-- A conjunction of two terms in a predicate's operand is refused: it is not read as the
left-side pattern `p #as X`. -/
theorem exRead_noAs :
    (match exRead N1 eqPredAnd with | .error f => decide (f.reason = .patternConnective) | .ok _ => false) = true := by
  decide +kernel

/-- `condOf` on the fixture's predicate, in the kernel. -/
theorem condOf_eq : condOf N1 [⟨"X", "Bool"⟩, ⟨"B", "Bool"⟩] (.equals bool bool B (notB X)) =
    .ok (.equals Srt.bool (.var 1) notX, [⟨"X", "Bool"⟩, ⟨"B", "Bool"⟩]) := by
  kernel_rfl

end HandEx

/-- info: 'RhsReader.HandEx.exRead_eqB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms HandEx.exRead_eqB
/-- info: 'RhsReader.HandEx.exRead_none' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms HandEx.exRead_none
/-- info: 'RhsReader.HandEx.exRead_eqTwo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms HandEx.exRead_eqTwo
/-- info: 'RhsReader.HandEx.exRead_eqUnderAnd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms HandEx.exRead_eqUnderAnd
/-- info: 'RhsReader.HandEx.exRead_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms HandEx.exRead_refused
/-- info: 'RhsReader.HandEx.exRead_noAs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms HandEx.exRead_noAs
/-- info: 'RhsReader.HandEx.condOf_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms HandEx.condOf_eq

/--
info: KCore.Parse.exRead: [String.Internal.append]
KCore.Parse.condOf: [String.Internal.append]
-/
#guard_msgs in
#eval show Lean.MetaM Unit from do
  for root in [``exRead, ``condOf] do IO.println s!"{root}: {← opaqueReach [root]}"

end RhsReader
