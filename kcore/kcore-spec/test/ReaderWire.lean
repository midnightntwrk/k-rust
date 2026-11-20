/-
  The reader's clauses of an equation whose right side holds `\or` or `\exists`
  (`Parse.clausesBody`, which `Parse.fnClauses` maps over a function's equations): in order, the
  attribute test, the alternatives that are `\bottom` left out (`dropEmptyAlts`), `Parse.exRead`
  where the text holds the function's `functional` sentence and its declarations give Bool its
  literals only (`Names.boolLits`), CE's arm for an `\or` `frRead` does not read for want of the
  `functional` sentence or past 8 alternatives (`ceOr`), `Parse.frRead`, CE's arm for a right side
  with an `\exists` at the top once binders are moved there (`ceEqn`) or a conjunction of terms
  (`ceShape`), then the one clause of `Parse.clauseBody`. CE's arm is the one clause
  `Parse.ceRead` gives (`ReadingNote.existentialClause`).
  Run from the package root: `lake env lean -j1 test/ReaderWire.lean`.

  On the kompiled texts of the fixtures (test/constructs/fixtures, from the cache `kfix.py` keeps),
  `run` prints the clauses of the function's equation, whether they are those `exRead` or `frRead`
  gives, whether `ceRead` reads the equation too, the sentence's notes and the definition built:
  - `e3-ml-eq-rhs-or-total` (`h(X) => f(X) #Or g(X)`, h `total`): `frRead`'s three clauses,
    `orAsCases`, `coreOK`.
  - `e3-eq-exists-bool-ml` (`f(X) => #Exists B:Bool. (B #And {B #Equals notBool X})`, f `total`)
    and `e3-eq-exists-bool-ml-loop`: `exRead`'s three clauses though `ceRead` reads the equation
    too, `existsAsCases`, `coreOK`, `readsConfined` (the last clause keeps the binder).
  - `e3-ml-eq-rhs-or` (h not `total`): the text holds no `functional` sentence of h, so the
    clause is `ceRead`'s, `existentialClause`, `coreOK`.
  - `e3-ml-eq-rhs-or-empty` (`h(X) => g(#Bottom) #Or X`): one clause, `h(X) = X`, `orBottom`.
  - `e3-ml-eq-rhs-or-bottom` (`f(X) => X #Or #Bottom`): one clause as before.
  - `e3-eq-exists-bool-ml` with a `subsort` axiom of a sort into Bool added (`subBool`): the
    names do not hold `boolLits`, `exRead` is not entered though it reads the equation, and the
    clause is `ceRead`'s.

  Hand-written equations (`Hand`, over the names `N0`), printed and kernel-checked (`kernel_rfl`):
  - `eqH`, `h(X) => f(X) #Or g(X)`: the reader's clauses are `frRead`'s (`wire_fr`); `eqP`,
    `p(X) => #Exists B:Bool. (B #And {B #Equals notBool X})`: they are `exRead`'s (`wire_ex`).
  - `eqPlain`, no connective: `clauseBody`'s clause (`wire_plain`); `eqEmpty`,
    `f(X) => g(#Bottom) #Or X`, f without its `functional` sentence: read as `f(X) => X`
    (`wire_empty`).
  - `eqH2`, `h2(X, Y) => f(Y) #Or g(X)`, paired with a disjunct whose binders are Y then X: the
    clauses are over Y then X and each alternative's `pre` is `⌈rhs⌉` over them (`wire_excl`).
  - `eqOw`, an `[owise]` equation with `\or`: three clauses of priority 200 (`wire_owise`).
  - `eqPc`, `p(c(X)) => #Exists B:Bool. …`, c an overloading symbol with a function overload: the
    pattern's cut adds the variable `Ovl0` and the conjunct `Ovl0 ∈ c(X)` of every `pre`; the last
    clause's binder is numbered past both variables (`wire_cut`).
  - `eqP` over names without `boolLits`: `exRead` is not entered though it reads it, and the
    clause is `ceRead`'s (`wire_ce_noLits`).
  - CE's arm: `f(X) => f(X) #Or g(X)`, f without its `functional` sentence (`wire_ce_or`);
    `h(X) => f(X) #And g(X)` (`wire_ce_and`); nine alternatives (`wire_ce_many`); a binder in an
    alternative, moved to the top where its body equates it with no term and kept in the
    alternative where it does (`wire_ce_hoist`); an empty right side stays the bottom arm's
    (`wire_ce_empty`); `ceCases` on each (`wire_ce_cases`).
  - `clauseExcl` on a clause with an existential variable past the disjunct's: `exs` unchanged,
    `post` renumbered (`excl_exs`).

  The stages of a package (`Stages`), on `f2-examples/mleqort` (the kompiled text of
  `e3-ml-eq-rhs-or-total`), as `kcore gen` writes them for a function whose clauses are checked in
  blocks: `Parse.clauseOf` on h's pair by the kernel (three clauses of one equation, those
  `Parse.frClauses` gives for `f(X)`, `g(X)`: `cls2_frClauses`), `fnClauses` from the block, and the
  productions with that table (`symProdT_eq`).

  `coreOf`'s check of Bool on the built definition (`CoreOfBool`): `coreOf` refuses, with
  `existentialEquation` naming Bool, an equation `exRead` reads (`exCases`) in a definition whose
  `litSort Srt.bool` is false. `exRead` is entered only where the names hold `boolLits`
  (`boolLitsOf`, the conjuncts of `litSort` at Bool that the text's declarations decide), and the
  library's conjuncts are false at Bool (`library_lits`: no module of the library gives Bool a
  subsort, constructor, token or byte sort, nor does a fixed constructor, `#KConfigValue` or a
  builtin collection), so no text reaches the refusal: a value the text gives Bool (`subBoolD`, a
  declared sort Foo below Bool, with the sentences kompile writes for its predicate) makes `boolLits` false and the equation is
  `ceRead`'s, not `exRead`'s. The check is run on the stages of `finish` with the names' bit
  set (`finishWith`): on `e3-eq-exists-bool-ml` with `subBoolD`, refused `existentialEquation`
  (Bool); on the text itself, read with `litSort Srt.bool` true; with the bit unset, `subBoolD`'s
  text is read through `ceRead`, `coreOK` false (`litSort Srt.bool` false: the subsort into Bool).
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

open KCore KCore.Parse

namespace ReaderWire

/-! ## The harness -/

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

def showT (sym : Sym → String) (names : List String) : Term → String
  | .var i => names.getD i s!"#{i}"
  | .app f ts => sym f ++ "(" ++ ", ".intercalate (ts.attach.map fun ⟨t, _⟩ => showT sym names t) ++ ")"
  | .inj _ _ t => "inj(" ++ showT sym names t ++ ")"
  | .as t i => showT sym names t ++ " #as " ++ names.getD i s!"#{i}"
  | .dv _ (.bool b) => s!"{b}"
  | .dv _ (.int i) => s!"{i}"
  | .dv _ l => s!"{repr l}"

/-- A condition; a variable no name of `names` is for (one a binder binds) as `#i`. -/
def showC (sym : Sym → String) (names : List String) : Cond → String
  | .top => "⊤" | .bot => "⊥"
  | .not p => "¬" ++ showC sym names p
  | .and p q => "(" ++ showC sym names p ++ " ∧ " ++ showC sym names q ++ ")"
  | .or p q => "(" ++ showC sym names p ++ " ∨ " ++ showC sym names q ++ ")"
  | .implies p q => "(" ++ showC sym names p ++ " → " ++ showC sym names q ++ ")"
  | .ceil _ t => s!"⌈{showT sym names t}⌉"
  | .equals _ t u => s!"({showT sym names t} = {showT sym names u})"
  | .mem _ t u => s!"({showT sym names t} ∈ {showT sym names u})"
  | .exMatch .. => "exMatch…"
  | .ex _ b => "∃." ++ showC sym names b
  | .all _ b => "∀." ++ showC sym names b

/-- A clause's fields, its variables under the names of its presentation. -/
def showClause (sym : Sym → String) (i : Nat) (x : Clause × ClausePres) : IO Unit := do
  let (cl, cp) := x
  let T := showT sym cp.names
  IO.println s!"  [{i}] vars {cp.names} ({cl.vars.length}) pats {cl.pats.map T} req {cl.req.map T} prio {cl.prio}"
  IO.println s!"      pre {showC sym cp.names cl.pre}"
  IO.println s!"      rhs {T cl.rhs} ens {cl.ens.map T} exs {cl.exs} post {showC sym cp.names cl.post}"

def showRd (sym : Sym → String) (what : String) (r : Rd (List (Clause × ClausePres))) : IO Unit :=
  match r with
  | .error f => IO.println s!"{what}: refused {f.reason.name} ({f.detail.take 120})"
  | .ok xs => do
    IO.println s!"{what}: clauses {xs.length}"
    for (x, i) in xs.zipIdx do showClause sym i x

/-- The text of fixture `n` as the reader reads it: for the function `fn`, the clauses
`clauses?` gives its equations, whether they are those `exRead` and `frRead` give, whether
`ceRead` reads the equation too, the sentence's notes, and the definition built. `edit` changes
the text first. -/
def run (n fn : String) (edit : Kore.Definition → Kore.Definition := id) : IO Unit := do
  let k := edit (← load n)
  let some m := k.modules.getLast? | IO.println s!"{n}: no module"
  let S := scan m.sentences
  match envOf m S with
  | .error f => IO.println s!"{n}: envOf fails {f.reason.name}"
  | .ok E =>
    IO.println s!"{n}: boolLits {E.N.boolLits}"
    for e in S.eqs.filter (·.fn == fn) do
      let r := clauses? E.N E.src e none
      showRd (fun f => if f < nRegSyms then regSymNames.getD f "" else E.N.syms.getD (f - nRegSyms) "") s!"{n} {fn}" r
      let mine : Option String := r.toOption.map fun (xs : List (Clause × ClausePres)) => reprStr (xs.map fun x => x.1)
      let same := fun (x : Rd (Option (List Clause × List KoreAML.Var))) => match x with
        | .ok (some (cs, _)) => if mine.isNone then "not taken" else toString (mine == some (reprStr cs))
        | .ok none => "none"
        | .error f => s!"refused {f.reason.name}"
      IO.println s!"  the reader's clauses are exRead's: {same (exRead E.N e)}; frRead's: {same (frRead E.N e)}; ceRead reads the equation: {(ceRead E.N e).toOption.isSome}"
    let notes := (connReadings k).map fun (_, ns) => ns.map ReadingNote.name
    match Parse.parse k with
    | .error r => IO.println s!"  notes {notes}; refused {r.reason.name} ({r.detail.take 100})"
    | .ok d => IO.println s!"  notes {notes}; read; coreOK {d.sem.coreOK}; readsConfined {d.sem.readsConfined}; litSort Bool {d.sem.litSort Srt.bool}"

/-- The text with a `subsort` axiom of a sort Foo into Bool added to its module: its declarations
then give Bool an element beside its literals. -/
def subBool (k : Kore.Definition) : Kore.Definition :=
  let ax : Kore.Axiom :=
    { sortVars := [], pattern := .top (KoreAML.srt "K"),
      attributes := [⟨⟨⟨"subsort"⟩⟩, [KoreAML.srt "Foo", KoreAML.srt "Bool"], []⟩] }
  match k.modules.reverse with
  | m :: rest => { k with modules := ({ m with sentences := m.sentences ++ [.axiom ax] } :: rest).reverse }
  | [] => k

/--
info: e3-eq-exists-bool-ml: boolLits false
e3-eq-exists-bool-ml Lblf: clauses 1
  [0] vars [X, B] (2) pats [X] req none prio 50
      pre ⊤
      rhs B ens none exs [1] post (B = LblnotBool'Unds'(X))
  the reader's clauses are exRead's: false; frRead's: none; ceRead reads the equation: true
  notes [[existentialClause]]; read; coreOK true; readsConfined true; litSort Bool true
-/
#guard_msgs in
#eval show IO Unit from do
  run "e3-eq-exists-bool-ml" "Lblf" subBool
/--
info: e3-ml-eq-rhs-or-total: boolLits true
e3-ml-eq-rhs-or-total Lblh: clauses 3
  [0] vars [X] (1) pats [X] req none prio 50
      pre ⌈Lblf(X)⌉
      rhs Lblf(X) ens none exs [] post ⊤
  [1] vars [X] (1) pats [X] req none prio 50
      pre ⌈Lblg(X)⌉
      rhs Lblg(X) ens none exs [] post ⊤
  [2] vars [X] (1) pats [X] req none prio 50
      pre (¬⌈Lblf(X)⌉ ∧ ¬⌈Lblg(X)⌉)
      rhs Lblf(X) ens (some false) exs [] post ⊤
  the reader's clauses are exRead's: none; frRead's: true; ceRead reads the equation: true
  notes [[orAsCases]]; read; coreOK true; readsConfined false; litSort Bool true
e3-eq-exists-bool-ml: boolLits true
e3-eq-exists-bool-ml Lblf: clauses 3
  [0] vars [X] (1) pats [X] req none prio 50
      pre (⌈true⌉ ∧ (true = LblnotBool'Unds'(X)))
      rhs true ens none exs [] post ⊤
  [1] vars [X] (1) pats [X] req none prio 50
      pre (⌈false⌉ ∧ (false = LblnotBool'Unds'(X)))
      rhs false ens none exs [] post ⊤
  [2] vars [X] (1) pats [X] req none prio 50
      pre ¬∃.(⌈#1⌉ ∧ (#1 = LblnotBool'Unds'(X)))
      rhs true ens (some false) exs [] post ⊤
  the reader's clauses are exRead's: true; frRead's: none; ceRead reads the equation: true
  notes [[existsAsCases]]; read; coreOK true; readsConfined true; litSort Bool true
e3-eq-exists-bool-ml-loop: boolLits true
e3-eq-exists-bool-ml-loop Lblf: clauses 3
  [0] vars [] (0) pats [] req none prio 50
      pre ⌈Lblpick(true)⌉
      rhs Lblpick(true) ens none exs [] post ⊤
  [1] vars [] (0) pats [] req none prio 50
      pre ⌈Lblpick(false)⌉
      rhs Lblpick(false) ens none exs [] post ⊤
  [2] vars [] (0) pats [] req none prio 50
      pre ¬∃.⌈Lblpick(#0)⌉
      rhs Lblpick(true) ens (some false) exs [] post ⊤
  the reader's clauses are exRead's: true; frRead's: none; ceRead reads the equation: true
  notes [[existsAsCases]]; read; coreOK true; readsConfined true; litSort Bool true
e3-ml-eq-rhs-or: boolLits true
e3-ml-eq-rhs-or Lblh: clauses 1
  [0] vars [X, 'Hash'Or0] (2) pats [X] req none prio 50
      pre ⊤
      rhs 'Hash'Or0 ens none exs [1] post (('Hash'Or0 ∈ Lblf(X)) ∨ ('Hash'Or0 ∈ Lblg(X)))
  the reader's clauses are exRead's: none; frRead's: refused manyValuedRightSide; ceRead reads the equation: true
  notes [[existentialClause]]; read; coreOK true; readsConfined true; litSort Bool true
e3-ml-eq-rhs-or-empty: boolLits true
e3-ml-eq-rhs-or-empty Lblh: clauses 1
  [0] vars [X] (1) pats [X] req none prio 50
      pre ⊤
      rhs X ens none exs [] post ⊤
  the reader's clauses are exRead's: none; frRead's: none; ceRead reads the equation: false
  notes [[orBottom]]; read; coreOK true; readsConfined false; litSort Bool true
e3-ml-eq-rhs-or-bottom: boolLits true
e3-ml-eq-rhs-or-bottom Lblf: clauses 1
  [0] vars [X] (1) pats [X] req none prio 50
      pre ⊤
      rhs X ens none exs [] post ⊤
  the reader's clauses are exRead's: none; frRead's: none; ceRead reads the equation: false
  notes [[orBottom]]; read; coreOK true; readsConfined false; litSort Bool true
-/
#guard_msgs in
#eval show IO Unit from do
  run "e3-ml-eq-rhs-or-total" "Lblh"
  run "e3-eq-exists-bool-ml" "Lblf"
  run "e3-eq-exists-bool-ml-loop" "Lblf"
  run "e3-ml-eq-rhs-or" "Lblh"
  run "e3-ml-eq-rhs-or-empty" "Lblh"
  run "e3-ml-eq-rhs-or-bottom" "Lblf"

/-! ## Hand-written equations -/

namespace Hand

open KoreAML (ev ap srt evar)

/-- f, g, h : Int → Int, h2 : Int × Int → Int, p, c : Bool → Bool, the symbols `nRegSyms` to
`nRegSyms + 5`; h, h2 and p have their `functional` sentences; c is an overloading symbol that
overloads a function (its applications in a pattern are cut); Bool has its literals only. -/
def N0 : Names :=
  { sorts := []
    syms := ["Lblf", "Lblg", "Lblh", "Lblh2", "Lblp", "Lblc"]
    keyFns := [(nRegSyms, "Int"), (nRegSyms + 1, "Int"), (nRegSyms + 2, "Int"), (nRegSyms + 3, "Int"),
               (nRegSyms + 4, "Bool")]
    fnlSyms := [("Lblh", false), ("Lblh2", false), ("Lblp", false)]
    ovlCutSyms := [(nRegSyms + 5, "Bool")]
    boolLits := true }

def sym (f : Sym) : String := if f < nRegSyms then regSymNames.getD f "" else N0.syms.getD (f - nRegSyms) ""

def int : Kore.KSort := srt "Int"
def bool : Kore.KSort := srt "Bool"
def X : Kore.Pattern := ev "VarX" int
def Y : Kore.Pattern := ev "VarY" int
def fOf (t : Kore.Pattern) : Kore.Pattern := ap "Lblf" [t]
def gOf (t : Kore.Pattern) : Kore.Pattern := ap "Lblg" [t]
def uid : List Kore.AppPattern := [KoreAML.attrStr "UNIQUE'Unds'ID" "u"]

/-- `h(X) => f(X) #Or g(X)`. -/
def eqH : RawEqn := ⟨"Lblh", [X], none, none, .or int [fOf X, gOf X], uid, none, false⟩
/-- `h(X) => f(X)`. -/
def eqPlain : RawEqn := ⟨"Lblh", [X], none, none, fOf X, uid, none, false⟩
/-- `f(X) => g(#Bottom) #Or X`: f has no `functional` sentence. -/
def eqEmpty : RawEqn := ⟨"Lblf", [X], none, none, .or int [gOf (.bottom int), X], uid, none, false⟩
/-- `h2(X, Y) => f(Y) #Or g(X)`. -/
def eqH2 : RawEqn := ⟨"Lblh2", [X, Y], none, none, .or int [fOf Y, gOf X], uid, none, false⟩
/-- A disjunct that excludes `eqH2`, its binders Y then X: `∃Y. ∃X. (⊤ ∧ (X0 ∈ X ∧ X1 ∈ Y ∧ ⊤))`. -/
def dH2 : Kore.Pattern :=
  .exist (srt "R") (evar "VarY" int) (.exist (srt "R") (evar "VarX" int)
    (.and (srt "R") [.top (srt "R"),
      .and (srt "R") [.in int (srt "R") (ev "X0" int) X,
        .and (srt "R") [.in int (srt "R") (ev "X1" int) Y, .top (srt "R")]]]))
/-- `h(X) => f(X) #Or g(X) [owise]`: an `[owise]` equation (its exclusion is not read here). -/
def eqOw : RawEqn := { eqH with competitors := some [] }

def XB : Kore.Pattern := ev "VarX" bool
def B : Kore.Pattern := ev "VarB" bool
def notB (t : Kore.Pattern) : Kore.Pattern := ap "LblnotBool'Unds'" [t]
def exBody : Kore.Pattern := .exist bool (evar "VarB" bool) (.and bool [B, .equals bool bool B (notB XB)])
/-- `p(X) => #Exists B:Bool. (B #And {B #Equals notBool X})`. -/
def eqP : RawEqn := ⟨"Lblp", [XB], none, none, exBody, uid, none, false⟩
/-- `p(c(X)) => #Exists B:Bool. (B #And {B #Equals notBool X})`: the pattern applies c. -/
def eqPc : RawEqn := ⟨"Lblp", [ap "Lblc" [XB]], none, none, exBody, uid, none, false⟩

/--
info: eqH: clauses 3
  [0] vars [X] (1) pats [X] req none prio 50
      pre ⌈Lblf(X)⌉
      rhs Lblf(X) ens none exs [] post ⊤
  [1] vars [X] (1) pats [X] req none prio 50
      pre ⌈Lblg(X)⌉
      rhs Lblg(X) ens none exs [] post ⊤
  [2] vars [X] (1) pats [X] req none prio 50
      pre (¬⌈Lblf(X)⌉ ∧ ¬⌈Lblg(X)⌉)
      rhs Lblf(X) ens (some false) exs [] post ⊤
eqPlain: clauses 1
  [0] vars [X] (1) pats [X] req none prio 50
      pre ⊤
      rhs Lblf(X) ens none exs [] post ⊤
eqEmpty: clauses 1
  [0] vars [X] (1) pats [X] req none prio 50
      pre ⊤
      rhs X ens none exs [] post ⊤
eqH2, no exclusion: clauses 3
  [0] vars [X, Y] (2) pats [X, Y] req none prio 50
      pre ⌈Lblf(Y)⌉
      rhs Lblf(Y) ens none exs [] post ⊤
  [1] vars [X, Y] (2) pats [X, Y] req none prio 50
      pre ⌈Lblg(X)⌉
      rhs Lblg(X) ens none exs [] post ⊤
  [2] vars [X, Y] (2) pats [X, Y] req none prio 50
      pre (¬⌈Lblf(Y)⌉ ∧ ¬⌈Lblg(X)⌉)
      rhs Lblf(Y) ens (some false) exs [] post ⊤
eqH2, excluded by dH2: clauses 3
  [0] vars [Y, X] (2) pats [X, Y] req none prio 50
      pre ⌈Lblf(Y)⌉
      rhs Lblf(Y) ens none exs [] post ⊤
  [1] vars [Y, X] (2) pats [X, Y] req none prio 50
      pre ⌈Lblg(X)⌉
      rhs Lblg(X) ens none exs [] post ⊤
  [2] vars [Y, X] (2) pats [X, Y] req none prio 50
      pre (¬⌈Lblf(Y)⌉ ∧ ¬⌈Lblg(X)⌉)
      rhs Lblf(Y) ens (some false) exs [] post ⊤
eqOw: clauses 3
  [0] vars [X] (1) pats [X] req none prio 200
      pre ⌈Lblf(X)⌉
      rhs Lblf(X) ens none exs [] post ⊤
  [1] vars [X] (1) pats [X] req none prio 200
      pre ⌈Lblg(X)⌉
      rhs Lblg(X) ens none exs [] post ⊤
  [2] vars [X] (1) pats [X] req none prio 200
      pre (¬⌈Lblf(X)⌉ ∧ ¬⌈Lblg(X)⌉)
      rhs Lblf(X) ens (some false) exs [] post ⊤
eqP: clauses 3
  [0] vars [X] (1) pats [X] req none prio 50
      pre (⌈true⌉ ∧ (true = LblnotBool'Unds'(X)))
      rhs true ens none exs [] post ⊤
  [1] vars [X] (1) pats [X] req none prio 50
      pre (⌈false⌉ ∧ (false = LblnotBool'Unds'(X)))
      rhs false ens none exs [] post ⊤
  [2] vars [X] (1) pats [X] req none prio 50
      pre ¬∃.(⌈#1⌉ ∧ (#1 = LblnotBool'Unds'(X)))
      rhs true ens (some false) exs [] post ⊤
eqPc: clauses 3
  [0] vars [X, Ovl0] (2) pats [Ovl0] req none prio 50
      pre ((Ovl0 ∈ Lblc(X)) ∧ (⌈true⌉ ∧ (true = LblnotBool'Unds'(X))))
      rhs true ens none exs [] post ⊤
  [1] vars [X, Ovl0] (2) pats [Ovl0] req none prio 50
      pre ((Ovl0 ∈ Lblc(X)) ∧ (⌈false⌉ ∧ (false = LblnotBool'Unds'(X))))
      rhs false ens none exs [] post ⊤
  [2] vars [X, Ovl0] (2) pats [Ovl0] req none prio 50
      pre ((Ovl0 ∈ Lblc(X)) ∧ ¬∃.(⌈#2⌉ ∧ (#2 = LblnotBool'Unds'(X))))
      rhs true ens (some false) exs [] post ⊤
eqP, Bool not its literals: clauses 1
  [0] vars [X, B] (2) pats [X] req none prio 50
      pre ⊤
      rhs B ens none exs [1] post (B = LblnotBool'Unds'(X))
-/
#guard_msgs in
#eval show IO Unit from do
  showRd sym "eqH" (clauses? N0 "" eqH none)
  showRd sym "eqPlain" (clauses? N0 "" eqPlain none)
  showRd sym "eqEmpty" (clauses? N0 "" eqEmpty none)
  showRd sym "eqH2, no exclusion" (clauses? N0 "" eqH2 none)
  showRd sym "eqH2, excluded by dH2" (clauses? N0 "" eqH2 (some dH2))
  showRd sym "eqOw" (clauses? N0 "" eqOw none)
  showRd sym "eqP" (clauses? N0 "" eqP none)
  showRd sym "eqPc" (clauses? N0 "" eqPc none)
  showRd sym "eqP, Bool not its literals" (clauses? { N0 with boolLits := false } "" eqP none)

/-! ### Kernel-checked -/

/-- **`\or`, in the kernel**: the reader's clauses of `eqH` are those `frRead` gives. -/
theorem wire_fr : (clausesBody N0 "" eqH none).map (·.map (·.1)) =
    (frRead N0 eqH).map (fun x => (x.map (·.1)).getD []) := by kernel_rfl

/-- **`\exists B:Bool`, in the kernel**: the reader's clauses of `eqP` are those `exRead` gives. -/
theorem wire_ex : (clausesBody N0 "" eqP none).map (·.map (·.1)) =
    (exRead N0 eqP).map (fun x => (x.map (·.1)).getD []) := by kernel_rfl

/-- An equation without `\or` or `\exists` falls through both: `clauseBody`'s one clause. -/
theorem wire_plain : clausesBody N0 "" eqPlain none = (clauseBody N0 "" eqPlain none).map ([·]) := by kernel_rfl

/-- An alternative that is `\bottom` is left out: `g(#Bottom) #Or X` is read as `X`, of a
function without its `functional` sentence. -/
theorem wire_empty : clausesBody N0 "" eqEmpty none =
    (clauseBody N0 "" { eqEmpty with rhs := X } none).map ([·]) := by kernel_rfl

/-- The clause's `pre` is `⌈rhs⌉`. -/
def preCeilRhs (cl : Clause) : Bool :=
  match cl.pre with
  | .ceil _ t => Term.beq t cl.rhs
  | _ => false

/-- **Paired with an exclusion, in the kernel**: the variables are the disjunct's, Y then X, and
each alternative's `pre` is `⌈rhs⌉` over them: `pre` is renumbered with the right side. Without
the disjunct the alternatives are over X then Y. -/
theorem wire_excl :
    ((clausesBody N0 "" eqH2 (some dH2)).toOption.map fun xs =>
      (xs.map (·.2.names), (xs.take 2).map (·.1.rhs), (xs.take 2).all (preCeilRhs ·.1), xs.length)) =
      some ([["Y", "X"], ["Y", "X"], ["Y", "X"]],
        [.app nRegSyms [.var 0], .app (nRegSyms + 1) [.var 1]], true, 3) ∧
    ((clausesBody N0 "" eqH2 none).toOption.map fun xs =>
      (xs.map (·.2.names), (xs.take 2).map (·.1.rhs), (xs.take 2).all (preCeilRhs ·.1), xs.length)) =
      some ([["X", "Y"], ["X", "Y"], ["X", "Y"]],
        [.app nRegSyms [.var 1], .app (nRegSyms + 1) [.var 0]], true, 3) := by
  constructor <;> kernel_rfl

/-- An `[owise]` equation read by cases: its clauses, each of priority 200. -/
theorem wire_owise : ((clausesBody N0 "" eqOw none).toOption.map fun xs => xs.map (·.1.prio)) =
    some [200, 200, 200] := by kernel_rfl

def notX : Term := .app (regSymNames.idxOf "LblnotBool'Unds'") [.var 0]

/-- **A cut pattern beside the binder, in the kernel**: `p(c(X))` is `p(Ovl0)` with
`Ovl0 ∈ c(X)` a conjunct of every clause's `pre`; the clause has two variables, and the last
clause's binder is the index 2, past both. -/
theorem wire_cut : ((clausesBody N0 "" eqPc none).toOption.map fun xs =>
      (xs.map (·.1.vars.length), xs.map (·.1.pats), (xs.getLast?.map (·.1.pre)))) =
    some ([2, 2, 2], [[.var 1], [.var 1], [.var 1]],
      some (.and (.mem Srt.bool (.var 1) (.app (nRegSyms + 5) [.var 0]))
        (.not (.ex Srt.bool (.and (.ceil Srt.bool (.var 2)) (.equals Srt.bool (.var 2) notX)))))) := by
  kernel_rfl

/-- **Bool with a value beside its literals**: where the names do not hold `boolLits`, `exRead`
is not entered (it would read the equation) and the equation is CE's: its one clause is `ceRead`'s,
the binder an existential variable. -/
theorem wire_ce_noLits :
    (clausesBody { N0 with boolLits := false } "" eqP none).map (·.map (·.1)) =
      (ceRead { N0 with boolLits := false } eqP).map (fun x => [x.1]) ∧
    ((exRead { N0 with boolLits := false } eqP).toOption.join.isSome) = true := by
  constructor <;> kernel_rfl

/-- **`clauseExcl` maps `exs`**: a clause with an existential variable Z (the index 2, past the
disjunct's variables) and `post := Z ∈ f(Y)`, paired with `dH2`: `exs` is `[2]` still, and `post`
is over the reordered variables, `Z ∈ f(#0)`. -/
theorem excl_exs :
    ((clauseExcl N0 "" eqH2 (some dH2) [⟨"X", "Int"⟩, ⟨"Y", "Int"⟩, ⟨"Z", "Int"⟩]
        { vars := [], pats := [.var 0, .var 1], req := none, rhs := .var 2, ens := none, exs := [2],
          post := .mem Srt.int (.var 2) (.app nRegSyms [.var 1]) }).toOption.map fun x =>
      (x.2.names, x.1.pats, x.1.rhs, x.1.exs, x.1.post matches .mem _ (.var 2) (.app _ [.var 0]))) =
    some (["Y", "X", "Z"], [.var 1, .var 0], .var 2, [2], true) := by kernel_rfl

/-! ### CE's arm (`ceRead`, `ceOr`, `ceShape`, `ceCases`) -/

/-- `f(X) => f(X) #Or g(X)`: f has no `functional` sentence. -/
def eqFOr : RawEqn := ⟨"Lblf", [X], none, none, .or int [fOf X, gOf X], uid, none, false⟩
/-- `h(X) => f(X) #And g(X)`: a conjunction of two terms. -/
def eqAnd : RawEqn := ⟨"Lblh", [X], none, none, .and int [fOf X, gOf X], uid, none, false⟩
/-- `f(X) ∨ … ∨ f(X)`, n + 1 alternatives nested to the left. -/
def orN : Nat → Kore.Pattern
  | 0 => fOf X
  | n + 1 => .or int [orN n, fOf X]
/-- `h(X) => f(X) #Or … #Or f(X)`, nine alternatives, h with its `functional` sentence. -/
def eqMany : RawEqn := ⟨"Lblh", [X], none, none, orN 8, uid, none, false⟩
/-- `f(X) => X #Or #Exists Z:Int. (Z #And {Z #Equals g(X)})`: a binder in an alternative. -/
def eqAlt : RawEqn :=
  ⟨"Lblf", [X], none, none,
    .or int [X, .exist int (evar "VarZ" int) (.and int [ev "VarZ" int, .equals int int (ev "VarZ" int) (gOf X)])],
    uid, none, false⟩
/-- `h(X) => f(X) #And {X #Equals X}`: a term with a predicate, no conjunction of terms. -/
def eqPred : RawEqn := ⟨"Lblh", [X], none, none, .and int [fOf X, .equals int int X X], uid, none, false⟩

/-- **An `\or` without the `functional` sentence, in the kernel**: the one clause `ceRead` gives. -/
theorem wire_ce_or : (clausesBody N0 "" eqFOr none).map (·.map (·.1)) =
    (ceRead N0 eqFOr).map (fun x => [x.1]) := by kernel_rfl

/-- **A conjunction of terms, in the kernel**: the one clause `ceRead` gives. -/
theorem wire_ce_and : (clausesBody N0 "" eqAnd none).map (·.map (·.1)) =
    (ceRead N0 eqAnd).map (fun x => [x.1]) := by kernel_rfl

/-- **Nine alternatives, in the kernel**: past 8, the one clause `ceRead` gives, though h has its
`functional` sentence. -/
theorem wire_ce_many : (clausesBody N0 "" eqMany none).map (·.map (·.1)) =
    (ceRead N0 eqMany).map (fun x => [x.1]) := by kernel_rfl

/-- `f(X) => X #Or #Exists Z:Int. (g(Z) #And {f(Z) #Equals X})`: a binder in an alternative whose
body equates it with no term. -/
def eqAltFree : RawEqn :=
  ⟨"Lblf", [X], none, none,
    .or int [X, .exist int (evar "VarZ" int) (.and int [gOf (ev "VarZ" int), .equals int int (fOf (ev "VarZ" int)) X])],
    uid, none, false⟩

/-- **A binder in an alternative, in the kernel**: one whose body equates it with no term is moved
to the top (`ceEqn`, every sort accepted; `coreOf` tests the sort on the built definition), then
`ceRead`: `exs` is Z then the disjunction's variable. One whose body equates it with a term stays
in its alternative: `exs` is the disjunction's variable alone. -/
theorem wire_ce_hoist : (clausesBody N0 "" eqAltFree none).map (·.map (·.1)) =
      (ceRead N0 (ceEqn N0 eqAltFree)).map (fun x => [x.1]) ∧
    ((clausesBody N0 "" eqAltFree none).toOption.map fun xs => xs.map (·.1.exs)) = some [[1, 2]] ∧
    (clausesBody N0 "" eqAlt none).map (·.map (·.1)) = (ceRead N0 eqAlt).map (fun x => [x.1]) ∧
    ((clausesBody N0 "" eqAlt none).toOption.map fun xs => xs.map (·.1.exs)) = some [[1]] := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> kernel_rfl

/-- `h(X) => f(X) #And g(#Bottom)`: an empty right side (`σ(…, ⊥, …) = ⊥`, `φ ∧ ⊥ = ⊥`). -/
def eqAndBot : RawEqn := ⟨"Lblh", [X], none, none, .and int [fOf X, gOf (.bottom int)], uid, none, false⟩

/-- **An empty right side is the bottom arm's, in the kernel**: a conjunction of terms one of
which is empty is `clauseBody`'s clause (the `ensures` false), not CE's. -/
theorem wire_ce_empty : clausesBody N0 "" eqAndBot none = (clauseBody N0 "" eqAndBot none).map ([·]) ∧
    ceCases N0 eqAndBot = false := by
  constructor <;> kernel_rfl

/-- **Which equations are CE's**: `ceCases` holds of those `clausesBody` gives to `ceRead`, and
not of `frRead`'s (`eqH`), `exRead`'s (`eqP`), a plain equation's or a term with a predicate
(`clauseBody`'s). -/
theorem wire_ce_cases :
    [ceCases N0 eqFOr, ceCases N0 eqAnd, ceCases N0 eqMany, ceCases N0 eqAlt, ceCases N0 eqAltFree,
      ceCases { N0 with boolLits := false } eqP,
      ceCases N0 eqH, ceCases N0 eqP, ceCases N0 eqPlain, ceCases N0 eqPred] =
    [true, true, true, true, true, true, false, false, false, false] := by kernel_rfl

end Hand

/-! ## The stages of a package, on a text with an equation read by cases

`f2-examples/mleqort` is the kompiled text of `e3-ml-eq-rhs-or-total`. The checks are those
`kcore gen` writes for a function whose clauses are checked in blocks (`Tie.Cls*`, `Tie.Prods*`),
here for h, whose one equation gives three clauses: `Parse.clauseOf` on the block of its pairs by
the kernel, the function's `fnClauses` from the block, and the productions with that table. -/

namespace Stages

kore_term kore from "f2-examples/mleqort.kompile.kore" cut [100, 200, 300]
parse_stages stage from "f2-examples/mleqort.kompile.kore" cut [100, 200, 300] scan_blocks [1, 1, 1, 1]
  prod_blocks [3] rule_blocks [] event_blocks [] clause_blocks [2, 1, 1]

theorem scanIs0 : ScanIs kore.segs 0 1 stage.scan0 := by unfold ScanIs; kernel_rfl
theorem scanIs1 : ScanIs kore.segs 1 1 stage.scan1 := by unfold ScanIs; kernel_rfl
theorem scanIs2 : ScanIs kore.segs 2 1 stage.scan2 := by unfold ScanIs; kernel_rfl
theorem scanIs3 : ScanIs kore.segs 3 1 stage.scan3 := by unfold ScanIs; kernel_rfl

noncomputable def scanAll : Scan := ((stage.scan0.append stage.scan1).append stage.scan2).append stage.scan3

theorem env_eq : envOf (kore.modules.getLastD default) scanAll = .ok stage.env := by kernel_rfl

/-- **The clauses of h's one pair, by the kernel**: `clauseOf` on the block. -/
theorem clsIs2_0 : MapIs (clauseOf stage.env.N stage.env.src) (fnPairs scanAll.eqs "Lblh") 0 1 stage.cls2_0 := by
  unfold MapIs; kernel_rfl

theorem pairs2_length : (fnPairs scanAll.eqs "Lblh").length = 1 := by decide +kernel

theorem cls2 : fnClauses stage.env.N stage.env.src scanAll.eqs "Lblh" = .ok stage.cls2_0 :=
  MapIs.all pairs2_length clsIs2_0

/-- The one equation gives three clauses. -/
theorem cls2_lengths : stage.cls2_0.map (·.length) = [3] := by decide +kernel

/-- **They are `frClauses`', by the kernel**: the alternatives `f(X)`, `g(X)` with no condition, f
and g the symbols `nRegSyms + 4` and `nRegSyms + 5` of the text (test/EqRhsOr.lean's `F`, `G`,
whose `frClauses_h` gives these clauses as `hCl1`, `hCl2`, `hCl3`). -/
theorem cls2_frClauses : stage.cls2_0.map (·.map (·.1)) =
    [Parse.frClauses Srt.int [Srt.int] [.var 0] none 50 false
      [(.app (nRegSyms + 4) [.var 0], []), (.app (nRegSyms + 5) [.var 0], [])]] := by
  kernel_rfl

/-- **The productions, h's clauses from the block.** -/
theorem prodsIs0 : MapIs (symProd stage.env scanAll.eqs) (prodSyms scanAll stage.env) 0 3 stage.prods0 := by
  rw [← symProdT_eq (ov := [("Lblh", stage.cls2_0)]) (List.forall_mem_cons.2 ⟨cls2, (fun _ h => nomatch h)⟩)]
  unfold MapIs; kernel_rfl

end Stages

/-! ## `coreOf`'s check of Bool on the built definition -/

namespace CoreOfBool

/-- The sentences of the module `m` that apply the sort predicate of the sort `X` (its declaration,
its `functional` axiom, its equations), printed with X renamed `Y` and their unique ids prefixed,
and read back: the sentences kompile writes for the predicate of a sort Y declared as X is. -/
def predSentencesAs (m : Kore.Module) (X Y : String) : List Kore.Sentence :=
  let mine := m.sentences.filter fun s => ((Kore.Printer.sentence s).splitOn s!"Lblis{X}\{").length > 1
  let txt := "\n".intercalate (mine.map fun s =>
    ((((Kore.Printer.sentence s).replace s!"Lblis{X}\{" s!"Lblis{Y}\{").replace s!"Sort{X}\{" s!"Sort{Y}\{").replace
      s!"Var{X}:" s!"Var{Y}:").replace "UNIQUE'Unds'ID{}(\"" s!"UNIQUE'Unds'ID\{}(\"{Y}-")
  match Kore.parseDefinition s!"[]\nmodule PRED\n{txt}\nendmodule\n[]" with
  | .ok d => d.modules.flatMap (·.sentences)
  | .error _ => []

/-- `subBool` with the sort Foo declared as kompile declares a user sort: the text gives Bool the
elements of Foo. Foo's predicate `isFoo` is declared with its `functional` axiom and its equations
(`isFoo(inj{Foo,KItem}(X)) = true`, `isFoo(K) = false` otherwise), those of `isKCell` renamed
(`predSentencesAs`): kompile writes them for every user sort, and a text without them states no
clause of the predicate the semantics has for Foo (`Parse.predFnNamesPR` reads it from the text's
equations, `predFnsOfPR` from its declaration). -/
def subBoolD (k : Kore.Definition) : Kore.Definition :=
  let sd : Kore.Sentence := .sort { sort := ⟨⟨"SortFoo"⟩⟩, sortVars := [], attributes := [] }
  let ax : Kore.Axiom :=
    { sortVars := [], pattern := .top (KoreAML.srt "K"),
      attributes := [⟨⟨⟨"subsort"⟩⟩, [KoreAML.srt "Foo", KoreAML.srt "Bool"], []⟩] }
  match k.modules.reverse with
  | m :: rest =>
    { k with modules := ({ m with sentences := m.sentences ++ [sd, .axiom ax] ++ predSentencesAs m "KCell" "Foo" } ::
      rest).reverse }
  | [] => k

/-- info: isFoo's sentences: 4 -/
#guard_msgs in
#eval show IO Unit from do
  let k ← load "e3-eq-exists-bool-ml"
  let some m := k.modules.getLast? | pure ()
  IO.println s!"isFoo's sentences: {(predSentencesAs m "KCell" "Foo").length}"

/-- `finish` with the names' `boolLits` set to `b` after `envOf`. -/
def finishWith (b : Bool) (m : Kore.Module) (S : Scan) : Rd Definition := do
  let E ← envOf m S
  let E := { E with N := { E.N with boolLits := b } }
  let symProds ← (prodSyms S E).mapM (symProd E S.eqs)
  let rules ← S.rewrites.mapM (ruleOf E.N E.src)
  assemble m S E symProds rules

/-- The text of fixture `n`, changed by `edit`: the names' `boolLits`, then `finishWith b`, then
`parse`, each refusal with its whole detail. -/
def runWith (n : String) (edit : Kore.Definition → Kore.Definition) (b : Bool) : IO Unit := do
  let k := edit (← load n)
  let some m := k.modules.getLast? | IO.println s!"{n}: no module"
  let S := scan m.sentences
  match envOf m S with
  | .error f => IO.println s!"{n}: envOf fails {f.reason.name}"
  | .ok E => IO.println s!"{n}: boolLits {E.N.boolLits}; finish with boolLits {b}:"
  match finishWith b m S with
  | .error f => IO.println s!"  refused {f.reason.name} ({f.detail})"
  | .ok d => IO.println s!"  read; coreOK {d.sem.coreOK}; litSort Bool {d.sem.litSort Srt.bool}"
  match Parse.parse k with
  | .error r => IO.println s!"  parse: refused {r.reason.name} ({r.detail})"
  | .ok d => IO.println s!"  parse: read; litSort Bool {d.sem.litSort Srt.bool}"

/--
info: e3-eq-exists-bool-ml: boolLits false; finish with boolLits true:
  refused existentialEquation (Bool: the text's declarations give the sort no value beside its literals (Names.boolLits), and the definition read has one (litSort): the equation, read by cases over a Bool variable (existsAsCases), would state more than the text)
  parse: read; litSort Bool false
e3-eq-exists-bool-ml: boolLits false; finish with boolLits false:
  read; coreOK false; litSort Bool false
  parse: read; litSort Bool false
e3-eq-exists-bool-ml: boolLits true; finish with boolLits true:
  read; coreOK true; litSort Bool true
  parse: read; litSort Bool true
-/
#guard_msgs in
#eval show IO Unit from do
  runWith "e3-eq-exists-bool-ml" subBoolD true
  runWith "e3-eq-exists-bool-ml" subBoolD false
  runWith "e3-eq-exists-bool-ml" id true

/-- **The library gives Bool no value beside its literals**: the conjuncts of `litSort` at Bool
that read the library's data (its modules' subsorts, constructors, token and byte sorts; the fixed
constructors, `#KConfigValue`'s and the builtin collections) hold of every definition. -/
theorem library_lits :
    (library.all (fun m => m.subsorts.all (·.2 != Srt.bool) && m.ctors.all (·.result != Srt.bool) &&
      !m.tokenSorts.contains Srt.bool && !m.byteSorts.contains Srt.bool) &&
     fixedCtors.all (·.result != Srt.bool) && kconfigCtor.result != Srt.bool &&
     builtinColls.all (·.sort != Srt.bool)) = true := by
  decide +kernel

end CoreOfBool

end ReaderWire
