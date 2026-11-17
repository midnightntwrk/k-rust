/-
  The reading functions of KcoreSpec/ReadFns.lean for an equation's right side that holds `\or`
  (`Parse.frRead`), run on the kompiled texts of the fixtures (test/constructs/fixtures; K 7.1.337
  kompile's KORE, from the cache `kfix.py` keeps: `$KCORE_KFIX_CACHE`, else
  `$XDG_CACHE_HOME/kcore-kfix`, else `~/.cache/kcore-kfix`, the text named by the sha256 of the
  fixture's kompile.txt) and on hand-written equations. Run from the package root:
  `lake env lean -j1 test/RhsReader.lean`.

  `Parse.clauseBody` does not call these functions: the reader refuses each of these texts as
  before (their accounts are unchanged). Each clause a function gives is put in the definition the
  landed reader builds from the text with that equation's right side replaced by a plain term, and
  printed with `clauseSorted`, `condOK` of its predicates and `clauseE3`, the conjunct CN-4 §4.9
  gives `clausesPlain` for one clause (the landed `clausesPlain` asks `pre = \top`, so it is false
  of these clauses).

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
  Kernel-checked (`kernel_rfl`, `decide +kernel`): `frRead` on the fixture's equation written by
  hand (`Hand.eqH`; `tie` checks that it is the scanned text's equation) and on the hand-written
  equations; `frClauses` with an `ensures`, and its length.
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

/-- `read` on the equations of the functions `fns` of fixture `n`: a refusal, `none`, or the
clauses, put in the definition built from the patched text. -/
def run (n : String) (fns : List String) (read : Names → RawEqn → Rd (Option (List Clause × List KoreAML.Var))) :
    IO Unit := do
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
          match read E.N e with
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
  sortedOK but clausesPlain true; clausesPlain false; every clause clauseE3 true; readsConfined true; litSort Bool true
e3-ml-eq-rhs-or Lblh: refused KCore.Parse.RefusalReason.manyValuedRightSide (\or: the sentence gives the function every element of each side; the function is not declared total, so where the sides differ that is more than one element, which no clause states)
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
eqNF: refused KCore.Parse.RefusalReason.manyValuedRightSide (\or: the sentence gives the function every element of each side; the function is not declared total, so where the sides differ that is more than one element, which no clause states)
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

end RhsReader
