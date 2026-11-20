/-
  A binder kept in its alternative of an `\or` on an equation's right side (`Parse.ceKeep`,
  `Parse.hoistExK`, `Parse.memOf`'s `\exists` arm, in CE's arm of `Parse.clausesBody`). Run from
  the package root: `lake env lean -j1 test/ExClauseScoped.lean`.
  The kompiled texts are read from the cache `kfix.py` keeps, as test/ExClauseReader.lean reads them.

  `(∃x:s. φ) ∨ ψ = ∃x:s. (φ ∨ ψ)` (N3) leaves the moved x equated with no term where ψ holds, so the
  clause is admitted only at a confined s. Where φ equates x with a term that does not hold x, and s
  is not Bool with its literals alone (the one sort the names show confined), CE's arm leaves the
  binder in its alternative (`ceEqn`), and `memOf` reads the alternative as `Cond.ex s (Z ∈ φ)`:
  `Z ∈ ∃x. φ = ∃x. (Z ∈ φ)` in every interpretation, nothing asked of s. The binder's index is the
  one past the clause's variables, each numbered before the memberships are read.
  Hand-written (`HandScoped`, over `N2` and `NB`): `eqFix`, `h(X) => X #Or #Exists Z. (Z #And {Z
  #Equals f(X)})`, is read with `exs` the disjunction's variable alone and `post (#Or0 ∈ X) ∨ ∃.
  ((#Or0 ∈ #2) ∧ (#2 = f(X)))` (`clFix`); `eqFree` (the body equates Z with no term) and `eqSelf`
  (with a term holding Z) are moved as before; `eqUnderApp` (the `\or` under an application) and
  `eqTwo` (a binder in each alternative, of one name) keep theirs; `eqArg` (a binder named as the
  argument) is refused `patternConnective`; `eqBool` is moved over `NB`; where the names give Bool a
  value beside its literals its alternative `∃C. (#Or0 ∈ C ∧ C = X)` is read as `#Or0 ∈ X`. With no sort accepted as having a value the kept binder
  is refused `existentialEquation` as a moved one is.
  Kernel-checked: `scoped_steps` (`ceEqn`, `ceRead`'s clause, the reader's clause, the refusal's
  reason), `scoped_fixes` (the body fixes the bound index; `Clause.fixedExs` holds the disjunction's
  variable where the test of a value accepts Int and is empty where it accepts no sort).
  On the fixtures (`runScoped`, the text as it is): `e3-eq-exists-ml-in-or-int` and
  `e3-eq-exists-ml-in-or-float` keep the binder and are read, `Cond.bound` and `clausePlainEx` true
  of the clause in the definition built (Int and Float are not confined and have a value,
  `Semantics.hasValue`); `e3-eq-exists-ml-in-or` (Bool, confined) has its binder moved, as before;
  `e3-eq-exists-ml-in-or-empty` (a sort without a value) keeps the binder and is refused
  `existentialEquation` by `coreOf` (`ceHoistFault?`).
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

open KCore KCore.Parse

namespace ExClauseScoped

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

/-- `ceRead` on a hand-written equation, a symbol and a sort the registry does not name printed
by number. -/
def showHand (what : String) (r : Rd (Clause × List KoreAML.Var)) : IO Unit :=
  match r with
  | .error f => IO.println s!"{what}: refused {repr f.reason} ({f.detail})"
  | .ok (cl, vs) => do
    IO.println s!"{what}:"
    showFields (fun f => regSymNames.getD f s!"sym{f - nRegSyms}") (fun s => regSortNames.getD s s!"sort{s - nRegSorts}") 0 cl vs


/-! ## The hand-written equations -/

namespace HandScoped

open KoreAML (ev ap srt evar)

/-- f, g, h : Int → Int, the symbols `nRegSyms` to `nRegSyms + 2`. -/
def N2 : Names :=
  { sorts := [], syms := ["Lblf", "Lblg", "Lblh"]
    keyFns := [(nRegSyms, "Int"), (nRegSyms + 1, "Int"), (nRegSyms + 2, "Int")] }

/-- f, g : Bool → Bool, the symbols `nRegSyms + 4` and `nRegSyms + 5`; f has its `functional`
sentence; Bool has its literals only. -/
def NB : Names :=
  { sorts := []
    syms := ["LblisKCell", "LblisKCellOpt", "Lbl'-LT-'k'-GT-'", "LblnoKCell", "Lblf", "Lblg"]
    keyFns := [(nRegSyms + 4, "Bool"), (nRegSyms + 5, "Bool")]
    fnlSyms := [("Lblf", false)]
    boolLits := true }

def int : Kore.KSort := srt "Int"
def bS : Kore.KSort := srt "Bool"
def X : Kore.Pattern := ev "VarX" int
def Z : Kore.Pattern := ev "VarZ" int
def Xp : Kore.Pattern := ev "VarX" bS
def Bp : Kore.Pattern := ev "VarB" bS
def f (p : Kore.Pattern) : Kore.Pattern := ap "Lblf" [p]
def g (p : Kore.Pattern) : Kore.Pattern := ap "Lblg" [p]
def eqI (p q : Kore.Pattern) : Kore.Pattern := .equals int int p q
/-- `#Exists V:Int. body`. -/
def ex (v : String) (body : Kore.Pattern) : Kore.Pattern := .exist int (evar v int) body
def exB (body : Kore.Pattern) : Kore.Pattern := .exist bS (evar "VarB" bS) body
def bodyP : Kore.Pattern := .and bS [Bp, .equals bS bS Bp Xp]
def uid : List Kore.AppPattern := [KoreAML.attrStr "UNIQUE'Unds'ID" "u"]

def eqn (rhs : Kore.Pattern) : RawEqn := ⟨"Lblh", [X], none, none, rhs, uid, none, false⟩

/-- `h(X) => X #Or #Exists Z:Int. (Z #And {Z #Equals f(X)})`: the body equates Z with a term. -/
def eqFix : RawEqn := eqn (.or int [X, ex "VarZ" (.and int [Z, eqI Z (f X)])])
/-- `h(X) => X #Or #Exists Z:Int. (f(Z) #And {g(Z) #Equals X})`: the body equates Z with no term. -/
def eqFree : RawEqn := eqn (.or int [X, ex "VarZ" (.and int [f Z, eqI (g Z) X])])
def eqFree' : RawEqn := eqn (ex "VarZ" (.or int [X, .and int [f Z, eqI (g Z) X]]))
/-- `h(X) => X #Or #Exists Z:Int. (Z #And {Z #Equals f(Z)})`: the term holds Z. -/
def eqSelf : RawEqn := eqn (.or int [X, ex "VarZ" (.and int [Z, eqI Z (f Z)])])
/-- `h(X) => g(X #Or #Exists Z:Int. (Z #And {Z #Equals f(X)}))`: the `\or` under an application. -/
def eqUnderApp : RawEqn := eqn (g (.or int [X, ex "VarZ" (.and int [Z, eqI Z (f X)])]))
/-- Two alternatives each with a binder named Z, both fixed. -/
def eqTwo : RawEqn :=
  eqn (.or int [ex "VarZ" (.and int [Z, eqI Z (f X)]), ex "VarZ" (.and int [g Z, eqI Z (g X)])])
/-- A binder named as the argument. -/
def eqArg : RawEqn := eqn (.or int [X, ex "VarX" (.and int [X, eqI X (.dv int "0")])])
/-- `f(X) => X #Or #Exists B:Bool. (B #And {B #Equals X})`, over `NB`. -/
def eqBool : RawEqn := ⟨"Lblf", [Xp], none, none, .or bS [Xp, exB bodyP], uid, none, false⟩
def eqBool' : RawEqn := ⟨"Lblf", [Xp], none, none, exB (.or bS [Xp, bodyP]), uid, none, false⟩

/-- The clause read from `eqFix`: X, then the disjunction's variable; the binder's index is 2. -/
def clFix : Clause :=
  { vars := [Srt.int, Srt.int], pats := [.var 0], req := none, rhs := .var 1, ens := none, exs := [1],
    post := .or (.mem Srt.int (.var 1) (.var 0))
      (.ex Srt.int (.and (.mem Srt.int (.var 1) (.var 2)) (.equals Srt.int (.var 2) (.app nRegSyms [.var 0])))) }

def showKeep (what : String) (N : Names) (e : RawEqn) : IO Unit := do
  let eC := ceEqn N e
  IO.println s!"{what}: ceEqn leaves the right side {eC.rhs == e.rhs}; binders at the top {(peelExists eC.rhs).1.map (·.var.ident.name)}; a binder heads an alternative {altEx (peelExists eC.rhs).2}; ceCases {ceCases N e}"
  showHand what (ceRead N eC)

end HandScoped

/--
info: eqFix: ceEqn leaves the right side true; binders at the top []; a binder heads an alternative true; ceCases true
eqFix:
  [0] vars [X:Int, 'Hash'Or0:Int] pats [X] req none prio 50 aside false
      pre ⊤
      rhs 'Hash'Or0 ens none exs [1] post (('Hash'Or0 ∈[Int] X) ∨ ∃.(('Hash'Or0 ∈[Int] #2) ∧ (#2 =[Int] sym0(X))))
eqFree: ceEqn leaves the right side false; binders at the top [VarZ]; a binder heads an alternative false; ceCases true
eqFree:
  [0] vars [X:Int, Z:Int, 'Hash'Or0:Int] pats [X] req none prio 50 aside false
      pre ⊤
      rhs 'Hash'Or0 ens none exs [1, 2] post (('Hash'Or0 ∈[Int] X) ∨ (('Hash'Or0 ∈[Int] sym0(Z)) ∧ (sym1(Z) =[Int] X)))
eqSelf: ceEqn leaves the right side false; binders at the top [VarZ]; a binder heads an alternative false; ceCases true
eqSelf:
  [0] vars [X:Int, Z:Int, 'Hash'Or0:Int] pats [X] req none prio 50 aside false
      pre ⊤
      rhs 'Hash'Or0 ens none exs [1, 2] post (('Hash'Or0 ∈[Int] X) ∨ (('Hash'Or0 ∈[Int] Z) ∧ (Z =[Int] sym0(Z))))
eqUnderApp: ceEqn leaves the right side true; binders at the top []; a binder heads an alternative true; ceCases true
eqUnderApp:
  [0] vars [X:Int, 'Hash'Or0:Int] pats [X] req none prio 50 aside false
      pre ⊤
      rhs sym1('Hash'Or0) ens none exs [1] post (('Hash'Or0 ∈[Int] X) ∨ ∃.(('Hash'Or0 ∈[Int] #2) ∧ (#2 =[Int] sym0(X))))
eqTwo: ceEqn leaves the right side true; binders at the top []; a binder heads an alternative true; ceCases true
eqTwo:
  [0] vars [X:Int, 'Hash'Or0:Int] pats [X] req none prio 50 aside false
      pre ⊤
      rhs 'Hash'Or0 ens none exs [1] post (∃.(('Hash'Or0 ∈[Int] #2) ∧ (#2 =[Int] sym0(X))) ∨ ∃.(('Hash'Or0 ∈[Int] sym1(#2)) ∧ (#2 =[Int] sym1(X))))
eqArg: ceEqn leaves the right side true; binders at the top []; a binder heads an alternative true; ceCases true
eqArg: refused KCore.Parse.RefusalReason.patternConnective (VarX: bound in an alternative, named as a variable of the clause)
eqBool: ceEqn leaves the right side false; binders at the top [VarB]; a binder heads an alternative false; ceCases true
eqBool:
  [0] vars [X:Bool, B:Bool, 'Hash'Or0:Bool] pats [X] req none prio 50 aside false
      pre ⊤
      rhs 'Hash'Or0 ens none exs [1, 2] post (('Hash'Or0 ∈[Bool] X) ∨ (('Hash'Or0 ∈[Bool] B) ∧ (B =[Bool] X)))
eqBool, Bool with a value beside its literals: ceEqn leaves the right side true; binders at the top []; a binder heads an alternative true; ceCases true
eqBool, Bool with a value beside its literals:
  [0] vars [X:Bool, 'Hash'Or0:Bool] pats [X] req none prio 50 aside false
      pre ⊤
      rhs 'Hash'Or0 ens none exs [1] post (('Hash'Or0 ∈[Bool] X) ∨ ('Hash'Or0 ∈[Bool] X))
eqFix, no sort accepted: refused KCore.Parse.RefusalReason.existentialEquation (VarZ: bound in one alternative of \or at a sort without a value (Int, which the test of a value does not accept))
-/
#guard_msgs in
open HandScoped in
#eval show IO Unit from do
  showKeep "eqFix" N2 eqFix
  showKeep "eqFree" N2 eqFree
  showKeep "eqSelf" N2 eqSelf
  showKeep "eqUnderApp" N2 eqUnderApp
  showKeep "eqTwo" N2 eqTwo
  showKeep "eqArg" N2 eqArg
  showKeep "eqBool" NB eqBool
  showKeep "eqBool, Bool with a value beside its literals" { NB with boolLits := false } eqBool
  match hoistExistsK (ceKeep N2) (fun _ => false) int eqFix with
  | .error f => IO.println s!"eqFix, no sort accepted: refused {repr f.reason} ({f.detail})"
  | .ok _ => IO.println "eqFix, no sort accepted: read"

namespace HandScoped

/-- **The kept binder, in the kernel**: `ceEqn` leaves `eqFix` and moves `eqFree`'s binder; the
clause `ceRead` gives of `eqFix` is `clFix`, and the reader's (`clausesBody`) is it; a Bool binder is
moved where the names give Bool its literals alone, and kept otherwise; the test of a value is asked
of a kept binder's sort. -/
theorem scoped_steps :
    (ceEqn N2 eqFix).rhs = eqFix.rhs ∧ (ceEqn N2 eqFree).rhs = eqFree'.rhs ∧
    (ceRead N2 eqFix).toOption.map (·.1) = some clFix ∧
    (clausesBody N2 "" eqFix none).toOption.map (·.map (·.1)) = some [clFix] ∧
    (ceEqn NB eqBool).rhs = eqBool'.rhs ∧ (ceEqn { NB with boolLits := false } eqBool).rhs = eqBool.rhs ∧
    (match hoistExistsK (ceKeep N2) (fun _ => false) int eqFix with
      | .error f => some f.reason | .ok _ => none) = some .existentialEquation := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> kernel_rfl

/-- **What admits the clause** (`Cond.fixes`, `Clause.fixedExs`), no sort confined: the binder's
body fixes the bound index 2 by a term over the other variables; the existential variable 1 is
fixed, in both alternatives, where the test of a value accepts Int, and not where it accepts no
sort (the second alternative then fixes nothing). -/
theorem scoped_fixes :
    Cond.fixes (fun _ => false) (fun _ => false) (fun j => j != 2) 2 3
      (.and (.mem Srt.int (.var 1) (.var 2)) (.equals Srt.int (.var 2) (.app nRegSyms [.var 0]))) = true ∧
    clFix.fixedExs (fun _ => false) (fun s => s == Srt.int) = [1] ∧
    clFix.fixedExs (fun _ => false) (fun _ => false) = [] := by
  decide +kernel

end HandScoped

/-- info: 'ExClauseScoped.HandScoped.scoped_steps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms HandScoped.scoped_steps
/-- info: 'ExClauseScoped.HandScoped.scoped_fixes' depends on axioms: [propext] -/
#guard_msgs in #print axioms HandScoped.scoped_fixes

/-- The reader on the equation of `fn` in fixture `n`: what `ceEqn` does with its binder, the clause
`ceRead` gives, and the definition built from the text: of each clause of the function there,
`Cond.bound` of its `post`, `fixedExs` and `clausePlainEx`, and of the binder's sort `rs`, the
tests `confined` and `hasValue`. -/
def runScoped (n fn rs : String) : IO Unit := do
  let k ← load n
  let some m := k.modules.getLast? | IO.println s!"{n}: no module"
  let S := scan m.sentences
  match envOf m S with
  | .error f => IO.println s!"{n}: envOf fails {repr f.reason}"
  | .ok E =>
    for e in S.eqs.filter (·.fn == fn) do
      let eC := ceEqn E.N { e with rhs := dropEmptyAlts e.rhs }
      IO.println s!"{n} {fn}: ceEqn: binders at the top {(peelExists eC.rhs).1.map (·.var.ident.name)}; a binder heads an alternative {altEx (peelExists eC.rhs).2}; ceCases {ceCases E.N e}"
      showHand "  ceRead" (ceRead E.N eC)
  let notes := (connReadings k).map fun (_, ns) => ns.map ReadingNote.name
  match Parse.parse k with
  | .error r => IO.println s!"  notes {notes}; refused {repr r.reason} ({r.detail})"
  | .ok d =>
    let c := d.sem
    let s := ((List.range (nRegSorts + c.sortNames.length)).find? (c.sortName · == rs)).getD 0
    IO.println s!"  notes {notes}; read; coreOK {c.coreOK}; {rs}: confined {c.confined s}, hasValue {c.hasValue s}"
    for f in c.fns.filter (c.symName ·.label == fn) do
      for cl in f.clauses do
        IO.println s!"  clause: vars {cl.vars.length} exs {cl.exs}; Cond.bound post {Cond.bound c cl.vars.length cl.post}; fixedExs {cl.fixedExs c.confined c.hasValue}; clausePlainEx {c.clausePlainEx cl}"

/--
info: e3-eq-exists-ml-in-or-int Lblf: ceEqn: binders at the top []; a binder heads an alternative true; ceCases true
  ceRead:
  [0] vars [X:Int, 'Hash'Or0:Int] pats [X] req none prio 50 aside false
      pre ⊤
      rhs 'Hash'Or0 ens none exs [1] post (('Hash'Or0 ∈[Int] X) ∨ ∃.(('Hash'Or0 ∈[Int] #2) ∧ (#2 =[Int] Lbl'UndsPlus'Int'Unds'(X, 1))))
  notes [[existentialClause]]; read; coreOK true; Int: confined false, hasValue true
  clause: vars 2 exs [1]; Cond.bound post true; fixedExs [1]; clausePlainEx true
e3-eq-exists-ml-in-or-float Lblf: ceEqn: binders at the top []; a binder heads an alternative true; ceCases true
  ceRead:
  [0] vars [X:Float, 'Hash'Or0:Float] pats [X] req none prio 50 aside false
      pre ⊤
      rhs 'Hash'Or0 ens none exs [1] post (('Hash'Or0 ∈[Float] X) ∨ ∃.(('Hash'Or0 ∈[Float] #2) ∧ (#2 =[Float] Lbl'UndsPlus'Float'UndsUnds'FLOAT'Unds'Float'Unds'Float'Unds'Float(X, KCore.Lit.float 53 11 4607182418800017408))))
  notes [[existentialClause]]; read; coreOK true; Float: confined false, hasValue true
  clause: vars 2 exs [1]; Cond.bound post true; fixedExs [1]; clausePlainEx true
e3-eq-exists-ml-in-or Lblf: ceEqn: binders at the top [VarB]; a binder heads an alternative false; ceCases true
  ceRead:
  [0] vars [X:Bool, B:Bool, 'Hash'Or0:Bool] pats [X] req none prio 50 aside false
      pre ⊤
      rhs 'Hash'Or0 ens none exs [1, 2] post (('Hash'Or0 ∈[Bool] X) ∨ (('Hash'Or0 ∈[Bool] B) ∧ (B =[Bool] LblnotBool'Unds'(X))))
  notes [[existentialClause], [existentialClause]]; read; coreOK true; Bool: confined true, hasValue true
  clause: vars 3 exs [1, 2]; Cond.bound post true; fixedExs [2]; clausePlainEx true
e3-eq-exists-ml-in-or Lblfx: ceEqn: binders at the top [VarB]; a binder heads an alternative false; ceCases true
  ceRead:
  [0] vars [X:Bool, B:Bool, 'Hash'Or0:Bool] pats [X] req none prio 50 aside false
      pre ⊤
      rhs 'Hash'Or0 ens none exs [1, 2] post (('Hash'Or0 ∈[Bool] X) ∨ (('Hash'Or0 ∈[Bool] B) ∧ (B =[Bool] X)))
  notes [[existentialClause], [existentialClause]]; read; coreOK true; Bool: confined true, hasValue true
  clause: vars 3 exs [1, 2]; Cond.bound post true; fixedExs [2]; clausePlainEx true
e3-eq-exists-ml-in-or-empty Lblfl: ceEqn: binders at the top []; a binder heads an alternative true; ceCases true
  ceRead:
  [0] vars ['Hash'Or0:Bool] pats [] req none prio 50 aside false
      pre ⊤
      rhs 'Hash'Or0 ens none exs [0] post (('Hash'Or0 ∈[Bool] true) ∨ ∃.(('Hash'Or0 ∈[Bool] sym7(#1)) ∧ (#1 =[sort2] sym8())))
  notes [[existentialClause]]; refused KCore.Parse.RefusalReason.existentialEquation (VarB: bound in one alternative of \or at a sort without a value (S, which the test of a value does not accept): Semantics.hasValue, on the definition read, finds no value of the sort at every interpretation of the parameters (no literal, no empty collection, no term of constructors and injections); the alternative's elements depend on elements of the sort that no value names)
-/
#guard_msgs in
#eval show IO Unit from do
  runScoped "e3-eq-exists-ml-in-or-int" "Lblf" "Int"
  runScoped "e3-eq-exists-ml-in-or-float" "Lblf" "Float"
  runScoped "e3-eq-exists-ml-in-or" "Lblf" "Bool"
  runScoped "e3-eq-exists-ml-in-or" "Lblfx" "Bool"
  runScoped "e3-eq-exists-ml-in-or-empty" "Lblfl" "S"

end ExClauseScoped
