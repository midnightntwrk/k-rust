/-
  KORE building blocks: sorts, variables, applications, attributes, and the axioms kompile
  generates from declarations and equations, in kompile's shape. Reviewed layer: `emit` writes
  the KORE text with them (kept from F0's Emit when F0 was removed, P1.4).
-/
import KcoreSpec.Kore.Base
import KoreParser

set_option autoImplicit false

namespace KoreAML

/-- The KORE sort of a sort name: `Nat` ↦ `SortNat{}`. -/
def srt (n : String) : Kore.KSort := .ctor ⟨⟨"Sort" ++ n⟩⟩ []

/-- The sort variable `R` of a generated axiom. -/
def Rv : Kore.SortVar := ⟨⟨⟨"R"⟩⟩⟩
def R : Kore.KSort := .var Rv

def evar (n : String) (s : Kore.KSort) : Kore.EVar := ⟨⟨⟨n⟩⟩, s⟩
def ev (n : String) (s : Kore.KSort) : Kore.Pattern := .var (.evar (evar n s))
def ap (f : String) (args : List Kore.Pattern) : Kore.Pattern := .app ⟨⟨f⟩⟩ [] args
def injP (a b : String) (t : Kore.Pattern) : Kore.Pattern := .app ⟨⟨"inj"⟩⟩ [srt a, srt b] [t]
def kseq1 (item : Kore.Pattern) : Kore.Pattern := ap "kseq" [item, ap "dotk" []]
def dv (s v : String) : Kore.Pattern := .dv (srt s) v

def attr (n : String) : Kore.AppPattern := ⟨⟨⟨n⟩⟩, [], []⟩
def attrStr (n v : String) : Kore.AppPattern := ⟨⟨⟨n⟩⟩, [], [.string v]⟩
def locAttr (l : Loc) : Kore.AppPattern :=
  attrStr "org'Stop'kframework'Stop'attributes'Stop'Location" s!"Location({l.l1},{l.c1},{l.l2},{l.c2})"
def srcAttr (path : String) : Kore.AppPattern :=
  attrStr "org'Stop'kframework'Stop'attributes'Stop'Source" s!"Source({path})"
def uidAttr (u : String) : Kore.AppPattern := attrStr "UNIQUE'Unds'ID" u
def kywdAttr (k : String) : Kore.AppPattern := attrStr "symbol'Kywd'" k

def axiomR (p : Kore.Pattern) (attrs : List Kore.AppPattern) : Kore.Sentence :=
  .axiom { sortVars := [Rv], pattern := p, attributes := attrs }
def axiom0 (p : Kore.Pattern) (attrs : List Kore.AppPattern) : Kore.Sentence :=
  .axiom { sortVars := [], pattern := p, attributes := attrs }
def symbolDecl (f : String) (args : List String) (res : String) (attrs : List Kore.AppPattern) :
    Kore.Sentence :=
  .symbol { symbol := { ident := ⟨⟨f⟩⟩, sortVars := [] }, sorts := args.map srt, sort := srt res,
            attributes := attrs }

/-- Variables `pre0 : s₀, pre1 : s₁, …` (from index `i`). -/
def numbered (pre : String) : Nat → List String → List Kore.EVar
  | _, [] => []
  | i, s :: ss => evar (pre ++ toString i) (srt s) :: numbered pre (i + 1) ss

def vars (xs : List Kore.EVar) : List Kore.Pattern := xs.map (.var ∘ .evar)

/-- `∃b₁. ∃b₂. … body`, binders at the sort `s`. -/
def existsAll (s : Kore.KSort) (bs : List Kore.EVar) (body : Kore.Pattern) : Kore.Pattern :=
  bs.foldr (fun b acc => .exist s b acc) body

/-- `∃Val:res. Val = f(K0, …)` ([functional]). -/
def functionalAx (f : String) (args : List String) (res : String) : Kore.Sentence :=
  let val := evar "Val" (srt res)
  axiomR (.exist R val (.equals (srt res) R (.var (.evar val)) (ap f (vars (numbered "K" 0 args)))))
    [attr "functional"]

/-- `∃Val:B. Val = inj{A,B}(From)` ([subsort{A,B}]). -/
def subsortAx (a b : String) : Kore.Sentence :=
  let val := evar "Val" (srt b)
  axiomR (.exist R val (.equals (srt b) R (.var (.evar val)) (injP a b (ev "From" (srt a)))))
    [⟨⟨⟨"subsort"⟩⟩, [srt a, srt b], []⟩]

/-- Injectivity `c(X̄) ∧ c(Ȳ) → c(X̄ ∧ Ȳ)` ([constructor]). -/
def injectivityAx (c : CtorSig) : Kore.Sentence :=
  let xs := numbered "X" 0 c.args
  let ys := numbered "Y" 0 c.args
  let meet := (xs.zip ys).map fun (x, y) => Kore.Pattern.and x.sort [.var (.evar x), .var (.evar y)]
  axiom0 (.implies (srt c.result) (.and (srt c.result) [ap c.name (vars xs), ap c.name (vars ys)])
    (ap c.name meet)) [attr "constructor"]

/-- Distinctness `¬(c(X̄) ∧ c'(Ȳ))` of two constructors of one sort ([constructor]). -/
def distinctnessAx (c c' : CtorSig) : Kore.Sentence :=
  axiom0 (.not (srt c.result) (.and (srt c.result)
    [ap c.name (vars (numbered "X" 0 c.args)), ap c'.name (vars (numbered "Y" 0 c'.args))]))
    [attr "constructor"]

/-- A constructor's axioms: functionality, injectivity (with arguments), and distinctness from
each later constructor of its sort. -/
def ctorAxioms (c : CtorSig) (later : List CtorSig) : List Kore.Sentence :=
  [functionalAx c.name c.args c.result] ++
  (if c.args.isEmpty then [] else [injectivityAx c]) ++
  (later.filter (·.result == c.result)).map (distinctnessAx c)

/-- kompile's names in a no-junk axiom: the first variable named `base` keeps it, later ones of
another sort get `baseV2`, `baseV3`, …; one sort keeps one name. `seen` lists, per base name, the
sorts named so far. -/
def noJunkName (seen : List (String × List String)) (base s : String) :
    String × List (String × List String) :=
  let sorts := (seen.lookup base).getD []
  let rest := seen.filter (·.1 != base)
  match sorts.idxOf? s with
  | some i => (if i == 0 then base else base ++ "V" ++ toString (i + 1), seen)
  | none => (if sorts.isEmpty then base else base ++ "V" ++ toString (sorts.length + 1),
             (base, sorts ++ [s]) :: rest)

def noJunkVars (seen : List (String × List String)) :
    List (String × String) → List Kore.EVar × List (String × List String)
  | [] => ([], seen)
  | (base, s) :: rest =>
    let (n, seen) := noJunkName seen base s
    let (xs, seen) := noJunkVars seen rest
    (evar n (srt s) :: xs, seen)

def noJunkDisjuncts (N : String) (seen : List (String × List String)) : List Gen → List Kore.Pattern
  | [] => [.bottom (srt N)]
  | .ctor c :: gs =>
    let (xs, seen) := noJunkVars seen ((List.range c.args.length).map (fun i => "X" ++ toString i) |>.zip c.args)
    existsAll (srt N) xs (ap c.name (vars xs)) :: noJunkDisjuncts N seen gs
  | .inj a :: gs =>
    let (n, seen) := noJunkName seen "Val" a
    let x := evar n (srt a)
    .exist (srt N) x (injP a N (.var (.evar x))) :: noJunkDisjuncts N seen gs

/-- `\and{R}(\in{s₀,R}(X0:s₀, p₀), \and{R}(…, \top{R}()))` from formal index `i`. -/
def argsConj : Nat → List (String × Kore.Pattern) → Kore.Pattern
  | _, [] => .top R
  | i, (s, p) :: rest => .and R [.in (srt s) R (ev s!"X{i}" (srt s)) p, argsConj (i + 1) rest]

/-- The premise of an equation with argument sorts `args` and patterns `pats`. -/
def premise (args : List String) (pats : List Kore.Pattern) : Kore.Pattern :=
  .and R [.top R, argsConj 0 (args.zip pats)]

/-- `\or{R}(e₁, \or{R}(…, \bottom{R}()))`. -/
def anyOf : List Kore.Pattern → Kore.Pattern
  | [] => .bottom R
  | e :: es => .or R [e, anyOf es]

/-- The premise of an `owise` equation: no competitor applies, and its own patterns match. -/
def owisePremise (args : List String) (competitors : List Kore.Pattern) (pats : List Kore.Pattern) :
    Kore.Pattern :=
  .and R [.not R (anyOf competitors), premise args pats]

/-- `\implies{R}(prem, \equals{res,R}(f(X0, …), \and{res}(rhs, ens)))`: `ens` is `\top{res}()` for
an equation without an `ensures`, `\equals{Bool,res}(E, \dv{Bool}("true"))` for one with `ensures E`. -/
def equationAx (f : String) (args : List String) (res : String) (prem rhs ens : Kore.Pattern)
    (attrs : List Kore.AppPattern) : Kore.Sentence :=
  axiomR (.implies R prem (.equals (srt res) R (ap f (vars (numbered "X" 0 args)))
    (.and (srt res) [rhs, ens]))) attrs

/-- `equationAx` with the left side given as a pattern, for an equation of a symbol that is applied
at sort arguments: `\implies{R}(prem, \equals{res,R}(lhs, \and{res}(rhs, ens)))`. -/
def equationAt (lhs : Kore.Pattern) (res : String) (prem rhs ens : Kore.Pattern)
    (attrs : List Kore.AppPattern) : Kore.Sentence :=
  axiomR (.implies R prem (.equals (srt res) R lhs (.and (srt res) [rhs, ens]))) attrs

/-- `equationAx` is `equationAt` at the plain application of `f` to the formal arguments. -/
theorem equationAx_eq_at (f : String) (args : List String) (res : String) (prem rhs ens : Kore.Pattern)
    (attrs : List Kore.AppPattern) :
    equationAx f args res prem rhs ens attrs =
      equationAt (ap f (vars (numbered "X" 0 args))) res prem rhs ens attrs := rfl

/-- A variable as `emit` writes it: the presentation's name, the core's sort. -/
structure Var where
  name : String
  sort : String
  deriving Repr, Inhabited

def Var.kore (v : Var) : Kore.EVar := evar ("Var" ++ v.name) (srt v.sort)

/-- The variables of a clause or rule: the core's sorts named by the presentation. -/
def varList (sorts names : List String) : List Var := (withPres sorts names).map fun (s, n) => ⟨n, s⟩

def varAt (vs : List Var) (i : Nat) : Kore.Pattern := .var (.evar (vs.getD i default).kore)

def isLabel (X : String) : String := "Lblis" ++ X
def projLabel (X : String) : String := "Lblproject'Coln'" ++ X

/-- `kseq(inj{X,KItem}(x), dotk)`: the K sequence holding one item of sort X. -/
def asK (X : String) (x : Kore.Pattern) : Kore.Pattern := kseq1 (injP X "KItem" x)

end KoreAML
