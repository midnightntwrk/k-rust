/-
  `TightSem` of a right side from the decision `tightB` (KcoreSpec/TieFRTightB.lean), on fixture
  `e3-ml-eq-rhs-or-nest` (test/constructs/fixtures): the right side of its sentence 346,
  `(k(f(X) #Or g(X)) #Or #Bottom) #And {X *Int X >=Int 0 #Equals true}`, of the equation of h.
  Run from the package root: `lake env lean -j1 test/TieFRTightB.lean`.

  The operands `tightB` reads as terms of Int are `f(X)`, `g(X)` and the two alternatives
  `k(f(X))`, `k(g(X))` of `k(f(X) ∨ g(X))` (`ops_terms`); the `\or`, `\bottom` and the lifted
  conjunct state their sort at their head. `tight_guards` is `readings_of_frT`'s `hT` for this
  text, in a model with `NodeFacts` and `TermsInSort`; `tightB_H` is the decision at the semantics
  with any hook parameters.
-/
import KcoreSpec.TieFRTightB

set_option autoImplicit false
set_option maxRecDepth 100000

namespace KCore.TieFRTightBTest

open ML KoreAML KoreAML.TieFR KCore.TieFRRead KCore.TieFRTightB
open Faithful.UndefRhsWitness (cellSorts cellCtors cellSubsorts)

def F : Sym := nRegSyms + 4
def G : Sym := nRegSyms + 5
def K : Sym := nRegSyms + 6
def H : Sym := nRegSyms + 7
def kfX : Term := .app K [.app F [.var 0]]
def kgX : Term := .app K [.app G [.var 0]]
/-- `X *Int X >=Int 0`. -/
def bX : Term := .app intGe [.app intMul [.var 0, .var 0], .dv Srt.int (.int 0)]

def fFn : Fn := ⟨F, [Srt.int], Srt.int, [⟨[Srt.int], [.var 0], none, .var 0, none, 50, false, [], .top, .top⟩], true⟩
def gFn : Fn := ⟨G, [Srt.int], Srt.int,
  [⟨[Srt.int], [.var 0], none, .app intAdd [.var 0, .dv Srt.int (.int 0)], none, 50, false, [], .top, .top⟩], true⟩
def kFn : Fn := ⟨K, [Srt.int], Srt.int,
  [⟨[Srt.int], [.var 0], none, .app intAdd [.var 0, .dv Srt.int (.int 1)], none, 50, false, [], .top, .top⟩], true⟩
def xsC : List (Term × List Term) := [(kfX, [bX]), (kgX, [bX])]
def hFn : Fn := ⟨H, [Srt.int], Srt.int, Parse.frClauses Srt.int [Srt.int] [.var 0] none 50 false (frAltsOf xsC), true⟩

def c : Semantics :=
  { lib := {}
    sortNames := ["KCell", "KCellOpt"]
    symNames := ["LblisKCell", "LblisKCellOpt", "Lbl'-LT-'k'-GT-'", "LblnoKCell", "Lblf", "Lblg", "Lblk", "Lblh"]
    userSorts := cellSorts
    ctors := cellCtors
    fns := [fFn, gFn, kFn, hFn]
    userSubsorts := cellSubsorts
    pgmSort := Srt.k
    rules := [] }

def iS : Kore.KSort := srt "Int"
def bS : Kore.KSort := srt "Bool"
def xK : Kore.Pattern := ev "VarX" iS
def fK : Kore.Pattern := ap "Lblf" [xK]
def gK : Kore.Pattern := ap "Lblg" [xK]
/-- `k(f(X) ∨ g(X))`. -/
def kOr : Kore.Pattern := ap "Lblk" [.or iS [fK, gK]]
def bK : Kore.Pattern := ap "Lbl'Unds-GT-Eqls'Int'Unds'" [ap "Lbl'UndsStar'Int'Unds'" [xK, xK], .dv iS "0"]
def eqK : Kore.Pattern := .equals bS iS bK (.dv bS "true")
/-- The right side: `(k(f(X) ∨ g(X)) ∨ ⊥) ∧ {X *Int X >=Int 0 #Equals true}`. -/
def pT : Kore.Pattern := .and iS [.or iS [kOr, .bottom iS], eqK]

/-- Sentence 346: `X0 ∈ VarX → h(X0) = pT ∧ ⊤`. -/
def ax346 : Kore.Axiom :=
  { sortVars := [Rv]
    pattern := .implies R
      (.and R [.top R, .and R [.in iS R (ev "X0" iS) xK, .top R]])
      (.equals iS R (ap "Lblh" [ev "X0" iS]) (.and iS [pT, .top iS]))
    attributes := [] }

def NT : Parse.Names :=
  { sorts := ["KCell", "KCellOpt"]
    syms := ["LblisKCell", "LblisKCellOpt", "Lbl'-LT-'k'-GT-'", "LblnoKCell", "Lblf", "Lblg", "Lblk", "Lblh"]
    keyFns := [(nRegSyms + 4, "Int"), (nRegSyms + 5, "Int"), (nRegSyms + 6, "Int"), (nRegSyms + 7, "Int")]
    fnlSyms := [("Lblh", false)] }

/-- The text's table and guards, the table of `Γ`'s items for h, and the variables read. -/
def tbl : VarTable := tableOf ax346.sortVars ax346.pattern
def ws : List P := guardsOf ax346
def r : EVar := tbl.ev (sortVarKey Rv)
def tblG : VarTable := [.sortVar "R", .evar "X0" (srt "Int"), .evar "VarV0" (srt "Int")]
def vsF : List KoreAML.Var := [⟨"X", "Int"⟩]

/-- The equation as the reader takes it, read as h's clauses with the variables `vsF` (kernel). -/
def eqT : Parse.RawEqn := ⟨"Lblh", [xK], none, none, pT, [], none, false⟩
theorem frRead_eqT : Parse.frRead NT eqT = .ok (some (hFn.clauses, vsF)) := by kernel_rfl

/-- The operands the decision reads as terms: of the six operands of the right side's connectives,
`k(f(X) ∨ g(X))`, `f(X)` and `g(X)`; the first by its alternatives `k(f(X))`, `k(g(X))`. -/
theorem ops_terms : (connOps pT).filter (fun x => opLeaf x.2 && !opStatedK x.2) = [(iS, kOr), (iS, fK), (iS, gK)] ∧
    Parse.orAlts kOr = [ap "Lblk" [fK], ap "Lblk" [gK]] ∧ Parse.orAlts fK = [fK] := ⟨rfl, rfl, rfl⟩

/-- **The decision** (kernel): the right side is `tightB` over the variables read. -/
theorem tightB_pT : tightB NT c tblG tbl [Srt.int] vsF pT = true := by decide +kernel

/-- The decision at the semantics with any hook parameters: no part of it reads them. -/
theorem tightB_H (Hk : HookParams) : tightB NT (c.withHooks Hk) tblG tbl [Srt.int] vsF pT = true := tightB_pT

/-- The other decisions `tightSem_of_guardsB` takes (kernel): the sorts of the variables read, the
tables aligned on them, and the guards holding each in its sort. -/
theorem rt_facts : Parse.varSorts NT vsF = .ok [Srt.int] ∧ TermRT.alignOK c tblG tbl [Srt.int] vsF = true ∧
    TieFRVars.guardsHold ws tbl vsF = true :=
  ⟨by kernel_rfl, by decide +kernel, by decide +kernel⟩

/-- A right side with an operand of another sort than its connective's is not `tightB`:
`\or{Int}(f(X), true)`. -/
example : tightB NT c tblG tbl [Srt.int] vsF (.or iS [fK, .dv bS "true"]) = false := by decide +kernel

section
variable {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}

/-- **`TightSem` of the right side at the valuations of the guards**, from the decisions. -/
theorem tight_guards (Fc : HoldsShape.NodeFacts c I) (hTS : Faithful.TermsInSort c I) :
    ∀ e m, At I ws r e m → TightSem I tbl e pT :=
  tightSem_of_guardsB Fc hTS rfl rfl rt_facts.1 rt_facts.2.1 rt_facts.2.2 tightB_pT

end

end KCore.TieFRTightBTest

#check @KCore.TieFRTightB.tightSem_of_tightB
#check @KCore.TieFRTightB.tightSem_of_guardsB
#check @KCore.TieFRTightBTest.tight_guards
/-- info: 'KCore.TieFRTightB.tightSem_of_guardsB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.TieFRTightB.tightSem_of_guardsB
/-- info: 'KCore.TieFRTightBTest.tight_guards' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.TieFRTightBTest.tight_guards
