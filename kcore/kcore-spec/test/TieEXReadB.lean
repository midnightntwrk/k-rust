/-
  The readings of an equation with `\exists` over one Bool variable on its right side, from the
  decision `exReadB` (KcoreSpec/TieEXReadB.lean), on fixture `e3-eq-exists-bool-ml`
  (test/constructs/fixtures): its sentence `rule f(X) => #Exists B:Bool. (B #And {B #Equals notBool X})`
  with f `total`. Run from the package root: `lake env lean -j1 test/TieEXReadB.lean`.

  - `c`, `ax`: f with the clauses `Parse.exRead` reads of the equation (`exRead_eq`, kernel), and
    the sentence as kore.txt writes it, written with the builders of Kore/Build.lean.
  - `exReadB_eq` (kernel): the decision, over the sentence's table and the table of `Γ`'s items.
    The body's term is B and its predicate `B = notBool(X)` (`body_split`).
  - `facts`: the six readings `TieEX`'s lemmas take, in a model with `NodeFacts` and
    `TermsInSort`; `readings`: `TieFR.Readings` of the split, with `boolClosed`.
  - `UA`: the decision on the body `g(B ∧ (B = X))` of fixture `e3-eq-exists-ml-under-app`, the
    right side `Parse.exEqn?` gives of `f(X) => g(#Exists B:Bool. (B #And {B #Equals X}))`: the
    predicate stands under the application of g, the body's term is `g(B)`.
-/
import KcoreSpec.TieEXReadB

set_option autoImplicit false
set_option maxRecDepth 100000

namespace KCore.TieEXReadBTest

open ML KoreAML KoreAML.TieFR KCore.TieEX KCore.TieEXReadB
open Faithful.UndefRhsWitness (cellSorts cellCtors cellSubsorts)

def Fs : Sym := nRegSyms + 4
def Gs : Sym := nRegSyms + 5
def litT (b : Bool) : Term := .dv Srt.bool (.bool b)
def bS : Kore.KSort := srt "Bool"
def Xp : Kore.Pattern := ev "VarX" bS
def Bp : Kore.Pattern := ev "VarB" bS
def vsF : List KoreAML.Var := [⟨"X", "Bool"⟩]
def Bv : KoreAML.Var := ⟨"B", "Bool"⟩
/-- The table of `Γ`'s items for f: R, the argument, the clause's variable and the binder. -/
def tblG : VarTable := [.sortVar "R", .evar "X0" bS, .evar "VarV0" bS, .evar "VarV1" bS]

/-- The sentence `X0 ∈ VarX → f(X0) = rhs ∧ ⊤`. -/
def axOf (rhs : Kore.Pattern) : Kore.Axiom :=
  { sortVars := [Rv]
    pattern := .implies R
      (.and R [.top R, .and R [.in bS R (ev "X0" bS) Xp, .top R]])
      (.equals bS R (ap "Lblf" [ev "X0" bS]) (.and bS [rhs, .top bS]))
    attributes := [] }

/-! ## `e3-eq-exists-bool-ml` -/

def notX : Term := .app boolNot [.var 0]
/-- The alternative of the instance at the literal b: the term b, with `b = notBool(X)`. -/
def xLit (b : Bool) : Term × List Cond := (litT b, [.equals Srt.bool (litT b) notX])
/-- The alternative of the body with B the variable at index 1: B, with `B = notBool(X)`. -/
def jB : Term × List Cond := (.var 1, [.equals Srt.bool (.var 1) notX])

def fFn : Fn := ⟨Fs, [Srt.bool], Srt.bool,
  Parse.exClauses Srt.bool [Srt.bool] [.var 0] none 50 false [xLit true, xLit false] [jB], true⟩

def c : Semantics :=
  { lib := {}
    sortNames := ["KCell", "KCellOpt"]
    symNames := ["LblisKCell", "LblisKCellOpt", "Lbl'-LT-'k'-GT-'", "LblnoKCell", "Lblf"]
    userSorts := cellSorts
    ctors := cellCtors
    fns := [fFn]
    userSubsorts := cellSubsorts
    pgmSort := Srt.k
    rules := [] }

def NT : Parse.Names :=
  { sorts := ["KCell", "KCellOpt"]
    syms := ["LblisKCell", "LblisKCellOpt", "Lbl'-LT-'k'-GT-'", "LblnoKCell", "Lblf"]
    keyFns := [(nRegSyms + 4, "Bool")]
    fnlSyms := [("Lblf", false)]
    boolLits := true }

/-- The binder's body `B ∧ (B = notBool(X))`. -/
def bodyK : Kore.Pattern := .and bS [Bp, .equals bS bS Bp (ap "LblnotBool'Unds'" [Xp])]
def ax : Kore.Axiom := axOf (.exist bS (evar "VarB" bS) bodyK)
def eqT : Parse.RawEqn := ⟨"Lblf", [Xp], none, none, .exist bS (evar "VarB" bS) bodyK, [], none, false⟩

/-- **The reader reads the equation as f's clauses** (kernel). -/
theorem exRead_eq : Parse.exRead NT eqT = .ok (some (fFn.clauses, vsF)) := by kernel_rfl

def tbl : VarTable := tableOf ax.sortVars ax.pattern
def ws : List P := guardsOf ax
def vsC : List KoreAML.Var := Faithful.canonVars c [Srt.bool]
def xB : EVar := tbl.ev (evarKey Bv.kore)

/-- The body's term and its `\equals`. -/
theorem body_split : bodyTerm bodyK = Bp ∧ bodyEqs bodyK = [(bS, Bp, ap "LblnotBool'Unds'" [Xp])] := by
  decide +kernel

/-- **The decision** (kernel). -/
theorem exReadB_eq : exReadB NT c tblG tbl [Srt.bool] vsF Bv Srt.bool bodyK (.top bS)
    (xLit true) (xLit false) jB = true := by decide +kernel

/-- The decision at the semantics with any hook parameters (kernel): the function of the hook
parameters is the constant `true`, no part of the decision reading them. -/
theorem exReadB_fun : (fun Hk : HookParams => exReadB NT (c.withHooks Hk) tblG tbl [Srt.bool] vsF Bv Srt.bool bodyK
    (.top bS) (xLit true) (xLit false) jB) = fun _ => true := by kernel_rfl

theorem exReadB_H (Hk : HookParams) : exReadB NT (c.withHooks Hk) tblG tbl [Srt.bool] vsF Bv Srt.bool bodyK
    (.top bS) (xLit true) (xLit false) jB = true := congrFun exReadB_fun Hk

/-- An alternative that is not the body's: the instance at `true` with the term `false`. -/
example : exReadB NT c tblG tbl [Srt.bool] vsF Bv Srt.bool bodyK (.top bS)
    (litT false, [.equals Srt.bool (litT true) notX]) (xLit false) jB = false := by decide +kernel

/-- The other decisions `exFacts_of_exB` takes (kernel): the sorts of the variables read, the guards
holding each in its sort and R's variable a sort, and the result sort's name. -/
theorem lit_facts : Parse.varSorts NT vsF = .ok [Srt.bool] ∧ TieFRVars.guardsHold ws tbl vsF = true ∧
    sortGuard (tblG.ev (sortVarKey Rv)) ∈ ws ∧ trSort tblG (srtOf c Srt.bool) = TieFRRead.boolP :=
  ⟨by kernel_rfl, by decide +kernel, by decide +kernel, by decide +kernel⟩

section
variable {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}

/-- **The readings**, in a model with `NodeFacts c I` and `TermsInSort c I`. -/
theorem facts (Fc : HoldsShape.NodeFacts c I) (hTS : Faithful.TermsInSort c I) :
    ∃ β, IsSort I β ∧ (∀ (e : Valuation M) a, (trSort tblG (srtOf c Srt.bool)).interpret I e a ↔ a = β) ∧
      ExFacts I c tblG vsC ws β (xsOfB (xLit true) (xLit false)) [jB] (tr ⟨tbl, []⟩ bodyK)
        (tr ⟨tbl, []⟩ (.top bS)) xB (CGof I c tblG vsC) (CGof I c tblG (vsBof c [Srt.bool])) := by
  obtain ⟨β, hβ, hβd⟩ := TieFRRead.boolDen_of Fc
  have hσ : ∀ (e : Valuation M) a, (trSort tblG (srtOf c Srt.bool)).interpret I e a ↔ a = β := fun e a => by
    rw [lit_facts.2.2.2]; exact hβd e a
  exact ⟨β, hβ, hσ, exFacts_of_exB Fc hTS rfl rfl (al := []) lit_facts.1 lit_facts.2.1 lit_facts.2.2.1 hσ hβ
    rfl rfl exReadB_eq⟩

/-- **The readings of the split** (`TieFR.Readings`), with `boolClosed`, at any premise. -/
theorem readings (Fc : HoldsShape.NodeFacts c I) (hTS : Faithful.TermsInSort c I)
    (hcl : I ⊧ᴵ Faithful.boolClosed c) (prem : P) :
    ∃ β, Readings I ws (tblG.ev (sortVarKey Rv)) β prem
      (sAnd (sExists xB TieFRRead.boolP (tr ⟨tbl, []⟩ bodyK)) (tr ⟨tbl, []⟩ (.top bS)))
      (xsOfB (xLit true) (xLit false) true ++ xsOfB (xLit true) (xLit false) false) (altPC c tblG vsC)
      (altGC (CGof I c tblG vsC)) (clauseQC c tblG vsC Srt.bool prem) (lastBQC c tblG vsC Srt.bool prem [jB]) := by
  obtain ⟨β, hβ, hσ, X⟩ := facts Fc hTS
  exact ⟨β, X.readings Fc hcl lit_facts.2.2.1 hσ hβ⟩

end

/-! ## The body of `e3-eq-exists-ml-under-app` -/

namespace UA

/-- The alternatives: at the literal b, `g(b)` with `b = X`; with B the variable at index 1,
`g(B)` with `B = X`. -/
def xLit (b : Bool) : Term × List Cond := (.app Gs [litT b], [.equals Srt.bool (litT b) (.var 0)])
def jB : Term × List Cond := (.app Gs [.var 1], [.equals Srt.bool (.var 1) (.var 0)])

def fFn : Fn := ⟨Fs, [Srt.bool], Srt.bool,
  Parse.exClauses Srt.bool [Srt.bool] [.var 0] none 50 false [xLit true, xLit false] [jB], true⟩
def gFn : Fn := ⟨Gs, [Srt.bool], Srt.bool,
  [⟨[Srt.bool], [.var 0], none, .app boolNot [.var 0], none, 50, false, [], .top, .top⟩], true⟩

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

def NT : Parse.Names :=
  { sorts := ["KCell", "KCellOpt"]
    syms := ["LblisKCell", "LblisKCellOpt", "Lbl'-LT-'k'-GT-'", "LblnoKCell", "Lblf", "Lblg"]
    keyFns := [(nRegSyms + 4, "Bool"), (nRegSyms + 5, "Bool")]
    fnlSyms := [("Lblf", false)]
    boolLits := true }

/-- The body under the binder at the top: `g(B ∧ (B = X))`. -/
def bodyK : Kore.Pattern := ap "Lblg" [.and bS [Bp, .equals bS bS Bp Xp]]
/-- The text's sentence, the `\exists` under g. -/
def ax : Kore.Axiom := axOf (ap "Lblg" [.exist bS (evar "VarB" bS) (.and bS [Bp, .equals bS bS Bp Xp])])
def eqT : Parse.RawEqn := ⟨"Lblf", [Xp], none, none, .exist bS (evar "VarB" bS) bodyK, [], none, false⟩
def tbl : VarTable := tableOf ax.sortVars ax.pattern

/-- **The reader reads the equation with the binder at the top as f's clauses** (kernel). -/
theorem exRead_eq : Parse.exRead NT eqT = .ok (some (fFn.clauses, vsF)) := by kernel_rfl

/-- The body's term is `g(B)`, its `\equals` `B = X`. -/
theorem body_split : bodyTerm bodyK = ap "Lblg" [Bp] ∧ bodyEqs bodyK = [(bS, Bp, Xp)] := by decide +kernel

/-- **The decision** (kernel), over the text's table. -/
theorem exReadB_eq : exReadB NT c tblG tbl [Srt.bool] vsF Bv Srt.bool bodyK (.top bS)
    (xLit true) (xLit false) jB = true := by decide +kernel

end UA

end KCore.TieEXReadBTest

#check @KCore.TieEXReadB.exFacts_of_exB
#check @KCore.TieEXReadB.ExFacts.readings
#check @KCore.TieEXReadB.bodySplit_sem
#check @KCore.TieEXReadB.interp_substEvar_one
#check @KCore.TieEXReadBTest.facts
#check @KCore.TieEXReadBTest.readings
/-- info: 'KCore.TieEXReadB.exFacts_of_exB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.TieEXReadB.exFacts_of_exB
/-- info: 'KCore.TieEXReadBTest.readings' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.TieEXReadBTest.readings
/-- info: 'KCore.TieEXReadBTest.UA.exReadB_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.TieEXReadBTest.UA.exReadB_eq
