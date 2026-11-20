/-
  The right side with its `\exists` moved out of an application (KcoreSpec/TieExHoistB.lean), on
  fixture `e3-eq-exists-ml-under-app` (test/constructs/fixtures): its sentence
  `rule f(X) => g(#Exists B:Bool. (B #And {B #Equals X}))`. Run from the package root:
  `lake env lean -j1 test/TieExHoistB.lean`.

  - `ax`: the sentence as kore.txt writes it, written with the builders of Kore/Build.lean; `eqUA`
    the equation as the reader takes it.
  - `exEqn_ua` (kernel): the reader (`Parse.exEqn?`) moves the binder to the top, giving the
    equation with the right side `rhs'`, `∃B:Bool. g(B ∧ (B = X))`.
  - `hoistB_ua` (kernel): the decision, between the text's right side and the reader's, over the
    sentence's table.
  - `text_shape`, `text_hoisted`: the translated sentence is `eqnPat` with the right side
    `tr rhs ∧ ⊤`, and holds in the models where `eqnPat` with `(∃B:Bool. tr (g(B ∧ (B = X)))) ∧ ⊤`
    does: the shape `TieEX`'s lemmas read (`TieEX.rhs_ex`).
-/
import KcoreSpec.TieExHoistB
import KcoreSpec.TieFRRead

set_option autoImplicit false
set_option maxRecDepth 100000

namespace KCore.TieExHoistBTest

open ML KoreAML KoreAML.TieFR KCore.TieExHoistB

def bS : Kore.KSort := srt "Bool"
def Xp : Kore.Pattern := ev "VarX" bS
def Bp : Kore.Pattern := ev "VarB" bS
/-- The binder's body `B ∧ (B = X)`. -/
def bodyP : Kore.Pattern := .and bS [Bp, .equals bS bS Bp Xp]
/-- The text's right side `g(∃B:Bool. (B ∧ (B = X)))`. -/
def rhs : Kore.Pattern := ap "Lblg" [.exist bS (evar "VarB" bS) bodyP]
/-- The body under the binder at the top: `g(B ∧ (B = X))`. -/
def bodyG : Kore.Pattern := ap "Lblg" [bodyP]

/-- The sentence: `X0 ∈ VarX → f(X0) = g(∃B:Bool. (B ∧ (B = X))) ∧ ⊤`. -/
def ax : Kore.Axiom :=
  { sortVars := [Rv]
    pattern := .implies R
      (.and R [.top R, .and R [.in bS R (ev "X0" bS) Xp, .top R]])
      (.equals bS R (ap "Lblf" [ev "X0" bS]) (.and bS [rhs, .top bS]))
    attributes := [] }

/-- f, g : Bool → Bool; f has its `functional` sentence; Bool has its literals only. -/
def NB : Parse.Names :=
  { sorts := []
    syms := ["LblisKCell", "LblisKCellOpt", "Lbl'-LT-'k'-GT-'", "LblnoKCell", "Lblf", "Lblg"]
    keyFns := [(nRegSyms + 4, "Bool"), (nRegSyms + 5, "Bool")]
    fnlSyms := [("Lblf", false)]
    boolLits := true }

def eqUA : Parse.RawEqn := ⟨"Lblf", [Xp], none, none, rhs, [], none, false⟩

/-- **The reader moves the binder to the top** (kernel): the equation it reads by cases has the
right side `∃B:Bool. g(B ∧ (B = X))`, the binder not renamed. -/
theorem exEqn_ua : Parse.exEqn? NB eqUA = some { eqUA with rhs := .exist bS (evar "VarB" bS) bodyG } := by
  kernel_rfl

def textItem : Item := trAxiom [] [] ⟨0, "E3-EQ-EXISTS-ML-UNDER-APP", ax⟩
def tbl : VarTable := tableOf ax.sortVars ax.pattern
def ctx : Ctx := ⟨tbl, []⟩
def ws : List P := guardsOf ax
def r : EVar := tbl.ev (sortVarKey Rv)
def prem : P := tr ctx (.and R [.top R, .and R [.in bS R (ev "X0" bS) Xp, .top R]])
def BoolP : P := trSort tbl bS
def Ff : P := tr ctx (ap "Lblf" [ev "X0" bS])
def xB : EVar := tbl.ev (evarKey (evar "VarB" bS))
def ensT : P := tr ctx (.top bS)

/-- **The decision** (kernel): the text's right side is `g[∃B. φ]`, B free in no side pattern of
the context, and the reader's is `∃B. g[φ]`. -/
theorem hoistB_ua : hoistB ctx rhs (.exist bS (evar "VarB" bS) bodyG) = true := by decide +kernel

/-- The context found is the application of g with the hole its one argument. -/
example : (exCtx? rhs).map (·.1) = some (.app ⟨⟨"Lblg"⟩⟩ [] [] .hole []) := rfl

/-- A side pattern that reads the binder's variable: `h(B, ∃B. B)` is not `∃B. h(B, B)`. -/
example : hoistB ctx (ap "Lblh" [Bp, .exist bS (evar "VarB" bS) Bp])
    (.exist bS (evar "VarB" bS) (ap "Lblh" [Bp, Bp])) = false := by decide +kernel

theorem text_shape : textItem.pat = eqnPat ws r prem BoolP Ff (sAnd (tr ctx rhs) ensT) :=
  trAxiom_eqnPat [] [] _ _ ax rfl rfl

/-- The reader's right side translates as `∃B:Bool. tr (g(B ∧ (B = X)))`. -/
theorem hoisted_shape : tr ctx (.exist bS (evar "VarB" bS) bodyG) =
    sExists xB TieFRRead.boolP (tr ctx bodyG) := by decide +kernel

section
variable {M : Type} {I : Interpretation KoreAML.Sym M}

/-- **The sentence holds where the sentence with the binder at the top of its right side does.** -/
theorem text_hoisted (hD : DefOK I) :
    (I ⊧ᴵ textItem.pat) ↔
      (I ⊧ᴵ eqnPat ws r prem BoolP Ff (sAnd (sExists xB TieFRRead.boolP (tr ctx bodyG)) ensT)) := by
  rw [text_shape, ← hoisted_shape]
  exact eqnPat_hoistB hD hoistB_ua

end

end KCore.TieExHoistBTest

#check @KCore.TieExHoistB.tr_hoistB
#check @KCore.TieExHoistB.eqnPat_hoistB
#check @KCore.TieExHoistBTest.text_hoisted
/-- info: 'KCore.TieExHoistB.eqnPat_hoistB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.TieExHoistB.eqnPat_hoistB
/-- info: 'KCore.TieExHoistBTest.text_hoisted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.TieExHoistBTest.text_hoisted
