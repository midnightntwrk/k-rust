/-
  `readsConfined` reads the binders of a rule's predicates. Run from the package root:
  `lake env lean test/ReadsBinders.lean`. Kernel-checked.

  The rule `<k> X:Int ~> Rest </k> <generatedCounter> N </generatedCounter> => <k> Rest </k>
  <generatedCounter> N </generatedCounter>`, X the key of `N +Int 1`, beside a rule of priority 200
  on every configuration. With `pre := X ∈ N +Int 1` (`cM`) or `pre := (0 <=Int N) = true ∧
  X ∈ N +Int 1` (`cC`), a conjunction of `\in` and `\equals` atoms whose variables the left side
  binds (`opens = []`), the definition reads no confined sort and its theory is `Γ`
  (`readsM`, `readsC`, `ΓcM`, `ΓcC`). With `pre := ∃ Y:Int. Y ∈ N +Int 1` (`cE`), a binder, it reads
  one (`readsE`).
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 100000

namespace KCore

namespace ReadsBindersTest

open GroundTerm Faithful
open Faithful.UndefRhsWitness (kIds cellSorts cellCtors cellSubsorts)

def lhsK : Term :=
  .app topLabel [.app kIds.label [.app kseq [.inj Srt.int Srt.kitem (.var 2), .var 0]], .app counterLabel [.var 1]]
def rhsK : Term := .app topLabel [.app kIds.label [.var 0], .app counterLabel [.var 1]]
/-- `N +Int 1` -/
def fN : Term := .app intAdd [.var 1, .dv Srt.int (.int 1)]

/-- `pre := X ∈ N +Int 1` -/
def kcMem : Rule :=
  { vars := [Srt.k, Srt.int, Srt.int], lhs := lhsK, req := none, rhs := rhsK, ens := none, prio := 50,
    pre := .mem Srt.int (.var 2) fN }

/-- `pre := (0 <=Int N) = true ∧ X ∈ N +Int 1` -/
def kcConj : Rule :=
  { kcMem with
    pre := .and (.equals Srt.bool (.app intLe [.dv Srt.int (.int 0), .var 1]) (.dv Srt.bool (.bool true)))
      (.mem Srt.int (.var 2) fN) }

/-- `pre := ∃ Y:Int. Y ∈ N +Int 1`, the bound variable the index after the rule's three. -/
def kcEx : Rule :=
  { kcMem with pre := .ex Srt.int (.mem Srt.int (.var 3) fN) }

/-- `<k> K </k> <generatedCounter> N </generatedCounter> => <k> K </k> <generatedCounter> 7 </generatedCounter>` -/
def r200 : Rule :=
  { vars := [Srt.k, Srt.int], lhs := .app topLabel [.app kIds.label [.var 0], .app counterLabel [.var 1]],
    req := none, rhs := .app topLabel [.app kIds.label [.var 0], .app counterLabel [.dv Srt.int (.int 7)]],
    ens := none, prio := 200 }

def base : Semantics :=
  { lib := { sortsBelowKItem := [Srt.int] }
    sortNames := ["KCell", "KCellOpt"]
    symNames := ["LblisKCell", "LblisKCellOpt", "Lbl'-LT-'k'-GT-'", "LblnoKCell"]
    userSorts := cellSorts
    ctors := cellCtors
    fns := []
    userSubsorts := cellSubsorts
    pgmSort := Srt.k
    rules := [] }

def cM : Semantics := { base with rules := [kcMem, r200] }
def cC : Semantics := { base with rules := [kcConj, r200] }
def cE : Semantics := { base with rules := [kcEx, r200] }

theorem coreM : cM.coreOK = true := by decide_cheap

theorem coreC : cC.coreOK = true := by decide_cheap

/-- The rules' predicates are well sorted, their left sides bind every variable, and the
definitions are accepted by `coreOK` (`coreM`, `coreC`, conjunct by conjunct). -/
theorem facts : cM.coreOK = true ∧ cC.coreOK = true ∧ kcMem.opens = [] ∧ kcConj.opens = [] ∧
    kcMem.pre.isTop = false ∧ kcConj.pre.isTop = false ∧ kcMem.pre.hasBinder = false ∧
    kcConj.pre.hasBinder = false ∧ kcEx.pre.hasBinder = true :=
  ⟨coreM, coreC, by decide +kernel⟩

/-- **A `pre` of atoms over bound variables reads no confined sort.** -/
theorem readsM : cM.readsConfined = false := by decide +kernel
theorem readsC : cC.readsConfined = false := by decide +kernel

/-- **So the theory is `Γ`.** -/
theorem ΓcM : Γc cM = Γ cM := Γc_plain readsM
theorem ΓcC : Γc cC = Γ cC := Γc_plain readsC

/-- **A `pre` with a binder reads one.** -/
theorem readsE : cE.readsConfined = true := by decide +kernel

end ReadsBindersTest

end KCore

#print axioms KCore.ReadsBindersTest.coreM
#print axioms KCore.ReadsBindersTest.coreC
#print axioms KCore.ReadsBindersTest.facts
#print axioms KCore.ReadsBindersTest.readsM
#print axioms KCore.ReadsBindersTest.readsC
#print axioms KCore.ReadsBindersTest.ΓcM
#print axioms KCore.ReadsBindersTest.ΓcC
#print axioms KCore.ReadsBindersTest.readsE
