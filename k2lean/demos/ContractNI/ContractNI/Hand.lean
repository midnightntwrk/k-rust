import ContractNI.Tr
import Contract.Preserves
import KPrelude.Scaffold

/-! The hand module of `ContractNI`: what the noninterference statement is about. A program is
`secure` at a labelling `G` of the local variables when the checker (the fixture contractsec)
accepts its translation; the locals' store (`<env>`) holds values (`Good`); two stores are `lowEq`
when they agree on the locals `G` labels `lo`; `HiOnly` is a store that changes only at the
others. -/

namespace ContractNI

open KPrelude

/-- The checker accepts the program at the labelling `G`. -/
def secure (G : ContractSec.SortMap) (P : Contract.SortStmt) : Prop :=
  ContractSec.K.«sec(_,_)_CONTRACTSEC_Bool_Stmt_Map» (tr_SortStmt P) G = some true

/-- A runtime value: what an assignment stores. -/
def isVal : Contract.SortKItem → Bool
  | .inj_Int _ => true
  | .inj_Bool _ => true
  | _ => false

/-- A store: canonical, and every identifier holds a value. -/
def Good (E : Contract.SortMap) : Prop :=
  MapHook.WF E ∧ ∀ X v, MapHook.lookup E (Contract.SortKItem.inj_Id X) = some v → isVal v = true

/-- `X` is labelled `lo`. -/
def Low (G : ContractSec.SortMap) (X : Contract.SortId) : Prop :=
  MapHook.lookup G (ContractSec.SortKItem.inj_Id (tr_SortId X)) = some (ContractSec.SortKItem.inj_Level .lo)

/-- Two stores that agree on the identifiers `G` labels `lo`. -/
def lowEq (G : ContractSec.SortMap) (E₁ E₂ : Contract.SortMap) : Prop :=
  Good E₁ ∧ Good E₂ ∧ ∀ X : Contract.SortId, Low G X →
    MapHook.lookup E₁ (Contract.SortKItem.inj_Id X) = MapHook.lookup E₂ (Contract.SortKItem.inj_Id X)

/-- The store changes only at high identifiers, and stays a store. -/
def HiOnly (G : ContractSec.SortMap) (E E' : Contract.SortMap) : Prop :=
  Good E' ∧ ∀ X, Low G X → MapHook.lookup E (Contract.SortKItem.inj_Id X) = MapHook.lookup E' (Contract.SortKItem.inj_Id X)

end ContractNI
