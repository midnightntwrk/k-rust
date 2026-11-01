import Handoff.Functions

/-! The instance of `handoff`'s parameters the witnesses run at, by hand. -/

namespace HandoffRaceConf

/-- A running sum: a segment adds the resumed value to the process's state, and outputs the new
state. It is computable, so the elaborator's search and the kernel run it. -/
def sum : Handoff.Hooks where
  «fn.next(_,_)_HANDOFF_Int_Int_Int» S V := some (S + V)
  «fn.out(_,_)_HANDOFF_Int_Int_Int» S V := some (S + V)

end HandoffRaceConf
