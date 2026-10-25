import Race.Preserves
import KPrelude.Scaffold

/-! The hand module of `RaceConf`: the program hypothesis `H` of the confluence statement. Every
pair of steps of the fixture `race` joins without one (the generated `Confluence.lean` proves
all of them), so `H` is `True`. -/

namespace RaceConf

open KPrelude

def H (_ : Race.SortGeneratedTopCell) : Prop := True

theorem H.preserved : Preserved Race.Step H := fun _ _ _ _ => trivial

end RaceConf
