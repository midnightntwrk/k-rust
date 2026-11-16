/-
Copyright (c) 2022 Institute for Logic and Data Science (ILDS). All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Horațiu Cheval
-/

import MatchingLogic.Pattern 
import MatchingLogic.Substitution

set_option autoImplicit false 

namespace ML

def Premises (𝕊 : Type) : Type := Set $ Pattern 𝕊  

-- Upstream wrote `attribute [reducible] Premises in instance ...`; Lean then added the
-- attribute globally anyway (newer Lean rejects the misleading `in`), so it is global here.
attribute [reducible] Premises
instance {𝕊} : Membership (Pattern 𝕊) (Premises 𝕊) := inferInstance

namespace Premises 

variable {𝕊 : Type}

/-- Lifts a function on patterns to a function on sets of premises. -/
@[simp]
def map (f : Pattern 𝕊 → Pattern 𝕊) : Premises 𝕊 → Premises 𝕊 := Set.image f

