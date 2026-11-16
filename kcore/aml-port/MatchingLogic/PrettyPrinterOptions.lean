/-
Copyright (c) 2022 Institute for Logic and Data Science (ILDS). All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Horațiu Cheval
-/

import Lean.Data.Options 

open Lean 

namespace ML

register_option Pattern.pp_interpret_hiding : Bool := {
  defValue := false
  descr := "Specifies whether to display `Pattern.interpret I e φ` simply as `∥φ∥` or not."
}
