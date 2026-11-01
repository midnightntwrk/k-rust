import Lake
open Lake DSL

/-- The transaction statement of the parameterized form: a script with one run to no task left ends
in that run's configuration in every order (the work measure, `gen --measure`, with TwoParamConf's
`terminal_unique`), for every semantics of the lower layer. -/
package «TwoParamTx» where
  leanOptions := #[⟨`autoImplicit, false⟩]

require k2lean from "../../lean"
require «TwoParam» from "../../generated/twoparam"
require «TwoParamConf» from "../TwoParamConf"

@[default_target]
lean_lib TwoParamTx
