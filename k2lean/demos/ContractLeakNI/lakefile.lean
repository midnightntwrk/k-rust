import Lake
open Lake DSL

/-- Noninterference up to disclosure for the fixture `contract` refuted by two runs, under a
checker that misses a flow (`tests/contractsec-leaky.py`). -/
package «ContractLeakNI» where
  leanOptions := #[⟨`autoImplicit, false⟩]

require k2lean from "../../lean"
require «Contract» from "../../generated/contract"
require «ContractSecLeak» from "../../generated/contractsecleak"

@[default_target]
lean_lib ContractLeakNI
