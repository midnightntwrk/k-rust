import Lake
open Lake DSL

/-- Noninterference up to disclosure for the fixture `contract` with its store an input
(`tests/contract-env.py`), the two runs' stores related by `lowEq G`, and the fixture's security
checker `contractsec`. -/
package «ContractEnvNI» where
  leanOptions := #[⟨`autoImplicit, false⟩]

require k2lean from "../../lean"
require «ContractEnv» from "../../generated/contractenv"
require «ContractSec» from "../../generated/contractsec"

@[default_target]
lean_lib ContractEnvNI
