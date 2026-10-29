import Lake
open Lake DSL

/-- Noninterference up to disclosure for the fixture `contract`, a contract with private state,
and its security checker, the fixture `contractsec`. -/
package «ContractNI» where
  leanOptions := #[⟨`autoImplicit, false⟩]

require k2lean from "../../lean"
require «Contract» from "../../generated/contract"
require «ContractSec» from "../../generated/contractsec"

@[default_target]
lean_lib ContractNI
