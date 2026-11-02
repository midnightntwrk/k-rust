import Lake
open Lake DSL

/-- Noninterference up to disclosure for the fixture `contract` with its values' leaves declared
below `KResult` (`KResult ::= Int | Bool`, `tests/contract-values.py`), and the fixture's security
checker `contractsec`. -/
package «ContractValsNI» where
  leanOptions := #[⟨`autoImplicit, false⟩]

require k2lean from "../../lean"
require «ContractVals» from "../../generated/contractvals"
require «ContractSec» from "../../generated/contractsec"

@[default_target]
lean_lib ContractValsNI
