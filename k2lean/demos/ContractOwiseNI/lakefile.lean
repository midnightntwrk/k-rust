import Lake
open Lake DSL

/-- ContractNI with priority ranks: noninterference up to disclosure for the fixture `contract`
with `owise` rules (`tests/contract-owise.py`), and its security checker, the fixture
`contractsec`. -/
package «ContractOwiseNI» where
  leanOptions := #[⟨`autoImplicit, false⟩]

require k2lean from "../../lean"
require «ContractOw» from "../../generated/contractow"
require «ContractSec» from "../../generated/contractsec"

@[default_target]
lean_lib ContractOwiseNI
