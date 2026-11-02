import Lake
open Lake DSL

/-- Noninterference with every observed cell compared by equality and nothing released: the
fixture `contract`, its ledger, transcript and disclosed values observed, for a checker that
gives `disclose(E)` the level of `E` (`tests/contractsec-norelease.py`). -/
package «ContractObsNI» where
  leanOptions := #[⟨`autoImplicit, false⟩]

require k2lean from "../../lean"
require «Contract» from "../../generated/contract"
require «ContractSecNR» from "../../generated/contractsecnr"

@[default_target]
lean_lib ContractObsNI
