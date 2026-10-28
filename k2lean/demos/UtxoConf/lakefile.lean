import Lake
open Lake DSL

/-- The fixture `utxo` (coroutines in a cell map over a UTXO ledger): steps of two processes join
generically, given the joins left open (`k2lean confluence --threads procs`). -/
package «UtxoConf» where
  leanOptions := #[⟨`autoImplicit, false⟩]

require k2lean from "../../lean"
require «Utxo» from "../../generated/utxo"

@[default_target]
lean_lib UtxoConf
