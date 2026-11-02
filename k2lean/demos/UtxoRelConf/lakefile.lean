import Lake
open Lake DSL

/-- The fixture `utxo` with the last creator of an output and a log of the outputs created and spent,
cells no rule reads (`tests/utxo-relaxed.py`): steps of two processes join generically modulo `<last>`
not compared and `<log>` up to order (`--equiv`), two creations or spends at two keys of the ledger
commuting (relaxed cells in the views' classes). -/
package «UtxoRelConf» where
  leanOptions := #[⟨`autoImplicit, false⟩]

require k2lean from "../../lean"
require «UtxoRel» from "../../generated/utxorel"

@[default_target]
lean_lib UtxoRelConf
