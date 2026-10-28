import Measure.Diverges
import KPrelude.Tactic

/-! The proofs that K's rewriting of the least fixed points does not terminate (TERM-1).
Written once by k2lean and never overwritten: edit it. Each is `theorem F.diverges :
F.diverges.statement`, an infinite chain of pending calls (`KPrelude.Pending.chain_of_fixed`,
`chain_of_cycle`); `MeasureTest/Diverges.lean` checks it. A group with no proof here is open. The
groups when this file was written:
- `K.norm.diverges`
-/

namespace Measure

open KPrelude

end Measure
