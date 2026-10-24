import ImpWrites.Invariant
import KImp.Preserves
import KPrelude.InvTactic
import KPrelude.InvColl

/-! Every rule of kimp keeps `Invariant x`, by `k2l_preserve`'s closers alone. -/

namespace ImpWrites

open KPrelude

namespace hand

-- k2lean new-invariant --from-log: new hand cases go above this line
end hand

/-- Every rule of kimp keeps `Invariant x`. -/
theorem preserved (x : KImp.SortId) : Preserved KImp.Step (Invariant x) := by
  k2l_preserve [kOf, kContent, envOf, envContent, writesK, writesI, writesS] hand ImpWrites.hand

end ImpWrites
