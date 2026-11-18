/-
  A clause's variables range over their sorts: `pred` is declared on `Nat`, and at a term that is
  not a `Nat` it has no value. At the Int literal 0 (not `s(_)`), neither of `pred`'s clauses
  applies: `pred(s(N))` does not match a literal, and the catch-all `pred(N)` asks `N` to have sort
  `Nat`. Checked over peano's generated package, from kcore-spec:
      LEAN_PATH=examples/peano/.lake/build/lib/lean:$(lake env printenv LEAN_PATH) lean test/PredSorted.lean
-/
import Peano

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace Peano

open KCore

private theorem lfPred : c.lookupFn Sym.«pred» = some (c.fns[0]'(by decide +kernel)) := rfl

/-- `pred` has no value at a term that is not a `Nat`. -/
theorem pred_no_value_off_nat : ¬ ∃ r, Eval c Sym.«pred» [.dv KCore.Srt.int (.int 0)] (some r) := by
  rintro ⟨r, hz⟩
  cases hz with
  | clauseEx hfn hmem _ _ _ _ _ hne =>
    rw [lfPred] at hfn
    cases hfn
    exact absurd ((by decide +kernel : ∀ cl ∈ (c.fns[0]'(by decide +kernel)).clauses, cl.exs = []) _ hmem) hne
  | clause hfn hmem hσ hmatch hreq _ hprio _ hrhs =>
    rw [lfPred] at hfn
    cases hfn
    rcases List.mem_cons.mp hmem with rfl | hmem
    · cases hmatch with
      | cons h _ => cases h with
        | hook hp _ _ => exact absurd hp (by decide)
        | coll hc _ _ _ => exact absurd hc (by decide)
        | ovl _ ho _ _ => exact absurd ho (by decide)
    · rw [List.mem_singleton.mp hmem] at hσ hmatch
      cases hmatch with
      | cons h _ => cases h with
        | var hl =>
          obtain ⟨v, hv, hs⟩ := hσ 0 _ rfl
          rw [hl] at hv; cases hv
          exact absurd hs (by decide)

#print axioms pred_no_value_off_nat

end Peano
