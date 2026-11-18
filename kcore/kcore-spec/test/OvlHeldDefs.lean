/-
  `Semantics.ovlHeld` (KcoreSpec/FaithOK.lean), `Cond.conjuncts` and `memHeld`
  (KcoreSpec/OvlHeldDefs.lean) at data.
  Run from the package root: `lake env lean -j1 test/OvlHeldDefs.lean`. Kernel-checked
  (`decide +kernel`).

  The semantics is the reader's for `f2-examples/ovlsub.kompile.kore` (`ovlsub.k`): `capGas`
  overloads the constructor `capN`, N < Gas, Gas has the value `inf` outside N.
  - `ovlHeld`: `capGas` passes by the empty `all` (its closure holds no function); a symbol that
    overloads none fails. `cFn A`: the same with a function `fI : A -> Gas` added to `capGas`'s
    overloads; `capGas` passes at A := Bool (confined) and fails at A := Int (not confined).
  - `Cond.conjuncts`: a nested `and` flattens, left to right; any other condition is its own one
    conjunct.
  - `memHeld`, at the cut `V ∈ t` with V the variable 2: held where t holds the variable under a
    constructor (`capN(G)`), also as a conjunct of an `and`; not held under `or` or `not`, not where
    V is not bound, not for a variable t does not hold. At `V ∈ capGas(G)` the variable
    is held: `capGas` is `ovlHeld`, so `holds` names it.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

open KCore

namespace OvlHeldDefs

definition_of defn from "f2-examples/ovlsub.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem

def capN : Sym := 387
def inf : Sym := 389
def run : Sym := 390
def capGas : Sym := 394
def gasS : Srt := 32
def nS : Srt := 33

theorem names_ok : c.symName capN = "LblcapN" ∧ c.symName capGas = "LblcapGas" ∧ c.symName run = "Lblrun" ∧
    c.sortName gasS = "Gas" ∧ c.sortName nS = "N" ∧ c.isCtor capN = true ∧ c.isOvl capGas = true := by
  decide +kernel

/-! ## `ovlHeld` -/

/-- `capGas` is an ordinary overloading symbol: its closure holds `capN` and no function, so it is
`ovlHeld` by the empty `all`. `run`, a constructor, overloads nothing and is not. -/
theorem ovlHeld_ordinary : c.ovlClosure capGas = [capGas, capN] ∧ c.fnOverloads capGas = [] ∧
    c.ovlHeld capGas = true ∧ c.ovlHeld run = false ∧ c.ovlHeld capN = false := by
  decide +kernel

/-- A function `fI : A -> Gas` among `capGas`'s overloads. -/
def fI : Sym := 5000
noncomputable def cFn (A : Srt) : Semantics :=
  { c with ovls := [⟨⟨capGas, [gasS], gasS⟩, [capN, fI]⟩],
           fns := c.fns ++ [{ label := fI, args := [A], result := gasS, clauses := [] }] }

/-- The function overload's argument sort decides: Bool is confined, Int is not. -/
theorem ovlHeld_fn : ((cFn Srt.bool).fnOverloads capGas).map (·.label) = [fI] ∧
    (cFn Srt.bool).confined Srt.bool = true ∧ (cFn Srt.bool).ovlHeld capGas = true ∧
    (cFn Srt.int).confined Srt.int = false ∧ (cFn Srt.int).ovlHeld capGas = false := by
  decide +kernel

/-! ## `Cond.conjuncts` -/

example (a b d : Cond) : (Cond.and (.and a b) d).conjuncts = a.conjuncts ++ b.conjuncts ++ d.conjuncts := rfl
example : (Cond.and (.and .top (.ceil gasS (.var 0))) (.or .top .bot)).conjuncts =
    [.top, .ceil gasS (.var 0), .or .top .bot] := rfl
example (p q : Cond) : (Cond.or p q).conjuncts = [.or p q] ∧ (Cond.not p).conjuncts = [.not p] := ⟨rfl, rfl⟩

/-! ## `memHeld` -/

/-- `V ∈ capN(G)`, G the variable 0, V the variable 2. -/
def cutN : Cond := .mem nS (.var 2) (.app capN [.var 0])
/-- `V ∈ capGas(G)`. -/
def cutGas : Cond := .mem gasS (.var 2) (.app capGas [.var 0])

theorem memHeld_rows :
    memHeld c [2] cutN 0 = true ∧ memHeld c [2] (.and (.ceil nS (.var 2)) cutN) 0 = true ∧
    memHeld c [2] cutN 1 = false ∧
    memHeld c [2] (.or cutN .top) 0 = false ∧ memHeld c [2] (.not cutN) 0 = false ∧
    memHeld c [1] cutN 0 = false ∧
    heldOccs c (.app capGas [.var 0]) = [0] ∧ memHeld c [2] cutGas 0 = true := by
  decide +kernel

end OvlHeldDefs
