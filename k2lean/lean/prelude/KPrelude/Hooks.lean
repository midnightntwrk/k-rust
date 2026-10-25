/-!
# `INT`, `BOOL` and `KEQUAL` hooks

Each hook is a Lean definition with the meaning `domains.md` gives it. A hook that K leaves
undefined at some arguments returns `Option` and is `none` exactly there (`#Ceil` rules of
`domains.md`: `/Int`, `%Int`, `divInt`, `modInt` at divisor 0, `>>Int`/`<<Int` at a negative
shift, `^Int` at a negative exponent).

`/Int` and `%Int` truncate (`INT.tdiv`, `INT.tmod`); `divInt` and `modInt` are Euclidean
(`INT.ediv`, `INT.emod`). Lean's `/` and `%` on `Int` are `Int.ediv`/`Int.emod` and are total
(`x / 0 = 0`), so they are not used for `/Int` and `%Int`.

The `BOOL` connectives are total functions on `Bool`; the generator applies them to defined
operands only (matching logic: an operand that is `⊥` makes the whole application `⊥`).
-/

namespace KPrelude.IntHook

def add (a b : Int) : Int := a + b
def sub (a b : Int) : Int := a - b
def mul (a b : Int) : Int := a * b
def tdiv (a b : Int) : Option Int := if b = 0 then none else some (a.tdiv b)
def tmod (a b : Int) : Option Int := if b = 0 then none else some (a.tmod b)
def ediv (a b : Int) : Option Int := if b = 0 then none else some (a.ediv b)
def emod (a b : Int) : Option Int := if b = 0 then none else some (a.emod b)
def pow (a b : Int) : Option Int := if b < 0 then none else some (a ^ b.toNat)
def shl (a b : Int) : Option Int := if b < 0 then none else some (a <<< b.toNat)
def shr (a b : Int) : Option Int := if b < 0 then none else some (a >>> b.toNat)
def neg (a : Int) : Int := -a
def abs (a : Int) : Int := if a < 0 then -a else a
def min (a b : Int) : Int := if a ≤ b then a else b
def max (a b : Int) : Int := if a ≤ b then b else a
def lt (a b : Int) : Bool := decide (a < b)
def le (a b : Int) : Bool := decide (a ≤ b)
def gt (a b : Int) : Bool := decide (a > b)
def ge (a b : Int) : Bool := decide (a ≥ b)
def eq (a b : Int) : Bool := decide (a = b)
def ne (a b : Int) : Bool := decide (a ≠ b)

theorem tdiv_eq_some {a b r : Int} : tdiv a b = some r ↔ b ≠ 0 ∧ a.tdiv b = r := by
  unfold tdiv; split <;> simp_all

/-! Laws K states as equations or simplification rules of `domains.md` that need more than
unfolding (used by the generated equation proofs). -/

theorem emod_of_lt {x n : Int} (h₀ : 0 ≤ x) (h₁ : x < n) : emod x n = some x := by
  unfold emod; rw [ite_eq_right (by omega)]; exact congrArg some (Int.emod_eq_of_lt h₀ h₁)

theorem tmod_of_lt {x n : Int} (h₀ : 0 ≤ x) (h₁ : x < n) : tmod x n = some x := by
  unfold tmod; rw [ite_eq_right (by omega)]; exact congrArg some (Int.tmod_eq_of_lt h₀ h₁)

theorem int_emod_eq_of_lt {a b : Int} (h₀ : 0 ≤ a) (h₁ : a < b) : a.emod b = a := Int.emod_eq_of_lt h₀ h₁

theorem int_ediv_eq_tdiv_sub_emod (a b : Int) (h : b ≠ 0) : a.ediv b = (a - a.emod b).tdiv b := by
  have e : a - a.emod b = b * a.ediv b := by
    have := Int.emod_add_mul_ediv a b
    change a.emod b + b * a.ediv b = a at this
    omega
  rw [e, Int.mul_tdiv_cancel_left _ h]

/-- `I1 divInt I2 = (I1 -Int (I1 modInt I2)) /Int I2` (`domains.md`). -/
theorem ediv_eq_tdiv_sub_emod (a b : Int) (h : b ≠ 0) :
    ediv a b = (emod a b).bind fun r => tdiv (a - r) b := by
  unfold ediv emod tdiv
  simp only [ite_eq_right h, Option.bind_some, Option.some.injEq]
  have e : a - a.emod b = b * a.ediv b := by
    have := Int.emod_add_mul_ediv a b
    change a.emod b + b * a.ediv b = a at this
    omega
  rw [e, Int.mul_tdiv_cancel_left _ h]

end KPrelude.IntHook

namespace KPrelude.BoolHook

def not (a : Bool) : Bool := !a
def and (a b : Bool) : Bool := a && b
def or (a b : Bool) : Bool := a || b
def xor (a b : Bool) : Bool := a ^^ b
def implies (a b : Bool) : Bool := !a || b
def eq (a b : Bool) : Bool := a == b
def ne (a b : Bool) : Bool := a != b

end KPrelude.BoolHook

namespace KPrelude.KEqHook

/-- `==K`: equality of K terms. Faithful because generated term types are canonical. -/
def eq {α : Type} [DecidableEq α] (a b : α) : Bool := decide (a = b)
def ne {α : Type} [DecidableEq α] (a b : α) : Bool := !decide (a = b)
/-- `#if _ #then _ #else _ #fi` -/
def ite {α : Type} (c : Bool) (a b : α) : α := if c then a else b

end KPrelude.KEqHook
