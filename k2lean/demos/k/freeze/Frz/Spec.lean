/-! The specification of the freeze fixture (CT-3): two recursive functions, one by well-founded
recursion with a measure and a decreasing proof. -/

namespace Frz

def f : Nat → Nat
  | 0 => 0
  | n + 1 => f n + 2

def g (n : Nat) : Nat := if h : n = 0 then 0 else g (n - 1) + 1
termination_by n
decreasing_by omega

end Frz
