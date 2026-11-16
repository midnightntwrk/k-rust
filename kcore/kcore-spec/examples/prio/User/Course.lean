/-
  The facts the course derives on prio (`f2-examples/prio.k`), as theorems over the generated
  package: `go(d)` steps to `out(d)` by the rule of priority 40; `go(b)` steps to `other(b)` by
  the rule of priority 50, since the rule of priority 40 does not apply to it (`b` is not a `D`);
  and `go(d)` does not step to `other(d)`: the rule of priority 50 matches `go(d)`, but the rule of
  priority 40 applies and blocks it.
-/
import User.Cert

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace Prio.CertTest

open KCore Prio

/-- `go(b)` and `other(b)`; b of sort B. -/
def goB : GroundTerm := .ctor Sym.«go» [.ctor Sym.«b» []]
def otherB : GroundTerm := .ctor Sym.«other» [.ctor Sym.«b» []]

/-- The configurations: each item alone in the k cell, the counter at 0. -/
def goDcfg : Config c := ⟨pcfg goD, sortOf_of_T T_eq (by decide +kernel)⟩
def outDcfg : Config c := ⟨pcfg outD, sortOf_of_T T_eq (by decide +kernel)⟩
def otherDcfg : Config c := ⟨pcfg otherD, sortOf_of_T T_eq (by decide +kernel)⟩
def goBcfg : Config c := ⟨pcfg goB, sortOf_of_T T_eq (by decide +kernel)⟩
def otherBcfg : Config c := ⟨pcfg otherB, sortOf_of_T T_eq (by decide +kernel)⟩

/-- A rule the matcher finds no well-sorted match of at x does not apply to x. -/
theorem notApplies_of {r : Rule} (hr : r ∈ c.rules) {x : GroundTerm}
    (h : ((Exec.matchP c (Exec.patFuel [r.lhs]) [] r.lhs x).filter (Exec.wellSorted c r.vars)).isEmpty = true) :
    NotApplies c r x := fun _ hσ hm => by
  obtain ⟨_, hm₀, _⟩ := Exec.rule_match_complete ok matchReady hr
    (Rule.wellSorted_of_at (Semantics.ok_rule ok hr).2.2.2 hσ) hm
  rw [List.isEmpty_iff.mp h] at hm₀
  cases hm₀

/-- No rule has a priority below 40. -/
private theorem rule_prios : ∀ r ∈ c.rules, ¬ r.prio < 40 := by decide +kernel

/-- **`go(d)` steps to `out(d)`**, by the rule `go(X:D) => out(X)` of priority 40 under X ↦ d,
the rest of the k cell ↦ `.K`, the counter cell ↦ 0; no rule has a smaller priority. -/
theorem step_goD : Step c goDcfg outDcfg :=
  .rule _ (List.mem_of_getElem? rule0) [(0, .ctor Sym.«d» []), (1, .ctor dotk []), (2, ctr0)]
    (Exec.wellSorted_iff.mp (by decide +kernel))
    (.ctor rfl (.cons (.ctor rfl (.cons (.ctor rfl (.cons
      (.ctor rfl (.cons (.inj (w := .ctor Sym.«d» []) (.var rfl)) .nil))
      (.cons (.var rfl) .nil))) .nil)) (.cons (.var rfl) .nil)))
    (fun _ h => nomatch h) .top
    (.ctor rfl (.cons (.ctor rfl (.cons (.ctor rfl (.cons
      (.ctor rfl (.cons (.inj .var) .nil))
      (.cons .var .nil))) .nil)) (.cons .var .nil)))
    (fun _ h => nomatch h) .top (fun r hr hlt => absurd hlt (rule_prios r hr))

/-- The rule of priority 40 is the only rule of a priority below 50, and it does not apply to
`go(b)`: no well-sorted substitution makes its left side denote it, since `b` is not a `D`. -/
private theorem below50_goB : ∀ r ∈ c.rules, r.prio < 50 →
    ((Exec.matchP c (Exec.patFuel [r.lhs]) [] r.lhs (pcfg goB)).filter (Exec.wellSorted c r.vars)).isEmpty = true := by
  decide +kernel

/-- **`go(b)` steps to `other(b)`**, by the rule `go(X:B) => other(X)` of priority 50 under
X ↦ b: the rule of priority 40 does not apply to `go(b)`. -/
theorem step_goB : Step c goBcfg otherBcfg :=
  .rule _ (List.mem_of_getElem? rule1) [(0, .ctor Sym.«b» []), (1, .ctor dotk []), (2, ctr0)]
    (Exec.wellSorted_iff.mp (by decide +kernel))
    (.ctor rfl (.cons (.ctor rfl (.cons (.ctor rfl (.cons
      (.ctor rfl (.cons (.var rfl) .nil))
      (.cons (.var rfl) .nil))) .nil)) (.cons (.var rfl) .nil)))
    (fun _ h => nomatch h) .top
    (.ctor rfl (.cons (.ctor rfl (.cons (.ctor rfl (.cons
      (.ctor rfl (.cons .var .nil))
      (.cons .var .nil))) .nil)) (.cons .var .nil)))
    (fun _ h => nomatch h) .top (fun r hr hlt => notApplies_of hr (below50_goB r hr hlt))

/-- The left side of the rule of priority 50, `go(X:B)`, denotes `go(d)` under X ↦ d (as a `B`). -/
theorem rule1_matches_goD : PatVal c [(0, .inj Srt.«D» Srt.«B» (.ctor Sym.«d» [])), (1, .ctor dotk []), (2, ctr0)]
    (.app KCore.topLabel [(.app Prio.Sym.«<k>» [(.app KCore.kseq [(.app Prio.Sym.«go» [(.var 0)]), (.var 1)])]), (.var 2)])
    (pcfg goD) :=
  .ctor rfl (.cons (.ctor rfl (.cons (.ctor rfl (.cons
    (.ctor rfl (.cons (.var rfl) .nil))
    (.cons (.var rfl) .nil))) .nil)) (.cons (.var rfl) .nil))

/-- **`go(d)` does not step to `other(d)`**: its one step is to `out(d)` (prio is deterministic),
the rule of priority 40 blocking the rule of priority 50, which matches (`rule1_matches_goD`). -/
theorem not_step_goD_otherD : ¬ Step c goDcfg otherDcfg := fun h =>
  absurd (Exec.same_iff.mpr (congrArg Subtype.val (deterministic c.hooks h step_goD))) (by decide +kernel)

#eval show Lean.CoreM Unit from do
  for n in [``notApplies_of, ``step_goD, ``step_goB, ``rule1_matches_goD, ``not_step_goD_otherD] do
    let axs ← Lean.collectAxioms n
    unless axs.all ([``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "{n}: axioms {axs}"

end Prio.CertTest
