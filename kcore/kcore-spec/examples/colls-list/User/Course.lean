/-
  The facts the course derives on colls-list (`f2-examples/colls-list.k`): the stack cell's list
  patterns denote the list `[1, 2]`, read from the front by `pop` (`ListItem(X) L`, X ↦ 1,
  L ↦ [2]) and from the back by `drop` (`L ListItem(_)`, L ↦ [1], `_` ↦ 2). A list pattern
  symbol denotes the list its operation builds from the parts' values (`PatVal.coll`).
-/
import CollsList

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace CollsList.Course

open KCore CollsList

/-- An Int, and the same Int as a list element (injected into `KItem`). -/
def ival (n : Int) : GroundTerm := .dv KCore.Srt.int (.int n)
def iv (n : Int) : GroundTerm := .inj KCore.Srt.int KCore.Srt.kitem (ival n)
/-- A list of the library's `List` sort. -/
def list (es : List GroundTerm) : GroundTerm := .list KCore.Srt.list es

/-- `pop`'s left side: `pop` at the head of the k cell (the rest variable 0), the stack cell
holding `ListItem(X) L` (X variable 1, L variable 2), the sum cell S (variable 3), the counter
cell variable 4. -/
theorem pop_lhs : c.rules[1]?.map Rule.lhs = some
  (.app KCore.topLabel [.app Sym.«<k>» [.app KCore.kseq [.inj Srt.«Op» KCore.Srt.kitem (.app Sym.«pop» []), .var 0]],
    .app Sym.«<stack>» [.app KCore.listConcat [.app KCore.listElem [.inj KCore.Srt.int KCore.Srt.kitem (.var 1)], .var 2]],
    .app Sym.«<sum>» [.var 3], .var 4]) := by
  kernel_rfl

/-- `drop`'s left side: `drop` at the head of the k cell (the rest variable 0), the stack cell
holding `L ListItem(_)` (L variable 1, `_` variable 2), the sum cell variable 3, the counter cell
variable 4. -/
theorem drop_lhs : c.rules[2]?.map Rule.lhs = some
  (.app KCore.topLabel [.app Sym.«<k>» [.app KCore.kseq [.inj Srt.«Op» KCore.Srt.kitem (.app Sym.«drop» []), .var 0]],
    .app Sym.«<stack>» [.app KCore.listConcat [.var 1, .app KCore.listElem [.var 2]]],
    .var 3, .var 4]) := by
  kernel_rfl

/-- **`pop` reads the front**: under X ↦ 1, L ↦ [2], `ListItem(X) L` denotes `[1, 2]`:
`ListItem(X)` denotes `[1]`, and `[1]` followed by `[2]` is `[1, 2]`. -/
theorem pop_matches : PatVal c [(1, ival 1), (2, list [iv 2])]
    (.app KCore.listConcat [.app KCore.listElem [.inj KCore.Srt.int KCore.Srt.kitem (.var 1)], .var 2])
    (list [iv 1, iv 2]) :=
  .coll (by decide +kernel) (by decide +kernel)
    (.cons (.coll (vs := [iv 1]) (v := list [iv 1]) (by decide +kernel) (by decide +kernel)
      (.cons (.inj (w := ival 1) (.var rfl)) .nil) (by decide +kernel))
      (.cons (.var rfl) .nil))
    (by decide +kernel)

/-- **`drop` reads the back**: under L ↦ [1], `_` ↦ 2, `L ListItem(_)` denotes `[1, 2]`. -/
theorem drop_matches : PatVal c [(1, list [iv 1]), (2, iv 2)]
    (.app KCore.listConcat [.var 1, .app KCore.listElem [.var 2]])
    (list [iv 1, iv 2]) :=
  .coll (by decide +kernel) (by decide +kernel)
    (.cons (.var rfl)
      (.cons (.coll (vs := [iv 2]) (v := list [iv 2]) (by decide +kernel) (by decide +kernel)
        (.cons (.var rfl) .nil) (by decide +kernel)) .nil))
    (by decide +kernel)

#eval show Lean.CoreM Unit from do
  for n in [``pop_lhs, ``drop_lhs, ``pop_matches, ``drop_matches] do
    let axs ← Lean.collectAxioms n
    unless axs.all ([``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "{n}: axioms {axs}"

end CollsList.Course
