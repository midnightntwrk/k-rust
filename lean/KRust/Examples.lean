/- Executable checks of the model of `KRust.TermAttributes`: `#guard` evaluates each at build time.
Anchors verified at ce4084a5 (term.rs:888 is the `_ => false` arm of
`structurally_distinct_after_normalization`). -/
import KRust.TermAttributes

namespace KRust.Examples
open KRust.TermAttributes

def int (v : String) : Term := .dv "SortInt" v
def injK (s : SortName) (t : Term) : Term := .inj s "SortKItem" t
def ctor (n : String) : Sym :=
  { name := n, symbolType := .constructor, anywhere := false, declaredFunction := false,
    injective := false, macroOrAlias := false, other := "" }
def kcell : Sym := ctor kCellName
def mac : Sym := { ctor "macro" with macroOrAlias := true }

-- Distinct domain values are structurally distinct; equal ones are not (the `self == other` guard).
#guard structDistinct (int "1") (int "2")
#guard !structDistinct (int "1") (int "1")
-- Mixed headers fall to the `_ => false` arm (term.rs:888): the matcher would decide them.
#guard !structDistinct (injK "SortInt" (int "1")) (injK "SortString" (.dv "SortString" "a"))

-- Narrowed class: one header per map.
#guard ceilFree (.map "M" [(injK "SortInt" (int "1"), int "0"), (injK "SortInt" (int "2"), int "0")] none)
#guard !ceilFree (.map "M" [(injK "SortInt" (int "1"), int "0"),
                            (injK "SortString" (.dv "SortString" "a"), int "0")] none)
-- `k ↦ 1` and `k ↦ 2` survive the pair dedup; the adjacency check rejects them.
#guard !ceilFree (.map "M" [(int "1", int "1"), (int "1", int "2")] none)
#guard ceilFree (.and (int "1") (int "2"))

-- The k-cell count saturates at 2; the walk stops below a k cell.
#guard kCells (.app (ctor "top") [] [.app kcell [] [.app kcell [] []], int "0"]) == 1
#guard kCells (.app (ctor "top") [] [.app kcell [] [], .app kcell [] [], .app kcell [] []]) == 2
#guard (findK (.app (ctor "top") [] [.app kcell [] [], .app kcell [] [], .app kcell [] []]) []).length == 2
#guard firstMacro (.list "L" [int "1", .app mac [] []] none) == some "macro"

end KRust.Examples
