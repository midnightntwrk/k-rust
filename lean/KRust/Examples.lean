/- Executable checks of the model of `KRust.TermAttributes`: `#guard` evaluates each at build time. -/
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
def wrap : Sym := { ctor "wrap" with symbolType := .function .Total, anywhere := true, injective := true }

-- Distinct domain values are structurally distinct; equal ones are not (the `self == other` guard).
#guard structDistinct (fun _ => false) (fun _ _ => false) (int "1") (int "2")
#guard !structDistinct (fun _ => false) (fun _ _ => false) (int "1") (int "1")
-- Mixed headers fall to the `_ => false` arm: the matcher would decide them.
#guard !structDistinct (fun _ => false) (fun _ _ => false) (injK "SortInt" (int "1"))
  (injK "SortString" (.dv "SortString" "a"))
-- An anywhere application decides only when the simplifier certified it as a normal form
-- (`evaluated`): `wrap(s(z))` may equal `wrap(z)` by an anywhere equation.
#guard !structDistinct (fun _ => false) (fun _ _ => false) (.app wrap [] [.app (ctor "s") [] [.app (ctor "z") [] []]])
  (.app wrap [] [.app (ctor "z") [] []])
#guard structDistinct (fun _ => true) (fun _ _ => false) (.app wrap [] [.app (ctor "s") [] [.app (ctor "z") [] []]])
  (.app wrap [] [.app (ctor "z") [] []])
-- Constructors decide without a certificate, whatever lies below them.
#guard structDistinct (fun _ => false) (fun _ _ => false) (.app (ctor "c") [] [.app wrap [] [.app (ctor "z") [] []]])
  (.app (ctor "d") [] [.app wrap [] [.app (ctor "z") [] []]])
#guard !structDistinct (fun _ => false) (fun _ _ => false) (.app (ctor "c") [] [.app (ctor "z") [] []])
  (.app wrap [] [.app (ctor "z") [] []])
-- A constructor application is not the value of an injection; an uncertified anywhere one may be.
#guard structDistinct (fun _ => false) (fun _ _ => false) (.app (ctor "c") [] [])
  (injK "SortInt" (int "1"))
#guard !structDistinct (fun _ => false) (fun _ _ => false) (.app wrap [] [.app (ctor "z") [] []])
  (injK "SortInt" (int "1"))

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
