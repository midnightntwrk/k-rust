/-
  Kernel instances of `tieFilterMap_range` and `tieFilterMap_whole` (KcoreSpec/TieChunks.lean), the
  join `tiegen --heads-plain` writes for `absent_proj_below`'s first conjunct: a list filtered and
  mapped, equal to another list mapped, from one decision per range. Here a list of eleven pairs,
  filtered by its second component and mapped to its first, cut into ranges of four (one of which
  holds no member, k = 0, and an open last range), against the list of the members' first
  components mapped by a function other than the filter's map.
  Run from the package root: `lake env lean -j1 test/TieFilterMapInst.lean`.
-/
import KcoreSpec

set_option autoImplicit false

namespace KCore.TieFilterMapInst

open KCore

def l : List (Nat × Bool) :=
  [(1, true), (2, false), (3, false), (4, true), (5, false), (6, false), (7, false), (8, false),
   (9, true), (10, false), (11, true)]

def p (x : Nat × Bool) : Bool := x.2
def f (x : Nat × Bool) : Nat × Option Nat := (x.1, some (x.1 * 2))
def m : List Nat := [1, 4, 9, 11]
def g (n : Nat) : Nat × Option Nat := (n, some (n + n))

theorem r0 : (((l.drop 0).take 4).filter p).map f = ((m.drop 0).take 2).map g := by decide +kernel
theorem r4 : (((l.drop 4).take 4).filter p).map f = ((m.drop 2).take 0).map g := by decide +kernel
theorem r8 : ((l.drop 8).filter p).map f = (m.drop 2).map g := by decide +kernel

/-- The whole equation from the three ranges. -/
theorem whole : (l.filter p).map f = m.map g :=
  tieFilterMap_whole (l := l) (p := p) (f := f) (m := m) (g := g) <|
    tieFilterMap_range (l := l) (p := p) (f := f) (m := m) (g := g) (a := 0) (n := 4) (b := 0) (k := 2) r0 <|
    tieFilterMap_range (l := l) (p := p) (f := f) (m := m) (g := g) (a := 4) (n := 4) (b := 2) (k := 0) r4 <|
    r8

/-- The joined statement is the one decided at once. -/
example : (l.filter p).map f = m.map g := by decide +kernel

end KCore.TieFilterMapInst

#print axioms KCore.TieFilterMapInst.whole
