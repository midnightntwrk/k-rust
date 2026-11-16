/-
  The map pattern `K |-> V M` against a map whose rest is not known (`PatVal.mapLookup`), and the
  value of a left-hand side read symbol by symbol (`Term.instP`) at a map with concrete keys and
  free values. Run from the package root: `lake env lean test/Fire.lean`.
-/
import KcoreSpec

set_option autoImplicit false

open KCore

/-- A key: the identifier x injected into KItem. -/
def key (x : String) : GroundTerm := .inj Srt.ident Srt.kitem (.dv Srt.ident (.tok x))

/-- `$a |-> V M` matches a map whose first entry is `$a`'s, whatever the other entries `es` are
(sorted, as every map of the sort is), with M taking them: the pattern's K bound to `$a`, V to v,
M to the other entries. -/
example (c : Semantics) (v : GroundTerm) (es : Entries) (hs : keysSorted ((key "$a", v) :: es) = true) :
    PatVal c [(0, key "$a"), (1, v), (2, .map Srt.map es)]
      (.app mapConcat [.app mapElem [.var 0, .var 1], .var 2]) (.map Srt.map ((key "$a", v) :: es)) := by
  refine PatVal.mapLookup (s := Srt.map) hs (by simp [findK, GroundTerm.cmp_refl]) (.var rfl) (.var rfl)
    (.var ?_)
  simp [eraseK, GroundTerm.cmp_refl]
  rfl

/-- With the entry in the middle: two concrete keys around `$b`, free values. -/
example (c : Semantics) (u v w : GroundTerm) :
    Term.instP c [(0, key "$b"), (1, v), (2, .map Srt.map [(key "$a", u), (key "$c", w)])]
      (.app mapConcat [.app mapElem [.var 0, .var 1], .var 2]) =
      some (.map Srt.map [(key "$a", u), (key "$b", v), (key "$c", w)]) := by
  rfl

/-- `Term.instP` and the aliases give `PatVal` (`PatVal.of_instP`) at that map. -/
example (c : Semantics) (u v w : GroundTerm) :
    PatVal c [(0, key "$b"), (1, v), (2, .map Srt.map [(key "$a", u), (key "$c", w)])]
      (.app mapConcat [.app mapElem [.var 0, .var 1], .var 2])
      (.map Srt.map [(key "$a", u), (key "$b", v), (key "$c", w)]) :=
  PatVal.of_instP _ _ (by rfl) rfl
