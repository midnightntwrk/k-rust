/-
  The facts the course derives on kimp's variable lookup, `CALC.var` (rule 19, `Kimp.rule19`):
  its env cell's pattern, `X |-> V M` (`_Map_(X |-> V, M)`, X variable 0, V variable 2, M
  variable 3), denotes the environment `{x ↦ 1, y ↦ 2}` under two substitutions, one for each way
  to split the map: X = x with M = {y ↦ 2}, and X = y with M = {x ↦ 1}. A map has no first entry.
  The whole left side, against the configuration whose k cell holds the identifier x, matches only
  with X = x: the k cell fixes X.
-/
import Kimp.Surface
import KcoreSpec.SymbolicLemmas

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace Kimp.Course

open KCore Kimp

/-- An identifier, an Int value in the env cell (injected into `KItem`), and a map key. -/
def ident (x : String) : GroundTerm := .dv KCore.Srt.ident (.tok x)
def iv (n : Int) : GroundTerm := .inj KCore.Srt.int KCore.Srt.kitem (.dv KCore.Srt.int (.int n))
def key (x : String) : GroundTerm := .inj KCore.Srt.ident KCore.Srt.kitem (ident x)

/-- The environment `{x ↦ 1, y ↦ 2}`: its entries in the order of their keys. -/
def env : GroundTerm := .map KCore.Srt.map [(key "x", iv 1), (key "y", iv 2)]

/-- The env cell's map pattern in `CALC.var`'s left side: `X |-> V M`. -/
def mapPat : Term :=
  .app KCore.mapConcat [.app KCore.mapElem [.inj KCore.Srt.ident KCore.Srt.kitem (.var 0), .var 2], .var 3]

/-- `CALC.var`'s left side: X at the head of the k cell, and the env cell (aliased, variable 4)
holding `X |-> V M`; the counter cell is variable 5. -/
theorem rule19_lhs : c.rules[19]?.map Rule.lhs = some
    (.app KCore.topLabel [.app Sym.«<k>» [.app KCore.kseq [.inj KCore.Srt.ident KCore.Srt.kitem (.var 0), .var 1]],
      .as (.app Sym.«<env>» [mapPat]) 4, .var 5]) :=
  congrArg (Option.map Rule.lhs) rule19

/-- **Split at x**: under X ↦ x, V ↦ 1, M ↦ {y ↦ 2}, `X |-> V M` denotes `{x ↦ 1, y ↦ 2}`:
`{x ↦ 1}` joined with `{y ↦ 2}`. -/
theorem mapPat_x : PatVal c [(0, ident "x"), (2, iv 1), (3, .map KCore.Srt.map [(key "y", iv 2)])] mapPat env :=
  .hook Exec.patternHooks_concat
    (.cons (.hook (v := .map KCore.Srt.map [(key "x", iv 1)]) Exec.patternHooks_elem (.cons (.inj (w := ident "x") (.var rfl)) (.cons (.var rfl) .nil))
      (Exec.hook_mapElem _ _)) (.cons (.var rfl) .nil))
    (by decide +kernel)

/-- **Split at y**: under X ↦ y, V ↦ 2, M ↦ {x ↦ 1}, `X |-> V M` denotes the same map:
`{y ↦ 2}` joined with `{x ↦ 1}`. -/
theorem mapPat_y : PatVal c [(0, ident "y"), (2, iv 2), (3, .map KCore.Srt.map [(key "x", iv 1)])] mapPat env :=
  .hook Exec.patternHooks_concat
    (.cons (.hook (v := .map KCore.Srt.map [(key "y", iv 2)]) Exec.patternHooks_elem (.cons (.inj (w := ident "y") (.var rfl)) (.cons (.var rfl) .nil))
      (Exec.hook_mapElem _ _)) (.cons (.var rfl) .nil))
    (by decide +kernel)

/-- `CALC.var`'s whole left side (`rule19_lhs`). -/
def lhs : Term :=
  .app KCore.topLabel [.app Sym.«<k>» [.app KCore.kseq [.inj KCore.Srt.ident KCore.Srt.kitem (.var 0), .var 1]],
    .as (.app Sym.«<env>» [mapPat]) 4, .var 5]

theorem rule19_lhs_eq : c.rules[19]?.map Rule.lhs = some lhs := rule19_lhs

/-- The configuration holding the identifier x, then `.K`, in the k cell, `env` in the env cell,
and the counter at 0. -/
def cfgX : GroundTerm :=
  .ctor KCore.topLabel [.ctor Sym.«<k>» [.ctor KCore.kseq [key "x", .ctor KCore.dotk []]],
    .ctor Sym.«<env>» [env], .ctor KCore.counterLabel [.dv KCore.Srt.int (.int 0)]]

/-- `mapPat_x`'s substitution extended to the rule's other variables: the rest of the k cell
(variable 1) ↦ `.K`, the env cell (variable 4) ↦ itself, the counter cell (variable 5) ↦ 0. -/
def σx : Subst :=
  [(0, ident "x"), (2, iv 1), (3, .map KCore.Srt.map [(key "y", iv 2)]),
    (1, .ctor KCore.dotk []), (4, .ctor Sym.«<env>» [env]), (5, .ctor KCore.counterLabel [.dv KCore.Srt.int (.int 0)])]

/-- **The whole left side at x**: under `σx`, `CALC.var`'s left side denotes `cfgX`; its env cell's
map pattern splits `env` at x as in `mapPat_x`. -/
theorem lhs_x : PatVal c σx lhs cfgX :=
  .ctor rfl (.cons (.ctor rfl (.cons (.ctor rfl (.cons (.inj (w := ident "x") (.var rfl)) (.cons (.var rfl) .nil))) .nil))
    (.cons (.as (.ctor rfl (.cons
      (.hook Exec.patternHooks_concat
        (.cons (.hook (v := .map KCore.Srt.map [(key "x", iv 1)]) Exec.patternHooks_elem
          (.cons (.inj (w := ident "x") (.var rfl)) (.cons (.var rfl) .nil)) (Exec.hook_mapElem _ _))
          (.cons (.var rfl) .nil))
        (by decide +kernel)) .nil)) rfl)
      (.cons (.var rfl) .nil)))

/-- **Only at x**: no substitution giving X (variable 0) the identifier y matches `CALC.var`'s left
side against `cfgX` (in particular no well-sorted one): the k cell holds x, which X's occurrence
there must denote, though `mapPat_y` splits `env` at y. -/
theorem lhs_not_y (σ : Subst) (h0 : σ.lookup 0 = some (ident "y")) : ¬ PatVal c σ lhs cfgX := by
  intro h
  have hk := ((PatVals.cons_cons_iff.mp
    ((PatVal.app_ctor_iff (f := KCore.topLabel) rfl (by decide)).mp h).2).1)
  have hs := ((PatVals.cons_cons_iff.mp
    ((PatVal.app_ctor_iff (f := Sym.«<k>») rfl (by decide)).mp hk).2).1)
  have hx := ((PatVals.cons_cons_iff.mp
    ((PatVal.app_ctor_iff (f := KCore.kseq) rfl (by decide)).mp hs).2).1)
  obtain ⟨w, hw, he⟩ := PatVal.inj_iff.mp hx
  rw [PatVal.var_iff, h0] at hw
  cases hw
  exact absurd he (by decide)

#eval show Lean.CoreM Unit from do
  for n in [``rule19_lhs, ``mapPat_x, ``mapPat_y, ``rule19_lhs_eq, ``lhs_x, ``lhs_not_y] do
    let axs ← Lean.collectAxioms n
    unless axs.all ([``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "{n}: axioms {axs}"

end Kimp.Course
