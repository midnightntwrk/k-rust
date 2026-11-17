/-
  `KCore.setvar_rewrite_singleton` at the rewrite axiom of e3-setvar-rewrite
  (`rule <k> c(@S, @S) => d(@S) ... </k>`, test/constructs/fixtures/e3-setvar-rewrite/kore.txt).
  Run from the package root, after the library: `lake env lean -j1 test/SetVarRewrite.lean`.

  - `ax`: the axiom's pattern, `\rewrites(\and(<generatedTop>(<k>(kseq(inj(c(@S, @S)), K)), C), ⊤),
    \and(<generatedTop>(<k>(kseq(inj(d(@S)), K)), C), ⊤))`.
  - `tr_ax`: its translation under its own table is `sRewrites` of the two sides, each an `SvCtx`
    at the set variable: the left with two occurrences, the right with one.
  - `sides`: no side pattern of either holds the set variable.
  - `singleton`: the theorem at them: at a point, the two sides' implication at every set S inside
    U is "for all a₀, a₁ in U with the point in `L[a₀, a₁]`, the point has a successor in `R[z]`
    for a z that is a₀ or a₁".
-/
import KcoreSpec.SetVarRewrite

set_option autoImplicit false
set_option maxRecDepth 100000

open ML KoreAML KCore

namespace SetVarRewrite

def topC : Kore.KSort := srt "GeneratedTopCell"
def expS : Kore.KSort := srt "Exp"
def S : Kore.SVar := ⟨⟨⟨"VarS"⟩⟩, expS⟩
def dv1 : Kore.Pattern := ev "Var'Unds'DotVar1" (srt "K")
def dv0 : Kore.Pattern := ev "Var'Unds'DotVar0" (srt "GeneratedCounterCell")

/-- `<generatedTop>(<k>(kseq(inj{Exp,KItem}(x), K)), C)`. -/
def cfg (x : Kore.Pattern) : Kore.Pattern :=
  ap "Lbl'-LT-'generatedTop'-GT-'" [ap "Lbl'-LT-'k'-GT-'" [ap "kseq" [injP "Exp" "KItem" x, dv1]], dv0]

def ax : Kore.Pattern :=
  .rewrites topC
    (.and topC [cfg (ap "Lblc" [.var (.svar S), .var (.svar S)]), .top topC])
    (.and topC [cfg (ap "Lbld" [.var (.svar S)]), .top topC])

def ctx : Ctx := ⟨tableOf [] ax, []⟩
def X : SVar := ctx.vars.sv (svarKey S)

/-- The configuration around the `k` cell's first item, as a context of applications. -/
def cfgCtx (item : SvCtx) : SvCtx :=
  .andSide
    (.app (.app (.side (sym (.symbol "Lbl'-LT-'generatedTop'-GT-'")))
      (.app (.side (sym (.symbol "Lbl'-LT-'k'-GT-'")))
        (.app (.app (.side (sym (.symbol "kseq")))
          (.app (.side (sym (.symbol "inj") ⬝ trSort ctx.vars expS ⬝ trSort ctx.vars (srt "KItem"))) item))
          (.side (tr ctx dv1)))))
      (.side (tr ctx dv0)))
    (sTop (trSort ctx.vars topC))

def L : SvCtx := cfgCtx (.app (.app (.side (sym (.symbol "Lblc"))) .hole) .hole)
def R : SvCtx := cfgCtx (.app (.side (sym (.symbol "Lbld"))) .hole)

theorem tr_ax : tr ctx ax = sRewrites (trSort ctx.vars topC) (L.atSet X) (R.atSet X) := rfl

theorem holes : L.holes = 2 ∧ R.holes = 1 := ⟨rfl, rfl⟩

set_option linter.unusedSimpArgs false in
theorem sides : L.Sides X ∧ R.Sides X := by
  refine ⟨?_, ?_⟩ <;> simp only [L, R, cfgCtx, SvCtx.Sides, and_self, true_and, and_true] <;> decide

/-- **The theorem at the fixture's two sides.** -/
theorem singleton {M : Type} {I : Interpretation KoreAML.Sym M} (e : Valuation M) (U : Set M) (m : M) :
    (∀ A : Set M, (∀ x, A x → U x) →
        (L.atSet X).interpret I (svarAt_svin e X A) m →
        (sNext (R.atSet X)).interpret I (svarAt_svin e X A) m) ↔
      (∀ a : Nat → M, (∀ i, i < 2 → U (a i)) → L.den I e a 0 m →
        ∃ nx b, I.evalSymb .next nx ∧
          (∃ z : Nat → M, (∀ j, j < 1 → ∃ i, i < 2 ∧ z j = a i) ∧ R.den I e z 0 b) ∧
          I.evalApp nx b m) :=
  setvar_rewrite_singleton X L R sides.1 sides.2 e U m

end SetVarRewrite
