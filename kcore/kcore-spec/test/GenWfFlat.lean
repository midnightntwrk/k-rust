/-
  `Faithful.genWf`'s flat conjunct on small hand-built semantics. Run from the package root:
  `lake env lean -j1 test/GenWfFlat.lean`. Kernel-checked.

  `base` is Exp ::= x with the open generator `and : Exp Exp → Exp` (raw) and the configuration
  of `test/OpenGenSems.lean`; `withOvl` adds a sort B with a constructor `b` and an overloading
  symbol `o : → B`. Each refused semantics changes one thing of these: a constructor with an
  argument at Exp (`ctorArg`), a subsort pair below Exp (`subBelow`), the open generator named like
  the constructor `x` (`nameCtor`), the overloading symbol at Exp (`ovlAt`). Each is accepted with
  the same parameter not raw, so the conjuncts that read raw parameters are what refuse it, and of
  those the one that asks the result sort to be a constructor sort holds (it holds of `base`,
  whose parameter has the same result sort).
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 100000

namespace KCore.GenWfFlat

open KCore KCore.Faithful

def cellSorts : List Srt := [Srt.top, Srt.topFrag, nRegSorts, nRegSorts + 1, Srt.counter, Srt.counterOpt]
def cellCtors : List CtorSig :=
  [⟨topLabel, [nRegSorts, Srt.counter], Srt.top⟩, ⟨topFragLabel, [nRegSorts + 1, Srt.counterOpt], Srt.topFrag⟩,
   ⟨nRegSyms + 3, [Srt.k], nRegSorts⟩, ⟨nRegSyms + 4, [], nRegSorts + 1⟩,
   ⟨counterLabel, [Srt.int], Srt.counter⟩, ⟨noCounter, [], Srt.counterOpt⟩]
def cellSubsorts : List (Srt × Srt) := [(nRegSorts, nRegSorts + 1), (Srt.counter, Srt.counterOpt)]

def exp : Srt := nRegSorts + 2
def bS : Srt := nRegSorts + 3
def xS : Sym := nRegSyms + 5
def andS : Sym := nRegSyms + 6
def sS : Sym := nRegSyms + 7
def bC : Sym := nRegSyms + 8
def oS : Sym := nRegSyms + 9

def xSig : CtorSig := ⟨xS, [], exp⟩
def andP : ParamSig := { sig := ⟨andS, [exp, exp], exp⟩, raw := true }

def base : Semantics :=
  { lib := {}
    sortNames := ["KCell", "KCellOpt", "Exp"]
    symNames := []
    userSorts := cellSorts ++ [exp]
    ctors := cellCtors ++ [xSig]
    fns := []
    userSubsorts := cellSubsorts
    pgmSort := Srt.k
    rules := []
    params := [andP] }

def withOvl : Semantics :=
  { base with
    sortNames := ["KCell", "KCellOpt", "Exp", "B"]
    userSorts := cellSorts ++ [exp, bS]
    ctors := cellCtors ++ [xSig, ⟨bC, [], bS⟩]
    ovls := [{ sig := ⟨oS, [], bS⟩, over := [] }] }

def ctorArg : Semantics := { base with ctors := cellCtors ++ [xSig, ⟨sS, [exp], exp⟩] }
def subBelow : Semantics :=
  { withOvl with ovls := [], userSubsorts := cellSubsorts ++ [(bS, exp)] }
def nameCtor : Semantics := { base with params := [{ sig := ⟨xS, [exp, exp], exp⟩, raw := true }] }
def ovlAt : Semantics := { withOvl with ovls := [{ sig := ⟨oS, [], exp⟩, over := [] }] }

/-- The same semantics with its parameters not raw. -/
def notRaw (c : Semantics) : Semantics := { c with params := c.params.map fun k => { k with raw := false } }

theorem accepted : genWf base = true ∧ genWf withOvl = true := by decide +kernel

theorem refused : genWf ctorArg = false ∧ genWf subBelow = false ∧ genWf nameCtor = false ∧
    genWf ovlAt = false := by decide +kernel

theorem refused_raw : genWf (notRaw ctorArg) = true ∧ genWf (notRaw subBelow) = true ∧
    genWf (notRaw nameCtor) = true ∧ genWf (notRaw ovlAt) = true := by decide +kernel

/-! One instance of each part. -/

example : xSig.args = [] :=
  genWf_flat_ctor accepted.1 (k := andP) (by decide) rfl (g := xSig) (by decide +kernel) rfl

example : bS ≠ exp :=
  genWf_flat_ovl accepted.2 (k := andP) (by decide +kernel) rfl (g := ⟨oS, [], bS⟩) (by decide +kernel)

example : Srt.kitem ≠ exp :=
  genWf_flat_sub accepted.1 (k := andP) (by decide) rfl (a := exp) (by decide +kernel)

example : xSig.name ≠ andS ∧ (⟨oS, [], bS⟩ : CtorSig).name ≠ andS :=
  ⟨(genWf_flat_name accepted.2 (k := andP) (by decide +kernel) rfl).1 xSig (by decide +kernel),
   (genWf_flat_name accepted.2 (k := andP) (by decide +kernel) rfl).2 _ (by decide +kernel)⟩

end KCore.GenWfFlat
