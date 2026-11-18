/-
  Kernel facts (examples/run.sh): `KimpNI` (Spec.lean) is not vacuous. At a labelling with one high
  and one low identifier, the checker accepts a program whose branch on the high identifier writes
  only it, and rejects an explicit flow (`l = h;`) and implicit flows through `if` and `while`
  (k2lean's demos/ImpNI/ImpNI/Examples.lean, the same programs). The empty store is a store, and
  two empty stores agree on the low identifiers. The checker's verdicts are computed by KCore's
  executable evaluation and read as `Eval` facts through its soundness (`evalF_sound`), from the
  checker's three core facts, and are its only results since evaluation is functional
  (`Eval.functional`, its clauses of one priority being coherent: `coherent`).
-/
import NI.Spec
import KcoreSpec.EvalComplete
import KcoreSpec.MatchIndependent

set_option autoImplicit false

namespace NI

open KCore KCore.Exec

/-- The executable evaluation of the function f of the core `chk` at vs, with fuel n, gives w. -/
noncomputable def checkIn (chk : Semantics) (n : Nat) (f : Sym) (vs : List GroundTerm) (w : GroundTerm) : Bool :=
  match chk.lookupFn f with
  | some fn => chk.sortsOf vs == some fn.args &&
      (match evalF chk n f vs with
       | some (some v) => same v w
       | _ => false)
  | none => false

section
variable {chk : Semantics} (hok : chk.ok = true) (hsr : chk.srReady = true) (hmr : chk.matchReady = true)
include hok hsr hmr

theorem eval_of_checkIn {f : Sym} {vs : List GroundTerm} {w : GroundTerm} (n : Nat)
    (h : checkIn chk n f vs w = true) : Eval chk f vs (some w) := by
  unfold checkIn at h
  split at h
  · rename_i fn hfn
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨hvs, hev⟩ := h
    split at hev
    · rename_i v hv
      rw [same_iff.mp hev] at hv
      exact evalF_sound (sortCtx_of hok hsr (.inl (matchCtx_of hmr).noOvl)) (clauseCtx_of hok) (matchCtx_of hmr) n hv hfn hvs
    · cases hev
  · cases h

/-- The core's functions have one result: the computed one. -/
theorem eval_unique_of_checkIn (hco : CoherentAll chk) {f : Sym} {vs : List GroundTerm}
    {w : GroundTerm} {r : Option GroundTerm} (n : Nat) (h : checkIn chk n f vs w = true)
    (h' : Eval chk f vs r) : r = some w :=
  Eval.functional hco h' (eval_of_checkIn hok hsr hmr n h)

end

/-- The executable evaluation of the checker's function f at vs, with fuel n, gives w. -/
noncomputable def check (n : Nat) (f : Sym) (vs : List GroundTerm) (w : GroundTerm) : Bool :=
  checkIn ImpSec.c n f vs w

theorem sec_eval {f : Sym} {vs : List GroundTerm} {w : GroundTerm} (n : Nat)
    (h : check n f vs w = true) : Eval ImpSec.c f vs (some w) :=
  eval_of_checkIn ImpSec.ok ImpSec.srReady ImpSec.matchReady n h

/-- The checker's functions have one result: the computed one. -/
theorem sec_eval_unique {f : Sym} {vs : List GroundTerm} {w : GroundTerm} {r : Option GroundTerm}
    (n : Nat) (h : check n f vs w = true) (h' : Eval ImpSec.c f vs r) : r = some w :=
  eval_unique_of_checkIn ImpSec.ok ImpSec.srReady ImpSec.matchReady
    ImpSec.coherent n h h'

/-! ## A labelling and four programs (k2lean's) -/

def h : GroundTerm := ident "h"
def l : GroundTerm := ident "l"

/-- `h` is high, `l` is low. -/
def G0 : GroundTerm := .map KCore.Srt.map [(key h, .inj S.level Srt.kitem hi), (key l, .inj S.level Srt.kitem lo)]

def var (X : GroundTerm) : GroundTerm := .inj Srt.ident K.expr X
def num (n : Int) : GroundTerm := .inj Srt.int K.expr (.dv Srt.int (.int n))
def assign (X E : GroundTerm) : GroundTerm := .ctor K.assign [X, E]
def seq (S T : GroundTerm) : GroundTerm := .ctor K.seq [S, T]
def ifThen (C S : GroundTerm) : GroundTerm := .ctor K.ifThen [C, S]
def while_ (C S : GroundTerm) : GroundTerm := .ctor K.while_ [C, S]
def block (S : GroundTerm) : GroundTerm := .ctor K.block [S]
def plus (E F : GroundTerm) : GroundTerm := .ctor K.plus [E, F]
def gt (E F : GroundTerm) : GroundTerm := .ctor K.gt [E, F]

/-- `l = 1; h = l + 1; if (h > 0) h = 2;` -/
def ok : GroundTerm := seq (assign l (num 1)) (seq (assign h (plus (var l) (num 1))) (ifThen (gt (var h) (num 0)) (assign h (num 2))))
/-- `l = h;` -/
def explicitFlow : GroundTerm := assign l (var h)
/-- `if (h > 0) l = 1;` -/
def ifFlow : GroundTerm := ifThen (gt (var h) (num 0)) (assign l (num 1))
/-- `while (h > 0) { l = 1; h = 0; }` -/
def whileFlow : GroundTerm := while_ (gt (var h) (num 0)) (block (seq (assign l (num 1)) (assign h (num 0))))

theorem programs_sorted : (Kimp.c.sortsOf [ok, explicitFlow, ifFlow, whileFlow]).isSome = true := by decide +kernel
theorem G0_sorted : ImpSec.c.sortOf G0 = some Srt.map := by decide +kernel

theorem secure_ok : Secure G0 ok := sec_eval 200 (by decide +kernel)

theorem not_secure_explicitFlow : ¬ Secure G0 explicitFlow := fun hs => by
  have := sec_eval_unique 200 (w := bool false) (by decide +kernel) hs
  simp [KCore.bool] at this
theorem not_secure_ifFlow : ¬ Secure G0 ifFlow := fun hs => by
  have := sec_eval_unique 200 (w := bool false) (by decide +kernel) hs
  simp [KCore.bool] at this
theorem not_secure_whileFlow : ¬ Secure G0 whileFlow := fun hs => by
  have := sec_eval_unique 200 (w := bool false) (by decide +kernel) hs
  simp [KCore.bool] at this

theorem low_l : Low G0 l := sec_eval 200 (by decide +kernel)
theorem not_low_h : ¬ Low G0 h := fun hl => by
  have := sec_eval_unique 200 (w := hi) (by decide +kernel) hl
  simp [lo, hi, S.lo, S.hi] at this
  exact absurd this (by decide)

theorem good_empty : Good (.map KCore.Srt.map []) := ⟨by decide +kernel, fun _ _ hv => by simp [lookup, findK] at hv⟩
theorem lowEq_empty : LowEq G0 (.map KCore.Srt.map []) (.map KCore.Srt.map []) := fun _ _ => rfl

/-- info: 'NI.secure_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms secure_ok

/-- info: 'NI.not_secure_whileFlow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms not_secure_whileFlow

end NI
