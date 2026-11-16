/-
  Peano's eleven statements, over the generated package `Peano` (`kcore gen`). The user's package:
  readable terms and the statements. Matching ranges over well-sorted substitutions, so the
  equations of `pred` are stated for `N` of sort `Nat`.
-/
import Peano

set_option autoImplicit false

namespace Peano

open KCore

@[match_pattern, reducible] def z : GroundTerm := .ctor Sym.«z» []
@[match_pattern, reducible] def s (n : GroundTerm) : GroundTerm := .ctor Sym.«s» [n]
@[match_pattern, reducible] def run (n : GroundTerm) : GroundTerm := .ctor Sym.«run» [n]
@[match_pattern, reducible] def done (v : GroundTerm) : GroundTerm := .ctor Sym.«done» [v]
@[match_pattern, reducible] def natVal (n : GroundTerm) : GroundTerm := .inj Srt.«Nat» Srt.«Val» n
@[match_pattern, reducible] def counter (i : GroundTerm) : GroundTerm := .ctor counterLabel [i]
@[match_pattern, reducible] def top (k ctr : GroundTerm) : GroundTerm := .ctor topLabel [k, ctr]
@[match_pattern, reducible] def cfg (st ctr : GroundTerm) : GroundTerm :=
  top (.ctor Sym.«<k>» [.ctor kseq [.inj Srt.«State» KCore.Srt.kitem st, .ctor dotk []]]) ctr
def ctr0 : GroundTerm := counter (.dv KCore.Srt.int (.int 0))

abbrev Pred (n v : GroundTerm) : Prop := Eval c Sym.«pred» [n] (some v)

def deterministic.statement : Prop := ∀ x y y' : Config c, Step c x y → Step c x y' → y = y'
def pred_succ.statement : Prop := ∀ N : GroundTerm, c.sortOf N = some Srt.«Nat» → Pred (s N) N
def pred_owise.statement : Prop :=
  ∀ N : GroundTerm, c.sortOf N = some Srt.«Nat» → (∀ M, N ≠ s M) → Pred N z
def step_run_succ.statement : Prop :=
  ∃ x y : Config c, x.val = cfg (run (s z)) ctr0 ∧ y.val = cfg (run z) ctr0 ∧ Step c x y
def step_run_zero.statement : Prop :=
  ∃ x y : Config c, x.val = cfg (run z) ctr0 ∧ y.val = cfg (done (natVal z)) ctr0 ∧ Step c x y
def stuck_done.statement : Prop :=
  ∃ x : Config c, x.val = cfg (done (natVal z)) ctr0 ∧ ∀ y : Config c, ¬ Step c x y
def doneHoldsZero (x : Config c) : Prop := ∀ v ctr, x.val = cfg (done v) ctr → v = natVal z
def doneHoldsZero_fails.statement : Prop :=
  ∃ x : Config c, x.val = cfg (done (natVal (s z))) ctr0 ∧ ¬ doneHoldsZero x
/-- The start configurations: `run(n)` in the k cell. -/
def Start (x : Config c) : Prop := ∃ n ctr, x.val = cfg (run n) ctr
def doneHoldsZero_invariant.statement : Prop := Invariant c Start doneHoldsZero
def doneHoldsZero_reach.statement : Prop :=
  ∀ x y : Config c, Start x → Cert.Reach (Step c) x y → doneHoldsZero y
def counterIs (ctr : GroundTerm) (x : Config c) : Prop := ∃ k, x.val = top k ctr
def counterIs_invariant.statement : Prop := ∀ ctr : GroundTerm, Invariant c (counterIs ctr) (counterIs ctr)
def counterIs_reach.statement : Prop :=
  ∀ (ctr : GroundTerm) (x y : Config c), counterIs ctr x → Cert.Reach (Step c) x y → counterIs ctr y

end Peano
