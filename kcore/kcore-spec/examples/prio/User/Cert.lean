/-
  Run certificates over priorities (KcoreSpec/Cert.lean) on the generated package `Prio`
  (`f2-examples/prio.k`): `go(d)` steps to `out(d)` by the rule of priority 40; the certificate naming
  the rule of priority 50 for the same step is refused, since the rule of priority 40 applies.
-/
import Prio
import KcoreSpec.Cert

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace Prio.CertTest

open KCore KCore.Cert Prio

def ctr0 : GroundTerm := .ctor counterLabel [.dv KCore.Srt.int (.int 0)]
def pcfg (st : GroundTerm) : GroundTerm :=
  .ctor topLabel [.ctor Sym.«<k>» [.ctor kseq [st, .ctor dotk []]], ctr0]
/-- `go(d)`, `out(d)`, `other(d)`; d of sort D, below B and C. -/
def goD : GroundTerm := .ctor Sym.«go» [.inj Srt.«D» Srt.«B» (.ctor Sym.«d» [])]
def outD : GroundTerm := .ctor Sym.«out» [.inj Srt.«D» Srt.«C» (.ctor Sym.«d» [])]
def otherD : GroundTerm := .ctor Sym.«other» [.inj Srt.«D» Srt.«B» (.ctor Sym.«d» [])]

theorem prio_run : checkRun c 100 (pcfg goD) [(0, pcfg outD)] (pcfg outD) = true := by decide +kernel
/-- Rule 1 (priority 50) matches `go(d)` and would give `other(d)`, but rule 0 (priority 40)
applies, so the step is not a step and the certificate is refused. -/
theorem prio_refused : checkRun c 100 (pcfg goD) [(1, pcfg otherD)] (pcfg otherD) = false := by
  decide +kernel

theorem prio_reaches :
    ∃ (hs : c.sortOf (pcfg goD) = some topCellSort) (hf : c.sortOf (pcfg outD) = some topCellSort),
      Reach (Step c) ⟨_, hs⟩ ⟨_, hf⟩ :=
  checkRun_sound ok srReady matchReady prio_run c.hooks

/-- info: 'Prio.CertTest.prio_reaches' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms prio_reaches

end Prio.CertTest
