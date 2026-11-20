/-
  The steps of e3-ml-rule-lhs-or's rule, under every interpretation of the parameters: K 7.1.337
  kompile's text of the fixture (`f2-examples/e3-ml-rule-lhs-or.kompile.kore`,
  `rule <k> d(X, a()) #Or d(a(), X) => X ... </k>`), read by the reader, the statement over
  `c0.withHooks H` for every `H : HookParams`, `c0` the reading. Run from the package root:
  `lake env lean -j1 test/RuleLhsOrStepH.lean`.

  Sentence 104 is read through `orSplit` as two rules, one per disjunct: `d(X, a()) => X` and
  `d(a(), X) => X`, with no condition (`read_shape`). An element of `d(X, a()) ∨ d(a(), X)` is
  `d(x, a)` or `d(a, x)`, x the value of X, so:
  `lhsOr_steps`: the one successor of `<k> d(b, a) </k>` and of `<k> d(a, b) </k>` is `<k> b </k>`
  (one disjunct holds each, at X the value `b`); the one successor of `<k> d(a, a) </k>` is
  `<k> a </k>` (both disjuncts hold it, each at X the value `a`); `<k> d(b, b) </k>` has no
  successor (neither disjunct holds it: `a` and `b` are apart). The rules bind their variable on
  the left side, so the executable step lists the successors exactly (`CExec.execReady`,
  `CExec.step_iff_at`), and the list at the four configurations is the same under every H
  (`dba_withHooks`, `dab_withHooks`, `daa_withHooks`, `dbb_withHooks`, checked by the kernel: the
  text declares no function and no parameter that is an open generator).

  test/NoteOrVar.lean ties Γ's two rule items to sentence 104 for every H (`rule_from_text`), on
  `f2-examples/mlorvar.kompile.kore`, the same text byte for byte.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

open KCore
open ML Faithful

namespace RuleLhsOrStepH

/-- The configuration `<generatedTop>(<k>(kseq(inj{s,KItem}(st), dotk)), <generatedCounter>(0))`,
the k cell's symbol `kCell`. -/
def cfgOf (kCell : Sym) (s : Srt) (st : GroundTerm) : GroundTerm :=
  .ctor topLabel [.ctor kCell [.ctor kseq [.inj s Srt.kitem st, .ctor dotk []]], .ctor counterLabel [int 0]]

/-- The configuration pattern `<generatedTop>(<k>(kseq(inj{s,KItem}(p), Vk)), Vc)`. -/
def cfgPat (kCell : Sym) (s : Srt) (p : Term) (k c : Nat) : Term :=
  .app topLabel [.app kCell [.app kseq [.inj s Srt.kitem p, .var k]], .var c]

def exp : Srt := 32
def kCell : Sym := 383
def symA : Sym := 385
def symB : Sym := 386
def symD : Sym := 388

def aT : GroundTerm := .ctor symA []
def bT : GroundTerm := .ctor symB []
def cfg (st : GroundTerm) : GroundTerm := cfgOf kCell exp st

namespace MlLhsOr
open KCore.TieRuleLhs (cfgH)

definition_of defn from "f2-examples/e3-ml-rule-lhs-or.kompile.kore"

noncomputable abbrev c0 : Semantics := defn.sem

theorem noRaw0 : ∀ k ∈ c0.params, k.raw = false := by decide +kernel

theorem names_ok : c0.sortName exp = "Exp" ∧ c0.symName kCell = "Lbl'-LT-'k'-GT-'" ∧
    c0.symName symA = "Lbla" ∧ c0.symName symB = "Lblb" ∧ c0.symName symD = "Lbld" := by
  decide +kernel

/-- The rules as read, one per disjunct: `d(X, a()) => X` and `d(a(), X) => X`, X the variable 0,
no `requires`, no `ensures`, no existential variable, and no condition beside the match. -/
theorem read_shape : c0.rules.map (fun r => (r.lhs, r.req.isNone, r.rhs, r.ens.isNone, r.exs, r.pre, r.post)) =
    [(cfgPat kCell exp (.app symD [.var 0, .app symA []]) 1 2, true, cfgPat kCell exp (.var 0) 1 2, true, [],
      .top, .top),
     (cfgPat kCell exp (.app symD [.app symA [], .var 0]) 1 2, true, cfgPat kCell exp (.var 0) 1 2, true, [],
      .top, .top)] := rfl

theorem hready : CExec.execReady c0 = true := by decide +kernel
theorem noFns : c0.fns = [] := by decide +kernel
/-- The text declares no function, so evaluation has one result under every interpretation. -/
theorem fnDetH (H : HookParams) : FnDet (c0.withHooks H) :=
  fnDet_of_agree (fun _ h => by rw [show (c0.withHooks H).fns = c0.fns from rfl, noFns] at h; cases h)
    (fun _ h => by rw [show (c0.withHooks H).fns = c0.fns from rfl, noFns] at h; cases h)

def DBA : Config c0 := ⟨cfg (.ctor symD [bT, aT]), by decide +kernel⟩
def DAB : Config c0 := ⟨cfg (.ctor symD [aT, bT]), by decide +kernel⟩
def DAA : Config c0 := ⟨cfg (.ctor symD [aT, aT]), by decide +kernel⟩
def DBB : Config c0 := ⟨cfg (.ctor symD [bT, bT]), by decide +kernel⟩
def A : Config c0 := ⟨cfg aT, by decide +kernel⟩
def B : Config c0 := ⟨cfg bT, by decide +kernel⟩

kernel_rfl dba_withHooks : ∀ H : HookParams,
  CExec.successorsN (c0.withHooks H) 50 DBA.val = CExec.successorsN c0 50 DBA.val
kernel_rfl dab_withHooks : ∀ H : HookParams,
  CExec.successorsN (c0.withHooks H) 50 DAB.val = CExec.successorsN c0 50 DAB.val
kernel_rfl daa_withHooks : ∀ H : HookParams,
  CExec.successorsN (c0.withHooks H) 50 DAA.val = CExec.successorsN c0 50 DAA.val
kernel_rfl dbb_withHooks : ∀ H : HookParams,
  CExec.successorsN (c0.withHooks H) 50 DBB.val = CExec.successorsN c0 50 DBB.val
kernel_rfl dba_fuel_withHooks : ∀ H : HookParams,
  CExec.outOfFuel (c0.withHooks H) 50 DBA.val = CExec.outOfFuel c0 50 DBA.val
kernel_rfl dab_fuel_withHooks : ∀ H : HookParams,
  CExec.outOfFuel (c0.withHooks H) 50 DAB.val = CExec.outOfFuel c0 50 DAB.val
kernel_rfl daa_fuel_withHooks : ∀ H : HookParams,
  CExec.outOfFuel (c0.withHooks H) 50 DAA.val = CExec.outOfFuel c0 50 DAA.val
kernel_rfl dbb_fuel_withHooks : ∀ H : HookParams,
  CExec.outOfFuel (c0.withHooks H) 50 DBB.val = CExec.outOfFuel c0 50 DBB.val

theorem dba_list : CExec.successorsN c0 50 DBA.val = [B.val] := by decide +kernel
theorem dab_list : CExec.successorsN c0 50 DAB.val = [B.val] := by decide +kernel
/-- Both rules apply at `d(a, a)`, each with the successor `<k> a </k>`. -/
theorem daa_list : ∀ y, y ∈ CExec.successorsN c0 50 DAA.val ↔ y = A.val := by
  have h : CExec.successorsN c0 50 DAA.val = [A.val, A.val] := by decide +kernel
  intro y
  rw [h]
  simp only [List.mem_cons, List.not_mem_nil, or_false, or_self]
theorem dbb_list : CExec.successorsN c0 50 DBB.val = [] := by decide +kernel

/-- **`orSplit`, for every interpretation**: the one successor of `<k> d(b, a) </k>` and of
`<k> d(a, b) </k>` is `<k> b </k>`, the one successor of `<k> d(a, a) </k>` is `<k> a </k>`, and
`<k> d(b, b) </k>` has no successor: a configuration steps exactly where one of the disjuncts
`d(X, a())`, `d(a(), X)` holds its k cell's item, to the value of X there. -/
theorem lhsOr_steps (H : HookParams) :
    (∀ y, Step (c0.withHooks H) (cfgH noRaw0 DBA H) y ↔ y = cfgH noRaw0 B H) ∧
    (∀ y, Step (c0.withHooks H) (cfgH noRaw0 DAB H) y ↔ y = cfgH noRaw0 B H) ∧
    (∀ y, Step (c0.withHooks H) (cfgH noRaw0 DAA H) y ↔ y = cfgH noRaw0 A H) ∧
    ∀ y, ¬ Step (c0.withHooks H) (cfgH noRaw0 DBB H) y := by
  have hr := (CExec.execReady_withHooks c0 H).trans hready
  refine ⟨fun y => ?_, fun y => ?_, fun y => ?_, CExec.noStep_at hr (fnDetH H) (n := 50) (x := cfgH noRaw0 DBB H)
    ((dbb_fuel_withHooks H).trans (by decide +kernel)) ((dbb_withHooks H).trans dbb_list)⟩
  · have hf : CExec.outOfFuel (c0.withHooks H) 50 (cfgH noRaw0 DBA H).val = false :=
      (dba_fuel_withHooks H).trans (by decide +kernel)
    have hl : CExec.successorsN (c0.withHooks H) 50 (cfgH noRaw0 DBA H).val = [B.val] :=
      (dba_withHooks H).trans dba_list
    rw [CExec.step_iff_at (x := cfgH noRaw0 DBA H) (y := y) hr (fnDetH H) hf, hl, List.mem_singleton]
    exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
  · have hf : CExec.outOfFuel (c0.withHooks H) 50 (cfgH noRaw0 DAB H).val = false :=
      (dab_fuel_withHooks H).trans (by decide +kernel)
    have hl : CExec.successorsN (c0.withHooks H) 50 (cfgH noRaw0 DAB H).val = [B.val] :=
      (dab_withHooks H).trans dab_list
    rw [CExec.step_iff_at (x := cfgH noRaw0 DAB H) (y := y) hr (fnDetH H) hf, hl, List.mem_singleton]
    exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
  · have hf : CExec.outOfFuel (c0.withHooks H) 50 (cfgH noRaw0 DAA H).val = false :=
      (daa_fuel_withHooks H).trans (by decide +kernel)
    have hl : CExec.successorsN (c0.withHooks H) 50 (cfgH noRaw0 DAA H).val = CExec.successorsN c0 50 DAA.val :=
      daa_withHooks H
    rw [CExec.step_iff_at (x := cfgH noRaw0 DAA H) (y := y) hr (fnDetH H) hf, hl, daa_list]
    exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩

/-- info: 'RuleLhsOrStepH.MlLhsOr.lhsOr_steps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms lhsOr_steps

end MlLhsOr

end RuleLhsOrStepH
