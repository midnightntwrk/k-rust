/-
  The steps of e3-ml-rule-lhs-or-rhs-and's rules (test/PredFixtures.lean's `RhsAnd.MlOrAnd`), under
  every interpretation of the parameters: K 7.1.337 kompile's text of the fixture
  (`f2-examples/e3-ml-rule-lhs-or-rhs-and.kompile.kore`, `rule <k> c(X) #Or d(X) => X #And a() ... </k>`),
  read by the reader, the statement over `c0.withHooks H` for every `H : HookParams`, `c0` the
  reading. Run from the package root: `lake env lean -j1 test/RuleOrAndStepH.lean`.

  Sentence 104 is read through `orSplit` as two rules, one per disjunct, each through `andTermsCut`
  in the variable form: `c(X) => X` and `d(X) => X`, each with `post := X ∈ a()` (`read_shape`).
  `orAnd_steps`: the one successor of `<k> c(a) </k>` and of `<k> d(a) </k>` is `<k> a </k>`, and
  `<k> c(b) </k>` has no successor (`X ∧ a()` is X where X is `a` and is empty elsewhere, and the
  rule of d does not match `c(b)`). The rules bind their variables on the left side and their
  `post` is a membership, so the executable step lists the successors exactly (`CExec.execReady`,
  `CExec.step_iff_at`), and the list at the three configurations is the same under every H
  (`ca_withHooks`, `da_withHooks`, `cb_withHooks`, checked by the kernel: the text declares no
  function and no parameter that is an open generator).

  test/TieE3MlRuleLhsOrRhsAnd104.lean ties Γ's two rule items to sentence 104 for every H
  (`rule_from_text_sig`).
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

open KCore
open ML Faithful

namespace RuleOrAndStepH

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
def symC : Sym := 387
def symD : Sym := 388

def aT : GroundTerm := .ctor symA []
def bT : GroundTerm := .ctor symB []
def cfg (st : GroundTerm) : GroundTerm := cfgOf kCell exp st

namespace MlOrAnd
open KCore.TieRuleLhs (cfgH)

definition_of defn from "f2-examples/e3-ml-rule-lhs-or-rhs-and.kompile.kore"

noncomputable abbrev c0 : Semantics := defn.sem

theorem noRaw0 : ∀ k ∈ c0.params, k.raw = false := by decide +kernel

theorem names_ok : c0.sortName exp = "Exp" ∧ c0.symName kCell = "Lbl'-LT-'k'-GT-'" ∧
    c0.symName symA = "Lbla" ∧ c0.symName symB = "Lblb" ∧ c0.symName symC = "Lblc" ∧
    c0.symName symD = "Lbld" := by
  decide +kernel

/-- The rules as read: `c(X) => X` and `d(X) => X`, X the variable 0, no `ensures`, no existential
variable, and `post` the membership `X ∈ a()`. -/
theorem read_shape : c0.rules.map (fun r => (r.lhs, r.rhs, r.ens.isNone, r.exs, r.post)) =
    [(cfgPat kCell exp (.app symC [.var 0]) 1 2, cfgPat kCell exp (.var 0) 1 2, true, [],
      .mem exp (.var 0) (.app symA [])),
     (cfgPat kCell exp (.app symD [.var 0]) 1 2, cfgPat kCell exp (.var 0) 1 2, true, [],
      .mem exp (.var 0) (.app symA []))] := rfl

theorem hready : CExec.execReady c0 = true := by decide +kernel
theorem noFns : c0.fns = [] := by decide +kernel
/-- The text declares no function, so evaluation has one result under every interpretation. -/
theorem fnDetH (H : HookParams) : FnDet (c0.withHooks H) :=
  fnDet_of_agree (fun _ h => by rw [show (c0.withHooks H).fns = c0.fns from rfl, noFns] at h; cases h)
    (fun _ h => by rw [show (c0.withHooks H).fns = c0.fns from rfl, noFns] at h; cases h)

def CA : Config c0 := ⟨cfg (.ctor symC [aT]), by decide +kernel⟩
def DA : Config c0 := ⟨cfg (.ctor symD [aT]), by decide +kernel⟩
def CB : Config c0 := ⟨cfg (.ctor symC [bT]), by decide +kernel⟩
def A : Config c0 := ⟨cfg aT, by decide +kernel⟩

kernel_rfl ca_withHooks : ∀ H : HookParams,
  CExec.successorsN (c0.withHooks H) 50 CA.val = CExec.successorsN c0 50 CA.val
kernel_rfl da_withHooks : ∀ H : HookParams,
  CExec.successorsN (c0.withHooks H) 50 DA.val = CExec.successorsN c0 50 DA.val
kernel_rfl cb_withHooks : ∀ H : HookParams,
  CExec.successorsN (c0.withHooks H) 50 CB.val = CExec.successorsN c0 50 CB.val
kernel_rfl ca_fuel_withHooks : ∀ H : HookParams,
  CExec.outOfFuel (c0.withHooks H) 50 CA.val = CExec.outOfFuel c0 50 CA.val
kernel_rfl da_fuel_withHooks : ∀ H : HookParams,
  CExec.outOfFuel (c0.withHooks H) 50 DA.val = CExec.outOfFuel c0 50 DA.val
kernel_rfl cb_fuel_withHooks : ∀ H : HookParams,
  CExec.outOfFuel (c0.withHooks H) 50 CB.val = CExec.outOfFuel c0 50 CB.val

theorem ca_list : CExec.successorsN c0 50 CA.val = [A.val] := by decide +kernel
theorem da_list : CExec.successorsN c0 50 DA.val = [A.val] := by decide +kernel
theorem cb_list : CExec.successorsN c0 50 CB.val = [] := by decide +kernel

/-- **`orSplit` with `andTermsCut` in the variable form, for every interpretation**: the one
successor of `<k> c(a) </k>` and of `<k> d(a) </k>` is `<k> a </k>`, and `<k> c(b) </k>` has no
successor: `a() ∧ X` is X where X is `a` and is empty elsewhere, at the rule of each disjunct. -/
theorem orAnd_steps (H : HookParams) :
    (∀ y, Step (c0.withHooks H) (cfgH noRaw0 CA H) y ↔ y = cfgH noRaw0 A H) ∧
    (∀ y, Step (c0.withHooks H) (cfgH noRaw0 DA H) y ↔ y = cfgH noRaw0 A H) ∧
    ∀ y, ¬ Step (c0.withHooks H) (cfgH noRaw0 CB H) y := by
  have hr := (CExec.execReady_withHooks c0 H).trans hready
  refine ⟨fun y => ?_, fun y => ?_, CExec.noStep_at hr (fnDetH H) (n := 50) (x := cfgH noRaw0 CB H)
    ((cb_fuel_withHooks H).trans (by decide +kernel)) ((cb_withHooks H).trans cb_list)⟩
  · have hf : CExec.outOfFuel (c0.withHooks H) 50 (cfgH noRaw0 CA H).val = false :=
      (ca_fuel_withHooks H).trans (by decide +kernel)
    have hl : CExec.successorsN (c0.withHooks H) 50 (cfgH noRaw0 CA H).val = [A.val] :=
      (ca_withHooks H).trans ca_list
    rw [CExec.step_iff_at (x := cfgH noRaw0 CA H) (y := y) hr (fnDetH H) hf, hl, List.mem_singleton]
    exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
  · have hf : CExec.outOfFuel (c0.withHooks H) 50 (cfgH noRaw0 DA H).val = false :=
      (da_fuel_withHooks H).trans (by decide +kernel)
    have hl : CExec.successorsN (c0.withHooks H) 50 (cfgH noRaw0 DA H).val = [A.val] :=
      (da_withHooks H).trans da_list
    rw [CExec.step_iff_at (x := cfgH noRaw0 DA H) (y := y) hr (fnDetH H) hf, hl, List.mem_singleton]
    exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩

/-- info: 'RuleOrAndStepH.MlOrAnd.orAnd_steps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms orAnd_steps

end MlOrAnd

end RuleOrAndStepH
