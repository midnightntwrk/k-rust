/-
  The fixture `e6-rangemap-keys` (test/constructs/fixtures/e6-rangemap-keys; its kompiled text
  `f2-examples/e6rmkeys.kompile.kore`): `keys(RangeMap)` applied in a rule's right side, for every
  interpretation H of the points the text leaves open. Run from the package root:
  `lake env lean -j1 test/RangeMapKeysFixture.lean`.

  The text: `rule <k> go => res(keys(([0, 3) r|-> a) ([5, 7) r|-> b))) </k>`; kompile leaves the
  application of `keys` unevaluated in the rule's right side. The expectation is domains.md's prose
  (K 7.1.337, 620-625): `keys(M)` is the Set of all the ranges of M; a Set holds KItems, so each
  range as its injection into KItem.
  - `keys` is read as the interpreted symbol `rmKeys` (hook `RANGEMAP.keys`, an entry of
    `hookTable`), not as a parameter symbol: the rule's right side applies `rmKeys` and the text
    has no parameter symbol (`keys_interpreted`). The fixture `e6-rangemap`'s text declares `keys`
    and does not apply it, so its reading shows nothing of the symbol.
  - At `M := [0,3) ↦ a, [5,7) ↦ b`, `keys(M)` is the Set of `inj{Range,KItem}([0,3))` and
    `inj{Range,KItem}([5,7))` (`keys_value`), under every interpretation: `hook` gives a value, so
    no fallback is read (`keys_hookRes`).
  - `<k> go </k>` steps to `<k> res(keys(M)) </k>` under every interpretation (`go_step`), and to
    nothing else (`go_only`).
  The symbol numbers are the reader's for this text, each checked by its name (`syms_named`).
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.RangeMapKeysFixture

open KCore

definition_of defn from "f2-examples/e6rmkeys.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem

/-! ## The symbols and values -/

def kCell : Sym := 382
def aS : Sym := 384
def bS : Sym := 385
def goS : Sym := 386
def resS : Sym := 387

theorem syms_named : c.symName kCell = "Lbl'-LT-'k'-GT-'" ∧ c.symName aS = "Lbla" ∧ c.symName bS = "Lblb" ∧
    c.symName goS = "Lblgo" ∧ c.symName resS = "Lblres" := by
  decide +kernel

/-- **`keys` is an interpreted hook of the text**: the symbol the rule's right side applies under
`res` is `rmKeys`, named `Lblkeys'LParUndsRParUnds'RANGEMAP'Unds'Set'Unds'RangeMap`, whose hook is
`RANGEMAP.keys`, an entry of `hookTable`; the text has no parameter symbol (an applied library
symbol that no hook interprets is one). -/
theorem keys_interpreted : c.symName rmKeys = "Lblkeys'LParUndsRParUnds'RANGEMAP'Unds'Set'Unds'RangeMap" ∧
    isHook rmKeys = true ∧ regHookNames.lookup rmKeys = some "RANGEMAP.keys" ∧
    (hookTable.lookup rmKeys).isSome = true ∧ c.params = [] ∧
    (c.rules.map fun r => r.rhs.syms.contains rmKeys) = [true] := by
  decide +kernel

def a : GroundTerm := .ctor aS []
def b : GroundTerm := .ctor bS []

/-- `M`, the canonical value of `([0,3) r|-> a) ([5,7) r|-> b)`. -/
def M : GroundTerm := rmV [(rangeT 0 3, a), (rangeT 5 7, b)]

/-- The Set of M's two ranges, each injected into KItem, in the Set's order. -/
def keysM : GroundTerm :=
  .set Srt.set [.inj Srt.range Srt.kitem (rangeT 0 3), .inj Srt.range Srt.kitem (rangeT 5 7)]

/-- **`keys(M)` is the Set of M's ranges** (domains.md 620-625): `rmKeysHook`'s value, which
`hook` gives at `rmKeys`; M is a value of sort RangeMap and the Set a value of sort Set. -/
theorem keys_value : rmKeysHook [M] = some keysM ∧ hook rmKeys [M] = some (some keysM) ∧
    c.sortOf M = some Srt.rangeMap ∧ c.sortOf keysM = some Srt.set := by
  decide +kernel

/-- Under every interpretation the result of `keys` at M is that Set: `hook` gives a value, and the
interpretation is read only where it gives none. -/
theorem keys_hookRes (H : HookParams) : (c.withHooks H).hookRes rmKeys [M] = some (some keysM) :=
  Semantics.hookRes_of_value keys_value.2.1

/-- The configuration `<k> t </k>` with the generated counter at 0. -/
def cfg (t : GroundTerm) : GroundTerm :=
  .ctor topLabel [.ctor kCell [.ctor kseq [t, .ctor dotk []]], .ctor counterLabel [int 0]]

/-! ## Under an interpretation -/

theorem raw_free : ∀ k ∈ c.params, k.raw = false := fun k hk => by
  rw [keys_interpreted.2.2.2.2.1] at hk; cases hk

theorem sortOfH (H : HookParams) : (c.withHooks H).sortOf = c.sortOf := Semantics.sortOf_withHooks c H raw_free

private theorem hok : c.ok = true := by decide +kernel
private theorem hsr : c.srReady = true := by decide +kernel
private theorem hmr : c.matchReady = true := by decide +kernel
theorem coreOK : c.coreOK = true := by decide +kernel

theorem cfg_sorted (t : GroundTerm) (H : HookParams) (h : c.sortOf (cfg t) = some topCellSort) :
    (c.withHooks H).sortOf (cfg t) = some topCellSort := by rw [sortOfH]; exact h

/-- `<k> go </k>` and `<k> res(keys(M)) </k>`. -/
def Go (H : HookParams) : Config (c.withHooks H) := ⟨cfg (.ctor goS []), cfg_sorted _ H (by decide +kernel)⟩
def Res (H : HookParams) : Config (c.withHooks H) :=
  ⟨cfg (.ctor resS [keysM]), cfg_sorted _ H (by decide +kernel)⟩

/-! ## The step, for every interpretation -/

/-- **`<k> go </k>` steps to `<k> res(keys(M)) </k>`**, under every interpretation: the check reads
none (`checkStep_withHooks`). -/
theorem go_step (H : HookParams) : Step (c.withHooks H) (Go H) (Res H) := by
  have hok' := (Semantics.ok_withHooks c H).trans hok
  have hsr' := (Semantics.srReady_withHooks c H).trans hsr
  have hmr' := (Semantics.matchReady_withHooks c H).trans hmr
  have hc : Cert.checkStep (c.withHooks H) 50 (c.rules[0]'(by decide +kernel)) (cfg (.ctor goS []))
      (cfg (.ctor resS [keysM])) = true :=
    (Cert.checkStep_withHooks c H raw_free 50 _ _ _).trans (by decide +kernel)
  obtain ⟨_, hstep⟩ := Cert.step_of_listed hok' hsr' hmr' (x := Go H)
    (Cert.listed_of_checkStep (c := c.withHooks H) (List.getElem_mem _) hc)
  exact hstep

kernel_rfl clausesFixed_withHooks : ∀ (c : Semantics) (H : HookParams),
  (c.withHooks H).clausesFixed = c.clausesFixed

theorem coherent (H : HookParams) : CoherentAll (c.withHooks H) :=
  Det.coherentAll_of_nil ((Semantics.ok_withHooks c H).trans hok) ((Semantics.srReady_withHooks c H).trans hsr)
    ((Semantics.matchReady_withHooks c H).trans hmr) ((clausesFixed_withHooks c H).trans (by decide +kernel))
    ((Semantics.agreeObligations_withHooks c H).trans (by decide +kernel))

noncomputable def r0 : Rule := c.rules[0]'(by decide +kernel)

/-- The text has the one rule. -/
theorem rules_one {r : Rule} (h : r ∈ c.rules) : r = r0 := by
  have hl : c.rules.length = 1 := by decide +kernel
  obtain ⟨x, hx⟩ := List.length_eq_one_iff.mp hl
  have h0 : r0 = x := by unfold r0; simp only [hx, List.getElem_cons_zero]
  rw [hx, List.mem_singleton] at h
  rw [h, h0]

/-- The rule's left side `<k> go ~> . </k>` with the counter cell its one variable, which is the
one variable of its right side. -/
theorem r0_lhs : r0.lhs = .app topLabel [.app kCell [.app kseq [.app goS [], .app dotk []]], .var 0] := rfl
theorem r0_rhsVars : varOccs r0.rhs = [0] := by decide +kernel

/-- A match of the rule's left side at `<k> go </k>` gives the counter cell to variable 0. -/
theorem match_var {H : HookParams} {σ : Subst} (h : PatVal (c.withHooks H) σ r0.lhs (Go H).val) :
    σ.lookup 0 = some (.ctor counterLabel [int 0]) := by
  rw [r0_lhs] at h
  obtain ⟨-, vs, hvs, hps⟩ := PatVal.app_inv (by decide) h
    (show c.isCtor topLabel = true by decide +kernel)
  have hvs' : cfg (.ctor goS []) = .ctor topLabel vs := hvs
  cases hvs'
  obtain ⟨v1, vs1, hv1, -, hps1⟩ := hps.cons_inv
  cases hv1
  obtain ⟨v2, vs2, hv2, hp2, -⟩ := hps1.cons_inv
  cases hv2
  exact hp2.var_inv

/-- **`<k> res(keys(M)) </k>` is the only successor of `<k> go </k>`**, under every
interpretation: the one rule's right side has one result at the left side's match. -/
theorem go_only (H : HookParams) (y : Config (c.withHooks H)) (h : Step (c.withHooks H) (Go H) y) :
    y = Res H := by
  obtain ⟨r, σ, hb⟩ := step_iff_by.mp h
  obtain ⟨r', σ', hb'⟩ := step_iff_by.mp (go_step H)
  cases rules_one hb.mem
  cases rules_one hb'.mem
  have hag : ∀ i ∈ varOccs r0.rhs, σ.lookup i = σ'.lookup i := fun i hi => by
    rw [r0_rhsVars, List.mem_singleton] at hi
    subst hi
    rw [match_var hb.hmatch, match_var hb'.hmatch]
  exact Subtype.ext (Option.some.inj
    (EvalTerm.functional (coherent H) (Exec.EvalTerm.congr hb.heval hag) hb'.heval))

/-- info: 'KCore.RangeMapKeysFixture.keys_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms keys_value
/-- info: 'KCore.RangeMapKeysFixture.go_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms go_step
/-- info: 'KCore.RangeMapKeysFixture.go_only' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms go_only

end KCore.RangeMapKeysFixture
