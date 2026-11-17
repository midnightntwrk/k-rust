/-
  The fixture `e6-rangemap` (test/constructs/fixtures/e6-rangemap; its kompiled text
  `f2-examples/e6rm.kompile.kore`) at the level of Γ and of `Step`, for every interpretation H of the
  points the text leaves open. Run from the package root: `lake env lean test/RangeMapGamma.lean`.

  The text: `m => ([0, 3) r|-> a) ([5, 7) r|-> b)` (`m` a total function of no argument) and the rule
  `<k> go => res(size(m), m[1], m[3] orDefault c, 2 in_keys(m), 3 in_keys(m), size(M2), find_range(M2, 4),
  size(([0, 10) r|-> a) [ [3, 5) <- b ]), size(([0, 10) r|-> a) [ [3, 5) <- undef ]),
  ([0, 10) r|-> a) -RangeMap ([3, 5) r|-> a)) </k>`, with `M2 := ([0, 3) r|-> a) ([3, 5) r|-> a)`. Each
  expectation is from domains.md's prose (K 7.1.337) and the hooks' table, written here as literals:
  - `m` is `M := [0,3) ↦ a, [5,7) ↦ b`, for every H (`m_value`).
  - `go` steps to `res(2, a, c, true, false, 1, [0,5), 3, 2, [0,3) ↦ a, [5,10) ↦ a)`, for every H
    (`go_step`): sizes 2, 1, 3, 2; `m[1] = a` and `m[3] orDefault c = c` (ranges inclusive below,
    exclusive above, 498-499); `2 in_keys` true and `3` false; `M2` merged into `[0,5)` (499-500), so
    `find_range(M2, 4) = [0,5)`; the difference. That configuration has no successor (`res_stuck`).
  - Γ (c.withHooks H) holds, for every H, the graph sentence of each of those applications at its
    value (`gamma_vals`).
  - The two overlapping concatenations, of two values and of one value (`[0,3) ↦ a` with
    `[2,5) ↦ a`), are silent: the text names a run's exception (503-504) and "a partial function
    only defined on range maps with non overlapping ranges" (600-602), no `#False`, and the
    production is not `total` (508), so it states no value there, equal values included. Γ entails
    neither that the concatenation is ⊥ nor that it is `M` over the interpretations
    (`overlaps_undetermined`).
  - `M[9]`, a key of no range of M, is silent (534-535: the text describes a run's exception, no
    value): Γ entails neither that it is ⊥ nor that it is `a` over the interpretations
    (`lookup9_undetermined`), under `HookParams.none` it is ⊥ and under the interpretation answering
    `a` it is `a`, both theories having models (`sound_hyp`).
  The symbol numbers are the reader's for this text, each checked by its name (`syms_named`).
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.RangeMapGammaTest

open KCore ML Faithful

definition_of defn from "f2-examples/e6rm.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem

/-! ## The symbols and values -/

def kCell : Sym := 382
def aS : Sym := 384
def bS : Sym := 385
def cS : Sym := 386
def goS : Sym := 387
def resS : Sym := 388
def mS : Sym := 389

theorem syms_named : c.symName kCell = "Lbl'-LT-'k'-GT-'" ∧ c.symName aS = "Lbla" ∧ c.symName bS = "Lblb" ∧
    c.symName cS = "Lblc" ∧ c.symName goS = "Lblgo" ∧ c.symName resS = "Lblres" ∧ c.symName mS = "Lblm" := by
  decide +kernel

/-- Three KItem values. -/
def a : GroundTerm := .ctor aS []
def b : GroundTerm := .ctor bS []
def cv : GroundTerm := .ctor cS []

def elem (x y : Int) (v : GroundTerm) : GroundTerm := rmV [(rangeT x y, v)]

/-- `M`, the canonical value of `([0,3) r|-> a) ([5,7) r|-> b)`. -/
def M : GroundTerm := rmV [(rangeT 0 3, a), (rangeT 5 7, b)]
/-- `([0,3) r|-> a) ([3,5) r|-> a)`, merged (499-500). -/
def M2 : GroundTerm := rmV [(rangeT 0 5, a)]
def M10 : GroundTerm := elem 0 10 a
/-- `M10 [ [3,5) <- b ]` and `M10 [ [3,5) <- undef ]` (564-566, 574-576). -/
def Mupd : GroundTerm := rmV [(rangeT 0 3, a), (rangeT 3 5, b), (rangeT 5 10, a)]
def Mrem : GroundTerm := rmV [(rangeT 0 3, a), (rangeT 5 10, a)]
/-- `M10 -RangeMap ([3,5) r|-> a)` (584-588). -/
def Mdiff : GroundTerm := rmV [(rangeT 0 3, a), (rangeT 5 10, a)]

/-- The configuration `<k> t </k>` with the generated counter at 0. -/
def cfg (t : GroundTerm) : GroundTerm :=
  .ctor topLabel [.ctor kCell [.ctor kseq [t, .ctor dotk []]], .ctor counterLabel [int 0]]

def resV : GroundTerm :=
  .ctor resS [int 2, a, cv, bool true, bool false, int 1, rangeT 0 5, int 3, int 2, Mdiff]

/-! ## Sorts under an interpretation -/

theorem params_nil : c.params = [] := by decide +kernel

theorem raw_free : ∀ k ∈ c.params, k.raw = false := fun k hk => by rw [params_nil] at hk; cases hk

/-- A value's sort under every interpretation: the text has no open generator. -/
theorem sortOfH (H : HookParams) : (c.withHooks H).sortOf = c.sortOf := Semantics.sortOf_withHooks c H raw_free
theorem sortsOfH (H : HookParams) : (c.withHooks H).sortsOf = c.sortsOf := Semantics.sortsOf_withHooks c H raw_free

/-! ## The decided conditions -/

private theorem hok : c.ok = true := by decide +kernel
private theorem hsr : c.srReady = true := by decide +kernel
private theorem hmr : c.matchReady = true := by decide +kernel
theorem coreOK : c.coreOK = true := by decide +kernel


/-! ## `m`, for every interpretation -/

theorem evalFC_withHooks (H : HookParams) (n : Nat) (f : Sym) (vs : List GroundTerm) :
    Cert.evalFC (c.withHooks H) n f vs = Cert.evalFC c n f vs :=
  Cert.evalFC_withHooks c H raw_free n f vs

private theorem hfn : c.lookupFn mS = some (c.fns[0]'(by decide +kernel)) := rfl

/-- `m`'s one equation gives `M` under every interpretation: `evalFC` reads none. -/
theorem m_value (H : HookParams) : Eval (c.withHooks H) mS [] (some M) := by
  have hok' := (Semantics.ok_withHooks c H).trans hok
  have hsr' := (Semantics.srReady_withHooks c H).trans hsr
  have hmr' := (Semantics.matchReady_withHooks c H).trans hmr
  have hF : Exec.evalF (c.withHooks H) 50 mS [] = some (some M) :=
    Cert.evalFC_sound 50 (by rw [evalFC_withHooks]; decide +kernel)
  exact Exec.evalF_sound (sortCtx_of hok' hsr' (Exec.ovlCase_of hmr')) (Exec.clauseCtx_of hok') (Exec.matchCtx_of hmr') 50
    hF (by rw [Semantics.lookupFn_withHooks]; exact hfn) (by rw [sortsOfH]; decide +kernel)

/-- `FnHyp` under every interpretation: the one obligation the deciders name is `m`'s totality,
which `m_value` gives; the rest are decided on the data. -/
theorem fnHyp (H : HookParams) : FnHyp (c.withHooks H) := by
  have hcore : (c.withHooks H).coreOK = true := (Semantics.coreOK_withHooks c H).trans coreOK
  have hpl : (c.withHooks H).plain = true := (Semantics.plain_withHooks c H).trans (by decide +kernel)
  refine fnHyp_of_core (t := defn.cert) hcore
    (Semantics.rightHeld_withHooks (Semantics.rightHeld_of_valued (by decide +kernel)) H (by decide +kernel)) ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro f hf
    rw [orderObligations_withHooks, certObligations_withHooks,
      show c.orderObligations ++ defn.cert.obligations c = [] by decide +kernel] at hf
    exact absurd hf List.not_mem_nil
  · intro f hf fn hlook vs hvs
    rw [Semantics.totalObligations_withHooks, show c.totalObligations = [mS] by decide +kernel] at hf
    rw [List.mem_singleton] at hf
    subst hf
    rw [Semantics.lookupFn_withHooks, hfn, Option.some.injEq] at hlook
    subst hlook
    have hargs : (c.fns[0]'(by decide +kernel)).args = [] := by decide +kernel
    rw [hargs] at hvs
    cases vs with
    | nil => exact ⟨M, m_value H⟩
    | cons v vs =>
      rw [sortsOfH] at hvs; unfold Semantics.sortsOf at hvs
      split at hvs <;> simp at hvs
  · intro f hf
    rw [Semantics.agreeObligations_withHooks, show c.agreeObligations = [] by decide +kernel] at hf
    exact absurd hf List.not_mem_nil
  · intro p hp
    rw [Semantics.matchObligations_withHooks, show c.matchObligations = [] by decide +kernel] at hp
    exact absurd hp List.not_mem_nil
  · intro o ho
    rw [Semantics.lazyObligations_withHooks, show c.lazyObligations = [] by decide +kernel] at ho
    exact absurd ho List.not_mem_nil
  · exact openDecided_of_plain (fun r hr => needsWitness_of_binds ((Semantics.plain_parts hpl).1 r hr))
      (fun fn hfn cl hcl => Clause.needsWitness_of_binds ((Semantics.plain_parts hpl).2.1 fn hfn cl hcl))
  · exact openLaws_of_plain (Semantics.plain_parts hpl).2.2

/-! ## The step, for every interpretation -/

private theorem hrule : c.rules[0]? = some (c.rules[0]'(by decide +kernel)) := rfl

theorem cfg_sorted (t : GroundTerm) (H : HookParams) (h : c.sortOf (cfg t) = some topCellSort) :
    (c.withHooks H).sortOf (cfg t) = some topCellSort := by rw [sortOfH]; exact h

/-- **`go` steps to `res(2, a, c, true, false, 1, [0,5), 3, 2, [0,3) ↦ a, [5,10) ↦ a)`**, under every
interpretation: the check reads none (`checkStep_withHooks`). -/
theorem go_step (H : HookParams) :
    Step (c.withHooks H) ⟨cfg (.ctor goS []), cfg_sorted _ H (by decide +kernel)⟩
      ⟨cfg resV, cfg_sorted _ H (by decide +kernel)⟩ := by
  have hok' := (Semantics.ok_withHooks c H).trans hok
  have hsr' := (Semantics.srReady_withHooks c H).trans hsr
  have hmr' := (Semantics.matchReady_withHooks c H).trans hmr
  have hc : Cert.checkStep (c.withHooks H) 50 (c.rules[0]'(by decide +kernel)) (cfg (.ctor goS [])) (cfg resV) = true :=
    (Cert.checkStep_withHooks c H raw_free 50 _ _ _).trans (by decide +kernel)
  obtain ⟨_, hstep⟩ := Cert.step_of_listed hok' hsr' hmr'
    (x := ⟨cfg (.ctor goS []), cfg_sorted _ H (by decide +kernel)⟩)
    (Cert.listed_of_checkStep (c := c.withHooks H) (List.getElem_mem _) hc)
  exact hstep

kernel_rfl clausesFixed_withHooks : ∀ (c : Semantics) (H : HookParams),
  (c.withHooks H).clausesFixed = c.clausesFixed

theorem coherent (H : HookParams) : CoherentAll (c.withHooks H) :=
  Det.coherentAll_of_nil ((Semantics.ok_withHooks c H).trans hok) ((Semantics.srReady_withHooks c H).trans hsr)
    ((Semantics.matchReady_withHooks c H).trans hmr) ((clausesFixed_withHooks c H).trans (by decide +kernel))
    ((Semantics.agreeObligations_withHooks c H).trans (by decide +kernel))

theorem res_stuckCheck : Cert.stuckCheck c 50 (cfg resV) = true := by decide +kernel

/-- The configuration `go` reaches has no successor, under every interpretation. -/
theorem res_stuck (H : HookParams) : ∀ y, ¬ Step (c.withHooks H) ⟨cfg resV, cfg_sorted _ H (by decide +kernel)⟩ y :=
  Cert.stuckCheck_sound hok hsr hmr H (coherent H) (n := 50) res_stuckCheck

/-! ## Γ at the interpreted applications -/

/-- The interpreted symbol `k` applied to the values `vs`, as Γ writes it. -/
abbrev appP (c : Semantics) (k : CtorSig) (vs : List GroundTerm) : KoreAML.P :=
  KoreAML.den (symApp c k.name (GroundTerm.koreList c vs))

def sig (f : Sym) : CtorSig := (lookupSig hookSigs f).getD default

/-- A point: the interpreted symbol, its arguments, and a value. -/
structure Pt where
  f : Sym
  vs : List GroundTerm
  v : GroundTerm
  deriving DecidableEq

/-- The applications of the rule's right side (and of `m`'s), at their values. -/
def vals : List Pt :=
  [⟨rmConcat, [elem 0 3 a, elem 5 7 b], M⟩,
   ⟨rmSize, [M], int 2⟩,
   ⟨rmLookup, [M, kint 1], a⟩,
   ⟨rmLookupOrDefault, [M, kint 3, cv], cv⟩,
   ⟨rmInKeys, [kint 2, M], bool true⟩,
   ⟨rmInKeys, [kint 3, M], bool false⟩,
   ⟨rmConcat, [elem 0 3 a, elem 3 5 a], M2⟩,
   ⟨rmSize, [M2], int 1⟩,
   ⟨rmFindRange, [M2, kint 4], rangeT 0 5⟩,
   ⟨rmUpdate, [M10, rangeT 3 5, b], Mupd⟩,
   ⟨rmSize, [Mupd], int 3⟩,
   ⟨rmRemove, [M10, rangeT 3 5], Mrem⟩,
   ⟨rmSize, [Mrem], int 2⟩,
   ⟨rmDifference, [M10, elem 3 5 a], Mdiff⟩]

theorem vals_ok : vals.all (fun p => (sig p.f) ∈ hookSigs && (sig p.f).name == p.f &&
    c.sortsOf p.vs == some (sig p.f).args && hook p.f p.vs == some (some p.v)) = true := by
  decide +kernel

/-- Where `hook` gives a value, Γ states it, in every semantics. -/
theorem gamma_val (c : Semantics) {k : CtorSig} (hk : k ∈ hookSigs) {vs : List GroundTerm}
    (hvs : c.sortsOf vs = some k.args) {v : GroundTerm} (hh : hook k.name vs = some (some v)) :
    Γ c (appP c k vs ≡ den c v) :=
  Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl ⟨k, vs, some v, hk, hvs, hh, nofun, rfl⟩)))))

/-- Off the silent points, Γ states ⊥ where `hook` gives no value, in every semantics. -/
theorem gamma_bot (c : Semantics) {k : CtorSig} (hk : k ∈ hookSigs) {vs : List GroundTerm}
    (hvs : c.sortsOf vs = some k.args) (hh : hook k.name vs = some none) (hs : silent k.name vs = false) :
    Γ c (appP c k vs ≡ ⊥) :=
  Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl ⟨k, vs, none, hk, hvs, hh, fun _ => hs, rfl⟩)))))

/-- **Γ holds each application's value, for every interpretation**, and so entails it. -/
theorem gamma_vals : ∀ p ∈ vals, ∀ H : HookParams,
    Γ (c.withHooks H) (appP (c.withHooks H) (sig p.f) p.vs ≡ den (c.withHooks H) p.v) ∧
    (Γ (c.withHooks H) ⊧ (appP (c.withHooks H) (sig p.f) p.vs ≡ den (c.withHooks H) p.v)) := by
  intro p hp H
  have h := List.all_eq_true.mp vals_ok p hp
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hk, hname⟩, hvs⟩, hh⟩ := h
  have hg := gamma_val (c.withHooks H) hk (by rw [sortsOfH]; exact hvs) (by rw [hname]; exact hh)
  exact ⟨hg, fun hI => hI _ hg⟩

/-! ## Silent points: undetermined over the interpretations -/

/-- The interpretation that gives `v` everywhere. -/
def constH (v : GroundTerm) : HookParams := ⟨fun _ _ => some v⟩

/-- At a silent point, `Γ (c.withHooks H)` holds the fallback's graph. -/
theorem gamma_fallback (H : HookParams) {k : CtorSig}
    (hks : lookupSig hookSigs k.name = some k) {vs : List GroundTerm}
    (hvs : c.sortsOf vs = some k.args) (hh : hook k.name vs = some none) (hs : silent k.name vs = true) :
    Γ (c.withHooks H) (appP (c.withHooks H) k vs ≡ (match (c.withHooks H).fallback k.name vs with
      | some v => den (c.withHooks H) v
      | none => ⊥)) :=
  Or.inr (Or.inl ⟨k, vs, (lookupSig_spec hks).1, by rw [sortsOfH]; exact hvs, hh, hs, rfl⟩)

theorem fallback_none (k : CtorSig) (vs : List GroundTerm) :
    (c.withHooks HookParams.none).fallback k.name vs = none := by
  unfold Semantics.fallback; split <;> rfl

theorem fallback_const {k : CtorSig} (hks : lookupSig hookSigs k.name = some k)
    (vs : List GroundTerm) {v : GroundTerm} (hv : c.sortOf v = some k.result) :
    (c.withHooks (constH v)).fallback k.name vs = some v := by
  unfold Semantics.fallback; rw [hks, sortOfH]
  simp [Semantics.withHooks, constH, Option.filter, hv]

/-- **A silent point is undetermined**: over the interpretations, Γ entails neither that the
application has no value nor that it is `v`. Under `constH v` it is `v` in every model, under
`HookParams.none` it is ⊥ in every model, and both theories have models (`sound_hyp`). -/
theorem undetermined {k : CtorSig} (hks : lookupSig hookSigs k.name = some k) {vs : List GroundTerm}
    (hvs : c.sortsOf vs = some k.args) (hh : hook k.name vs = some none) (hs : silent k.name vs = true)
    {v : GroundTerm} (hv : c.sortOf v = some k.result) :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧ (appP (c.withHooks H) k vs ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧ (appP (c.withHooks H) k vs ≡ den (c.withHooks H) v)) := by
  constructor
  · intro hall
    obtain ⟨_, _, I, hI⟩ := (sound_hyp (c.withHooks (constH v)) ((Semantics.coreOK_withHooks c _).trans coreOK)
      (fnHyp _)).1
    have hIΓ : I ⊧ᴵP Γ (c.withHooks (constH v)) := fun φ h => hI φ (Or.inl (Or.inl h))
    have hD := defOK hIΓ
    have hfb := hIΓ _ (gamma_fallback (constH v) hks hvs hh hs)
    rw [fallback_const hks _ hv] at hfb
    have hbot := hall (constH v) hIΓ
    obtain ⟨x, hx, -⟩ := den_single hIΓ (c := c.withHooks (constH v)) (by rw [sortOfH]; exact hv) KoreAML.val0
    have h1 := (KoreAML.interp_equal hD).mp (hfb KoreAML.val0 default) x
    have h2 := (KoreAML.interp_equal hD).mp (hbot KoreAML.val0 default) x
    exact absurd (h2.mp (h1.mpr ((hx x).mpr rfl))) (by simp [Pattern.interpret])
  · intro hall
    obtain ⟨_, _, I, hI⟩ := (sound_hyp (c.withHooks HookParams.none)
      ((Semantics.coreOK_withHooks c _).trans coreOK) (fnHyp _)).1
    have hIΓ : I ⊧ᴵP Γ (c.withHooks HookParams.none) := fun φ h => hI φ (Or.inl (Or.inl h))
    have hD := defOK hIΓ
    have hfb := hIΓ _ (gamma_fallback HookParams.none hks hvs hh hs)
    rw [fallback_none] at hfb
    have hval := hall HookParams.none hIΓ
    obtain ⟨x, hx, -⟩ := den_single hIΓ (c := c.withHooks HookParams.none) (by rw [sortOfH]; exact hv)
      KoreAML.val0
    have h1 := (KoreAML.interp_equal hD).mp (hfb KoreAML.val0 default) x
    have h2 := (KoreAML.interp_equal hD).mp (hval KoreAML.val0 default) x
    exact absurd (h1.mp (h2.mpr ((hx x).mpr rfl))) (by simp [Pattern.interpret])

/-- `M[9]`: `hook` gives no value, the point is silent, and `a` has the result sort KItem. -/
theorem lookup9_ok : lookupSig hookSigs rmLookup = some (sig rmLookup) ∧ (sig rmLookup).name = rmLookup ∧
    c.sortsOf [M, kint 9] = some (sig rmLookup).args ∧ hook rmLookup [M, kint 9] = some none ∧
    silent rmLookup [M, kint 9] = true ∧ c.sortOf a = some (sig rmLookup).result := by
  decide +kernel

/-- **`M[9]` is undetermined**: over the interpretations, Γ entails neither that it has no value
nor that it is `a`. -/
theorem lookup9_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧ (appP (c.withHooks H) (sig rmLookup) [M, kint 9] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appP (c.withHooks H) (sig rmLookup) [M, kint 9] ≡ den (c.withHooks H) a)) := by
  obtain ⟨hks, hname, hvs, hh, hs, hv⟩ := lookup9_ok
  exact undetermined (by rw [hname]; exact hks) hvs (by rw [hname]; exact hh) (by rw [hname]; exact hs) hv

/-- The overlapping concatenations: of two values, and of one value; `M` is a value of the result
sort. -/
def overlaps : List Pt :=
  [⟨rmConcat, [elem 0 3 a, elem 2 5 b], M⟩,
   ⟨rmConcat, [elem 0 3 a, elem 2 5 a], M⟩]

/-- At each: `hook` gives no value, the point is silent, and `M` has the result sort RangeMap. -/
theorem overlaps_ok : overlaps.all (fun p => lookupSig hookSigs p.f == some (sig p.f) &&
    (sig p.f).name == p.f && c.sortsOf p.vs == some (sig p.f).args && hook p.f p.vs == some none &&
    silent p.f p.vs && c.sortOf p.v == some (sig p.f).result) = true := by
  decide +kernel

/-- **An overlapping concatenation is undetermined** (503-504, 600-602: no value is stated), equal
values included: over the interpretations, Γ entails neither that it has no value nor that it is
`M`. -/
theorem overlaps_undetermined : ∀ p ∈ overlaps,
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧ (appP (c.withHooks H) (sig p.f) p.vs ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appP (c.withHooks H) (sig p.f) p.vs ≡ den (c.withHooks H) p.v)) := by
  intro p hp
  have h := List.all_eq_true.mp overlaps_ok p hp
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨hks, hname⟩, hvs⟩, hh⟩, hs⟩, hv⟩ := h
  exact undetermined (by rw [hname]; exact hks) hvs (by rw [hname]; exact hh) (by rw [hname]; exact hs) hv

end KCore.RangeMapGammaTest

#print axioms KCore.RangeMapGammaTest.m_value
#print axioms KCore.RangeMapGammaTest.go_step
#print axioms KCore.RangeMapGammaTest.res_stuck
#print axioms KCore.RangeMapGammaTest.gamma_vals
#print axioms KCore.RangeMapGammaTest.overlaps_undetermined
#print axioms KCore.RangeMapGammaTest.lookup9_undetermined
