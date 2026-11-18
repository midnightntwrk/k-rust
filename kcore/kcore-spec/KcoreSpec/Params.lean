/-
  KCore, checked layer (P1.3): parameter symbols. A definition's hooked symbols that no registry hook
  interprets are parameters; `Semantics.hooks` interprets them, and `c.withHooks H` is the same
  definition under the interpretation H (Core.lean). Every generic theorem is stated for every
  `c`, so for every `c.withHooks H`, with no hypothesis on H: evaluation reads a parameter only
  through `paramVal`, which keeps a value of the declared result sort only (Evaluation.lean).

  The conditions decided on a definition's data never read `hooks`: each equation below is `rfl`
  for a variable `c`, so the kernel checks that the condition's definition does not unfold to
  `hooks`. A condition decided once on the parsed data (`hooks := HookParams.none`) therefore holds
  for every interpretation, and a decided theorem about the data (determinism up to listed
  overlaps) is a theorem about every interpretation (`deterministic_except_all`). The determinism
  kind for an interpretation (`Det.kindAll`, `Det.deciderAll`) is decided the same way: once on the
  data, its obligations stated under H.
-/
import KcoreSpec.DetSound
import KcoreSpec.DataCmd

set_option autoImplicit false

namespace KCore

kernel_rfl Semantics.ok_withHooks : ∀ (c : Semantics) (H : HookParams), (c.withHooks H).ok = c.ok
kernel_rfl Semantics.okAll_withHooks : ∀ (c : Semantics) (H : HookParams), (c.withHooks H).okAll = c.okAll
kernel_rfl Semantics.okM_withHooks : ∀ (c : Semantics) (H : HookParams), (c.withHooks H).okM = c.okM
kernel_rfl Semantics.srReady_withHooks :
  ∀ (c : Semantics) (H : HookParams), (c.withHooks H).srReady = c.srReady
kernel_rfl Semantics.matchReady_withHooks :
  ∀ (c : Semantics) (H : HookParams), (c.withHooks H).matchReady = c.matchReady
kernel_rfl Semantics.clausesFixed_withHooks :
  ∀ (c : Semantics) (H : HookParams), (c.withHooks H).clausesFixed = c.clausesFixed
kernel_rfl Semantics.matchObligations_withHooks :
  ∀ (c : Semantics) (H : HookParams), (c.withHooks H).matchObligations = c.matchObligations
kernel_rfl Semantics.agreeObligations_withHooks :
  ∀ (c : Semantics) (H : HookParams), (c.withHooks H).agreeObligations = c.agreeObligations
kernel_rfl Det.detOKExcept_withHooks : ∀ (c : Semantics) (T : Tables) (H : HookParams) (ix : Det.DetIndex)
  (ovl : List (Nat × Nat)), Det.detOKExcept (c.withHooks H) T ix ovl = Det.detOKExcept c T ix ovl
kernel_rfl Det.idxOK_withHooks : ∀ (c : Semantics) (T : Tables) (H : HookParams) (ix : Det.DetIndex),
  Det.idxOK (c.withHooks H) T ix = Det.idxOK c T ix
kernel_rfl Det.detCond_withHooks : ∀ (c : Semantics) (T : Tables) (H : HookParams) (p : Nat × Nat),
  Det.detCond (c.withHooks H) T p = Det.detCond c T p
kernel_rfl tables_withHooks : ∀ (c : Semantics) (H : HookParams), tables (c.withHooks H) = tables c
kernel_rfl Semantics.rawFree_withHooks :
  ∀ (c : Semantics) (H : HookParams), (c.withHooks H).rawFree = c.rawFree

/-- A value that applies no open generator has its sort at every interpretation: there the sort is
the tables' (`sortOfT_tables`), which hold no interpretation. -/
theorem Semantics.sortOf_withHooks_rawFree :
  ∀ (c : Semantics) (H : HookParams) {v : GroundTerm} (_hv : c.rawFree v = true),
    (c.withHooks H).sortOf v = c.sortOf v := fun c H v hv =>
  have hv' : (c.withHooks H).rawFree v = true := (congrFun (Semantics.rawFree_withHooks c H) v).trans hv
  (sortOfT_tables (c.withHooks H) v hv').symm.trans
    ((congrArg (fun T => sortOfT T c.lib v) (tables_withHooks c H)).trans (sortOfT_tables c v hv))

/-- A value's sort is the same under every interpretation where no parameter is an open generator
(`raw`): the sort of an open generator's application is read from the interpretation. -/
theorem Semantics.sortOf_withHooks :
  ∀ (c : Semantics) (H : HookParams) (_hr : ∀ k ∈ c.params, k.raw = false),
    (c.withHooks H).sortOf = c.sortOf := fun c H hr =>
  funext fun v => Semantics.sortOf_withHooks_rawFree c H (Semantics.rawFree_of_noRaw hr v)

kernel_rfl Definition.wf_withHooks :
  ∀ (d : Definition) (H : HookParams), wf { d with sem := d.sem.withHooks H } = wf d

/-- **Determinism up to listed overlaps, for every interpretation of the parameters**, from the
conditions decided once on the data and the coherence of the clauses of one priority under each
interpretation (`coherentAll_withHooks_of_nil`, FnExclusive.lean, where every clause is fixed and
no agreement is named); in a core `okM` accepts. -/
theorem Det.deterministic_except_all_okM {c : Semantics} (hok : c.okM = true) (hsr : c.srReady = true)
    (hmr : c.matchReady = true) (hmo : ∀ H, CoherentAll (c.withHooks H)) {T : Tables}
    (hT : T = tables c) {ix : Det.DetIndex} {ovl : List (Nat × Nat)}
    (hd : Det.detOKExcept c T ix ovl = true) (H : HookParams) {x y y' : Config (c.withHooks H)}
    (h : Step (c.withHooks H) x y) (h' : Step (c.withHooks H) x y') :
    y = y' ∨ ∃ i j, ((i, j) ∈ ovl ∨ (j, i) ∈ ovl) ∧ ∃ (hi : i < c.rules.length) (hj : j < c.rules.length),
      Det.Applies (c.withHooks H) c.rules[i] x.val ∧ Det.Applies (c.withHooks H) c.rules[j] x.val :=
  Det.deterministic_except_okM (c := c.withHooks H) ((Semantics.okM_withHooks c H).trans hok)
    ((Semantics.srReady_withHooks c H).trans hsr) ((Semantics.matchReady_withHooks c H).trans hmr)
    (hmo H) (hT.trans (tables_withHooks c H).symm) ((Det.detOKExcept_withHooks c T H ix ovl).trans hd) h h'

/-- **Determinism for every interpretation of the parameters**, from the condition decided once on
the data with no overlaps and coherence under each interpretation, in a core `okM` accepts. -/
theorem Det.deterministic_all_okM {c : Semantics} (hok : c.okM = true) (hsr : c.srReady = true)
    (hmr : c.matchReady = true) (hmo : ∀ H, CoherentAll (c.withHooks H)) {T : Tables}
    (hT : T = tables c) {ix : Det.DetIndex} (hd : Det.detOK c T ix = true) (H : HookParams)
    {x y y' : Config (c.withHooks H)} (h : Step (c.withHooks H) x y) (h' : Step (c.withHooks H) x y') :
    y = y' :=
  (Det.deterministic_except_all_okM hok hsr hmr hmo hT hd H h h').resolve_right
    fun ⟨_, _, hm, _⟩ => by rcases hm with hm | hm <;> cases hm

/-- **Determinism up to listed overlaps, for every interpretation of the parameters**, from the
conditions decided once on the data and the coherence of the clauses of one priority under each
interpretation (`coherentAll_withHooks_of_nil`, FnExclusive.lean, where every clause is fixed and
no agreement is named). -/
theorem Det.deterministic_except_all {c : Semantics} (hok : c.ok = true) (hsr : c.srReady = true)
    (hmr : c.matchReady = true) (hmo : ∀ H, CoherentAll (c.withHooks H)) {T : Tables}
    (hT : T = tables c) {ix : Det.DetIndex} {ovl : List (Nat × Nat)}
    (hd : Det.detOKExcept c T ix ovl = true) (H : HookParams) {x y y' : Config (c.withHooks H)}
    (h : Step (c.withHooks H) x y) (h' : Step (c.withHooks H) x y') :
    y = y' ∨ ∃ i j, ((i, j) ∈ ovl ∨ (j, i) ∈ ovl) ∧ ∃ (hi : i < c.rules.length) (hj : j < c.rules.length),
      Det.Applies (c.withHooks H) c.rules[i] x.val ∧ Det.Applies (c.withHooks H) c.rules[j] x.val :=
  Det.deterministic_except_all_okM (Semantics.okM_of_ok hok) hsr hmr hmo hT hd H h h'

/-- **Determinism for every interpretation of the parameters**, from the condition decided once on
the data with no overlaps and coherence under each interpretation. -/
theorem Det.deterministic_all {c : Semantics} (hok : c.ok = true) (hsr : c.srReady = true)
    (hmr : c.matchReady = true) (hmo : ∀ H, CoherentAll (c.withHooks H)) {T : Tables}
    (hT : T = tables c) {ix : Det.DetIndex} (hd : Det.detOK c T ix = true) (H : HookParams)
    {x y y' : Config (c.withHooks H)} (h : Step (c.withHooks H) x y) (h' : Step (c.withHooks H) x y') :
    y = y' :=
  Det.deterministic_all_okM (Semantics.okM_of_ok hok) hsr hmr hmo hT hd H h h'

/-- **The determinism kind, for an interpretation H of the parameters**: `Det.kind (c.withHooks H)`
indexed by the pairs of the data's rules (the same list), from the index checked once on the data. -/
@[reducible] def Det.kindAll {c : Semantics} (hmr : c.matchReady = true) {T : Tables} (hT : T = tables c)
    {ix : Det.DetIndex} (hidx : Det.idxOK c T ix = true) (H : HookParams)
    (Inv : Config (c.withHooks H) → Prop) : Kind where
  Idx := Nat × Nat
  idxs := Det.detIdx ix c.rules.length
  Ob p := Det.JoinsOn (c.withHooks H) Inv p.1 p.2
  Goal := ∀ x y y' : Config (c.withHooks H), Inv x → Step (c.withHooks H) x y → Step (c.withHooks H) x y' → y = y'
  glue := Det.joins_glue (Exec.matchCtx_of ((Semantics.matchReady_withHooks c H).trans hmr))
    (hT.trans (tables_withHooks c H).symm) ((Det.idxOK_withHooks c T H ix).trans hidx)

/-- Determinism's decider for `Det.kindAll`: the condition on the data (`detCond` does not read
`hooks`), sound under every interpretation from the conditions decided once on the data and
coherence under each interpretation. -/
def Det.deciderAll {c : Semantics} (hok : c.ok = true) (hsr : c.srReady = true)
    (hmo : ∀ H, CoherentAll (c.withHooks H)) {hmr : c.matchReady = true} {T : Tables}
    {hT : T = tables c} {ix : Det.DetIndex} {hidx : Det.idxOK c T ix = true} (H : HookParams)
    (Inv : Config (c.withHooks H) → Prop) : (Det.kindAll hmr hT hidx H Inv).Decider where
  cond := Det.detCond c T
  sound p h := Det.detCond_sound ((Semantics.ok_withHooks c H).trans hok)
    ((Semantics.srReady_withHooks c H).trans hsr) ((Semantics.matchReady_withHooks c H).trans hmr) (hmo H)
    (hT.trans (tables_withHooks c H).symm) p ((Det.detCond_withHooks c T H p).trans h)

/-- Determinism's decider for `Det.kindAll`: the condition on the data (`detCond` does not read
`hooks`), sound under every interpretation from the conditions decided once on the data and
coherence under each interpretation, in a core `okM` accepts. -/
def Det.deciderAll_okM {c : Semantics} (hok : c.okM = true) (hsr : c.srReady = true)
    (hmo : ∀ H, CoherentAll (c.withHooks H)) {hmr : c.matchReady = true} {T : Tables}
    {hT : T = tables c} {ix : Det.DetIndex} {hidx : Det.idxOK c T ix = true} (H : HookParams)
    (Inv : Config (c.withHooks H) → Prop) : (Det.kindAll hmr hT hidx H Inv).Decider where
  cond := Det.detCond c T
  sound p h := Det.detCond_sound_okM ((Semantics.okM_withHooks c H).trans hok)
    ((Semantics.srReady_withHooks c H).trans hsr) ((Semantics.matchReady_withHooks c H).trans hmr) (hmo H)
    (hT.trans (tables_withHooks c H).symm) p ((Det.detCond_withHooks c T H p).trans h)

/-- `asideFree` does not read the interpretation of the parameters. -/
theorem Semantics.asideFree_withHooks (c : Semantics) (H : HookParams) :
    (c.withHooks H).asideFree = c.asideFree := rfl

/-- The executable step lists exactly `Step`'s successors, for every interpretation of the
parameters (the executable step reads the same `paramVal`), where no clause is `aside`. -/
theorem Exec.step_iff_all {c : Semantics} (hok : c.ok = true) (hsr : c.srReady = true)
    (hmr : c.matchReady = true) (H : HookParams) (hco : CoherentAll (c.withHooks H))
    (x y : Config (c.withHooks H)) (hna : c.asideFree = true := by decide +kernel) :
    Step (c.withHooks H) x y ↔ ∃ n, (Exec.successorsN (c.withHooks H) n x.val).any (Exec.same · y.val) = true :=
  Exec.step_iff_of_ok (c.withHooks H) ((Semantics.ok_withHooks c H).trans hok)
    ((Semantics.srReady_withHooks c H).trans hsr) ((Semantics.matchReady_withHooks c H).trans hmr) hco x y
    (Semantics.asideFree_withHooks c H ▸ hna)

-- `overloadsOK` does not read the interpretation of the parameters.
kernel_rfl Semantics.overloadsOK_withHooks :
  ∀ (c : Semantics) (H : HookParams), (c.withHooks H).overloadsOK = c.overloadsOK

/-- The parameters' interpretation does not touch the overloading symbols. -/
theorem Semantics.ovlCase_withHooks {c : Semantics} (h : c.OvlCase) (H : HookParams) : (c.withHooks H).OvlCase :=
  h.imp id fun ⟨hok, hirr⟩ => ⟨(Semantics.overloadsOK_withHooks c H).trans hok, hirr⟩

/-- Subject reduction for every interpretation of the parameters, from `okAll`, `srReady` and
`OvlCase` decided once on the data. -/
theorem rhs_sorted_all_withHooks {c : Semantics} (hok : c.okAll = true) (hsr : c.srReady = true)
    (hov : c.OvlCase) (H : HookParams) {r : Rule} (hr : r ∈ c.rules) {σ : Subst} (hσ : (c.withHooks H).WellSorted r.vars σ)
    {v : GroundTerm} (he : EvalTerm (c.withHooks H) σ r.rhs (some v)) :
    (c.withHooks H).sortOf v = some topCellSort :=
  rhs_sorted_all (c := c.withHooks H) ((Semantics.okAll_withHooks c H).trans hok)
    ((Semantics.srReady_withHooks c H).trans hsr) (Semantics.ovlCase_withHooks hov H) hr hσ he

/-- No rule application is lost to sorts, for every interpretation of the parameters. -/
theorem step_of_apply_all_withHooks {c : Semantics} (hok : c.okAll = true) (hsr : c.srReady = true)
    (hov : c.OvlCase) (H : HookParams) {r : Rule} (hr : r ∈ c.rules) {x : Config (c.withHooks H)} {σ : Subst}
    (hσ : (c.withHooks H).WellSorted r.vars σ) (hm : PatVal (c.withHooks H) σ r.lhs x.val)
    (hreq : ∀ t, r.req = some t → EvalTerm (c.withHooks H) σ t (some (bool true)))
    (hpre : Holds (c.withHooks H) r.vars.length σ r.pre true)
    {v : GroundTerm} (he : EvalTerm (c.withHooks H) σ r.rhs (some v))
    (hens : ∀ t, r.ens = some t → EvalTerm (c.withHooks H) σ t (some (bool true)))
    (hpost : Holds (c.withHooks H) r.vars.length σ r.post true)
    (hprio : ∀ r' ∈ c.rules, r'.prio < r.prio → NotApplies (c.withHooks H) r' x.val) :
    Step (c.withHooks H) x ⟨v, rhs_sorted_all_withHooks hok hsr hov H hr hσ he⟩ :=
  .rule r hr σ hσ hm hreq hpre he hens hpost hprio

end KCore
