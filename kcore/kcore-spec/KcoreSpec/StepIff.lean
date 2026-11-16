/-
  KCore, checked layer: the executable step lists exactly the `Step` successors, for some fuel
  (`step_iff_of`), for a well-formed definition whose core `srReady` and `matchReady` accept
  (two decidable conditions, with the function labels those of `allFns`) and whose clauses of one
  priority are coherent (`CoherentAll`, read by the `→` direction only, through the executable
  evaluation's completeness, `EvalTerm.exec`). `Exec.step_iff` (StepIffWf.lean) states it from
  `wf`, `ok` and `CoherentAll`.

  The proof's core is the priority premise `hprio`:
  - `→`: every match of a rule of smaller priority than the rule that steps has, by `hprio`, a
    `requires` whose evaluation is not `true`; there are finitely many such matches (the matcher
    lists every well-sorted one, `matchP_complete`), so one fuel computes all of them
    (`fuel_list`, from fuel monotonicity of evaluation, `evalT_mono`), and at that fuel none of
    those rules is among the applying ones; the stepping rule is, so the smallest applying
    priority is its own (`successorsN_of`).
  - `←`: a listed successor's rule has the smallest applying priority, so every rule of a
    smaller priority has only `some false` values (`successorsN_mem`); for any well-sorted σ'
    under which such a rule's left-hand side denotes x, the matcher found a σ₀ agreeing with σ'
    on the rule's variables, its `requires` evaluated there is false or undefined, and so it is
    under σ' (`evalT_congr`, `evalT_sound`): `NotApplies`.
  So the applicability test is monotone in fuel in the sense the proof needs: a `requires` value
  `some b` computed at some fuel is computed at every larger fuel (`evalT_mono_le`, under
  coherence), and `none` (out of fuel) never lets a lower rule fire.
-/
import KcoreSpec.EvalComplete

set_option autoImplicit false

namespace KCore.Exec

open KCore

theorem binds_mem {n : Nat} {occs : List Nat} (h : binds n occs = true) : ∀ i < n, i ∈ occs := by
  simp only [binds, List.all_eq_true] at h
  exact fun i hi => List.contains_iff_mem.mp (h i (List.mem_range.mpr hi))

section

variable {c : Semantics} (hok : c.ok = true) (hsr : c.srReady = true) (hmr : c.matchReady = true)

include hok hmr in
/-- Every well-sorted σ under which a rule's left-hand side denotes x is matched by a substitution
the matcher lists, agreeing with σ on the rule's variables. -/
theorem rule_match_complete {r : Rule} (hr : r ∈ c.rules) {σ : Subst} (hσ : c.WellSorted r.vars σ)
    {x : GroundTerm} (hmatch : PatVal c σ r.lhs x) :
    ∃ σ₀ ∈ (matchP c (patFuel [r.lhs]) [] r.lhs x).filter (wellSorted c r.vars),
      ∀ i < r.vars.length, σ₀.lookup i = σ.lookup i := by
  have hmc := matchCtx_of hmr
  obtain ⟨hlt, hnm, hbd, -, -⟩ := ruleOK_of hok hr
  have hcov := binds_mem hbd
  have hn : 4 * termSize r.lhs ≤ patFuel [r.lhs] := by simp [patFuel, termSizeList]
  obtain ⟨σ₀, hm₀, hx₀, _, hb₀⟩ := matchP_complete hmc hσ (patFuel [r.lhs]) (σ := []) hn hnm hmatch hlt
    (fun _ _ h => by simp [List.lookup] at h)
  have hσ₀ := wellSorted_of_below hσ hx₀ hb₀ hcov
  exact ⟨σ₀, List.mem_filter.mpr ⟨hm₀, wellSorted_iff.mpr hσ₀⟩,
    fun i hi => agree_of_ext hx₀ hb₀ i (hcov i hi)⟩

include hok hsr hmr in
/-- A `requires` the executable step evaluates at fuel n under a listed match: its value is the
relation's under any σ agreeing on the rule's variables. -/
theorem req_sound {r : Rule} (hr : r ∈ c.rules) {n : Nat} {σ₀ σ : Subst} {t : Term}
    {v : Option GroundTerm} (ht : r.req = some t) (hσ₀ : c.WellSorted r.vars σ₀)
    (hσ : c.WellSorted r.vars σ) (hag : ∀ i < r.vars.length, σ₀.lookup i = σ.lookup i)
    (he : evalT c n σ₀ t = some v) : EvalTerm c σ t v := by
  have hsc := sortCtx_of hok hsr (Exec.ovlCase_of hmr)
  have hcc := clauseCtx_of hok
  have hmc := matchCtx_of hmr
  obtain ⟨-, -, -, hrq, -⟩ := ruleOK_of hok hr
  rw [ht] at hrq
  have hts := reqOK_some hrq
  have he' : evalT c n σ t = some v := by
    rw [← evalT_congr n (fun i hi => hag i (sortOfTerm_vars hts i hi))]; exact he
  exact evalT_sound hsc hcc hmc n he' headsOK_fns hσ hts

include hok hsr hmr in
/-- An `ensures` the executable step evaluates to `true` at fuel n is `true` in the relation. -/
theorem ens_sound {r : Rule} (hr : r ∈ c.rules) {n : Nat} {σ : Subst} (hσ : c.WellSorted r.vars σ)
    (hb : ensVal c n r σ = some true) : ∀ t, r.ens = some t → EvalTerm c σ t (some (bool true)) := by
  have hsc := sortCtx_of hok hsr (Exec.ovlCase_of hmr)
  have hcc := clauseCtx_of hok
  have hmc := matchCtx_of hmr
  intro t ht
  have hen := ruleOK_ens_of hok hr
  rw [ht] at hen
  unfold ensVal at hb
  rw [ht] at hb
  cases he' : evalT c n σ t with
  | none => simp [he'] at hb
  | some v =>
    simp only [he', Option.map_some, Option.some.injEq] at hb
    rw [isTrue_iff.mp hb] at he'
    exact evalT_sound hsc hcc hmc n he' headsOK_fns hσ (reqOK_some hen)

end

/-- Every successor the executable step lists, at any fuel, is a step. -/
theorem successorsN_sound {c : Semantics} (hok : c.ok = true) (hsr : c.srReady = true)
    (hmr : c.matchReady = true) {n : Nat} {x : Config c} {y : GroundTerm}
    (hy : y ∈ successorsN c n x.val) :
    ∃ r ∈ c.rules, ∃ σ, c.WellSorted r.vars σ ∧ PatVal c σ r.lhs x.val ∧
      (∀ t, r.req = some t → EvalTerm c σ t (some (bool true))) ∧
      EvalTerm c σ r.rhs (some y) ∧
      (∀ t, r.ens = some t → EvalTerm c σ t (some (bool true))) ∧ c.sortOf y = some topCellSort ∧
      (∀ r' ∈ c.rules, r'.prio < r.prio → NotApplies c r' x.val) := by
  have hsc := sortCtx_of hok hsr (Exec.ovlCase_of hmr)
  have hcc := clauseCtx_of hok
  have hmc := matchCtx_of hmr
  obtain ⟨r, hr, hlow, σ, hσm, he, hs, hen⟩ := successorsN_mem_ens hy
  obtain ⟨hσm, hb⟩ := ruleMatches_mem.mp hσm
  obtain ⟨hm, hws⟩ := List.mem_filter.mp hσm
  have hσ := wellSorted_iff.mp hws
  obtain ⟨_, hpv⟩ := matchP_sound _ (canonV_of_sortOf x.property) hm
  obtain ⟨_, _, _, hreq, hrhs⟩ := ruleOK_of hok hr
  refine ⟨r, hr, σ, hσ, hpv, fun t ht => ?_, evalT_sound hsc hcc hmc n he headsOK_fns hσ hrhs,
    ens_sound hok hsr hmr hr hσ hen, hs, fun r' hr' hlt σ' hσ' hpv' => ?_⟩
  · rw [ht] at hreq
    unfold reqVal at hb
    rw [ht] at hb
    cases he' : evalT c n σ t with
    | none => simp [he'] at hb
    | some v =>
      simp only [he', Option.map_some, Option.some.injEq] at hb
      rw [isTrue_iff.mp hb.symm] at he'
      exact evalT_sound hsc hcc hmc n he' headsOK_fns hσ (reqOK_some hreq)
  · have hσ' := Rule.wellSorted_of_at (Semantics.ok_rule hok hr').2.2.2 hσ'
    obtain ⟨σ₀, hσ₀m, hag⟩ := rule_match_complete hok hmr hr' hσ' hpv'
    have hσ₀ := wellSorted_iff.mp (List.mem_filter.mp hσ₀m).2
    have hf := hlow r' hr' hlt (σ₀, reqVal c n r' σ₀) (ruleMatches_mem.mpr ⟨hσ₀m, rfl⟩)
    simp only at hf
    unfold reqVal at hf
    cases ht : r'.req with
    | none => simp [ht] at hf
    | some t =>
      rw [ht] at hf
      cases he' : evalT c n σ₀ t with
      | none => simp [he'] at hf
      | some v =>
        simp only [he', Option.map_some, Option.some.injEq] at hf
        refine RuleReqFails.intro ht (req_sound hok hsr hmr hr' ht hσ₀ hσ' hag he') ?_
        intro hv
        rw [hv] at hf
        exact absurd (isTrue_iff.mpr rfl) (by rw [hf]; decide)

/-- `Exec.step_iff` on a core, from three decidable conditions on it, `Semantics.ok` and the two
that `wf` gives (`NamesApart.srReady_of_wf`, `NamesApart.matchReady_of_wf`), and the coherence of
its clauses of one priority (`CoherentAll`; the `→` direction: the executable evaluation takes one
candidate where several apply), and no clause `aside` (`asideFree`; the `→` direction: the
executable evaluation stops at the first clause that applies, `aside` or not). A definition's
proofs about its `Step` need only its core, so the kernel can check these without the emitted
KORE text. -/
theorem step_iff_of_ok (c : Semantics) (hok : c.ok = true) (hsr : c.srReady = true)
    (hmr : c.matchReady = true) (hco : CoherentAll c) (x y : Config c)
    (hna : c.asideFree = true := by decide +kernel) :
    Step c x y ↔ ∃ n, (successorsN c n x.val).any (same · y.val) = true := by
  have hsc := sortCtx_of hok hsr (Exec.ovlCase_of hmr)
  have hcc := clauseCtx_of hok
  have hmc := matchCtx_of hmr
  constructor
  · rintro ⟨r, hr, σ, hσ, hmatch, hreq, -, heval, hens, -, hprio⟩
    obtain ⟨-, -, -, hrq, hrt⟩ := ruleOK_of hok hr
    have hen := ruleOK_ens_of hok hr
    obtain ⟨σ₀, hσ₀m, hag⟩ := rule_match_complete hok hmr hr hσ hmatch
    have hcongr : ∀ t m, (∀ i ∈ varOccs t, i < r.vars.length) →
        evalT c m σ₀ t = evalT c m σ t :=
      fun t m hv => evalT_congr m (fun i hi => hag i (hv i hi))
    -- fuel for the rule's own `requires` and right-hand side
    obtain ⟨nq, hnq⟩ : ∃ nq, ∀ t, r.req = some t → evalT c nq σ t = some (some (bool true)) := by
      cases hreqc : r.req with
      | none => exact ⟨0, fun t ht => nomatch ht⟩
      | some t =>
        rw [hreqc] at hrq
        obtain ⟨n, hn⟩ := EvalTerm.exec hsc hcc hmc hco (Semantics.asideFree_spec hna) (hreq t hreqc) r.vars _ Srt.bool headsOK_fns hσ
          (reqOK_some hrq)
        exact ⟨n, fun t' ht' => by cases ht'; exact hn⟩
    obtain ⟨ne, hne⟩ : ∃ ne, ∀ t, r.ens = some t → evalT c ne σ t = some (some (bool true)) := by
      cases hensc : r.ens with
      | none => exact ⟨0, fun t ht => nomatch ht⟩
      | some t =>
        rw [hensc] at hen
        obtain ⟨n, hn⟩ := EvalTerm.exec hsc hcc hmc hco (Semantics.asideFree_spec hna) (hens t hensc) r.vars _ Srt.bool headsOK_fns hσ
          (reqOK_some hen)
        exact ⟨n, fun t' ht' => by cases ht'; exact hn⟩
    obtain ⟨nr, hnr⟩ := EvalTerm.exec hsc hcc hmc hco (Semantics.asideFree_spec hna) heval r.vars _ topCellSort headsOK_fns hσ hrt
    -- fuel for every listed match of every rule of a smaller priority
    let low := (c.rules.filter (·.prio < r.prio)).flatMap fun r' =>
      ((matchP c (patFuel [r'.lhs]) [] r'.lhs x.val).filter (wellSorted c r'.vars)).map (r', ·)
    obtain ⟨N, hN⟩ := fuel_list
      (P := fun n (a : Rule × Subst) => a.1 ∈ c.rules ∧ c.WellSorted a.1.vars a.2 ∧
        ∃ t v, a.1.req = some t ∧ evalT c n a.2 t = some v ∧ v ≠ some (bool true))
      (fun n a ⟨har, haw, t, v, ht, he, hv⟩ => by
        obtain ⟨-, -, -, hrq', -⟩ := ruleOK_of hok har
        rw [ht] at hrq'
        exact ⟨har, haw, t, v, ht, evalT_mono hsc hcc hmc hco n he headsOK_fns haw (reqOK_some hrq'), hv⟩)
      (l := low) (fun a ha => by
        obtain ⟨r', hr', ha⟩ := List.mem_flatMap.mp ha
        obtain ⟨hr', hlt⟩ := List.mem_filter.mp hr'
        obtain ⟨σ', hσ', rfl⟩ := List.mem_map.mp ha
        obtain ⟨hm', hws'⟩ := List.mem_filter.mp hσ'
        have hσw := wellSorted_iff.mp hws'
        obtain ⟨_, hpv⟩ := matchP_sound _ (canonV_of_sortOf x.property) hm'
        obtain ⟨t, v, ht, he, hv⟩ := (hprio r' hr' (by simpa using hlt) σ' (hσw.at _) hpv).req_of_top
          (Semantics.ok_rule hok hr').2.1
        obtain ⟨-, -, -, hrq', -⟩ := ruleOK_of hok hr'
        rw [ht] at hrq'
        obtain ⟨n, hn⟩ := EvalTerm.exec hsc hcc hmc hco (Semantics.asideFree_spec hna) he r'.vars _ Srt.bool headsOK_fns hσw
          (reqOK_some hrq')
        exact ⟨n, hr', hσw, t, v, ht, hn, hv⟩)
    refine ⟨max N (max nq (max nr ne)), ?_⟩
    rw [List.any_eq_true]
    refine ⟨y.val, ?_, same_iff.mpr rfl⟩
    have hrhs : evalT c (max N (max nq (max nr ne))) σ₀ r.rhs = some (some y.val) := by
      rw [hcongr r.rhs _ (sortOfTerm_vars hrt)]
      exact evalT_mono_le hsc hcc hmc hco (by omega) hnr headsOK_fns hσ hrt
    refine successorsN_of hr (fun r' hr' hlt σb hσb => ?_) (σ := σ₀)
      (ruleMatches_mem.mpr ⟨hσ₀m, ?_⟩) hrhs y.property ?_
    · obtain ⟨σ', b⟩ := σb
      obtain ⟨hσ', rfl⟩ := ruleMatches_mem.mp hσb
      have hmem : (r', σ') ∈ low :=
        List.mem_flatMap.mpr ⟨r', List.mem_filter.mpr ⟨hr', by simpa using hlt⟩,
          List.mem_map.mpr ⟨σ', hσ', rfl⟩⟩
      obtain ⟨t, v, ht, he, hv⟩ : ∃ t v, r'.req = some t ∧
          evalT c (max N (max nq (max nr ne))) σ' t = some v ∧ v ≠ some (bool true) :=
        (hN _ hmem _ (Nat.le_max_left _ _)).2.2
      show reqVal c _ r' σ' = some false
      unfold reqVal
      rw [ht]
      simp only [he, Option.map_some, Option.some.injEq]
      cases hb : isTrue v
      · rfl
      · exact absurd (isTrue_iff.mp hb) hv
    · unfold reqVal
      cases hreqc : r.req with
      | none => rfl
      | some t =>
        rw [hreqc] at hrq
        have hq : evalT c (max N (max nq (max nr ne))) σ₀ t = some (some (bool true)) := by
          rw [hcongr t _ (sortOfTerm_vars (reqOK_some hrq))]
          exact evalT_mono_le hsc hcc hmc hco (by omega) (hnq t hreqc) headsOK_fns hσ (reqOK_some hrq)
        simp [hq, isTrue_iff]
    · unfold ensVal
      cases hensc : r.ens with
      | none => rfl
      | some t =>
        rw [hensc] at hen
        have hq : evalT c (max N (max nq (max nr ne))) σ₀ t = some (some (bool true)) := by
          rw [hcongr t _ (sortOfTerm_vars (reqOK_some hen))]
          exact evalT_mono_le hsc hcc hmc hco (by omega) (hne t hensc) headsOK_fns hσ (reqOK_some hen)
        simp [hq, isTrue_iff]
  · rintro ⟨n, hn⟩
    rw [List.any_eq_true] at hn
    obtain ⟨z, hz, hs⟩ := hn
    rw [same_iff] at hs
    subst hs
    obtain ⟨r, hr, σ, hσ, hpv, hreq, heval, hens, _, hprio⟩ := successorsN_sound hok hsr hmr hz
    obtain ⟨-, hp, hq, -⟩ := Semantics.ok_rule hok hr
    exact Step.rule_top r hr σ hp hq hσ hpv hreq heval hens hprio

/-- `Exec.step_iff`, given the three decidable conditions on the core (`ok` is no longer part of
`wf`, which checks the wider `okAll`: a rule's collection patterns are outside the executable
matcher's theorems), coherence and no clause `aside`. -/
theorem step_iff_of (d : Definition) (hok : d.sem.ok = true) (hsr : d.sem.srReady = true)
    (hmr : d.sem.matchReady = true) (hco : CoherentAll d.sem) (x y : Config d.sem)
    (hna : d.sem.asideFree = true := by decide +kernel) :
    Step d.sem x y ↔ ∃ n, (successorsN d.sem n x.val).any (same · y.val) = true :=
  step_iff_of_ok d.sem hok hsr hmr hco x y hna

end KCore.Exec
