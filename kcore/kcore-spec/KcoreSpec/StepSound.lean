/-
  KCore, checked layer: what the executable step's priority selection lists (toward `Exec.step_iff`).

  `successorsN_mem`: a listed configuration comes from a rule r, one of r's matches whose
  `requires` evaluated to `true`, and its right-hand side; and every rule of a smaller priority
  than r had all its matches' `requires` evaluate to something other than `true` (`some false`)
  at the same fuel. `successorsN_of`: conversely, such a rule and match are listed. The step
  relation's premises are read off these in StepIff.lean.
-/
import KcoreSpec.EvalSound

set_option autoImplicit false

namespace KCore.Exec

open KCore

variable {c : Semantics}

/-- What `okM` checks of a rule's left side, `requires` and right-hand side. -/
theorem ruleOKM_of {r : Rule} (hok : c.okM = true) (hr : r ∈ c.rules) :
    sortOfTerm c.patCtx r.vars r.lhs = some topCellSort ∧ noMapIn r.lhs = true ∧
      binds r.vars.length (varOccs r.lhs) = true ∧
      reqOK (c.rhsCtx (c.fns.map Fn.sig)) r.vars r.req = true ∧
      sortOfTerm (c.rhsCtx (c.fns.map Fn.sig)) r.vars r.rhs = some topCellSort := by
  have hrule : c.ruleOKM r = true := by
    simp only [Semantics.okM, Bool.and_eq_true, List.all_eq_true] at hok
    exact hok.1.2 r hr
  simp only [Semantics.ruleOKM, Bool.and_eq_true, beq_iff_eq] at hrule
  exact ⟨hrule.1.1.1.1.1.1, hrule.1.1.1.1.1.2, hrule.1.1.1.1.2, hrule.1.1.1.2, hrule.1.2⟩

theorem ruleOK_of {r : Rule} (hok : c.ok = true) (hr : r ∈ c.rules) :
    sortOfTerm c.patCtx r.vars r.lhs = some topCellSort ∧ noMapIn r.lhs = true ∧
      binds r.vars.length (varOccs r.lhs) = true ∧
      reqOK (c.rhsCtx (c.fns.map Fn.sig)) r.vars r.req = true ∧
      sortOfTerm (c.rhsCtx (c.fns.map Fn.sig)) r.vars r.rhs = some topCellSort :=
  ruleOKM_of (Semantics.okM_of_ok hok) hr

/-- What `ok` checks of a rule's `ensures`: a Bool. -/
theorem ruleOKM_ens_of {r : Rule} (hok : c.okM = true) (hr : r ∈ c.rules) :
    reqOK (c.rhsCtx (c.fns.map Fn.sig)) r.vars r.ens = true := by
  have hrule : c.ruleOKM r = true := by
    simp only [Semantics.okM, Bool.and_eq_true, List.all_eq_true] at hok
    exact hok.1.2 r hr
  simp only [Semantics.ruleOKM, Bool.and_eq_true, beq_iff_eq] at hrule
  exact hrule.1.1.2

theorem ruleOK_ens_of {r : Rule} (hok : c.ok = true) (hr : r ∈ c.rules) :
    reqOK (c.rhsCtx (c.fns.map Fn.sig)) r.vars r.ens = true :=
  ruleOKM_ens_of (Semantics.okM_of_ok hok) hr

theorem headsOK_fns : HeadsOK c (c.fns.map Fn.sig) :=
  fun k hk => by obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hk; exact ⟨g, List.mem_append_left _ hg, rfl⟩

/-- The `requires` value the executable step attaches to a match. -/
def reqVal (c : Semantics) (n : Nat) (r : Rule) (σ : Subst) : Option Bool :=
  match r.req with
  | none => some true
  | some t => (evalT c n σ t).map isTrue

theorem ruleMatches_mem {n : Nat} {r : Rule} {x : GroundTerm} {σ : Subst} {b : Option Bool} :
    (σ, b) ∈ ruleMatches c n r x ↔
      σ ∈ (matchP c (patFuel [r.lhs]) [] r.lhs x).filter (wellSorted c r.vars) ∧ b = reqVal c n r σ := by
  unfold ruleMatches
  rw [List.mem_map]
  constructor
  · rintro ⟨σ', hσ', he⟩
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact ⟨hσ', by unfold reqVal; cases r.req <;> rfl⟩
  · rintro ⟨hσ, rfl⟩
    exact ⟨σ, hσ, by unfold reqVal; cases r.req <;> rfl⟩

/-- What a listed successor comes from, its `ensures` included. -/
theorem successorsN_mem_ens {n : Nat} {x y : GroundTerm} (hy : y ∈ successorsN c n x) :
    ∃ r ∈ c.rules,
      (∀ r' ∈ c.rules, r'.prio < r.prio → ∀ σb ∈ ruleMatches c n r' x, σb.2 = some false) ∧
      ∃ σ, (σ, some true) ∈ ruleMatches c n r x ∧ evalT c n σ r.rhs = some (some y) ∧
        c.sortOf y = some topCellSort ∧ ensVal c n r σ = some true := by
  unfold successorsN at hy
  dsimp only at hy
  split at hy
  · simp at hy
  · rename_i p hp
    rw [List.min?_eq_some_iff] at hp
    obtain ⟨-, hmin⟩ := hp
    rw [List.mem_flatMap] at hy
    obtain ⟨⟨r, l⟩, hrl, hy⟩ := hy
    obtain ⟨hrl, hpr⟩ := List.mem_filter.mp hrl
    simp only [beq_iff_eq] at hpr
    obtain ⟨hrl, -⟩ := List.mem_filter.mp hrl
    obtain ⟨r₀, hr₀, he⟩ := List.mem_map.mp hrl
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    refine ⟨r₀, hr₀, fun r' hr' hlt σb hσb => ?_, ?_⟩
    · refine Classical.byContradiction fun hne => ?_
      have hin : (r', ruleMatches c n r' x) ∈ (c.rules.map fun r => (r, ruleMatches c n r x)).filter
          fun (_, l) => l.any fun (_, b) => b != some false := by
        refine List.mem_filter.mpr ⟨List.mem_map.mpr ⟨r', hr', rfl⟩, ?_⟩
        simp only [List.any_eq_true, bne_iff_ne, ne_eq]
        exact ⟨σb, hσb, hne⟩
      have := hmin _ (List.mem_map.mpr ⟨_, hin, rfl⟩)
      simp only at this
      omega
    · rw [List.mem_filterMap] at hy
      obtain ⟨⟨σ, b⟩, hσb, hk⟩ := hy
      simp only at hk
      by_cases hb : b = some true
      · subst hb
        refine ⟨σ, hσb, ?_⟩
        simp only [beq_self_eq_true, ↓reduceIte] at hk
        cases he : evalT c n σ r₀.rhs with
        | none => rw [he] at hk; cases hk
        | some o =>
          cases o with
          | none => rw [he] at hk; cases hk
          | some y' =>
            rw [he] at hk
            dsimp only at hk
            split at hk
            · rename_i hc
              simp only [Bool.and_eq_true, beq_iff_eq] at hc
              cases hk; exact ⟨rfl, hc.1, hc.2⟩
            · cases hk
      · have : (b == some true) = false := by simpa using hb
        simp [this] at hk

/-- What a listed successor comes from. -/
theorem successorsN_mem {n : Nat} {x y : GroundTerm} (hy : y ∈ successorsN c n x) :
    ∃ r ∈ c.rules,
      (∀ r' ∈ c.rules, r'.prio < r.prio → ∀ σb ∈ ruleMatches c n r' x, σb.2 = some false) ∧
      ∃ σ, (σ, some true) ∈ ruleMatches c n r x ∧ evalT c n σ r.rhs = some (some y) ∧
        c.sortOf y = some topCellSort :=
  let ⟨r, hr, hlow, σ, hσ, he, hs, _⟩ := successorsN_mem_ens hy
  ⟨r, hr, hlow, σ, hσ, he, hs⟩

/-- A rule all of whose smaller-priority competitors have only `requires` values `some false`, and
one of its matches with `requires` `true`, a configuration as right-hand side and `ensures`
`true`, is listed. -/
theorem successorsN_of {n : Nat} {x y : GroundTerm} {r : Rule} (hr : r ∈ c.rules)
    (hlow : ∀ r' ∈ c.rules, r'.prio < r.prio → ∀ σb ∈ ruleMatches c n r' x, σb.2 = some false)
    {σ : Subst} (hσ : (σ, some true) ∈ ruleMatches c n r x)
    (he : evalT c n σ r.rhs = some (some y)) (hy : c.sortOf y = some topCellSort)
    (hens : ensVal c n r σ = some true) :
    y ∈ successorsN c n x := by
  unfold successorsN
  dsimp only
  have hin : (r, ruleMatches c n r x) ∈ (c.rules.map fun r => (r, ruleMatches c n r x)).filter
      fun (_, l) => l.any fun (_, b) => b != some false := by
    refine List.mem_filter.mpr ⟨List.mem_map.mpr ⟨r, hr, rfl⟩, ?_⟩
    simp only [List.any_eq_true, bne_iff_ne, ne_eq]
    exact ⟨_, hσ, by simp⟩
  have hmin : (((c.rules.map fun r => (r, ruleMatches c n r x)).filter
      fun (_, l) => l.any fun (_, b) => b != some false).map (·.1.prio)).min? = some r.prio := by
    rw [List.min?_eq_some_iff]
    refine ⟨List.mem_map.mpr ⟨_, hin, rfl⟩, fun q hq => ?_⟩
    obtain ⟨⟨r', l⟩, hrl, rfl⟩ := List.mem_map.mp hq
    obtain ⟨hrl, hany⟩ := List.mem_filter.mp hrl
    obtain ⟨r'', hr'', he'⟩ := List.mem_map.mp hrl
    simp only [Prod.mk.injEq] at he'
    obtain ⟨rfl, rfl⟩ := he'
    simp only [List.any_eq_true, bne_iff_ne, ne_eq] at hany
    obtain ⟨σb, hσb, hne⟩ := hany
    simp only
    refine Classical.byContradiction fun hlt => ?_
    exact hne (hlow r'' hr'' (by omega) σb hσb)
  rw [hmin]
  simp only
  rw [List.mem_flatMap]
  refine ⟨(r, ruleMatches c n r x), List.mem_filter.mpr ⟨hin, by simp⟩, ?_⟩
  rw [List.mem_filterMap]
  exact ⟨(σ, some true), hσ, by simp [he, hy, hens]⟩

end KCore.Exec
