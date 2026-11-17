/-
  A rewrite rule with an `ensures`, read from K 7.1.337 kompile's own KORE. Run from the package
  root: `lake env lean test/EnsuresRule.lean`.

  The axiom of a rule with an `ensures` B is `\rewrites(lhs ∧ req, rhs ∧ (B = true))`; the reader
  reads B as the rule's `ens` (`Rule.ens`), its `requires` and right side as written, and no sentence
  in another form than written.
  - `f2-examples/ensrule.kompile.kore` (`ensrule.k`): `assume(B) => ok() ensures B`, beside an
    `[owise]` rule on `other(_)`. In the kernel: `assume(true)` steps to `ok()`, `assume(false)` has
    no successor.
  - `f2-examples/ensrule-overlap.kompile.kore` (`ensrule-overlap.k`): the same rule beside an
    `[owise]` rule on any `Cmd`. At `assume(false)` the rule applies (its left side matches, it has no
    `requires`) and gives no successor (its `ensures` is false), so it blocks the `[owise]` rule. In
    the kernel: `assume(true)` steps to `ok()`, `assume(false)` has no successor (the `[owise]` rule
    does not step to `stuck()`).
  - `f2-examples/ensrule-prio.kompile.kore` (`ensrule-prio.k`): `assume(B, C) => ok() requires C
    ensures B` of priority 50 beside `assume(_, _) => stuck()` of priority 60. In the kernel:
    `assume(true, true)` steps to `ok()`; `assume(false, true)` has no successor (the first rule
    applies, its `ensures` is false, and it blocks the second); `assume(true, false)` steps to
    `stuck()` (the first rule's `requires` is false, so it does not apply).
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

open KCore

/-- The reader's verdict on the text at `path`, the classes read in another form than written, and
the number of rules with an `ensures`. -/
def verdict (path : String) : IO String := do
  match Kore.parseDefinition (← IO.FS.readFile path) with
  | .error e => return s!"KORE read error {e}"
  | .ok k =>
    let notes := (Parse.classCounts k).filter fun (n, _) => n.startsWith "read "
    return match Parse.parse k with
      | .ok d => s!"read {notes} {Parse.rulesWithEnsures d}"
      | .error r => s!"{r.reason.name} {notes}"

/--
info: read [] 1
read [] 1
read [] 1
-/
#guard_msgs in
#eval show IO Unit from do
  IO.println (← verdict "f2-examples/ensrule.kompile.kore")
  IO.println (← verdict "f2-examples/ensrule-overlap.kompile.kore")
  IO.println (← verdict "f2-examples/ensrule-prio.kompile.kore")


/-! ## No successor where a rule that applies has none

A configuration at which a rule r₀ applies (a match whose `requires` is `true`) and every rule of
priority at most r₀'s gives no successor (`Cert.ruleStuck`: at each match the `requires` is not
`true`, or the right side has no value, is no configuration, or the `ensures` is not `true`) has no
listed successor at any fuel: a listed successor comes from a rule all of whose smaller priorities
have every match's `requires` `false`, which r₀'s match excludes for every rule of a larger priority
than r₀'s; and a rule of priority at most r₀'s gives none (as `Cert.successorsN_nil_of_stuckCheck`). -/

section
open KCore.Exec KCore.Cert

theorem successorsN_nil_of_blocked {c : Semantics} (hok : c.ok = true) (hsr : c.srReady = true)
    (hmr : c.matchReady = true) (hco : CoherentAll c) {n : Nat} {x : GroundTerm} {r₀ : Rule}
    (hr₀ : r₀ ∈ c.rules)
    (happ : ((matchP c (patFuel [r₀.lhs]) [] r₀.lhs x).filter (wellSorted c r₀.vars)).any
      (fun σ => reqValC c n r₀ σ == some true) = true)
    (hst : c.rules.all (fun r => !decide (r.prio ≤ r₀.prio) || ruleStuck c n r x) = true)
    (m : Nat) : successorsN c m x = [] := by
  rw [List.eq_nil_iff_forall_not_mem]
  intro y hy
  obtain ⟨r, hr, hlow, σ, hσb, he, hs, hens⟩ := successorsN_mem_ens hy
  have hsc := sortCtx_of hok hsr (Exec.ovlCase_of hmr)
  have hcc := clauseCtx_of hok
  have hmc := matchCtx_of hmr
  -- a rule's sorted terms have one result at both fuels where both have one
  have hagree : ∀ {r : Rule} {σ : Subst} {t : Term} {v w : Option GroundTerm} {s : Srt},
      c.WellSorted r.vars σ → sortOfTerm (c.rhsCtx (c.fns.map Fn.sig)) r.vars t = some s →
      evalT c n σ t = some v → evalT c m σ t = some w → v = w := fun hσw ht hv hw =>
    EvalTerm.functional hco (evalT_sound hsc hcc hmc n hv headsOK_fns hσw ht)
      (evalT_sound hsc hcc hmc m hw headsOK_fns hσw ht)
  by_cases hp : r₀.prio < r.prio
  · obtain ⟨σ₀, hσ₀, hb₀⟩ := List.any_eq_true.mp happ
    have hq := reqValC_sound (beq_iff_eq.mp hb₀)
    have hl := hlow r₀ hr₀ hp (σ₀, reqVal c m r₀ σ₀) (ruleMatches_mem.mpr ⟨hσ₀, rfl⟩)
    simp only at hl
    have hσw : c.WellSorted r₀.vars σ₀ := wellSorted_iff.mp (List.mem_filter.mp hσ₀).2
    obtain ⟨-, -, -, hrqOK, -⟩ := ruleOK_of hok hr₀
    unfold reqVal at hq hl
    cases hrq : r₀.req with
    | none => rw [hrq] at hl; cases hl
    | some t =>
      rw [hrq] at hq hl hrqOK
      simp only at hq hl
      cases hn : evalT c n σ₀ t with
      | none => rw [hn] at hq; cases hq
      | some v =>
        cases hm : evalT c m σ₀ t with
        | none => rw [hm] at hl; cases hl
        | some w =>
          rw [hn] at hq; rw [hm] at hl
          cases hagree hσw (reqOK_some hrqOK) hn hm
          simp only [Option.map_some, Option.some.injEq] at hq hl
          rw [hq] at hl; cases hl
  · have hrs : ruleStuck c n r x = true := by
      have := List.all_eq_true.mp hst r hr
      simpa [Nat.le_of_not_lt hp] using this
    obtain ⟨hσm, hb⟩ := ruleMatches_mem.mp hσb
    have h2 := ruleStuck_at (List.all_eq_true.mp hrs σ hσm)
    have hσw : c.WellSorted r.vars σ := wellSorted_iff.mp (List.mem_filter.mp hσm).2
    obtain ⟨-, -, -, hrqOK, hrtOK⟩ := ruleOK_of hok hr
    have hreq : reqVal c n r σ = some true ∨ reqVal c n r σ = none := by
      unfold reqVal at hb ⊢
      cases hrq : r.req with
      | none => left; rfl
      | some t =>
        rw [hrq] at hb
        cases hm : evalT c m σ t with
        | none => simp [hm] at hb
        | some w =>
          cases hn : evalT c n σ t with
          | none => right; simp only [hn, Option.map_none]
          | some v =>
            left
            rw [hrq] at hrqOK
            cases hagree hσw (reqOK_some hrqOK) hn hm
            simp only [hm, Option.map_some, Option.some.injEq] at hb
            simp [hn, hb]
    rcases h2 with h2 | ⟨h2, h3⟩
    · rcases hreq with hreq | hreq <;> rw [hreq] at h2 <;> cases h2
    · rcases h3 with h3 | ⟨y', h3, hs'⟩
      · cases hagree hσw hrtOK h3 he
      · cases hagree hσw hrtOK h3 he
        rcases hs' with hs' | hs'
        · exact hs' hs
        · exact ensVal_not_false_true hok hsr hmr hco hr hσw hs' hens

end

namespace EnsRule

definition_of defn from "f2-examples/ensrule.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem

def kCell : Sym := 383
def assume : Sym := 385
def ok_ : Sym := 386
def cmdS : Srt := 32

theorem names_ok : c.symName kCell = "Lbl'-LT-'k'-GT-'" ∧ c.symName assume = "Lblassume" ∧
    c.symName ok_ = "Lblok" ∧ c.sortName cmdS = "Cmd" := by decide +kernel

/-- The rule `assume`: no `requires`, its `ensures` B (variable 0), its priority 50. -/
theorem assume_rule : c.rules.map (·.prio) = [50, 200] ∧ c.rules.map (·.req.isSome) = [false, false] ∧
    c.rules.map (fun r => r.ens.map (Term.beq (.var 0))) = [some true, none] := by
  decide +kernel

theorem ok : c.ok = true := by decide +kernel
theorem srReady : c.srReady = true := by decide +kernel
theorem matchReady : c.matchReady = true := by decide +kernel
theorem coherent : CoherentAll c :=
  Det.coherentAll_of_nil ok srReady matchReady (by decide +kernel) (by decide +kernel)

def cfg (st : GroundTerm) : GroundTerm :=
  .ctor topLabel [.ctor kCell [.ctor kseq [.inj cmdS Srt.kitem st, .ctor dotk []]],
    .ctor counterLabel [.dv Srt.int (.int 0)]]

def AssumeT : Config c := ⟨cfg (.ctor assume [.dv Srt.bool (.bool true)]), by decide +kernel⟩
def AssumeF : Config c := ⟨cfg (.ctor assume [.dv Srt.bool (.bool false)]), by decide +kernel⟩
def Ok : Config c := ⟨cfg (.ctor ok_ []), by decide +kernel⟩

/-- Where the `ensures` holds, the rule steps. -/
theorem step_true : Step c AssumeT Ok :=
  (Exec.step_iff_of_ok c ok srReady matchReady coherent _ _).mpr ⟨100, by decide +kernel⟩

/-- Where it fails, no rule gives a successor. -/
theorem stuck_false : ∀ y, ¬ Step c AssumeF y := by
  intro y h
  obtain ⟨n, hn⟩ := (Exec.step_iff_of_ok c ok srReady matchReady coherent _ y).mp h
  rw [Cert.successorsN_nil_of_stuckCheck ok srReady matchReady coherent (n := 100) (by decide +kernel) n] at hn
  cases hn

end EnsRule

namespace EnsRuleOverlap

definition_of defn from "f2-examples/ensrule-overlap.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem

def kCell : Sym := 383
def assume : Sym := 385
def ok_ : Sym := 386
def cmdS : Srt := 32

theorem names_ok : c.symName kCell = "Lbl'-LT-'k'-GT-'" ∧ c.symName assume = "Lblassume" ∧
    c.symName ok_ = "Lblok" ∧ c.sortName cmdS = "Cmd" := by decide +kernel

/-- The `[owise]` rule (priority 200) and `assume` (priority 50), neither with a `requires`;
`assume`'s `ensures` is B (variable 0) and its right side the written one. -/
theorem rules_shape : c.rules.map (·.prio) = [200, 50] ∧ c.rules.map (·.req.isSome) = [false, false] ∧
    c.rules.map (fun r => r.ens.map (Term.beq (.var 0))) = [none, some true] ∧
    c.rules.map (fun r => Term.beq (.app topLabel [.app kCell [.app kseq
        [.inj cmdS Srt.kitem (.app ok_ []), .app dotk []]], .var 1]) r.rhs) = [false, true] := by
  decide +kernel

theorem ok : c.ok = true := by decide +kernel
theorem srReady : c.srReady = true := by decide +kernel
theorem matchReady : c.matchReady = true := by decide +kernel
theorem coherent : CoherentAll c :=
  Det.coherentAll_of_nil ok srReady matchReady (by decide +kernel) (by decide +kernel)

def cfg (st : GroundTerm) : GroundTerm :=
  .ctor topLabel [.ctor kCell [.ctor kseq [.inj cmdS Srt.kitem st, .ctor dotk []]],
    .ctor counterLabel [.dv Srt.int (.int 0)]]

def AssumeT : Config c := ⟨cfg (.ctor assume [.dv Srt.bool (.bool true)]), by decide +kernel⟩
def AssumeF : Config c := ⟨cfg (.ctor assume [.dv Srt.bool (.bool false)]), by decide +kernel⟩
def Ok : Config c := ⟨cfg (.ctor ok_ []), by decide +kernel⟩

/-- Where the `ensures` holds, the rule steps. -/
theorem step_true : Step c AssumeT Ok :=
  (Exec.step_iff_of_ok c ok srReady matchReady coherent _ _).mpr ⟨100, by decide +kernel⟩

/-- Where it fails, the rule applies with no successor and blocks the `[owise]` rule: no successor. -/
theorem stuck_false : ∀ y, ¬ Step c AssumeF y := by
  intro y h
  obtain ⟨n, hn⟩ := (Exec.step_iff_of_ok c ok srReady matchReady coherent _ y).mp h
  rw [successorsN_nil_of_blocked ok srReady matchReady coherent (n := 100) (r₀ := c.rules[1]'(by decide +kernel))
    (List.getElem_mem _) (by decide +kernel) (by decide +kernel) n] at hn
  cases hn

end EnsRuleOverlap

namespace EnsRulePrio

definition_of defn from "f2-examples/ensrule-prio.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem

def kCell : Sym := 383
def assume : Sym := 385
def ok_ : Sym := 386
def stuck_ : Sym := 387
def cmdS : Srt := 32

theorem names_ok : c.symName kCell = "Lbl'-LT-'k'-GT-'" ∧ c.symName assume = "Lblassume" ∧
    c.symName ok_ = "Lblok" ∧ c.symName stuck_ = "Lblstuck" ∧ c.sortName cmdS = "Cmd" := by
  decide +kernel

/-- `assume` (priority 50) with its written `requires` C (variable 1), its `ensures` B (variable 0)
and its written right side; `fallback` (priority 60) without a `requires` or an `ensures`. -/
theorem rules_shape : c.rules.map (·.prio) = [50, 60] ∧
    c.rules.map (fun r => r.req.map (Term.beq (.var 1))) = [some true, none] ∧
    c.rules.map (fun r => r.ens.map (Term.beq (.var 0))) = [some true, none] ∧
    c.rules.map (fun r => Term.beq (.app topLabel [.app kCell [.app kseq
        [.inj cmdS Srt.kitem (.app ok_ []), .app dotk []]], .var 2]) r.rhs) = [true, false] := by
  decide +kernel

theorem ok : c.ok = true := by decide +kernel
theorem srReady : c.srReady = true := by decide +kernel
theorem matchReady : c.matchReady = true := by decide +kernel
theorem coherent : CoherentAll c :=
  Det.coherentAll_of_nil ok srReady matchReady (by decide +kernel) (by decide +kernel)

def cfg (st : GroundTerm) : GroundTerm :=
  .ctor topLabel [.ctor kCell [.ctor kseq [.inj cmdS Srt.kitem st, .ctor dotk []]],
    .ctor counterLabel [.dv Srt.int (.int 0)]]

def assumeV (b c : Bool) : GroundTerm := .ctor assume [.dv Srt.bool (.bool b), .dv Srt.bool (.bool c)]

def TT : Config c := ⟨cfg (assumeV true true), by decide +kernel⟩
def FT : Config c := ⟨cfg (assumeV false true), by decide +kernel⟩
def TF : Config c := ⟨cfg (assumeV true false), by decide +kernel⟩
def Ok : Config c := ⟨cfg (.ctor ok_ []), by decide +kernel⟩
def Stuck : Config c := ⟨cfg (.ctor stuck_ []), by decide +kernel⟩

/-- `requires` and `ensures` true: the rule of priority 50 steps. -/
theorem step_tt : Step c TT Ok :=
  (Exec.step_iff_of_ok c ok srReady matchReady coherent _ _).mpr ⟨100, by decide +kernel⟩

/-- `requires` true, `ensures` false: the rule of priority 50 applies with no successor and blocks
the rule of priority 60. -/
theorem stuck_ft : ∀ y, ¬ Step c FT y := by
  intro y h
  obtain ⟨n, hn⟩ := (Exec.step_iff_of_ok c ok srReady matchReady coherent _ y).mp h
  rw [successorsN_nil_of_blocked ok srReady matchReady coherent (n := 100) (r₀ := c.rules[0]'(by decide +kernel))
    (List.getElem_mem _) (by decide +kernel) (by decide +kernel) n] at hn
  cases hn

/-- `requires` false: the rule of priority 50 does not apply, and the rule of priority 60 steps. -/
theorem step_tf : Step c TF Stuck :=
  (Exec.step_iff_of_ok c ok srReady matchReady coherent _ _).mpr ⟨100, by decide +kernel⟩

end EnsRulePrio

#print axioms EnsRule.step_true
#print axioms EnsRule.stuck_false
#print axioms EnsRuleOverlap.step_true
#print axioms EnsRuleOverlap.stuck_false
#print axioms EnsRulePrio.step_tt
#print axioms EnsRulePrio.stuck_ft
#print axioms EnsRulePrio.step_tf
