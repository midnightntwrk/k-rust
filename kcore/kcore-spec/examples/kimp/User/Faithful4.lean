/-
  Kimp in the fourth stage of faithfulness. Its rules read and write the store through map
  patterns (`X |-> V M` in the `<env>` cell), so it is not in the third stage (`not_stage3`). It
  has no function of its own and no rule of a smaller priority than another, and its sort
  predicates' clauses are plain, so no negated premise reads a map pattern: it is in `Stage4a`,
  and every step of kimp is a theorem of `Γ`. It also satisfies `HypSound`, from which `step_sound`
  gives the same statement without `Hyp`. The decidable facts are kernel decisions.
-/
import Kimp.Facts
import KcoreSpec.FaithfulSound

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace Kimp.FaithfulWitness4

open KCore KCore.Faithful Kimp

instance : OvlOK c := .of_nil (by decide +kernel) (by decide +kernel)

theorem okAll : c.okAll = true := Semantics.okAll_of_ok ok

/-- Each rule's left side binds every variable of the rule (`ok_rule`). -/
theorem rules_bind : ∀ r ∈ c.rules, binds r.vars.length (varOccs r.lhs) = true :=
  fun _ hr => (Semantics.ok_rule ok hr).2.2.2

/-- Each rule's predicates are `\top` (`ok_rule`). -/
theorem rules_top : ∀ r ∈ c.rules, r.pre = .top ∧ r.post = .top :=
  fun _ hr => ⟨(Semantics.ok_rule ok hr).2.1, (Semantics.ok_rule ok hr).2.2.1⟩

/-- Each clause's patterns bind every variable of the clause (`ok_clauseBinds`). -/
theorem clauses_bind : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, binds cl.vars.length (varOccsList cl.pats) = true :=
  Semantics.ok_clauseBinds ok

theorem fns_empty : c.fns.isEmpty = true := by decide +kernel

theorem names_plain : c.ctorSigs.all (fun k => (instDecode? (c.symName k.name)).isNone) = true := by decide +kernel
theorem names_ovls : c.ovls.all (fun o => o.over.all fun g => (instDecode? (c.symName g)).isNone) = true := by
  decide +kernel
theorem names_fns : c.allFns.all (fun fn =>
    (fn.result :: fn.args).all (· < nRegSorts + c.sortNames.length)) = true := by decide +kernel

theorem namesNumbered : NamesNumbered c := by
  refine ⟨fun k hk => ?_, fun o ho g hg => ?_, fun fn hfn s hs => ?_⟩
  · have := List.all_eq_true.mp names_plain k hk
    exact Option.isNone_iff_eq_none.mp this
  · have := List.all_eq_true.mp (List.all_eq_true.mp names_ovls o ho) g hg
    exact Option.isNone_iff_eq_none.mp this
  · have := List.all_eq_true.mp names_fns fn hfn
    exact of_decide_eq_true (List.all_eq_true.mp this s hs)

/-- **Kimp satisfies `Hyp`**: it has no function of its own, so the obligations on functions hold
vacuously. -/
theorem hyp : Hyp c := by
  have hnil : c.fns = [] := List.isEmpty_iff.mp fns_empty
  refine ⟨okAll, srReady, fun fn hfn => ?_, fun fn hfn => ?_, fun fn hfn => ?_, fun fn hfn => ?_, namesNumbered⟩ <;>
    (rw [hnil] at hfn; exact absurd hfn List.not_mem_nil)

theorem genWf_ok : genWf c = true := by decide +kernel
theorem patHooks_ok : patHooksApart c = true := by decide +kernel
theorem prio_ok : c.rules.all (fun r => c.rules.all fun r0 => !decide (r.prio < r0.prio)) = true := by decide +kernel
theorem clauses_ok : c.allFns.all (fun fn => fn.clauses.all fun cl => plainPats c cl.pats) = true := by decide +kernel

/-- Some rule's left-hand side is a map pattern. -/
theorem has_map_pattern : c.rules.any (fun r => !plainPat c r.lhs) = true := by decide +kernel

/-- **Kimp is not in the third stage**: a rule's left-hand side is not plain. -/
theorem not_stage3 : ¬ Stage3 c := fun h => by
  obtain ⟨r, hr, hp⟩ := List.any_eq_true.mp has_map_pattern
  rw [h.2.1 r hr] at hp
  cases hp

/-- **Kimp is in the fourth stage, positive collection patterns.** -/
theorem stage4a : Stage4a c := by
  refine ⟨genWf_ok, patHooks_ok, fun r hr hn => ?_, fun fn hfn cl hcl _ => ?_⟩
  · obtain ⟨r0, hr0, hlt⟩ := hn
    have := List.all_eq_true.mp (List.all_eq_true.mp prio_ok r hr) r0 hr0
    simp [hlt] at this
  · exact List.all_eq_true.mp (List.all_eq_true.mp clauses_ok fn hfn) cl hcl

/-- Every step of kimp is a theorem of `Γ`, by the fourth stage's theorem. -/
theorem step_sound_stage4a' : ∀ x y : Config c, Step c x y → Γ c ⊧ (den c x.val ⇒ KoreAML.sNext (den c y.val)) :=
  step_sound_stage4a c hyp rules_bind rules_top clauses_bind stage4a

theorem mapSort_ok : mapSortOK c = true := by decide +kernel

/-- Kimp is in the fourth stage. -/
theorem stage4 : Stage4 c := stage4_of_stage4a stage4a mapSort_ok

theorem collSorts_ok : collSortsOK c = true := by decide +kernel
theorem colls_ok : collsOK c = true := by decide +kernel
theorem patHeads_ok : patHeadsOK c = true := by decide +kernel

/-- **Kimp satisfies `HypSound`.** -/
theorem hypSound : HypSound c :=
  ⟨okAll, srReady, namesNumbered, genWf_ok, patHooks_ok, collSorts_ok, colls_ok, patHeads_ok, inferInstance⟩

/-- **Every step of kimp is a theorem of `Γ`**, by `step_sound` from `HypSound`: in every model of
`Γ c`, a configuration has each of its `Step` successors as a successor, its store read through
the map symbols' graphs. -/
theorem step_sound : ∀ x y : Config c, Step c x y → Γ c ⊧ (den c x.val ⇒ KoreAML.sNext (den c y.val)) :=
  Faithful.step_sound c hypSound rules_bind rules_top clauses_bind

#print axioms step_sound

end Kimp.FaithfulWitness4
