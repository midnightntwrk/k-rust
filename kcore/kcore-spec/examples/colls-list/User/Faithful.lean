/-
  CollsList and step soundness. Its rules match the `<stack>` cell's list from the front
  (`ListItem(X:Int) L`) and from the back (`L ListItem(_)`), through the library's list symbols
  (`PatVal.coll`); its core is outside `ok` and inside `okAll`. It satisfies `HypSound`, so every
  step of it is a theorem of `Γ`. Its rules have one priority and its only functions are the sort
  predicates, whose patterns apply no list symbol, so no negated premise of its `Γ` reads a list
  pattern: the list patterns are read upwards only. The decidable facts are kernel decisions.
-/
import CollsList.Facts
import KcoreSpec.FaithfulSound

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace CollsList.FaithfulWitness

open KCore KCore.Faithful CollsList

theorem names_plain : c.ctorSigs.all (fun k => (iteSort? (c.symName k.name)).isNone) = true := by decide +kernel
theorem names_fns : c.allFns.all (fun fn => (iteSort? (c.symName fn.label)).isNone &&
    (fn.result :: fn.args).all (· < nRegSorts + c.sortNames.length)) = true := by decide +kernel

theorem namesNumbered : NamesNumbered c := by
  refine ⟨fun k hk => ?_, fun fn hfn => ?_, fun fn hfn s hs => ?_⟩
  · have := List.all_eq_true.mp names_plain k hk
    exact Option.isNone_iff_eq_none.mp this
  · have := List.all_eq_true.mp names_fns fn hfn
    simp only [Bool.and_eq_true] at this
    exact Option.isNone_iff_eq_none.mp this.1
  · have := List.all_eq_true.mp names_fns fn hfn
    simp only [Bool.and_eq_true] at this
    exact of_decide_eq_true (List.all_eq_true.mp this.2 s hs)

theorem genWf_ok : genWf c = true := by decide +kernel
theorem patHooks_ok : patHooksApart c = true := by decide +kernel
theorem collSorts_ok : collSortsOK c = true := by decide +kernel
theorem colls_ok : collsOK c = true := by decide +kernel
theorem patHeads_ok : patHeadsOK c = true := by decide +kernel

/-- Each rule's left side binds every variable of the rule. -/
theorem rules_bind : ∀ r ∈ c.rules, binds r.vars.length (varOccs r.lhs) = true := by decide +kernel
theorem clauses_bind : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, binds cl.vars.length (varOccsList cl.pats) = true := by
  decide +kernel

/-- **CollsList satisfies `HypSound`.** -/
theorem hypSound : HypSound c :=
  ⟨okAll, srReady, namesNumbered, genWf_ok, patHooks_ok, collSorts_ok, colls_ok, patHeads_ok,
    OvlOK.of_nil (by decide +kernel) (by decide +kernel)⟩

/-- Some rule's left-hand side applies a list pattern symbol (it is not plain). -/
theorem has_list_pattern : c.rules.any (fun r => !plainPat c r.lhs) = true := by decide +kernel

/-- No rule has a smaller priority than another. -/
theorem prio_flat : c.rules.all (fun r => c.rules.all fun r0 => !decide (r.prio < r0.prio)) = true := by decide +kernel

/-- **Every step of CollsList is a theorem of `Γ`**: in every model of `Γ c`, a configuration has
each of its `Step` successors as a successor. -/
theorem step_sound : ∀ x y : Config c, Step c x y → Γ c ⊧ (den c x.val ⇒ KoreAML.sNext (den c y.val)) :=
  Faithful.step_sound c hypSound rules_bind clauses_bind

#print axioms step_sound

end CollsList.FaithfulWitness
