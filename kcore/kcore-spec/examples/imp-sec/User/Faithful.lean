/-
  ImpSec and step soundness. `lev(X, X |-> L _:Map)` is a clause of a partial function over a
  map pattern: where it fails, `Eval` reads `lev` as undefined, and `Γ`'s closure axiom reads that
  clause negatively. ImpSec satisfies `HypSound`, so every step of it is a theorem of `Γ`. Nothing
  about termination, totality or the agreement of clauses is assumed. The decidable facts are kernel decisions.
-/
import ImpSec.Facts
import KcoreSpec.FaithfulSound

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace ImpSec.FaithfulWitness

open KCore KCore.Faithful ImpSec

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

theorem genWf_ok : genWf c = true := by decide +kernel
theorem patHooks_ok : patHooksApart c = true := by decide +kernel
theorem collSorts_ok : collSortsOK c = true := by decide +kernel
theorem colls_ok : collsOK c = true := by decide +kernel
theorem patHeads_ok : patHeadsOK c = true := by decide +kernel

/-- **ImpSec satisfies `HypSound`.** -/
theorem hypSound : HypSound c :=
  ⟨okAll, srReady, namesNumbered, genWf_ok, patHooks_ok, collSorts_ok, colls_ok, patHeads_ok,
    OvlOK.of_nil (by decide +kernel) (by decide +kernel)⟩

/-- Some clause's patterns are not plain: `lev`'s over the map pattern. -/
theorem has_map_clause : c.allFns.any (fun fn => fn.clauses.any fun cl => !plainPats c cl.pats) = true := by
  decide +kernel

/-- Some function of the definition is not declared total: `lev`, `conf`, `sec`. -/
theorem has_partial : c.fns.any (fun fn => !fn.total) = true := by decide +kernel

/-- **Every step of ImpSec is a theorem of `Γ`**: in every model of `Γ c`, a configuration has each
of its `Step` successors as a successor. -/
theorem step_sound : ∀ x y : Config c, Step c x y → Γ c ⊧ (den c x.val ⇒ KoreAML.sNext (den c y.val)) :=
  Faithful.step_sound c hypSound rules_bind rules_top clauses_bind

#print axioms step_sound

end ImpSec.FaithfulWitness
