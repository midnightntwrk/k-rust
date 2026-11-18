/-
  KCore. A competitor whose left side need not bind every variable, in any model of `Γc c`.

  `applies c r` binds the variables of r's left side and conditions (`leftVars`) only. Its other
  variables are free in it, and their sorts need not have an element in a model. So the reading
  below gives each of them the configuration sort and x's element (`Rule.leftSorts`, `fillV`): a
  term's sort reads the sorts of its own variables only (`sortOfTerm_congr`, ModelPat.lean), and a translated term
  the valuation at its own variables only (`tr_kore_congr`).

  - `NotApplies c r x` gives `¬applies` at x's element (`not_applies_of_notApplies_heldCEx`, SoundCEx.lean), for a rule
    with `ruleSorted`, `rulePlainOpen` and a larger rule: by the competition conjunct, each open
    condition variable is of a confined sort (`confined_value`), or the conditions are closed and
    `needsWitness` holds, so they are decided: `Refuted` fails where `applies` holds
    (`cond_not_refuted_at`), and `Witnessed` with x's match gives the rule's application at values.
  - Conversely, a rule that applies at values applies in a model (`applies_of_valuesSSx`), so where its
    `requires` has a result at each match, `¬applies` at a valuation gives `NotApplies`
    (`notApplies_of_not_appliesSSx`). No arm is read.

  This file holds the readings those lemmas share (`Rule.leftSorts`, `fillV`, `setV`,
  `PatVal.congr_lookup`); the lemmas themselves read the functions' clauses through
  `neg_of_coreCl` and are in OpenRuleStepCl.lean.
-/
import KcoreSpec.OpenSuccessor

set_option autoImplicit false

namespace KCore

/-- The sorts of the rule's variables, each variable that neither the left side nor the conditions
hold given the configuration sort. -/
def Rule.leftSorts (r : Rule) : List Srt :=
  (List.range r.vars.length).map fun i => if r.leftVars.contains i then r.vars.getD i 0 else topCellSort

theorem Rule.leftSorts_length (r : Rule) : r.leftSorts.length = r.vars.length := by simp [Rule.leftSorts]

theorem Rule.leftSorts_getElem? {r : Rule} {i : Nat} (hi : i < r.vars.length) (hl : i ∈ r.leftVars) :
    r.leftSorts[i]? = r.vars[i]? := by
  simp [Rule.leftSorts, hi, hl, List.getD_eq_getElem?_getD]

theorem Rule.leftSorts_getD {r : Rule} {i : Nat} (hi : i < r.vars.length) (hl : i ∈ r.leftVars) :
    r.leftSorts.getD i 0 = r.vars.getD i 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, r.leftSorts_getElem? hi hl]

theorem Rule.leftSorts_getD_off {r : Rule} {i : Nat} (hi : i < r.vars.length) (hl : i ∉ r.leftVars) :
    r.leftSorts.getD i 0 = topCellSort := by
  simp [Rule.leftSorts, hi, hl, List.getD_eq_getElem?_getD]

namespace Faithful

/-- `applies` of a rule whose premise predicate is `\top`: `∃x̄'. (lhs ∧ ⌈req = true⌉)`, x̄' the
variables of the left side and the conditions. -/
theorem applies_eq {c : Semantics} {r : Rule} (hpre : r.pre = .top) :
    applies c r (canonRulePres r) = KoreAML.existsAll (srtOf c topCellSort)
      ((((List.range r.vars.length).filter r.leftVars.contains).filterMap ((canonVars c r.vars)[·]?)).map
        KoreAML.Var.kore)
      (.and (srtOf c topCellSort) [Term.kore c (canonVars c r.vars) r.lhs,
        reqPat (srtOf c topCellSort) (r.req.map (Term.kore c (canonVars c r.vars)))]) := by
  simp only [applies, Cond.conj, hpre, Cond.isTop, if_true, List.append_nil]
  rfl

open ML
open KoreAML (DefOK Inh IsSort Closed VarKey VarTable)

section
variable {c : Semantics} {M : Type} {I : Interpretation KoreAML.Sym M}

/-- A key of the table and another key have different indices. -/
theorem ev_ne {tbl : VarTable} {k k' : VarKey} (hk : k ∈ tbl) (hne : k ≠ k') : tbl.ev k ≠ tbl.ev k' := by
  intro he
  by_cases hk' : k' ∈ tbl
  · exact hne (ev_inj hk hk' he)
  · simp only [VarTable.ev, VarTable.index, EVar.mk.injEq, Nat.add_right_cancel_iff] at he
    have h1 := List.idxOf_lt_length_of_mem hk
    rw [he, List.idxOf_eq_length hk'] at h1
    exact Nat.lt_irrefl _ h1

open Classical in
/-- The valuation that gives the canonical variables of `vars` not listed in `is`, through `tbl`,
the element a, and agrees with `e` elsewhere. -/
noncomputable def fillV (c : Semantics) (tbl : VarTable) (vars : List Srt) (is : List Nat) (a : M)
    (e : Valuation M) : Valuation M :=
  ⟨fun z => if ∃ i < vars.length, i ∉ is ∧ z = tbl.ev (canonKey c vars i) then a else e.evalEvar z, e.evalSvar⟩

theorem fillV_on {tbl : VarTable} {vars : List Srt} {is : List Nat} {a : M} {e : Valuation M} {i : Nat}
    (hi : i < vars.length) (hn : i ∉ is) : (fillV c tbl vars is a e).evalEvar (tbl.ev (canonKey c vars i)) = a := by
  show (if _ then _ else _) = _
  rw [if_pos ⟨i, hi, hn, rfl⟩]

theorem fillV_off {tbl : VarTable} {vars : List Srt} {is : List Nat} {a : M} {e : Valuation M}
    (hkeys : ∀ i < vars.length, i ∈ is → canonKey c vars i ∈ tbl) {i : Nat} (hi : i < vars.length) (his : i ∈ is) :
    (fillV c tbl vars is a e).evalEvar (tbl.ev (canonKey c vars i)) = e.evalEvar (tbl.ev (canonKey c vars i)) := by
  show (if _ then _ else _) = _
  rw [if_neg]
  rintro ⟨j, hj, hnj, he⟩
  refine ev_ne (hkeys i hi his) (fun hk => hnj ?_) he
  rw [← canonKey_inj hi hj hk]; exact his

open Classical in
/-- The valuation that gives the canonical variables of `vars` listed in `is`, through `tbl`, the
elements f gives them, and agrees with `e` elsewhere. -/
noncomputable def setV (c : Semantics) (tbl : VarTable) (vars : List Srt) (is : List Nat) (f : Nat → M)
    (e : Valuation M) : Valuation M :=
  ⟨fun z => if h : ∃ i < vars.length, i ∈ is ∧ z = tbl.ev (canonKey c vars i) then f (Classical.choose h)
    else e.evalEvar z, e.evalSvar⟩

theorem setV_on {tbl : VarTable} {vars : List Srt} {is : List Nat} {f : Nat → M} {e : Valuation M}
    (hkeys : ∀ i < vars.length, i ∈ is → canonKey c vars i ∈ tbl) {i : Nat} (hi : i < vars.length) (his : i ∈ is) :
    (setV c tbl vars is f e).evalEvar (tbl.ev (canonKey c vars i)) = f i := by
  have hex : ∃ j < vars.length, j ∈ is ∧ tbl.ev (canonKey c vars i) = tbl.ev (canonKey c vars j) :=
    ⟨i, hi, his, rfl⟩
  show (if h : _ then _ else _) = _
  rw [dif_pos hex]
  obtain ⟨hj, hjs, hje⟩ := Classical.choose_spec hex
  rw [(canonKey_inj hi hj (ev_inj (hkeys i hi his) (hkeys _ hj hjs) hje)).symm]

theorem setV_off {tbl : VarTable} {vars : List Srt} {is : List Nat} {f : Nat → M} {e : Valuation M}
    (hkeys : ∀ i < vars.length, i ∈ is → canonKey c vars i ∈ tbl) {i : Nat} (hi : i < vars.length) (his : i ∉ is) :
    (setV c tbl vars is f e).evalEvar (tbl.ev (canonKey c vars i)) = e.evalEvar (tbl.ev (canonKey c vars i)) := by
  show (if h : _ then _ else _) = _
  rw [dif_neg]
  rintro ⟨j, hj, hjs, he⟩
  refine ev_ne (hkeys j hj hjs) (fun hk => his ?_) he.symm
  rw [canonKey_inj hj hi hk] at hjs; exact hjs

end




/-! ## Matching reads σ at the pattern's variables only -/

mutual
  /-- Matching reads σ at the pattern's variables only. -/
  theorem PatVal.congr_lookup {c : Semantics} {σ σ' : Subst} : ∀ {p : Term} {v : GroundTerm}, PatVal c σ p v →
      (∀ j ∈ varOccs p, σ'.lookup j = σ.lookup j) → PatVal c σ' p v
    | .var j, v, h, ha => by
      cases h with
      | var h => exact .var (by rw [ha j (by simp [varOccs]), h])
    | .dv s l, v, h, _ => by cases h; exact .dv
    | .app f ps, v, h, ha => by
      have ha' : ∀ j ∈ varOccsList ps, σ'.lookup j = σ.lookup j := fun j hj => ha j (by simpa [varOccs] using hj)
      cases h with
      | ctor hc hs => exact .ctor hc (PatVals.congr_lookup hs ha')
      | hook hp hs hv => exact .hook hp (PatVals.congr_lookup hs ha') hv
      | coll hc hp hs hv => exact .coll hc hp (PatVals.congr_lookup hs ha') hv
      | ovl hc ho hs hv => exact .ovl hc ho (PatVals.congr_lookup hs ha') hv
    | .inj a b p, v, h, ha => by
      cases h with
      | inj h => exact .inj (PatVal.congr_lookup h fun j hj => ha j (by simpa [varOccs] using hj))
    | .as p i, v, h, ha => by
      cases h with
      | as h hi =>
        exact .as (PatVal.congr_lookup h fun j hj => ha j (by simp [varOccs, hj]))
          (by rw [ha i (by simp [varOccs]), hi])
    termination_by structural p => p
  theorem PatVals.congr_lookup {c : Semantics} {σ σ' : Subst} : ∀ {ps : List Term} {vs : List GroundTerm},
      PatVals c σ ps vs → (∀ j ∈ varOccsList ps, σ'.lookup j = σ.lookup j) → PatVals c σ' ps vs
    | [], vs, h, _ => by cases h; exact .nil
    | p :: ps, vs, h, ha => by
      cases h with
      | cons h hs =>
        exact .cons (PatVal.congr_lookup h fun j hj => ha j (by simp [varOccsList, hj]))
          (PatVals.congr_lookup hs fun j hj => ha j (by simp [varOccsList, hj]))
    termination_by structural ps => ps
end


end Faithful

end KCore
