/-
  KCore. A condition reads the list of the variables in scope at its own variables only.

  `condOK` and `Cond.kore` take the variables in scope as a list (of sorts, of Kore variables). Two
  lists of one length that agree at the variables the condition holds (`varOccsCond`) give one
  answer and one pattern: `condOK_congrVars`, `condKore_congrVs`, and for the canonical variables of
  two lists of sorts `condKore_congrCanon`. A binder extends both lists by the same variables, at
  the same indices.
-/
import KcoreSpec.ModelPat
import KcoreSpec.FaithfulStep

set_option autoImplicit false

namespace KCore

open Faithful

/-- Two lists of one length extended by one list agree where they agreed below their length. -/
theorem getElem?_append_congrVars {α : Type} {xs xs' ys : List α} (hl : xs.length = xs'.length) {i : Nat}
    (h : i < xs.length → xs[i]? = xs'[i]?) : (xs ++ ys)[i]? = (xs' ++ ys)[i]? := by
  by_cases hi : i < xs.length
  · rw [List.getElem?_append_left hi, List.getElem?_append_left (hl ▸ hi)]; exact h hi
  · rw [List.getElem?_append_right (by omega), List.getElem?_append_right (by omega), hl]

/-- `getElem?_append_congrVars` for `getD`. -/
theorem getD_append_congrVars {α : Type} {xs xs' ys : List α} {d : α} (hl : xs.length = xs'.length) {i : Nat}
    (h : i < xs.length → xs.getD i d = xs'.getD i d) : (xs ++ ys).getD i d = (xs' ++ ys).getD i d := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
  by_cases hi : i < xs.length
  · rw [List.getElem?_append_left hi, List.getElem?_append_left (hl ▸ hi), ← List.getD_eq_getElem?_getD,
      ← List.getD_eq_getElem?_getD]
    exact h hi
  · rw [List.getElem?_append_right (by omega), List.getElem?_append_right (by omega), hl]

mutual
  /-- A term's pattern reads the variables in scope at its own variables only. -/
  theorem termKore_congrVs {c : Semantics} {vs vs' : List KoreAML.Var} :
      ∀ (t : Term), (∀ i ∈ varOccs t, vs.getD i default = vs'.getD i default) → Term.kore c vs t = Term.kore c vs' t
    | .var i, h => by
      rw [Term.kore, Term.kore, KoreAML.varAt, KoreAML.varAt, h i (by simp [varOccs])]
    | .app f ts, h => by
      rw [Term.kore, Term.kore, termKoreList_congrVs ts (fun i hi => h i (by rw [varOccs]; exact hi))]
    | .inj a b t, h => by
      rw [Term.kore, Term.kore, termKore_congrVs t (fun i hi => h i (by rw [varOccs]; exact hi))]
    | .as t i, h => by
      rw [Term.kore, Term.kore, KoreAML.varAt, KoreAML.varAt, h i (by simp [varOccs]),
        termKore_congrVs t (fun j hj => h j (by rw [varOccs]; exact List.mem_append_left _ hj))]
    | .dv _ _, _ => by rw [Term.kore, Term.kore]
  theorem termKoreList_congrVs {c : Semantics} {vs vs' : List KoreAML.Var} :
      ∀ (ts : List Term), (∀ i ∈ varOccsList ts, vs.getD i default = vs'.getD i default) →
        Term.koreList c vs ts = Term.koreList c vs' ts
    | [], _ => by rw [Term.koreList, Term.koreList]
    | t :: ts, h => by
      rw [Term.koreList, Term.koreList,
        termKore_congrVs t (fun i hi => h i (by rw [varOccsList]; exact List.mem_append_left _ hi)),
        termKoreList_congrVs ts (fun i hi => h i (by rw [varOccsList]; exact List.mem_append_right _ hi))]
end

/-- **A condition's pattern reads the variables in scope at its own variables only**: two lists
of one length that agree at them give one pattern. -/
theorem condKore_congrVs {c : Semantics} (S : Kore.KSort) : ∀ (p : Cond) {vs vs' : List KoreAML.Var},
    vs.length = vs'.length → (∀ i ∈ varOccsCond vs.length p, vs.getD i default = vs'.getD i default) →
    Cond.kore c vs S p = Cond.kore c vs' S p
  | .top, _, _, _, _ => by rw [Cond.kore, Cond.kore]
  | .bot, _, _, _, _ => by rw [Cond.kore, Cond.kore]
  | .not p, vs, vs', hl, h => by
    rw [Cond.kore, Cond.kore, condKore_congrVs S p hl (fun i hi => h i (by rw [varOccsCond]; exact hi))]
  | .and p q, vs, vs', hl, h | .or p q, vs, vs', hl, h | .implies p q, vs, vs', hl, h => by
    rw [Cond.kore, Cond.kore,
      condKore_congrVs S p hl (fun i hi => h i (by rw [varOccsCond]; exact List.mem_append_left _ hi)),
      condKore_congrVs S q hl (fun i hi => h i (by rw [varOccsCond]; exact List.mem_append_right _ hi))]
  | .ceil s t, vs, vs', hl, h => by
    rw [Cond.kore, Cond.kore, termKore_congrVs t (fun i hi => h i (by rw [varOccsCond]; exact hi))]
  | .equals s t u, vs, vs', hl, h | .mem s t u, vs, vs', hl, h => by
    rw [Cond.kore, Cond.kore,
      termKore_congrVs t (fun i hi => h i (by rw [varOccsCond]; exact List.mem_append_left _ hi)),
      termKore_congrVs u (fun i hi => h i (by rw [varOccsCond]; exact List.mem_append_right _ hi))]
  | .exMatch ys s p t body, vs, vs', hl, h => by
    have hin : ∀ i, i ∈ varOccs p ∨ i ∈ varOccsCond (vs.length + ys.length) body → i < vs.length →
        vs.getD i default = vs'.getD i default := fun i hi hlt =>
      h i (by
        rw [varOccsCond]
        exact List.mem_append_right _ (List.mem_filter.mpr ⟨List.mem_append.mpr hi, by simpa using hlt⟩))
    simp only [Cond.kore]
    rw [← hl, termKore_congrVs t (fun i hi => h i (by rw [varOccsCond]; exact List.mem_append_left _ hi)),
      termKore_congrVs (vs' := vs' ++ _) p (fun i hi => getD_append_congrVars hl (hin i (Or.inl hi))),
      condKore_congrVs S body (vs' := vs' ++ _) (by rw [List.length_append, List.length_append, hl])
        (fun i hi => getD_append_congrVars hl (hin i (Or.inr (by
          simpa [List.length_append] using hi))))]
  | .ex s body, vs, vs', hl, h | .all s body, vs, vs', hl, h => by
    simp only [Cond.kore]
    rw [← hl, condKore_congrVs S body (vs' := vs' ++ _) (by rw [List.length_append, List.length_append, hl])
      (fun i hi => getD_append_congrVars hl (fun hlt => h i (by
        rw [varOccsCond]
        exact List.mem_filter.mpr ⟨by simpa [List.length_append] using hi, by simpa using hlt⟩)))]

/-- **A condition is well sorted by the sorts of its own variables**: two lists of sorts of one
length that agree at them give `condOK` one answer. -/
theorem condOK_congrVars {c : Semantics} : ∀ (p : Cond) {vars vars' : List Srt},
    vars.length = vars'.length → (∀ i ∈ varOccsCond vars.length p, vars[i]? = vars'[i]?) →
    c.condOK vars p = c.condOK vars' p
  | .top, _, _, _, _ => by rw [Semantics.condOK, Semantics.condOK]
  | .bot, _, _, _, _ => by rw [Semantics.condOK, Semantics.condOK]
  | .not p, vars, vars', hl, h => by
    rw [Semantics.condOK, Semantics.condOK, condOK_congrVars p hl (fun i hi => h i (by rw [varOccsCond]; exact hi))]
  | .and p q, vars, vars', hl, h | .or p q, vars, vars', hl, h | .implies p q, vars, vars', hl, h => by
    rw [Semantics.condOK, Semantics.condOK,
      condOK_congrVars p hl (fun i hi => h i (by rw [varOccsCond]; exact List.mem_append_left _ hi)),
      condOK_congrVars q hl (fun i hi => h i (by rw [varOccsCond]; exact List.mem_append_right _ hi))]
  | .ceil s t, vars, vars', hl, h => by
    rw [Semantics.condOK, Semantics.condOK, sortOfTerm_congr t (fun i hi => h i (by rw [varOccsCond]; exact hi))]
  | .equals s t u, vars, vars', hl, h | .mem s t u, vars, vars', hl, h => by
    rw [Semantics.condOK, Semantics.condOK,
      sortOfTerm_congr t (fun i hi => h i (by rw [varOccsCond]; exact List.mem_append_left _ hi)),
      sortOfTerm_congr u (fun i hi => h i (by rw [varOccsCond]; exact List.mem_append_right _ hi))]
  | .exMatch ys s p t body, vars, vars', hl, h => by
    have hin : ∀ i, i ∈ varOccs p ∨ i ∈ varOccsCond (vars.length + ys.length) body → i < vars.length →
        vars[i]? = vars'[i]? := fun i hi hlt =>
      h i (by
        rw [varOccsCond]
        exact List.mem_append_right _ (List.mem_filter.mpr ⟨List.mem_append.mpr hi, by simpa using hlt⟩))
    rw [Semantics.condOK, Semantics.condOK,
      sortOfTerm_congr t (fun i hi => h i (by rw [varOccsCond]; exact List.mem_append_left _ hi)),
      sortOfTerm_congr (vs' := vars' ++ ys) p (fun i hi => getElem?_append_congrVars hl (hin i (Or.inl hi))),
      condOK_congrVars body (vars' := vars' ++ ys) (by rw [List.length_append, List.length_append, hl])
        (fun i hi => getElem?_append_congrVars hl (hin i (Or.inr (by
          simpa [List.length_append] using hi))))]
  | .ex s body, vars, vars', hl, h | .all s body, vars, vars', hl, h => by
    rw [Semantics.condOK, Semantics.condOK,
      condOK_congrVars body (vars' := vars' ++ [s]) (by rw [List.length_append, List.length_append, hl])
        (fun i hi => getElem?_append_congrVars hl (fun hlt => h i (by
          rw [varOccsCond]
          exact List.mem_filter.mpr ⟨by simpa [List.length_append] using hi, by simpa using hlt⟩)))]

/-- Two lists of sorts of one length that agree at a variable name it alike. -/
theorem canonVars_getD_congrVars (c : Semantics) {vars vars' : List Srt} (hl : vars.length = vars'.length) {i : Nat}
    (h : vars[i]? = vars'[i]?) : (canonVars c vars).getD i default = (canonVars c vars').getD i default := by
  by_cases hi : i < vars.length
  · rw [canonVars_getD c hi, canonVars_getD c (hl ▸ hi), List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, h]
  · rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_eq_none (by rw [canonVars_length]; omega),
      List.getElem?_eq_none (by rw [canonVars_length]; omega)]

/-- **A condition's pattern over the canonical variables of two lists of sorts** of one length that
agree at the condition's variables is one pattern. -/
theorem condKore_congrCanon {c : Semantics} (S : Kore.KSort) (p : Cond) {vars vars' : List Srt}
    (hl : vars.length = vars'.length) (h : ∀ i ∈ varOccsCond vars.length p, vars[i]? = vars'[i]?) :
    Cond.kore c (canonVars c vars) S p = Cond.kore c (canonVars c vars') S p :=
  condKore_congrVs S p (by rw [canonVars_length, canonVars_length, hl])
    (fun i hi => canonVars_getD_congrVars c hl (h i (by rwa [canonVars_length] at hi)))

end KCore
