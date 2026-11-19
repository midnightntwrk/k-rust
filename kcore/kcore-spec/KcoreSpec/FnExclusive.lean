/-
  KCore, checked layer: what `fnExclusiveOK` (DefinitionWf.lean) means: each two equations of one
  priority of a function it accepts are coherent, in both orders (`fnExclusiveOK_sound`,
  `ClausesAgree`). Its three cases:
  - two lists of patterns `overlapList` finds apart match no argument list in common
    (`overlap_sound`): distinct literals, distinct constructors, a constructor term against a
    collection or a literal, injections from sorts without a common lower bound;
  - two clauses with one variable list and one pattern list, whose `requires` `reqsExclusive`
    accepts, never both apply at one argument list (`clausesExclusive_sound`);
  - two clauses whose right-hand sides are one closed term, neither with an `ensures`, give one
    result (`clausesAgree_sound`).
  `clausesAgree_of`: in a core that `ok` accepts, every function's equations agree, given the
  named obligations (`agreeObligations`); `coherentAll_of`: with the match obligations too, the
  clauses of one priority are coherent (`CoherentAll`).

  No case reads that evaluation is functional: where two `requires` are compared, they are
  compared at a term inside both, whose result is one under the first clause's match by the
  hypothesis `Coherent` grants (`HDet`). The two literal shapes:
  - a Bool literal of one `requires` negated in the other: the literal has one value;
  - `t ==K a` in one and `t ==K b` in the other, a and b ground values that differ: `==K` true is
    equality of the two values (`kEq_inv`), t has one value, and a ground constructor term
    evaluates to itself read as a value (`gval_eval`), injectively (`gval_inj`).
-/
import KcoreSpec.DetSound
import KcoreSpec.ClausesAgree

set_option autoImplicit false

namespace KCore.Det

open KCore KCore.Exec GroundTerm

variable {c : Semantics}

/-! ## Ground constructor terms -/

mutual
  /-- The value a `groundValue` term denotes: the term read as a value. -/
  def gval : Term → GroundTerm
    | .dv s l => .dv s l
    | .app f ts => .ctor f (gvalList ts)
    | .inj a b t => .inj a b (gval t)
    | .var _ => .dv 0 (.int 0)
    | .as _ _ => .dv 0 (.int 0)
    termination_by structural t => t
  def gvalList : List Term → List GroundTerm
    | [] => []
    | t :: ts => gval t :: gvalList ts
    termination_by structural ts => ts
end

theorem gval_not_inj : ∀ {t : Term}, c.groundValue t = true → (match t with | .inj .. => false | _ => true) = true →
    (gval t).isInj = false
  | .dv _ _, _, _ => rfl
  | .app _ _, _, _ => rfl
  | .inj _ _ _, _, h => by simp at h
  | .var _, h, _ => by simp [Semantics.groundValue] at h
  | .as _ _, h, _ => by simp [Semantics.groundValue] at h

mutual
  theorem gval_eval {σ : Subst} : ∀ {t : Term} {r : Option GroundTerm}, c.groundValue t = true →
      EvalTerm c σ t r → r = some (gval t)
    | .dv _ _, _, _, h => by cases h; rfl
    | .var _, _, hg, _ => by simp [Semantics.groundValue] at hg
    | .as _ _, _, hg, _ => by simp [Semantics.groundValue] at hg
    | .inj a b t, r, hg, h => by
      simp only [Semantics.groundValue, Bool.and_eq_true] at hg
      cases h with
      | inj h' =>
        rw [gval_eval hg.2 h', Option.map_some, gval, injNormal_of_not_inj (gval_not_inj hg.2 hg.1)]
    | .app f ts, r, hg, h => by
      simp only [Semantics.groundValue, Bool.and_eq_true] at hg
      have hct : c.isCtor f = true := hg.1
      cases h with
      | ctor _ hts =>
        rw [gvalList_eval hg.2 hts, allSome_map_some]
        rfl
      | hook hc _ _ _ _ => rw [hct] at hc; cases hc
      | param hc _ _ _ _ => rw [hct] at hc; cases hc
      | call hc _ _ _ _ _ => rw [hct] at hc; cases hc
      | callUndef hc _ _ _ _ => rw [hct] at hc; cases hc
      | ovl hc _ _ => rw [hct] at hc; cases hc
      | ovlFn hc _ => rw [hct] at hc; cases hc
  theorem gvalList_eval {σ : Subst} : ∀ {ts : List Term} {rs : List (Option GroundTerm)},
      c.groundValueList ts = true → EvalTerms c σ ts rs → rs = (gvalList ts).map some
    | [], _, _, h => by cases h; rfl
    | t :: ts, _, hg, h => by
      simp only [Semantics.groundValueList, Bool.and_eq_true] at hg
      cases h with
      | cons h1 hs => rw [gval_eval hg.1 h1, gvalList_eval hg.2 hs]; rfl
end

mutual
  theorem gval_inj : ∀ {t u : Term}, c.groundValue t = true → c.groundValue u = true →
      gval t = gval u → Term.beq t u = true
    | .dv s l, .dv s' l', _, _, h => by
      simp only [gval, GroundTerm.dv.injEq] at h
      simp [Term.beq, h.1, h.2]
    | .app f ts, .app g us, ht, hu, h => by
      simp only [Semantics.groundValue, Bool.and_eq_true] at ht hu
      simp only [gval, GroundTerm.ctor.injEq] at h
      simp only [Term.beq, Bool.and_eq_true, beq_iff_eq]
      exact ⟨h.1, gvalList_inj ht.2 hu.2 h.2⟩
    | .inj a b t, .inj a' b' u, ht, hu, h => by
      simp only [Semantics.groundValue, Bool.and_eq_true] at ht hu
      simp only [gval, GroundTerm.inj.injEq] at h
      simp only [Term.beq, Bool.and_eq_true, beq_iff_eq]
      exact ⟨⟨h.1, h.2.1⟩, gval_inj ht.2 hu.2 h.2.2⟩
    | .dv _ _, .app _ _, _, _, h => by simp [gval] at h
    | .dv _ _, .inj _ _ _, _, _, h => by simp [gval] at h
    | .app _ _, .dv _ _, _, _, h => by simp [gval] at h
    | .app _ _, .inj _ _ _, _, _, h => by simp [gval] at h
    | .inj _ _ _, .dv _ _, _, _, h => by simp [gval] at h
    | .inj _ _ _, .app _ _, _, _, h => by simp [gval] at h
    | .var _, _, ht, _, _ => by simp [Semantics.groundValue] at ht
    | .as _ _, _, ht, _, _ => by simp [Semantics.groundValue] at ht
    | .dv _ _, .var _, _, hu, _ => by simp [Semantics.groundValue] at hu
    | .dv _ _, .as _ _, _, hu, _ => by simp [Semantics.groundValue] at hu
    | .app _ _, .var _, _, hu, _ => by simp [Semantics.groundValue] at hu
    | .app _ _, .as _ _, _, hu, _ => by simp [Semantics.groundValue] at hu
    | .inj _ _ _, .var _, _, hu, _ => by simp [Semantics.groundValue] at hu
    | .inj _ _ _, .as _ _, _, hu, _ => by simp [Semantics.groundValue] at hu
  theorem gvalList_inj : ∀ {ts us : List Term}, c.groundValueList ts = true → c.groundValueList us = true →
      gvalList ts = gvalList us → Term.beqList ts us = true
    | [], [], _, _, _ => rfl
    | t :: ts, u :: us, ht, hu, h => by
      simp only [Semantics.groundValueList, Bool.and_eq_true] at ht hu
      simp only [gvalList, List.cons.injEq] at h
      simp only [Term.beqList, Bool.and_eq_true]
      exact ⟨gval_inj ht.1 hu.1 h.1, gvalList_inj ht.2 hu.2 h.2⟩
    | [], _ :: _, _, _, h => by simp [gvalList] at h
    | _ :: _, [], _, _, h => by simp [gvalList] at h
end

/-! ## `==K` -/

theorem hook_kEq (v w : GroundTerm) : hook kEq [v, w] = some (some (bool (GroundTerm.cmp v w == .eq))) := rfl
theorem isHook_kEq : isHook kEq = true := rfl

/-- `t ==K u` is true only where t and u have one value. -/
theorem kEq_inv {σ : Subst} {t u : Term} (h : EvalTerm c σ (.app kEq [t, u]) (some (bool true))) :
    ∃ v, EvalTerm c σ t (some v) ∧ EvalTerm c σ u (some v) := by
  generalize ht : Term.app kEq [t, u] = x at h
  generalize hr : some (bool true) = r at h
  cases h with
  | var => cases ht
  | dv => cases ht
  | inj _ => cases ht
  | @ctor _ _ _ rs _ _ =>
    cases ht
    cases h' : allSome rs <;> rw [h'] at hr <;> cases hr
  | @hook _ _ _ rs r' _ _ hts hh hund =>
    cases ht
    obtain ⟨r₁, r₂, rfl, h1, h2⟩ := evalTerms_two hts
    cases r₁ with
    | none => rw [hund (by simp [allSome])] at hr; cases hr
    | some w₁ =>
      cases r₂ with
      | none => rw [hund (by simp [allSome])] at hr; cases hr
      | some w₂ =>
        have hv := hh [w₁, w₂] (by simp [allSome])
        rw [Semantics.hookRes_of_value (hook_kEq w₁ w₂), Option.some.injEq] at hv
        subst hv
        have hb := bool_inj (Option.some.inj hr.symm)
        have he := GroundTerm.cmp_eq w₁ w₂ (beq_iff_eq.mp hb)
        subst he
        exact ⟨w₁, h1, h2⟩
  | param _ hh _ _ _ => cases ht; rw [isHook_kEq] at hh; cases hh
  | call _ hh _ _ _ _ => cases ht; rw [isHook_kEq] at hh; cases hh
  | callUndef _ hh _ _ _ => cases ht; rw [isHook_kEq] at hh; cases hh
  | ovl _ ho _ => cases ht; have := (c.isOvl_parts ho).2.1; rw [isHook_kEq] at this; cases this
  | ovlFn _ ho => cases ht; have := (c.isOvl_parts ho).2.1; rw [isHook_kEq] at this; cases this

/-- An Int comparison hook: on two Ints, the truth of `P`; elsewhere undefined. -/
theorem int2_inv {σ : Subst} {f : Sym} {t u : Term} {b : Bool} {P : Int → Int → Prop}
    [∀ x y, Decidable (P x y)] (hhk : isHook f = true)
    (hf : ∀ vs, hook f vs = some (int2 vs fun x y => some (bool (decide (P x y)))))
    (h : EvalTerm c σ (.app f [t, u]) (some (bool b))) (hs : silentKey f = false := by decide +kernel) :
    ∃ v w x y, EvalTerm c σ t (some v) ∧ EvalTerm c σ u (some w) ∧ asInt v = some x ∧
      asInt w = some y ∧ b = decide (P x y) := by
  generalize ht : Term.app f [t, u] = e at h
  generalize hr : some (bool b) = r at h
  cases h with
  | var => cases ht
  | dv => cases ht
  | inj _ => cases ht
  | @ctor _ _ _ rs _ _ =>
    cases ht
    cases h' : allSome rs <;> rw [h'] at hr <;> cases hr
  | @hook _ _ _ rs r' _ _ hts hh hund =>
    cases ht
    obtain ⟨r₁, r₂, rfl, h1, h2⟩ := evalTerms_two hts
    cases r₁ with
    | none => rw [hund (by simp [allSome])] at hr; cases hr
    | some w₁ =>
      cases r₂ with
      | none => rw [hund (by simp [allSome])] at hr; cases hr
      | some w₂ =>
        have hv := hh [w₁, w₂] (by simp [allSome])
        rw [Semantics.hookRes_of_notKey hs, hf, Option.some.injEq] at hv
        subst hv
        simp only [int2] at hr
        cases hx : asInt w₁ with
        | none => rw [hx] at hr; cases hr
        | some x =>
          cases hy : asInt w₂ with
          | none => rw [hx, hy] at hr; cases hr
          | some y =>
            rw [hx, hy] at hr
            simp only [Option.bind_some, Option.some.injEq] at hr
            exact ⟨w₁, w₂, x, y, h1, h2, hx, hy, bool_inj hr⟩
  | param _ hh _ _ _ => cases ht; rw [hhk] at hh; cases hh
  | call _ hh _ _ _ _ => cases ht; rw [hhk] at hh; cases hh
  | callUndef _ hh _ _ _ => cases ht; rw [hhk] at hh; cases hh
  | ovl _ ho _ => cases ht; have := (c.isOvl_parts ho).2.1; rw [hhk] at this; cases this
  | ovlFn _ ho => cases ht; have := (c.isOvl_parts ho).2.1; rw [hhk] at this; cases this

theorem hook_intLt (vs : List GroundTerm) : hook intLt vs = some (int2 vs fun x y => some (bool (decide (x < y)))) := rfl
theorem hook_intLe (vs : List GroundTerm) : hook intLe vs = some (int2 vs fun x y => some (bool (decide (x ≤ y)))) := rfl
theorem hook_intGt (vs : List GroundTerm) : hook intGt vs = some (int2 vs fun x y => some (bool (decide (x > y)))) := rfl
theorem hook_intGe (vs : List GroundTerm) : hook intGe vs = some (int2 vs fun x y => some (bool (decide (x ≥ y)))) := rfl
theorem hook_intEq (vs : List GroundTerm) : hook intEq vs = some (int2 vs fun x y => some (bool (decide (x = y)))) := rfl
theorem hook_intNe (vs : List GroundTerm) : hook intNe vs = some (int2 vs fun x y => some (bool (decide (x ≠ y)))) := rfl

/-- The Int comparisons and their complements have no silent points. -/
theorem silentKey_of_intCompl {f g : Sym} (h : (f, g) ∈ Semantics.intCompl) :
    silentKey f = false ∧ silentKey g = false := by
  simp only [Semantics.intCompl, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    exact ⟨silentKey_of_mem rfl, silentKey_of_mem rfl⟩

/-- The comparison `f` of `intCompl`, as its predicate. -/
theorem intCompl_cases {f g : Sym} (h : (f, g) ∈ Semantics.intCompl) :
    ∃ (P Q : Int → Int → Prop) (_ : ∀ x y, Decidable (P x y)) (_ : ∀ x y, Decidable (Q x y)),
      (∀ vs, hook f vs = some (int2 vs fun x y => some (bool (decide (P x y))))) ∧
      (∀ vs, hook g vs = some (int2 vs fun x y => some (bool (decide (Q x y))))) ∧
      isHook f = true ∧ isHook g = true ∧ ∀ x y, (Q x y ↔ ¬ P x y) := by
  simp only [Semantics.intCompl, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨_, _, inferInstance, inferInstance, hook_intLt, hook_intGe, rfl, rfl, fun x y => by omega⟩
  · exact ⟨_, _, inferInstance, inferInstance, hook_intGe, hook_intLt, rfl, rfl, fun x y => by omega⟩
  · exact ⟨_, _, inferInstance, inferInstance, hook_intLe, hook_intGt, rfl, rfl, fun x y => by omega⟩
  · exact ⟨_, _, inferInstance, inferInstance, hook_intGt, hook_intLe, rfl, rfl, fun x y => by omega⟩
  · exact ⟨_, _, inferInstance, inferInstance, hook_intEq, hook_intNe, rfl, rfl, fun x y => Iff.rfl⟩
  · exact ⟨_, _, inferInstance, inferInstance, hook_intNe, hook_intEq, rfl, rfl, fun x y => ⟨fun h hn => hn h, fun h => Classical.byContradiction h⟩⟩

theorem eqKLit_spec {p : Term × Bool} {x a : Term} (h : Semantics.eqKLit p = some (x, a)) :
    p = (.app kEq [x, a], true) := by
  unfold Semantics.eqKLit at h
  split at h
  · split at h
    · rename_i hf
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rw [beq_iff_eq.mp hf]
    · cases h
  · cases h

/-! ## Int bounds and disjunctions -/

/-- What the Int comparison g asserts of x and y. -/
def cmpHolds (g : Sym) (x y : Int) : Prop :=
  (g = intLt → x < y) ∧ (g = intLe → x ≤ y) ∧ (g = intGt → y < x) ∧ (g = intGe → y ≤ x) ∧
  (g = intEq → x = y) ∧ (g = intNe → x ≠ y)

/-- A comparison asserted `b` (`cmpAsserted`): its arguments are Ints that the asserted
comparison relates. -/
theorem cmpAsserted_sound {σ : Subst} {f g : Sym} {x y : Term} {b : Bool}
    (hg : Semantics.cmpAsserted f b = some g) (h : EvalTerm c σ (.app f [x, y]) (some (bool b))) :
    ∃ v w X Y, EvalTerm c σ x (some v) ∧ EvalTerm c σ y (some w) ∧ asInt v = some X ∧
      asInt w = some Y ∧ cmpHolds g X Y := by
  by_cases eintLt : f = intLt
  · subst eintLt
    obtain ⟨v, w, X, Y, ev, ew, hx, hy, hb⟩ := int2_inv rfl hook_intLt h
    refine ⟨v, w, X, Y, ev, ew, hx, hy, ?_⟩
    cases b <;> simp (config := {decide := true}) [Semantics.cmpAsserted] at hg <;> subst hg <;> simp at hb <;>
      simp only [cmpHolds] <;> refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro he <;> first | exact absurd he (by decide) | omega
  by_cases eintGe : f = intGe
  · subst eintGe
    obtain ⟨v, w, X, Y, ev, ew, hx, hy, hb⟩ := int2_inv rfl hook_intGe h
    refine ⟨v, w, X, Y, ev, ew, hx, hy, ?_⟩
    cases b <;> simp (config := {decide := true}) [Semantics.cmpAsserted] at hg <;> subst hg <;> simp at hb <;>
      simp only [cmpHolds] <;> refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro he <;> first | exact absurd he (by decide) | omega
  by_cases eintLe : f = intLe
  · subst eintLe
    obtain ⟨v, w, X, Y, ev, ew, hx, hy, hb⟩ := int2_inv rfl hook_intLe h
    refine ⟨v, w, X, Y, ev, ew, hx, hy, ?_⟩
    cases b <;> simp (config := {decide := true}) [Semantics.cmpAsserted] at hg <;> subst hg <;> simp at hb <;>
      simp only [cmpHolds] <;> refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro he <;> first | exact absurd he (by decide) | omega
  by_cases eintGt : f = intGt
  · subst eintGt
    obtain ⟨v, w, X, Y, ev, ew, hx, hy, hb⟩ := int2_inv rfl hook_intGt h
    refine ⟨v, w, X, Y, ev, ew, hx, hy, ?_⟩
    cases b <;> simp (config := {decide := true}) [Semantics.cmpAsserted] at hg <;> subst hg <;> simp at hb <;>
      simp only [cmpHolds] <;> refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro he <;> first | exact absurd he (by decide) | omega
  by_cases eintEq : f = intEq
  · subst eintEq
    obtain ⟨v, w, X, Y, ev, ew, hx, hy, hb⟩ := int2_inv rfl hook_intEq h
    refine ⟨v, w, X, Y, ev, ew, hx, hy, ?_⟩
    cases b <;> simp (config := {decide := true}) [Semantics.cmpAsserted] at hg <;> subst hg <;> simp at hb <;>
      simp only [cmpHolds] <;> refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro he <;> first | exact absurd he (by decide) | omega
  by_cases eintNe : f = intNe
  · subst eintNe
    obtain ⟨v, w, X, Y, ev, ew, hx, hy, hb⟩ := int2_inv rfl hook_intNe h
    refine ⟨v, w, X, Y, ev, ew, hx, hy, ?_⟩
    cases b <;> simp (config := {decide := true}) [Semantics.cmpAsserted] at hg <;> subst hg <;> simp at hb <;>
      simp only [cmpHolds] <;> refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro he <;> first | exact absurd he (by decide) | omega
  exfalso
  simp [Semantics.cmpAsserted, eintLt, eintGe, eintLe, eintGt, eintEq, eintNe] at hg

theorem cmpFlip_sound {g g' : Sym} {x y : Int} (h : Semantics.cmpFlip g = some g') (hc : cmpHolds g x y) :
    cmpHolds g' y x := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hc
  by_cases eintLt : g = intLt
  · subst eintLt
    simp (config := {decide := true}) [Semantics.cmpFlip] at h
    subst h
    simp only [cmpHolds]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro he <;>
      first | exact absurd he (by decide) | (have := h1 rfl; omega) | (have := h2 rfl; omega) |
        (have := h3 rfl; omega) | (have := h4 rfl; omega) | (have := h5 rfl; omega) | (have := h6 rfl; omega)
  by_cases eintGe : g = intGe
  · subst eintGe
    simp (config := {decide := true}) [Semantics.cmpFlip] at h
    subst h
    simp only [cmpHolds]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro he <;>
      first | exact absurd he (by decide) | (have := h1 rfl; omega) | (have := h2 rfl; omega) |
        (have := h3 rfl; omega) | (have := h4 rfl; omega) | (have := h5 rfl; omega) | (have := h6 rfl; omega)
  by_cases eintLe : g = intLe
  · subst eintLe
    simp (config := {decide := true}) [Semantics.cmpFlip] at h
    subst h
    simp only [cmpHolds]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro he <;>
      first | exact absurd he (by decide) | (have := h1 rfl; omega) | (have := h2 rfl; omega) |
        (have := h3 rfl; omega) | (have := h4 rfl; omega) | (have := h5 rfl; omega) | (have := h6 rfl; omega)
  by_cases eintGt : g = intGt
  · subst eintGt
    simp (config := {decide := true}) [Semantics.cmpFlip] at h
    subst h
    simp only [cmpHolds]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro he <;>
      first | exact absurd he (by decide) | (have := h1 rfl; omega) | (have := h2 rfl; omega) |
        (have := h3 rfl; omega) | (have := h4 rfl; omega) | (have := h5 rfl; omega) | (have := h6 rfl; omega)
  by_cases eintEq : g = intEq
  · subst eintEq
    simp (config := {decide := true}) [Semantics.cmpFlip] at h
    subst h
    simp only [cmpHolds]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro he <;>
      first | exact absurd he (by decide) | (have := h1 rfl; omega) | (have := h2 rfl; omega) |
        (have := h3 rfl; omega) | (have := h4 rfl; omega) | (have := h5 rfl; omega) | (have := h6 rfl; omega)
  by_cases eintNe : g = intNe
  · subst eintNe
    simp (config := {decide := true}) [Semantics.cmpFlip] at h
    subst h
    simp only [cmpHolds]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro he <;>
      first | exact absurd he (by decide) | (have := h1 rfl; omega) | (have := h2 rfl; omega) |
        (have := h3 rfl; omega) | (have := h4 rfl; omega) | (have := h5 rfl; omega) | (have := h6 rfl; omega)
  exfalso
  simp [Semantics.cmpFlip, eintLt, eintGe, eintLe, eintGt, eintEq, eintNe] at h

theorem cmpBound_sound {g : Sym} {k x : Int} {lo hi : Option Int} (h : Semantics.cmpBound g k = some (lo, hi))
    (hc : cmpHolds g x k) : (∀ l, lo = some l → l ≤ x) ∧ (∀ u, hi = some u → x ≤ u) := by
  obtain ⟨h1, h2, h3, h4, h5, _⟩ := hc
  by_cases eintLt : g = intLt
  · subst eintLt
    simp (config := {decide := true}) [Semantics.cmpBound] at h
    obtain ⟨rfl, rfl⟩ := h
    constructor <;> intro z hz <;> cases hz <;>
      first | (have := h1 rfl; omega) | (have := h2 rfl; omega) | (have := h3 rfl; omega) |
        (have := h4 rfl; omega) | (have := h5 rfl; omega)
  by_cases eintLe : g = intLe
  · subst eintLe
    simp (config := {decide := true}) [Semantics.cmpBound] at h
    obtain ⟨rfl, rfl⟩ := h
    constructor <;> intro z hz <;> cases hz <;>
      first | (have := h1 rfl; omega) | (have := h2 rfl; omega) | (have := h3 rfl; omega) |
        (have := h4 rfl; omega) | (have := h5 rfl; omega)
  by_cases eintGt : g = intGt
  · subst eintGt
    simp (config := {decide := true}) [Semantics.cmpBound] at h
    obtain ⟨rfl, rfl⟩ := h
    constructor <;> intro z hz <;> cases hz <;>
      first | (have := h1 rfl; omega) | (have := h2 rfl; omega) | (have := h3 rfl; omega) |
        (have := h4 rfl; omega) | (have := h5 rfl; omega)
  by_cases eintGe : g = intGe
  · subst eintGe
    simp (config := {decide := true}) [Semantics.cmpBound] at h
    obtain ⟨rfl, rfl⟩ := h
    constructor <;> intro z hz <;> cases hz <;>
      first | (have := h1 rfl; omega) | (have := h2 rfl; omega) | (have := h3 rfl; omega) |
        (have := h4 rfl; omega) | (have := h5 rfl; omega)
  by_cases eintEq : g = intEq
  · subst eintEq
    simp (config := {decide := true}) [Semantics.cmpBound] at h
    obtain ⟨rfl, rfl⟩ := h
    constructor <;> intro z hz <;> cases hz <;>
      first | (have := h1 rfl; omega) | (have := h2 rfl; omega) | (have := h3 rfl; omega) |
        (have := h4 rfl; omega) | (have := h5 rfl; omega)
  exfalso
  simp [Semantics.cmpBound, eintLt, eintLe, eintGt, eintGe, eintEq] at h

theorem intLitOf_eval {σ : Subst} {y : Term} {k : Int} {r : Option GroundTerm}
    (h : Semantics.intLitOf y = some k) (e : EvalTerm c σ y r) : ∃ w, r = some w ∧ asInt w = some k := by
  unfold Semantics.intLitOf at h
  split at h
  · rename_i s k'
    split at h
    · rename_i hs
      cases h
      have hr : r = some (.dv s (.int k)) := by
        generalize ht : Term.dv s (.int k) = t at e
        cases e with
        | dv => cases ht; rfl
        | _ => cases ht
      refine ⟨_, hr, ?_⟩
      simp [asInt, hs]
    · cases h
  · cases h

/-- A literal `intBound` reads: the term is an Int within the bounds. -/
theorem intBound_sound {σ : Subst} {A t : Term} {b : Bool} {lo hi : Option Int}
    (h : Semantics.intBound (A, b) = some (t, lo, hi)) (e : EvalTerm c σ A (some (bool b))) :
    ∃ v x, EvalTerm c σ t (some v) ∧ asInt v = some x ∧ (∀ l, lo = some l → l ≤ x) ∧
      (∀ u, hi = some u → x ≤ u) := by
  cases A with
  | app f args =>
    rcases args with _ | ⟨x, _ | ⟨y, _ | ⟨_, _⟩⟩⟩
    · simp [Semantics.intBound] at h
    · simp [Semantics.intBound] at h
    · simp only [Semantics.intBound] at h
      cases hg : Semantics.cmpAsserted f b with
      | none => rw [hg] at h; cases h
      | some g =>
        rw [hg] at h
        simp only at h
        obtain ⟨v, w, X, Y, ev, ew, hx, hy, hc⟩ := cmpAsserted_sound hg e
        cases hk : Semantics.intLitOf y with
        | some k =>
          rw [hk] at h
          simp only at h
          obtain ⟨w', hw', hk'⟩ := intLitOf_eval hk ew
          cases hw'
          rw [hy] at hk'; cases hk'
          obtain ⟨⟨lo', hi'⟩, hb, he⟩ := Option.map_eq_some_iff.mp h
          simp only [Prod.mk.injEq] at he
          obtain ⟨rfl, rfl, rfl⟩ := he
          exact ⟨v, X, ev, hx, cmpBound_sound hb hc⟩
        | none =>
          rw [hk] at h
          simp only at h
          cases hk2 : Semantics.intLitOf x with
          | none => rw [hk2] at h; cases h
          | some k =>
            cases hg' : Semantics.cmpFlip g with
            | none => rw [hk2, hg'] at h; cases h
            | some g' =>
              rw [hk2, hg'] at h
              simp only at h
              obtain ⟨v', hv', hk'⟩ := intLitOf_eval hk2 ev
              cases hv'
              rw [hx] at hk'; cases hk'
              obtain ⟨⟨lo', hi'⟩, hb, he⟩ := Option.map_eq_some_iff.mp h
              simp only [Prod.mk.injEq] at he
              obtain ⟨rfl, rfl, rfl⟩ := he
              exact ⟨w, Y, ew, hy, cmpBound_sound hb (cmpFlip_sound hg' hc)⟩
    · simp [Semantics.intBound] at h
  | _ => simp [Semantics.intBound] at h

theorem boundsApart_sound {x : Int} {r r' : Option Int × Option Int} (h : Semantics.boundsApart r r' = true)
    (h1 : (∀ l, r.1 = some l → l ≤ x) ∧ (∀ u, r.2 = some u → x ≤ u))
    (h2 : (∀ l, r'.1 = some l → l ≤ x) ∧ (∀ u, r'.2 = some u → x ≤ u)) : False := by
  obtain ⟨lo, hi⟩ := r
  obtain ⟨lo', hi'⟩ := r'
  simp only [Semantics.boundsApart, Bool.or_eq_true] at h
  rcases h with h | h
  · split at h
    · rename_i l u
      have := h1.1 l rfl; have := h2.2 u rfl; simp at h; omega
    · cases h
  · split at h
    · rename_i l u
      have := h2.1 l rfl; have := h1.2 u rfl; simp at h; omega
    · cases h

theorem hook_or (vs : List GroundTerm) : hook boolOr vs = some (bool2 vs (· || ·)) := rfl
theorem isHook_or : isHook boolOr = true := rfl

theorem or_inv {σ : Subst} {t₁ t₂ : Term} (h : EvalTerm c σ (.app boolOr [t₁, t₂]) (some (bool true))) :
    EvalTerm c σ t₁ (some (bool true)) ∨ EvalTerm c σ t₂ (some (bool true)) := by
  generalize ht : Term.app boolOr [t₁, t₂] = t at h
  generalize hr : some (bool true) = r at h
  cases h with
  | @ctor _ _ _ rs _ _ =>
    cases ht
    cases h' : allSome rs <;> rw [h'] at hr <;> cases hr
  | @hook _ _ _ rs r' _ _ hts hh hund =>
    cases ht
    obtain ⟨r₁, r₂, rfl, h1, h2⟩ := evalTerms_two hts
    cases r₁ with
    | none => rw [hund (by simp [allSome])] at hr; cases hr
    | some w₁ =>
      cases r₂ with
      | none => rw [hund (by simp [allSome])] at hr; cases hr
      | some w₂ =>
        have hv := hh [w₁, w₂] (by simp [allSome])
        rw [Semantics.hookRes_of_notKey (f := boolOr) (silentKey_of_mem rfl), hook_or, Option.some.injEq] at hv
        subst hv
        have hr' := hr.symm
        unfold bool2 at hr'
        cases hx : asBool w₁ with
        | none => simp [hx] at hr'
        | some x =>
        cases hy : asBool w₂ with
        | none => simp [hx, hy] at hr'
        | some y =>
        simp only [hx, hy, Option.bind_some, Option.map_some, Option.some.injEq] at hr'
        have := bool_inj hr'
        rw [asBool_some hx] at h1; rw [asBool_some hy] at h2
        rw [← hr]
        cases x
        · cases y
          · simp at this
          · exact .inr h2
        · exact .inl h1
  | param _ hhk _ _ _ => cases ht; rw [isHook_or] at hhk; cases hhk
  | call _ hhk _ _ _ _ => cases ht; rw [isHook_or] at hhk; cases hhk
  | callUndef _ _ _ _ _ => cases ht; cases hr
  | ovl _ ho _ => cases ht; have := (c.isOvl_parts ho).2.1; rw [isHook_or] at this; cases this
  | ovlFn _ ho => cases ht; have := (c.isOvl_parts ho).2.1; rw [isHook_or] at this; cases this
  | _ => cases ht

/-! ## Patterns apart (`overlap`) -/

/-- Every pattern symbol of the library's map and collection patterns is a collection symbol. -/
theorem patternHooks_collHooks : ∀ g ∈ patternHooks ++ collPatternHooks, g ∈ collHooks := by decide

theorem collHead_of_hooks {f : Sym} (h : f ∈ patternHooks ++ collPatternHooks) : c.collHead f = true := by
  have := List.contains_iff_mem.mpr (patternHooks_collHooks f h)
  unfold Semantics.collHead; rw [this]; rfl

/-- A map pattern symbol, or a collection pattern symbol (`isCollPat`), is a collection symbol. -/
theorem collHead_of_patternHook {f : Sym} (h : patternHooks.contains f = true) : c.collHead f = true :=
  collHead_of_hooks (List.mem_append_left _ (List.contains_iff_mem.mp h))

theorem collHead_of_collPat {f : Sym} (hp : c.isCollPat f = true) : c.collHead f = true := by
  unfold Semantics.isCollPat at hp
  simp only [Bool.and_eq_true] at hp
  obtain ⟨-, hp⟩ := hp
  by_cases hh : isHook f = true
  · rw [if_pos hh] at hp
    exact collHead_of_hooks (List.mem_append_right _ (List.contains_iff_mem.mp hp))
  · rw [if_neg hh] at hp
    cases hk : c.lookupParam f with
    | none => rw [hk] at hp; cases hp
    | some k =>
      rw [hk] at hp
      simp only at hp
      cases hi : k.impl with
      | none => rw [hi] at hp; cases hp
      | some g =>
        rw [hi] at hp
        simp only at hp
        have hg : collHooks.contains g = true := by
          refine List.contains_iff_mem.mpr (patternHooks_collHooks g ?_)
          simp only [Bool.or_eq_true, List.contains_iff_mem] at hp
          rcases hp with hp | hp
          · exact List.mem_append_left _ hp
          · exact List.mem_append_right _ hp
        rw [Semantics.lookupParam_eq] at hk
        have hmem := List.mem_of_find?_eq_some hk
        have hname := List.find?_some hk
        unfold Semantics.collHead
        refine Bool.or_eq_true_iff.mpr (.inr (List.any_eq_true.mpr ⟨k, hmem, ?_⟩))
        simp only [Bool.and_eq_true]
        exact ⟨hname, by rw [hi]; exact hg⟩

/-- A pattern `f(…)` denotes a constructor term of f, or, f a collection symbol, a collection. -/
theorem PatVal.app_cases {f : Sym} (hf : c.ovlPlain f = true) {σ : Subst} {ps : List Term} {v : GroundTerm}
    (h : PatVal c σ (.app f ps) v) :
    (∃ vs, v = .ctor f vs ∧ PatVals c σ ps vs) ∨ (c.collHead f = true ∧ ∀ g vs, v ≠ .ctor g vs) := by
  generalize ht : Term.app f ps = t at h
  cases h with
  | ctor _ hs => cases ht; exact .inl ⟨_, rfl, hs⟩
  | hook hp _ hv =>
    cases ht
    obtain ⟨es, rfl⟩ := patternHook_map hp hv
    exact .inr ⟨collHead_of_patternHook hp, fun _ _ h => by cases h⟩
  | coll _ hp _ hv =>
    cases ht
    refine .inr ⟨collHead_of_collPat hp, fun _ _ h => ?_⟩
    rcases collVal_shape hp hv with ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ <;> cases h
  | ovl _ _ hs hv => cases ht; rw [norm_plain hf] at hv; exact .inl ⟨_, hv.symm, hs⟩
  | _ => cases ht

theorem PatVal.app_not_inj {f : Sym} (hf : c.ovlPlain f = true) {σ : Subst} {ps : List Term} {v : GroundTerm}
    (h : PatVal c σ (.app f ps) v) : v.isInj = false := by
  rcases PatVal.app_shapeO hf h with ⟨_, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ <;> rfl

/-- Only a pattern that can denote an injection (`injable`) denotes one, where it applies no
overloading symbol that overloads one (whose pattern denotes an injection where it is covered at a
smaller result sort). -/
theorem injable_of_isInj {σ : Subst} : ∀ {p : Term} {w : GroundTerm}, c.ovlFree p = true →
    PatVal c σ p w → w.isInj = true → injable p = true
  | .var _, _, _, _, _ => rfl
  | .inj _ _ _, _, _, _, _ => rfl
  | .dv _ _, _, _, h, hi => by rw [PatVal.dv_shape h] at hi; cases hi
  | .app _ _, _, hf, h, hi => by rw [PatVal.app_not_inj (ovlFree_app hf).1 h] at hi; cases hi
  | .as p _, _, hf, h, hi => by
    have := injable_of_isInj (by simpa [Semantics.ovlFree] using hf) (PatVal.as_inv h).1 hi
    simpa [injable, peelAs] using this

theorem ovlFree_peelAs : ∀ {q : Term}, c.ovlFree q = true → c.ovlFree (peelAs q) = true
  | .as q _, h => by simp only [peelAs]; exact ovlFree_peelAs (by simpa [Semantics.ovlFree] using h)
  | .var _, h => h
  | .dv _ _, h => h
  | .app _ _, h => h
  | .inj _ _ _, h => h

theorem peelAs_not_as : ∀ (q t : Term) (i : Nat), peelAs q ≠ .as t i
  | .as q _, t, i => by simp only [peelAs]; exact peelAs_not_as q t i
  | .var _, _, _ => by simp [peelAs]
  | .dv _ _, _, _ => by simp [peelAs]
  | .app _ _, _, _ => by simp [peelAs]
  | .inj _ _ _, _, _ => by simp [peelAs]

/-- A pattern and its aliased pattern (`peelAs`) have one sort and denote one value. -/
theorem peelAs_patVal {x : TermCtx} {vars : List Srt} {σ : Subst} : ∀ {q : Term} {s : Srt} {v : GroundTerm},
    sortOfTerm x vars q = some s → PatVal c σ q v → sortOfTerm x vars (peelAs q) = some s ∧ PatVal c σ (peelAs q) v
  | .as q _, _, _, hs, h => by
    simp only [peelAs]; exact peelAs_patVal (sortOfTerm_as hs).2 (PatVal.as_inv h).1
  | .var _, _, _, hs, h => ⟨hs, h⟩
  | .dv _ _, _, _, hs, h => ⟨hs, h⟩
  | .app _ _, _, _, hs, h => ⟨hs, h⟩
  | .inj _ _ _, _, _, hs, h => ⟨hs, h⟩

theorem injNormal_target {a a' b b' : Srt} {w w' : GroundTerm} (h : injNormal a b w = injNormal a' b' w') :
    b = b' := by
  obtain ⟨_, _, h1⟩ := injNormal_shape a b w
  obtain ⟨_, _, h2⟩ := injNormal_shape a' b' w'
  rw [h1, h2] at h
  cases h; rfl

/-- A value of sort a that is an injection is one from a sort below a. -/
theorem isInj_sorted {w : GroundTerm} {a : Srt} (hs : c.sortOf w = some a) (hi : w.isInj = true) :
    ∃ a₀ u, w = .inj a₀ a u ∧ (a₀, a) ∈ c.subsorts := by
  cases w with
  | inj a₀ a' u =>
    obtain ⟨h1, -, -, rfl⟩ := sortOf_inj.mp hs
    exact ⟨a₀, u, rfl, h1⟩
  | _ => cases hi

theorem le_of_sub {a b : Srt} (h : (a, b) ∈ c.subsorts) : c.le a b = true := by
  simp [Semantics.le, h]

/-- Two injections into one sort, from sorts a ≠ b, of values of sorts a and b, are one value only
when a and b have a common lower bound (`meet`) and one of the values is an injection. -/
theorem inj_meet {a b N N' : Srt} {w w' : GroundTerm} (hab : a ≠ b) (hw : c.sortOf w = some a)
    (hw' : c.sortOf w' = some b) (h : injNormal a N w = injNormal b N' w') :
    c.meet a b = true ∧ (w.isInj = true ∨ w'.isInj = true) := by
  cases hi : w.isInj with
  | true =>
    obtain ⟨a₀, u, rfl, ha₀⟩ := isInj_sorted hw hi
    refine ⟨?_, .inl rfl⟩
    cases hi' : w'.isInj with
    | true =>
      obtain ⟨b₀, u', rfl, hb₀⟩ := isInj_sorted hw' hi'
      simp only [injNormal, GroundTerm.inj.injEq] at h
      obtain ⟨rfl, -, -⟩ := h
      unfold Semantics.meet
      have : (c.subsorts.any fun (s, _) => c.le s a && c.le s b) = true :=
        List.any_eq_true.mpr ⟨(a₀, a), ha₀, by simp [le_of_sub ha₀, le_of_sub hb₀]⟩
      simp [this]
    | false =>
      rw [injNormal_of_not_inj hi'] at h
      simp only [injNormal, GroundTerm.inj.injEq] at h
      obtain ⟨rfl, -, -⟩ := h
      unfold Semantics.meet
      simp [le_of_sub ha₀]
  | false =>
    cases hi' : w'.isInj with
    | true =>
      obtain ⟨b₀, u', rfl, hb₀⟩ := isInj_sorted hw' hi'
      refine ⟨?_, .inr rfl⟩
      rw [injNormal_of_not_inj hi] at h
      simp only [injNormal, GroundTerm.inj.injEq] at h
      obtain ⟨rfl, -, -⟩ := h
      unfold Semantics.meet
      simp [le_of_sub hb₀]
    | false =>
      rw [injNormal_of_not_inj hi, injNormal_of_not_inj hi'] at h
      simp only [GroundTerm.inj.injEq] at h
      exact absurd h.1 hab

mutual
  /-- Two well-sorted patterns that `overlap` finds apart, applying no overloading symbol, denote
  no value in common. -/
  theorem overlap_sound_termF (hmc : MatchCtxO c) {vars vars' : List Srt} {σ σ' : Subst}
      (hσ : c.WellSorted vars σ) (hσ' : c.WellSorted vars' σ') : ∀ (p : Term) {q : Term} {s s' : Srt} {v : GroundTerm},
      c.ovlFree p = true → c.ovlFree q = true →
      sortOfTerm c.patCtxNF vars p = some s → sortOfTerm c.patCtxNF vars' q = some s' →
      overlap c.meet c.collHead p q = false → PatVal c σ p v → PatVal c σ' q v → False
    | .var _, _, _, _, _, _, _, _, _, ho, _, _ => by simp [overlap] at ho
    | .as p _, _, _, _, _, hpf, hqf, hs, hs', ho, hp, hq => by
      rw [overlap] at ho
      exact overlap_sound_termF hmc hσ hσ' p (by simpa [Semantics.ovlFree] using hpf) hqf
        (sortOfTerm_as hs).2 hs' ho (PatVal.as_inv hp).1 hq
    | .dv a l, q, _, _, v, _, hqf, _, hs', ho, hp, hq => by
      obtain ⟨hs₀, hq₀⟩ := peelAs_patVal hs' hq
      have hq₀f := ovlFree_peelAs hqf
      have hv := PatVal.dv_shape hp
      subst hv
      rw [overlap] at ho
      obtain ⟨q₀, he⟩ : ∃ q₀, peelAs q = q₀ := ⟨_, rfl⟩
      rw [he] at ho hs₀ hq₀ hq₀f
      cases q₀ with
      | var => simp at ho
      | dv b l' =>
        have := PatVal.dv_shape hq₀
        simp only [GroundTerm.dv.injEq] at this
        obtain ⟨rfl, rfl⟩ := this
        simp at ho
      | app g qs =>
        rcases PatVal.app_shapeO (ovlFree_app hq₀f).1 hq₀ with ⟨_, h⟩ | ⟨_, _, h⟩ | ⟨_, _, h⟩ | ⟨_, _, h⟩ <;> cases h
      | inj b N q' => have := PatVal.inj_shape hq₀; cases this
      | as t i => exact peelAs_not_as q t i he
    | .app f ps, q, s, _, v, hpf, hqf, hs, hs', ho, hp, hq => by
      obtain ⟨hs₀, hq₀⟩ := peelAs_patVal hs' hq
      have hq₀f := ovlFree_peelAs hqf
      obtain ⟨hfo, hpsf⟩ := ovlFree_app hpf
      rw [overlap] at ho
      obtain ⟨q₀, he⟩ : ∃ q₀, peelAs q = q₀ := ⟨_, rfl⟩
      rw [he] at ho hs₀ hq₀ hq₀f
      cases q₀ with
      | var => simp at ho
      | dv b l' =>
        rw [PatVal.dv_shape hq₀] at hp
        rcases PatVal.app_shapeO hfo hp with ⟨_, h⟩ | ⟨_, _, h⟩ | ⟨_, _, h⟩ | ⟨_, _, h⟩ <;> cases h
      | inj b N q' =>
        have h1 := PatVal.inj_shape hq₀
        rw [PatVal.app_not_inj hfo hp] at h1; cases h1
      | as t i => exact peelAs_not_as q t i he
      | app g qs =>
        obtain ⟨hgo, hqsf⟩ := ovlFree_app hq₀f
        simp only [Bool.or_eq_false_iff, Bool.and_eq_false_iff] at ho
        rcases PatVal.app_cases hfo hp with ⟨vs, rfl, hps⟩ | ⟨hcf, hnc⟩
        · rcases PatVal.app_cases hgo hq₀ with ⟨vs', he', hqs⟩ | ⟨-, hnc'⟩
          · simp only [GroundTerm.ctor.injEq] at he'
            obtain ⟨rfl, rfl⟩ := he'
            obtain ⟨k, -, hargs, -⟩ := sortOfTerm_app.mp hs
            obtain ⟨k', -, hargs', -⟩ := sortOfTerm_app.mp hs₀
            have hol : overlapList c.meet c.collHead ps qs = false := by
              rcases ho.2 with h | h
              · simp at h
              · exact h
            exact overlap_soundF hmc hσ hσ' ps hpsf hqsf hargs hargs' hol hps hqs
          · exact hnc' f vs rfl
        · rcases PatVal.app_cases hgo hq₀ with ⟨vs', rfl, -⟩ | ⟨hcg, -⟩
          · exact hnc g vs' rfl
          · rcases ho.1 with h | h
            · rw [hcf] at h; cases h
            · rw [hcg] at h; cases h
    | .inj a N p, q, s, _, v, hpf, hqf, hs, hs', ho, hp, hq => by
      obtain ⟨hs₀, hq₀⟩ := peelAs_patVal hs' hq
      have hq₀f := ovlFree_peelAs hqf
      have hpf' : c.ovlFree p = true := by simpa [Semantics.ovlFree] using hpf
      obtain ⟨w, hw, rfl⟩ := PatVal.inj_inv hp
      rw [overlap] at ho
      obtain ⟨q₀, he⟩ : ∃ q₀, peelAs q = q₀ := ⟨_, rfl⟩
      rw [he] at ho hs₀ hq₀ hq₀f
      cases q₀ with
      | var => simp at ho
      | dv b l' =>
        have h1 := PatVal.dv_shape hq₀
        have h2 := injNormal_isInj a N w
        rw [h1] at h2; cases h2
      | app g qs =>
        have h1 := PatVal.app_not_inj (ovlFree_app hq₀f).1 hq₀
        rw [injNormal_isInj] at h1; cases h1
      | as t i => exact peelAs_not_as q t i he
      | inj b N' q' =>
        have hq'f : c.ovlFree q' = true := by simpa [Semantics.ovlFree] using hq₀f
        obtain ⟨w', hw', he'⟩ := PatVal.inj_inv hq₀
        obtain ⟨-, hps, rfl⟩ := sortOfTerm_inj.mp hs
        obtain ⟨-, hqs, rfl⟩ := sortOfTerm_inj.mp hs₀
        have hsw := patVal_sortedAll hmc hσ hw hps
        have hsw' := patVal_sortedAll hmc hσ' hw' hqs
        simp only at ho
        by_cases hab : a = b
        · subst hab
          have hN := injNormal_target he'
          subst hN
          have hww := injNormal_inj hmc hsw hsw' he'
          subst hww
          rw [if_pos (beq_self_eq_true a)] at ho
          exact overlap_sound_termF hmc hσ hσ' p hpf' hq'f hps hqs ho hw hw'
        · have hne : (a == b) = false := beq_eq_false_iff_ne.mpr hab
          rw [if_neg (show ¬ (a == b) = true by rw [hne]; exact Bool.false_ne_true)] at ho
          simp only [Bool.and_eq_false_iff, Bool.or_eq_false_iff] at ho
          obtain ⟨hm, hi⟩ := inj_meet hab hsw hsw' he'
          rcases ho with h | ⟨h1, h2⟩
          · rw [hm] at h; cases h
          · rcases hi with hi | hi
            · rw [injable_of_isInj hpf' hw hi] at h1; cases h1
            · rw [injable_of_isInj hq'f hw' hi] at h2; cases h2
  /-- Two lists of well-sorted patterns that `overlapList` finds apart, applying no overloading
  symbol, denote no list of values in common: no argument list is matched by both. -/
  theorem overlap_soundF (hmc : MatchCtxO c) {vars vars' : List Srt} {σ σ' : Subst}
      (hσ : c.WellSorted vars σ) (hσ' : c.WellSorted vars' σ') : ∀ (ps : List Term) {qs : List Term} {ss ss' : List Srt} {vs : List GroundTerm},
      c.ovlFreeList ps = true → c.ovlFreeList qs = true →
      sortsOfTerms c.patCtxNF vars ps = some ss → sortsOfTerms c.patCtxNF vars' qs = some ss' →
      overlapList c.meet c.collHead ps qs = false → PatVals c σ ps vs → PatVals c σ' qs vs → False
    | [], _, _, _, _, _, _, _, _, ho, _, _ => by simp [overlapList] at ho
    | _ :: _, [], _, _, _, _, _, _, _, ho, _, _ => by simp [overlapList] at ho
    | p :: ps, q :: qs, _, _, _, hpf, hqf, hs, hs', ho, hp, hq => by
      obtain ⟨hpf1, hpf2⟩ := ovlFreeList_cons hpf
      obtain ⟨hqf1, hqf2⟩ := ovlFreeList_cons hqf
      obtain ⟨v, vs', rfl, hp1, hp2⟩ := PatVals.cons_inv' hp
      obtain ⟨v', vs'', he, hq1, hq2⟩ := PatVals.cons_inv' hq
      simp only [List.cons.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      obtain ⟨_, _, h1, h2, -⟩ := sortsOfTerms_cons.mp hs
      obtain ⟨_, _, h1', h2', -⟩ := sortsOfTerms_cons.mp hs'
      rw [overlapList] at ho
      cases hpq : overlap c.meet c.collHead p q with
      | false => exact overlap_sound_termF hmc hσ hσ' p hpf1 hqf1 h1 h1' hpq hp1 hq1
      | true =>
        rw [hpq, Bool.true_and] at ho
        exact overlap_soundF hmc hσ hσ' ps hpf2 hqf2 h2 h2' ho hp2 hq2
end

/-- Two well-sorted patterns that `overlap` finds apart denote no value in common (no overloading
symbol: `overlap_sound_termF`). -/
theorem overlap_sound_term (hmc : MatchCtx c) {vars vars' : List Srt} {σ σ' : Subst}
    (hσ : c.WellSorted vars σ) (hσ' : c.WellSorted vars' σ') (p : Term) {q : Term} {s s' : Srt} {v : GroundTerm}
    (hs : sortOfTerm c.patCtxNF vars p = some s) (hs' : sortOfTerm c.patCtxNF vars' q = some s')
    (ho : overlap c.meet c.collHead p q = false) (hp : PatVal c σ p v) (hq : PatVal c σ' q v) : False :=
  overlap_sound_termF hmc hσ hσ' p (ovlFree_of_nil hmc.noOvl p) (ovlFree_of_nil hmc.noOvl q) hs hs' ho hp hq

/-- Two lists of well-sorted patterns that `overlapList` finds apart denote no list of values in
common (no overloading symbol: `overlap_soundF`). -/
theorem overlap_sound (hmc : MatchCtx c) {vars vars' : List Srt} {σ σ' : Subst}
    (hσ : c.WellSorted vars σ) (hσ' : c.WellSorted vars' σ') (ps : List Term) {qs : List Term} {ss ss' : List Srt}
    {vs : List GroundTerm} (hs : sortsOfTerms c.patCtxNF vars ps = some ss)
    (hs' : sortsOfTerms c.patCtxNF vars' qs = some ss') (ho : overlapList c.meet c.collHead ps qs = false)
    (hp : PatVals c σ ps vs) (hq : PatVals c σ' qs vs) : False :=
  overlap_soundF hmc hσ hσ' ps (ovlFreeList_of_nil hmc.noOvl ps) (ovlFreeList_of_nil hmc.noOvl qs) hs hs' ho hp hq

theorem mem_pairs {α : Type} {a b : α} : ∀ {l : List α}, (a, b) ∈ pairs l → a ∈ l ∧ b ∈ l
  | [], h => by simp [pairs] at h
  | x :: l, h => by
    simp only [pairs, List.mem_append, List.mem_map, Prod.mk.injEq] at h
    rcases h with ⟨y, hy, rfl, rfl⟩ | h
    · exact ⟨List.mem_cons_self .., List.mem_cons_of_mem _ hy⟩
    · obtain ⟨h1, h2⟩ := mem_pairs h
      exact ⟨List.mem_cons_of_mem _ h1, List.mem_cons_of_mem _ h2⟩

/-! ## Literals are terms inside their `requires` -/

theorem mem_subterms_app {f : Sym} {ts : List Term} {t : Term} (h : t ∈ ts) : t ∈ subterms (.app f ts) := by
  simp only [subterms, List.mem_cons]
  refine .inr ?_
  induction ts with
  | nil => nomatch h
  | cons u us ih =>
    simp only [subtermsList, List.mem_append]
    rcases List.mem_cons.mp h with rfl | h
    · exact .inl (self_mem_subterms _)
    · exact .inr (ih h)

theorem mem_subterms_of_lits : ∀ {t A : Term} {b : Bool}, (A, b) ∈ lits t → A ∈ subterms t
  | .app f [t₁, t₂], A, b, hm => by
    simp only [lits] at hm
    split at hm
    · rcases List.mem_append.mp hm with hm | hm
      · exact subterms_trans (mem_subterms_app (List.mem_cons_self ..)) (mem_subterms_of_lits hm)
      · exact subterms_trans (mem_subterms_app (by simp)) (mem_subterms_of_lits hm)
    · simp only [List.mem_singleton, Prod.mk.injEq] at hm
      obtain ⟨rfl, rfl⟩ := hm
      exact self_mem_subterms _
  | .app f [t], A, b, hm => by
    simp only [lits] at hm
    split at hm
    · simp only [List.mem_singleton, Prod.mk.injEq] at hm
      obtain ⟨rfl, rfl⟩ := hm
      exact mem_subterms_app (List.mem_cons_self ..)
    · simp only [List.mem_singleton, Prod.mk.injEq] at hm
      obtain ⟨rfl, rfl⟩ := hm
      exact self_mem_subterms _
  | .dv s l, A, b, hm => by
    simp only [lits] at hm
    split at hm
    · nomatch hm
    · simp only [List.mem_singleton, Prod.mk.injEq] at hm
      obtain ⟨rfl, rfl⟩ := hm
      exact self_mem_subterms _
  | .var i, A, b, hm => by
    simp only [lits, List.mem_singleton, Prod.mk.injEq] at hm
    obtain ⟨rfl, rfl⟩ := hm
    exact self_mem_subterms _
  | .inj a b' t, A, b, hm => by
    simp only [lits, List.mem_singleton, Prod.mk.injEq] at hm
    obtain ⟨rfl, rfl⟩ := hm
    exact self_mem_subterms _
  | .as t i, A, b, hm => by
    simp only [lits, List.mem_singleton, Prod.mk.injEq] at hm
    obtain ⟨rfl, rfl⟩ := hm
    exact self_mem_subterms _
  | .app f [], A, b, hm => by
    simp only [lits, List.mem_singleton, Prod.mk.injEq] at hm
    obtain ⟨rfl, rfl⟩ := hm
    exact self_mem_subterms _
  | .app f (_ :: _ :: _ :: _), A, b, hm => by
    simp only [lits, List.mem_singleton, Prod.mk.injEq] at hm
    obtain ⟨rfl, rfl⟩ := hm
    exact self_mem_subterms _
  termination_by t => sizeOf t
  decreasing_by all_goals simp_wf; omega

theorem intBound_mem {A t : Term} {b : Bool} {lo hi : Option Int}
    (h : Semantics.intBound (A, b) = some (t, lo, hi)) : t ∈ subterms A := by
  cases A with
  | app f args =>
    rcases args with _ | ⟨x, _ | ⟨y, _ | ⟨_, _⟩⟩⟩
    all_goals try (simp [Semantics.intBound] at h; done)
    have hx : x ∈ subterms (.app f [x, y]) := mem_subterms_app (List.mem_cons_self ..)
    have hy : y ∈ subterms (.app f [x, y]) := mem_subterms_app (by simp)
    unfold Semantics.intBound at h
    cases hc : Semantics.cmpAsserted f b with
    | none => simp [hc] at h
    | some g =>
      cases hk : Semantics.intLitOf y with
      | some k =>
        simp only [hc, hk, Option.map_eq_some_iff, Prod.mk.injEq] at h
        obtain ⟨_, _, rfl, _⟩ := h
        exact hx
      | none =>
        cases hk' : Semantics.intLitOf x with
        | none => simp [hc, hk, hk'] at h
        | some k =>
          cases hg : Semantics.cmpFlip g with
          | none => simp [hc, hk, hk', hg] at h
          | some g' =>
            simp only [hc, hk, hk', hg, Option.map_eq_some_iff, Prod.mk.injEq] at h
            obtain ⟨_, _, rfl, _⟩ := h
            exact hy
  | _ => simp [Semantics.intBound] at h

/-! ## Exclusive `requires` -/

/-- Two literals `litsApart` accepts are never both asserted under one substitution, where the
terms inside one of them have one result there: each case compares the two at a term inside both. -/
theorem litsApart_sound {heads : List CtorSig} {vs : List Srt} {σ : Subst}
    {A A' : Term} {b b' : Bool} (hc : c.litsApart heads vs (A, b) (A', b') = true)
    (hF : (∀ X ∈ subterms A, Fun c σ X) ∨ ∀ X ∈ subterms A', Fun c σ X)
    (e1 : EvalTerm c σ A (some (bool b))) (e2 : EvalTerm c σ A' (some (bool b'))) : False := by
  have det : ∀ {X : Term}, X ∈ subterms A → X ∈ subterms A' → Fun c σ X := fun h h' =>
    hF.elim (fun hF => hF _ h) (fun hF => hF _ h')
  simp only [Semantics.litsApart, Bool.or_eq_true] at hc
  rcases hc with ((hc | hc) | hc) | hc
  · simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at hc
    obtain ⟨⟨he, hb⟩, -⟩ := hc
    have he := Term.beq_sound he
    subst he
    exact hb (bool_inj (Option.some.inj (det (self_mem_subterms _) (self_mem_subterms _) _ _ e1 e2)))
  · split at hc
    · rename_i x a x' a' hk hk'
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hc
      obtain ⟨⟨⟨⟨hx, -⟩, ha⟩, ha'⟩, hne⟩ := hc
      have hx := Term.beq_sound hx
      subst hx
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (eqKLit_spec hk)
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (eqKLit_spec hk')
      obtain ⟨v, ev1, ea⟩ := kEq_inv e1
      obtain ⟨v', ev2, ea'⟩ := kEq_inv e2
      have hvv := Option.some.inj (det (mem_subterms_app (List.mem_cons_self ..))
        (mem_subterms_app (List.mem_cons_self ..)) _ _ ev1 ev2)
      have hva := Option.some.inj (gval_eval ha ea)
      have hva' := Option.some.inj (gval_eval ha' ea')
      have := gval_inj ha ha' (hva.symm.trans (hvv.trans hva'))
      rw [this] at hne
      cases hne
    · cases hc
  · unfold Semantics.complLits at hc
    split at hc
    · rename_i f t u b₀ g t' u' b₀' heq heq'
      simp only [Prod.mk.injEq] at heq heq'
      obtain ⟨rfl, rfl⟩ := heq
      obtain ⟨rfl, rfl⟩ := heq'
      simp only [Bool.and_eq_true, List.contains_iff_mem, beq_iff_eq] at hc
      obtain ⟨⟨⟨⟨⟨hfg, ht⟩, hu⟩, hb⟩, -⟩, -⟩ := hc
      have ht := Term.beq_sound ht
      have hu := Term.beq_sound hu
      subst ht hu hb
      obtain ⟨P, Q, _, _, hP, hQ, hf, hg, hPQ⟩ := intCompl_cases hfg
      obtain ⟨hsf, hsg⟩ := silentKey_of_intCompl hfg
      obtain ⟨v, w, x, y, ev, ew, hx, hy, hb⟩ := int2_inv hf hP e1 hsf
      obtain ⟨v', w', x', y', ev', ew', hx', hy', hb'⟩ := int2_inv hg hQ e2 hsg
      have hv := Option.some.inj (det (mem_subterms_app (List.mem_cons_self ..))
        (mem_subterms_app (List.mem_cons_self ..)) _ _ ev ev')
      have hw := Option.some.inj (det (mem_subterms_app (by simp)) (mem_subterms_app (by simp)) _ _ ew ew')
      subst hv hw
      rw [hx] at hx'; rw [hy] at hy'
      cases Option.some.inj hx'; cases Option.some.inj hy'
      rw [hb] at hb'
      by_cases hp : P x y
      · have hq : ¬ Q x y := fun hq => (hPQ x y).mp hq hp
        simp [hp, hq] at hb'
      · have hq : Q x y := (hPQ x y).mpr hp
        simp [hp, hq] at hb'
    · cases hc
  · split at hc
    · rename_i x r x' r' hb hb'
      simp only [Bool.and_eq_true] at hc
      obtain ⟨⟨hx, -⟩, hap⟩ := hc
      have hx := Term.beq_sound hx
      subst hx
      obtain ⟨v, X, ev, hX, hr⟩ := intBound_sound hb e1
      obtain ⟨v', X', ev', hX', hr'⟩ := intBound_sound hb' e2
      have hvv := Option.some.inj (det (intBound_mem hb) (intBound_mem hb') _ _ ev ev')
      subst hvv
      rw [hX] at hX'; cases hX'
      exact boundsApart_sound hap hr hr'
    · cases hc

/-- A literal that `litExcluded` accepts against the literals of a `requires` cannot be asserted
when they all are, where the terms inside the literal, or those inside the others, have one
result. -/
theorem litExcluded_sound {heads : List CtorSig} {vs : List Srt} {σ : Subst}
    {ls' : List (Term × Bool)} {A : Term} {b : Bool}
    (hc : c.litExcluded heads vs ls' (A, b) = true)
    (hF : (∀ X ∈ subterms A, Fun c σ X) ∨ ∀ l ∈ ls', ∀ X ∈ subterms l.1, Fun c σ X)
    (e1 : EvalTerm c σ A (some (bool b)))
    (e2 : ∀ l ∈ ls', EvalTerm c σ l.1 (some (bool l.2))) : False := by
  have apart : ∀ {B : Term} {d : Bool}, (∀ X ∈ subterms B, X ∈ subterms A) →
      ls'.any (c.litsApart heads vs (B, d)) = true → EvalTerm c σ B (some (bool d)) → False := by
    intro B d hB h eB
    obtain ⟨⟨A', b'⟩, hm, h⟩ := List.any_eq_true.mp h
    exact litsApart_sound h (hF.elim (fun hF => .inl fun X hX => hF X (hB X hX))
      (fun hF => .inr (hF _ hm))) eB (e2 _ hm)
  unfold Semantics.litExcluded at hc
  split at hc
  · rename_i f A₁ A₂ heq
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    split at hc
    · rename_i hf
      have hf := beq_iff_eq.mp hf
      subst hf
      simp only [Bool.and_eq_true] at hc
      rcases or_inv e1 with h | h
      · exact apart (fun X hX => subterms_trans (mem_subterms_app (List.mem_cons_self ..)) hX) hc.1 h
      · exact apart (fun X hX => subterms_trans (mem_subterms_app (by simp)) hX) hc.2 h
    · exact apart (fun _ h => h) hc e1
  · exact apart (fun _ h => h) hc e1

/-- Two `requires` that `reqsExclusive` accepts are never both `true` under one substitution where
the terms inside one of them have one result. -/
theorem reqsExclusive_sound {heads : List CtorSig} {vs : List Srt} {σ : Subst}
    {q q' : Option Term} (h : c.reqsExclusive heads vs q q' = true)
    (hF : (∀ t, q = some t → HDet c σ t) ∨ ∀ t, q' = some t → HDet c σ t)
    (h1 : ∀ t, q = some t → EvalTerm c σ t (some (bool true)))
    (h2 : ∀ t, q' = some t → EvalTerm c σ t (some (bool true))) : False := by
  cases q with
  | none => simp [Semantics.reqsExclusive] at h
  | some t =>
  cases q' with
  | none => simp [Semantics.reqsExclusive] at h
  | some t' =>
  simp only [Semantics.reqsExclusive, List.any_eq_true] at h
  obtain ⟨⟨A, b⟩, hm, hc⟩ := h
  refine litExcluded_sound hc (hF.elim (fun hF => .inl fun X hX => hF t rfl X
      (subterms_trans (mem_subterms_of_lits hm) hX))
    (fun hF => .inr fun l hl X hX => hF t' rfl X (subterms_trans (mem_subterms_of_lits hl) hX)))
    (lits_sound (h1 t rfl) hm) (fun l hl => lits_sound (h2 t' rfl) hl)

/-- Two clauses that `clausesAgree` accepts are, in either order, the same instance of one
right-hand side: it is one term without variables. -/
theorem clausesAgree_sound {cl cl' : Clause} (h : clausesAgree cl cl' = true) (σ σ' : Subst) :
    (cl.rhs = cl'.rhs ∧ cl.ens = cl'.ens ∧ (∀ i ∈ varOccs cl.rhs, σ.lookup i = σ'.lookup i) ∧
      ∀ t, cl.ens = some t → ∀ i ∈ varOccs t, σ.lookup i = σ'.lookup i) ∧
    (cl'.rhs = cl.rhs ∧ cl'.ens = cl.ens ∧ (∀ i ∈ varOccs cl'.rhs, σ'.lookup i = σ.lookup i) ∧
      ∀ t, cl'.ens = some t → ∀ i ∈ varOccs t, σ'.lookup i = σ.lookup i) := by
  simp only [clausesAgree, Bool.and_eq_true, List.isEmpty_iff, Option.isNone_iff_eq_none] at h
  obtain ⟨⟨⟨hb, hv⟩, he⟩, he'⟩ := h
  have hb := Term.beq_sound hb
  exact ⟨⟨hb, he.trans he'.symm, fun i hi => (by rw [hv] at hi; cases hi),
      fun t ht => (by rw [he] at ht; cases ht)⟩,
    ⟨hb.symm, he'.trans he.symm, fun i hi => (by rw [← hb, hv] at hi; cases hi),
      fun t ht => (by rw [he'] at ht; cases ht)⟩⟩

/-- Two clauses that `clausesExclusive` accepts never both apply at one argument list, where the
terms of one of their `requires` have one result under its match: their matches agree on every
variable (`clauseFixed`), and their `requires` are then exclusive. -/
theorem clausesExclusive_sound (hmc : MatchCtxO c) {heads : List CtorSig} {cl cl' : Clause}
    {ss : List Srt} (hpt : sortsOfTerms c.patCtxNF cl.vars cl.pats = some ss)
    (hfx : c.clauseFixed cl = true) (hrq' : reqOK (c.rhsCtx heads) cl'.vars cl'.req = true)
    (h : c.clausesExclusive heads cl cl' = true) {vs : List GroundTerm} {σ σ' : Subst}
    (hσ : c.WellSorted cl.vars σ) (hm : PatVals c σ cl.pats vs)
    (hq : ∀ t, cl.req = some t → EvalTerm c σ t (some (bool true)))
    (hσ' : c.WellSorted cl'.vars σ') (hm' : PatVals c σ' cl'.pats vs)
    (hq' : ∀ t, cl'.req = some t → EvalTerm c σ' t (some (bool true)))
    (hF : (∀ t, cl.req = some t → HDet c σ t) ∨ ∀ t, cl'.req = some t → HDet c σ' t) : False := by
  simp only [Semantics.clausesExclusive, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨hv, hp⟩, hx⟩ := h
  have hp := Term.beqList_sound hp
  rw [← hv] at hσ' hrq'
  rw [← hp] at hm'
  unfold Semantics.clauseFixed at hfx
  split at hfx
  · rename_i D hD
    simp only [List.all_eq_true, List.contains_iff_mem, List.mem_range] at hfx
    have hag := uniqList_sound hmc hσ' hσ cl.pats hD hm' hm hpt (fun _ h => by cases h)
    -- the second clause's `requires` read under the first's match
    have hagt : ∀ t, cl'.req = some t → ∀ i ∈ varOccs t, σ'.lookup i = σ.lookup i := fun t ht i hi => by
      rw [ht] at hrq'
      exact hag i (hfx i (sortOfTerm_vars (reqOK_some hrq') i hi))
    refine reqsExclusive_sound hx (hF.elim .inl fun hF => .inr fun t ht u hu =>
        Fun.congr (fun i hi => (hagt t ht i (varOccs_subterms hu i hi)).symm) (hF t ht u hu))
      hq (fun t ht => Exec.EvalTerm.congr (hq' t ht) (hagt t ht))
  · cases hfx

/-- **The equations `fnExclusiveOK` accepts agree**: each two of one priority are coherent, in
both orders. Their patterns are apart (`overlap_sound`), or their `requires` exclude each other
(`clausesExclusive_sound`, comparing the two `requires` at terms inside both, which the first
clause's coherence gives one result), or their right-hand sides are one closed term and neither has
an `ensures` (`clausesAgree_sound`). -/
theorem fnExclusiveOK_sound (hmc : MatchCtxO c) {heads : List CtorSig} {f : Fn}
    (hfr : ∀ cl ∈ f.clauses, c.ovlFreeList cl.pats = true)
    (hcls : ∀ cl ∈ f.clauses, c.clauseSorted f heads cl = true)
    (hxs : ∀ cl ∈ f.clauses, cl.exs = []) (h : c.fnExclusiveOK heads f = true) :
    ClausesAgreePlain c f := by
  intro cl cl' hp hprio
  have hpair := List.all_eq_true.mp h _ hp
  obtain ⟨h1, h2⟩ := mem_pairs hp
  have hc1 := hcls cl h1
  have hc2 := hcls cl' h2
  have hw1 : ∀ {σ : Subst}, c.WellSortedAt cl.vars cl.univ σ → c.WellSorted cl.vars σ :=
    (wellSortedAt_univ (hxs cl h1)).mp
  have hw2 : ∀ {σ : Subst}, c.WellSortedAt cl'.vars cl'.univ σ → c.WellSorted cl'.vars σ :=
    (wellSortedAt_univ (hxs cl' h2)).mp
  simp only [Semantics.clauseSorted, Bool.and_eq_true, beq_iff_eq] at hc1 hc2
  replace hc1 := hc1.1
  replace hc2 := hc2.1
  have hn1 := hc1.1.1.1.1.1
  have hn2 := hc2.1.1.1.1.1
  simp only [Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_true, bne_iff_ne, ne_eq] at hpair
  rcases hpair with ((hne | ho) | ⟨hfx, hx⟩) | ha
  · exact (not_compete (by revert hne; simp) hprio).elim
  · exact ⟨fun vs σ σ' ⟨hσ, hm, _⟩ ⟨hσ', hm', _⟩ _ _ _ _ =>
        (overlap_soundF hmc (hw1 hσ) (hw2 hσ') cl.pats (hfr cl h1) (hfr cl' h2) hn1 hn2 ho hm hm').elim,
      fun vs σ' σ ⟨hσ', hm', _⟩ ⟨hσ, hm, _⟩ _ _ _ _ =>
        (overlap_soundF hmc (hw1 hσ) (hw2 hσ') cl.pats (hfr cl h1) (hfr cl' h2) hn1 hn2 ho hm hm').elim⟩
  · exact ⟨fun vs σ σ' ⟨hσ, hm, hq, _⟩ ⟨hσ', hm', hq', _⟩ hd _ _ _ =>
        (clausesExclusive_sound hmc hn1 hfx hc2.1.1.1.2 hx (hw1 hσ) hm hq (hw2 hσ') hm' hq' (.inl hd)).elim,
      fun vs σ' σ ⟨hσ', hm', hq', _⟩ ⟨hσ, hm, hq, _⟩ hd _ _ _ =>
        (clausesExclusive_sound hmc hn1 hfx hc2.1.1.1.2 hx (hw1 hσ) hm hq (hw2 hσ') hm' hq' (.inr hd)).elim⟩
  · exact ⟨fun vs σ σ' _ _ _ _ _ _ => .inl (clausesAgree_sound ha σ σ').1,
      fun vs σ' σ _ _ _ _ _ _ => .inl (clausesAgree_sound ha σ σ').2⟩

/-- In a core that `okM` and `srReady` accept, each function's equations agree: by
`fnExclusiveOK_sound` where `fnExclusiveOK` confirms it, and by the named obligation for the
functions it does not (`agreeObligations`). -/
theorem clausesAgree_of_okM {c : Semantics} (hok : c.okM = true) (hsr : c.srReady = true)
    (hmr : c.matchReady = true)
    (hob : ∀ f ∈ c.agreeObligations, ∀ fn, c.lookupFn f = some fn → ClausesAgree c fn) :
    ∀ fn ∈ c.fns, ClausesAgree c fn := by
  intro fn hfn
  have hsc := sortCtx_of_okM hok hsr (Exec.ovlCase_of hmr)
  by_cases hx : c.fnExclusiveOK (c.fns.map Fn.sig) fn = true
  · have hf := hok
    simp only [Semantics.okM, Bool.and_eq_true, Semantics.fnsOK, List.all_eq_true] at hf
    have hfo := hf.1.1.2 fn hfn
    simp only [Semantics.fnOK, List.all_eq_true] at hfo
    exact (fnExclusiveOK_sound (matchCtx_of hmr) (fun cl _ => ovlFreeList_of_nil (matchCtx_of hmr).noOvl _)
      (fun cl hcl => c.clauseSorted_of_all (c.clauseOKAll_of (hfo cl hcl))
        (c.clauseBound_of_plain (Semantics.noExsTop_of_okAll (Semantics.okAll_of_okM hok))
          (Semantics.preTop_of_okAll (Semantics.okAll_of_okM hok)) hfn hcl)
        (c.clausePreOK_of_plain (Semantics.preTop_of_okAll (Semantics.okAll_of_okM hok)) hfn hcl)
        (noFnOvlInL_of_ovlFree (matchCtx_of hmr) _ (ovlFreeList_of_nil (matchCtx_of hmr).noOvl _)))
      ((clauseCtx_of_okM hok).fnsNoExs fn hfn) hx).agree
      ((clauseCtx_of_okM hok).fnsNoExs fn hfn)
  · refine hob fn.label ?_ fn ?_
    · simp only [Semantics.agreeObligations, List.mem_map, List.mem_filter]
      exact ⟨fn, ⟨hfn, by simpa [(matchCtx_of hmr).noOvl] using hx⟩, rfl⟩
    · rw [Semantics.lookupFn_eq]
      exact find?_label hsc.nodupFns (List.mem_append_left _ hfn)

/-- In a core that `ok` and `srReady` accept, each function's equations agree
(`clausesAgree_of_okM`). -/
theorem clausesAgree_of {c : Semantics} (hok : c.ok = true) (hsr : c.srReady = true)
    (hmr : c.matchReady = true)
    (hob : ∀ f ∈ c.agreeObligations, ∀ fn, c.lookupFn f = some fn → ClausesAgree c fn) :
    ∀ fn ∈ c.fns, ClausesAgree c fn :=
  clausesAgree_of_okM (Semantics.okM_of_ok hok) hsr hmr hob

/-- **Coherence** in a core that `okM`, `srReady` and `matchReady` accept, given the named
obligations: match independence of the clauses `clauseFixed` does not confirm, and agreement of the
functions `fnExclusiveOK` does not. -/
theorem coherentAll_of_okM {c : Semantics} (hok : c.okM = true) (hsr : c.srReady = true)
    (hmr : c.matchReady = true) (hmo : MatchObligations c)
    (hob : ∀ f ∈ c.agreeObligations, ∀ fn, c.lookupFn f = some fn → ClausesAgree c fn) : CoherentAll c :=
  coherentAll_of_parts (matchIndependentAll_of_okM hok hmr hmo) fun f fn hfn => by
    obtain ⟨hmem, -⟩ := lookupFn_spec hfn
    rcases List.mem_append.mp hmem with h | h
    · exact clausesAgree_of_okM hok hsr hmr hob fn h
    · exact sortPreds_agree h

/-- **Coherence** in a core that `ok`, `srReady` and `matchReady` accept, given the named
obligations: match independence of the clauses `clauseFixed` does not confirm, and agreement of the
functions `fnExclusiveOK` does not. -/
theorem coherentAll_of {c : Semantics} (hok : c.ok = true) (hsr : c.srReady = true)
    (hmr : c.matchReady = true) (hmo : MatchObligations c)
    (hob : ∀ f ∈ c.agreeObligations, ∀ fn, c.lookupFn f = some fn → ClausesAgree c fn) : CoherentAll c :=
  coherentAll_of_okM (Semantics.okM_of_ok hok) hsr hmr hmo hob

/-- Coherence where every clause is fixed, given the named agreements, in a core `okM` accepts. -/
theorem coherentAll_of_fixed_okM {c : Semantics} (hok : c.okM = true) (hsr : c.srReady = true)
    (hmr : c.matchReady = true) (hcf : c.clausesFixed = true)
    (hob : ∀ f ∈ c.agreeObligations, ∀ fn, c.lookupFn f = some fn → ClausesAgree c fn) : CoherentAll c :=
  coherentAll_of_okM hok hsr hmr (.of_fixed hcf (matchCtx_of hmr).noOvl) hob

/-- Coherence where every clause is fixed, given the named agreements. -/
theorem coherentAll_of_fixed {c : Semantics} (hok : c.ok = true) (hsr : c.srReady = true)
    (hmr : c.matchReady = true) (hcf : c.clausesFixed = true)
    (hob : ∀ f ∈ c.agreeObligations, ∀ fn, c.lookupFn f = some fn → ClausesAgree c fn) : CoherentAll c :=
  coherentAll_of_fixed_okM (Semantics.okM_of_ok hok) hsr hmr hcf hob

/-- Coherence where every clause is fixed and no agreement is named, in a core `okM` accepts. -/
theorem coherentAll_of_nil_okM {c : Semantics} (hok : c.okM = true) (hsr : c.srReady = true)
    (hmr : c.matchReady = true) (hcf : c.clausesFixed = true) (hag : c.agreeObligations = []) :
    CoherentAll c :=
  coherentAll_of_okM hok hsr hmr (.of_fixed hcf (matchCtx_of hmr).noOvl) fun f hf => by rw [hag] at hf; nomatch hf

/-- Coherence where every clause is fixed and no agreement is named. -/
theorem coherentAll_of_nil {c : Semantics} (hok : c.ok = true) (hsr : c.srReady = true)
    (hmr : c.matchReady = true) (hcf : c.clausesFixed = true) (hag : c.agreeObligations = []) :
    CoherentAll c :=
  coherentAll_of_nil_okM (Semantics.okM_of_ok hok) hsr hmr hcf hag

end KCore.Det
