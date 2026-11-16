/-
  KCore, checked layer: the executable matcher is sound (toward `Exec.step_iff`, Exec.lean).

  `matchP_sound`: every substitution `matchP` returns extends its input, and under it the pattern
  denotes the value (`PatVal`), for a value whose maps are canonical (`canonV`, which every
  well-sorted value satisfies). The map case reads the matcher's flattening of a map pattern
  (`mapParts`): the entries `pickAll` chooses for the `|->` elements and the rest bound to the
  frame make up the map, and `mapParts_sound` rebuilds the `_Map_` tree's denotation from them
  (canonical maps, MapLaws.lean).
-/
import KcoreSpec.MapLaws

set_option autoImplicit false

namespace KCore.Exec

open KCore GroundTerm

variable {c : Semantics}

/-! ## Hooks of the map pattern symbols -/

theorem patternHooks_unit : patternHooks.contains mapUnit = true := rfl
theorem patternHooks_elem : patternHooks.contains mapElem = true := rfl
theorem patternHooks_concat : patternHooks.contains mapConcat = true := rfl

theorem hook_mapUnit : hook mapUnit [] = some (some (.map Srt.map [])) := rfl
theorem hook_mapElem (k v : GroundTerm) : hook mapElem [k, v] = some (some (.map Srt.map [(k, v)])) := rfl
theorem hook_mapConcat (s t : Srt) (a b : Entries) :
    hook mapConcat [.map s a, .map t b] = some ((union a b).map (.map Srt.map)) := rfl

/-! ## The elements and frames of a flattened map pattern -/

/-- Each element `(kp, vp)` denotes the entry at its position. -/
def Matched (c : Semantics) (σ : Subst) : List (Term × Term) → Entries → Prop
  | [], [] => True
  | q :: E, e :: P => (PatVal c σ q.1 e.1 ∧ PatVal c σ q.2 e.2) ∧ Matched c σ E P
  | _, _ => False

/-- Each frame variable holds the canonical map at its position. -/
def Framed (σ : Subst) : List Nat → List Entries → Prop
  | [], [] => True
  | i :: F, M :: Ms => (σ.lookup i = some (.map Srt.map M) ∧ keysSorted M = true) ∧ Framed σ F Ms
  | _, _ => False

theorem Matched.split {σ : Subst} : ∀ {E1 E2 : List (Term × Term)} {P : Entries},
    Matched c σ (E1 ++ E2) P → ∃ P1 P2, P = P1 ++ P2 ∧ Matched c σ E1 P1 ∧ Matched c σ E2 P2
  | [], _, P, h => ⟨[], P, rfl, trivial, h⟩
  | _ :: _, _, [], h => nomatch h
  | q :: E1, E2, e :: P, h => by
    obtain ⟨h1, h2⟩ := h
    obtain ⟨P1, P2, rfl, h3, h4⟩ := Matched.split h2
    exact ⟨e :: P1, P2, rfl, ⟨h1, h3⟩, h4⟩

theorem Matched.mono {σ σ' : Subst} (hx : Ext σ σ') : ∀ {E : List (Term × Term)} {P : Entries},
    Matched c σ E P → Matched c σ' E P
  | [], [], _ => trivial
  | [], _ :: _, h => nomatch h
  | _ :: _, [], h => nomatch h
  | _ :: _, _ :: _, ⟨⟨h1, h2⟩, h3⟩ => ⟨⟨PatVal.mono hx h1, PatVal.mono hx h2⟩, Matched.mono hx h3⟩

theorem Framed.split {σ : Subst} : ∀ {F1 F2 : List Nat} {Ms : List Entries},
    Framed σ (F1 ++ F2) Ms → ∃ M1 M2, Ms = M1 ++ M2 ∧ Framed σ F1 M1 ∧ Framed σ F2 M2
  | [], _, Ms, h => ⟨[], Ms, rfl, trivial, h⟩
  | _ :: _, _, [], h => nomatch h
  | i :: F1, F2, M :: Ms, h => by
    obtain ⟨h1, h2⟩ := h
    obtain ⟨M1, M2, rfl, h3, h4⟩ := Framed.split h2
    exact ⟨M :: M1, M2, rfl, ⟨h1, h3⟩, h4⟩

theorem perm4 {α : Type} (a b c' d : List α) : ((a ++ b) ++ (c' ++ d)).Perm ((a ++ c') ++ (b ++ d)) := by
  simp only [List.append_assoc]
  refine List.Perm.append_left a ?_
  rw [← List.append_assoc, ← List.append_assoc]
  exact List.Perm.append_right d List.perm_append_comm

/-! ## Rebuilding a map pattern's denotation -/

theorem mapParts_sound {σ : Subst} : ∀ (n : Nat) (p : Term) (E : List (Term × Term)) (F : List Nat),
    mapParts n p = some (E, F) → ∀ (P : Entries) (Ms : List Entries),
    Matched c σ E P → Framed σ F Ms → KeysApart (P ++ Ms.flatten) →
    ∀ m, keysSorted m = true → (∀ e, e ∈ m ↔ e ∈ P ++ Ms.flatten) → PatVal c σ p (.map Srt.map m)
  | 0, _, _, _, h, _, _, _, _, _, _, _, _ => by simp [mapParts] at h
  | n + 1, .var i, E, F, h, P, Ms, hE, hF, _, m, hm, hmem => by
    simp only [mapParts, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    match P, Ms, hE, hF with
    | [], [M], _, ⟨⟨hl, hs⟩, _⟩ =>
      have : m = M := entries_canon hm hs (fun e => by simpa using hmem e)
      subst this
      exact .var hl
  | n + 1, .app f [], E, F, h, P, Ms, hE, hF, _, m, _, hmem => by
    simp only [mapParts] at h
    split at h
    · rename_i hf
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      match P, Ms, hE, hF with
      | [], [], _, _ =>
        have : m = [] := List.eq_nil_iff_forall_not_mem.mpr fun e he => by simpa using (hmem e).mp he
        subst this
        rw [beq_iff_eq] at hf
        subst hf
        exact .hook patternHooks_unit .nil hook_mapUnit
    · cases h
  | n + 1, .app f [p, q], E, F, h, P, Ms, hE, hF, hap, m, hm, hmem => by
    simp only [mapParts] at h
    split at h
    · rename_i hf
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      match P, Ms, hE, hF with
      | [e], [], ⟨⟨h1, h2⟩, _⟩, _ =>
        have : m = [e] := entries_canon hm rfl (fun x => by simpa using hmem x)
        subst this
        rw [beq_iff_eq] at hf
        subst hf
        exact .hook patternHooks_elem (.cons h1 (.cons h2 .nil)) (hook_mapElem e.1 e.2)
    · split at h
      · rename_i _ hf
        simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
          Option.some.injEq] at h
        obtain ⟨⟨E1, F1⟩, h1, ⟨E2, F2⟩, h2, he⟩ := h
        simp only [Prod.mk.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        obtain ⟨P1, P2, rfl, hE1, hE2⟩ := Matched.split hE
        obtain ⟨M1, M2, rfl, hF1, hF2⟩ := Framed.split hF
        rw [List.flatten_append] at hap hmem
        have hap' := KeysApart.perm hap (perm4 P1 P2 M1.flatten M2.flatten)
        rw [KeysApart, List.pairwise_append] at hap'
        obtain ⟨ha1, ha2, hcross⟩ := hap'
        obtain ⟨hs1, hm1⟩ := sortE_spec ha1
        obtain ⟨hs2, hm2⟩ := sortE_spec ha2
        have ih1 := mapParts_sound n p E1 F1 h1 P1 M1 hE1 hF1 ha1 _ hs1 hm1
        have ih2 := mapParts_sound n q E2 F2 h2 P2 M2 hE2 hF2 ha2 _ hs2 hm2
        obtain ⟨m', hu, hmem'⟩ := union_exists (sorted_apart hs1)
          (fun e he e' he' => hcross e ((hm1 e).mp he) e' ((hm2 e').mp he'))
        have hsm' := union_sorted hs2 hu
        have : m' = m := entries_canon hsm' hm (fun e => by
          rw [hmem', hm1, hm2, hmem]
          simp only [List.mem_append, or_assoc, or_left_comm])
        subst this
        rw [beq_iff_eq] at hf
        subst hf
        exact .hook patternHooks_concat (.cons ih1 (.cons ih2 .nil)) (by rw [hook_mapConcat, hu]; rfl)
      · cases h
  | n + 1, .app _ [_], _, _, h, _, _, _, _, _, _, _, _ => by simp [mapParts] at h
  | n + 1, .app _ (_ :: _ :: _ :: _), _, _, h, _, _, _, _, _, _, _, _ => by simp [mapParts] at h
  | n + 1, .inj _ _ _, _, _, h, _, _, _, _, _, _, _, _ => by simp [mapParts] at h
  | n + 1, .as _ _, _, _, h, _, _, _, _, _, _, _, _ => by simp [mapParts] at h
  | n + 1, .dv _ _, _, _, h, _, _, _, _, _, _, _, _ => by simp [mapParts] at h

theorem pick_spec {es : Entries} {j : Nat} {e : GroundTerm × GroundTerm} {rest : Entries}
    (h : pick es j = some (e, rest)) : (e :: rest).Perm es ∧ rest.Sublist es := by
  simp only [pick, Option.map_eq_some_iff, Prod.mk.injEq] at h
  obtain ⟨e', he', rfl, rfl⟩ := h
  obtain ⟨hj, rfl⟩ := List.getElem?_eq_some_iff.mp he'
  refine ⟨?_, List.eraseIdx_sublist _ _⟩
  rw [List.eraseIdx_eq_take_drop_succ]
  conv => rhs; rw [← List.take_append_drop j es, List.drop_eq_getElem_cons hj]
  exact List.perm_middle.symm

/-! ## Soundness -/

set_option maxHeartbeats 800000 in
mutual
  theorem matchP_sound : ∀ (n : Nat) {σ σ' : Subst} {p : Term} {v : GroundTerm},
      canonV v = true → σ' ∈ matchP c n σ p v → Ext σ σ' ∧ PatVal c σ' p v
    | 0, _, _, _, _, _, h => by simp [matchP] at h
    | n + 1, σ, σ', .var i, v, _, h => by
      simp only [matchP, Option.mem_toList] at h
      obtain ⟨hx, hl⟩ := bindVar_ext h
      exact ⟨hx, .var hl⟩
    | n + 1, σ, σ', .dv s l, v, _, h => by
      cases v with
      | dv s' l' =>
        simp only [matchP] at h
        split at h
        · rename_i hc
          simp only [List.mem_singleton] at h
          subst h
          simp only [Bool.and_eq_true, beq_iff_eq] at hc
          obtain ⟨rfl, rfl⟩ := hc
          exact ⟨Ext.refl _, .dv⟩
        · simp at h
      | _ => simp [matchP] at h
    | n + 1, σ, σ', .inj a b p, v, hv, h => by
      cases v with
      | inj x b' u =>
        simp only [canonV, Bool.and_eq_true, Bool.not_eq_true'] at hv
        obtain ⟨hni, hu⟩ := hv
        simp only [matchP] at h
        split at h
        · rename_i hb
          rw [beq_iff_eq] at hb
          subst hb
          split at h
          · rename_i hx
            rw [beq_iff_eq] at hx
            subst hx
            obtain ⟨he, hp⟩ := matchP_sound n hu h
            have : injNormal x b u = .inj x b u := by
              cases u <;> simp_all [injNormal, GroundTerm.isInj]
            exact ⟨he, this ▸ .inj hp⟩
          · have hu' : canonV (.inj x a u) = true := by simp [canonV, hni, hu]
            obtain ⟨he, hp⟩ := matchP_sound n hu' h
            exact ⟨he, .inj (w := .inj x a u) hp⟩
        · simp at h
      | _ => simp [matchP] at h
    | n + 1, σ, σ', .as p i, v, hv, h => by
      simp only [matchP, List.mem_filterMap] at h
      obtain ⟨σ1, h1, hb⟩ := h
      obtain ⟨he1, hp1⟩ := matchP_sound n hv h1
      obtain ⟨he2, hl⟩ := bindVar_ext hb
      exact ⟨he1.trans he2, .as (PatVal.mono he2 hp1) hl⟩
    | n + 1, σ, σ', .app f ps, v, hv, h => by
      simp only [matchP] at h
      split at h
      · rename_i hc
        cases v with
        | ctor g vs =>
          simp only at h
          split at h
          · rename_i hg
            rw [beq_iff_eq] at hg
            subst hg
            simp only [canonV] at hv
            obtain ⟨he, hs⟩ := matchL_sound n hv h
            exact ⟨he, .ctor hc hs⟩
          · simp at h
        | _ => simp at h
      · split at h
        · rename_i _ hp
          split at h
          · rename_i s0 es E F hmp
            by_cases hs0 : (s0 == Srt.map) = true
            · rw [if_pos hs0] at h
              rw [beq_iff_eq] at hs0
              subst hs0
              simp only [canonV, Bool.and_eq_true] at hv
              obtain ⟨hes, hce⟩ := hv
              simp only [List.mem_flatMap] at h
              obtain ⟨⟨σ1, rest⟩, hpa, hfr⟩ := h
              obtain ⟨he1, P, hM, hperm, hsub⟩ := pickAll_sound n (canonEs_mem hce) hpa
              have hrs : keysSorted rest = true := sorted_sublist hsub hes
              have hapart : KeysApart (P ++ rest) := KeysApart.perm (sorted_apart hes) hperm.symm
              have hmemP : ∀ e, e ∈ es ↔ e ∈ P ++ rest := fun e => (hperm.mem_iff).symm
              rcases F with _ | ⟨i, _ | ⟨_, _⟩⟩
              · by_cases hre : rest.isEmpty = true
                · simp only [hre, ↓reduceIte, List.mem_singleton] at hfr
                  subst hfr
                  have hr : rest = [] := List.isEmpty_iff.mp hre
                  subst hr
                  exact ⟨he1, mapParts_sound (n + 1) (.app f ps) E [] hmp P [] hM trivial
                    (by simpa using hapart) es hes (fun e => by simpa using hmemP e)⟩
                · simp [hre] at hfr
              · simp only [Option.mem_toList] at hfr
                obtain ⟨he2, hl⟩ := bindVar_ext hfr
                exact ⟨he1.trans he2, mapParts_sound (n + 1) (.app f ps) E [i] hmp P [rest]
                  (Matched.mono he2 hM) ⟨⟨hl, hrs⟩, trivial⟩ (by simpa using hapart) es hes
                  (fun e => by simpa using hmemP e)⟩
              · simp at hfr
            · rw [if_neg hs0] at h; simp at h
          · simp at h
        · simp at h
  theorem matchL_sound : ∀ (n : Nat) {σ σ' : Subst} {ps : List Term} {vs : List GroundTerm},
      canonVs vs = true → σ' ∈ matchL c n σ ps vs → Ext σ σ' ∧ PatVals c σ' ps vs
    | 0, _, _, _, _, _, h => by simp [matchL] at h
    | n + 1, σ, σ', [], [], _, h => by
      simp only [matchL, List.mem_singleton] at h
      subst h
      exact ⟨Ext.refl _, .nil⟩
    | n + 1, σ, σ', p :: ps, v :: vs, hv, h => by
      simp only [canonVs, Bool.and_eq_true] at hv
      simp only [matchL, List.mem_flatMap] at h
      obtain ⟨σ1, h1, h2⟩ := h
      obtain ⟨he1, hp⟩ := matchP_sound n hv.1 h1
      obtain ⟨he2, hps⟩ := matchL_sound n hv.2 h2
      exact ⟨he1.trans he2, .cons (PatVal.mono he2 hp) hps⟩
    | n + 1, _, _, [], _ :: _, _, h => by simp [matchL] at h
    | n + 1, _, _, _ :: _, [], _, h => by simp [matchL] at h
  theorem pickAll_sound : ∀ (n : Nat) {σ σ' : Subst} {E : List (Term × Term)} {es rest : Entries},
      (∀ e ∈ es, canonV e.1 = true ∧ canonV e.2 = true) → (σ', rest) ∈ pickAll c n σ E es →
      Ext σ σ' ∧ ∃ P, Matched c σ' E P ∧ (P ++ rest).Perm es ∧ rest.Sublist es
    | 0, _, _, _, _, _, _, h => by simp [pickAll] at h
    | n + 1, σ, σ', [], es, rest, _, h => by
      simp only [pickAll, List.mem_singleton, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨Ext.refl _, [], trivial, List.Perm.refl _, List.Sublist.refl _⟩
    | n + 1, σ, σ', (kp, vp) :: E, es, rest, hc, h => by
      simp only [pickAll, List.mem_flatMap] at h
      obtain ⟨j, _, h⟩ := h
      split at h
      · rename_i k v rest0 hpk
        obtain ⟨hperm0, hsub0⟩ := pick_spec hpk
        have hkv : (k, v) ∈ es := hperm0.mem_iff.mp (List.mem_cons_self ..)
        obtain ⟨hck, hcv⟩ := hc _ hkv
        have hc0 : ∀ e ∈ rest0, canonV e.1 = true ∧ canonV e.2 = true :=
          fun e he => hc e (hsub0.subset he)
        simp only [List.mem_flatMap] at h
        obtain ⟨σ1, h1, σ2, h2, h3⟩ := h
        obtain ⟨he1, hp1⟩ := matchP_sound n hck h1
        obtain ⟨he2, hp2⟩ := matchP_sound n hcv h2
        obtain ⟨he3, P, hM, hperm, hsub⟩ := pickAll_sound n hc0 h3
        refine ⟨he1.trans (he2.trans he3), (k, v) :: P,
          ⟨⟨PatVal.mono (he2.trans he3) hp1, PatVal.mono he3 hp2⟩, hM⟩, ?_, hsub.trans hsub0⟩
        exact (List.Perm.cons _ hperm).trans hperm0
      · simp at h
end

end KCore.Exec
