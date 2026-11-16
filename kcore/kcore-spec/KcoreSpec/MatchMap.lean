/-
  KCore, checked layer: the executable matcher is complete on rule patterns, map patterns included
  (toward `Exec.step_iff`, Exec.lean).

  A map pattern with at most one frame (`noMapIn`, checked by `wf`) denotes a canonical map; the
  map splits into the entries its `|->` elements denote and the frame's map, all keys apart
  (`mapDecomp`). `pickAll` finds those entries (`pickAll_complete`), the rest is the frame's map
  (one canonical form, `entries_canon`), and `matchP_complete` follows.
-/
import KcoreSpec.MatchComplete

set_option autoImplicit false

namespace KCore.Exec

open KCore GroundTerm

variable {c : Semantics}

/-! ## The map pattern symbols as values -/

theorem hook_unit_eq (vs : List GroundTerm) :
    hook mapUnit vs = some (match vs with | [] => some (.map Srt.map []) | _ => none) := rfl
theorem hook_elem_eq (vs : List GroundTerm) :
    hook mapElem vs = some (match vs with | [k, w] => some (.map Srt.map [(k, w)]) | _ => none) := rfl
theorem hook_concat_eq (vs : List GroundTerm) :
    hook mapConcat vs = some (match vs with | [.map _ a, .map _ b] => (union a b).map (.map Srt.map) | _ => none) := rfl

theorem hook_unit_inv {vs : List GroundTerm} {v : GroundTerm} (h : hook mapUnit vs = some (some v)) :
    vs = [] ∧ v = .map Srt.map [] := by
  rw [hook_unit_eq] at h
  cases vs <;> simp_all

theorem hook_elem_inv {vs : List GroundTerm} {v : GroundTerm} (h : hook mapElem vs = some (some v)) :
    ∃ k w, vs = [k, w] ∧ v = .map Srt.map [(k, w)] := by
  rw [hook_elem_eq] at h
  match vs, h with
  | [k, w], h => exact ⟨k, w, rfl, by simpa using h.symm⟩

theorem hook_concat_inv {vs : List GroundTerm} {v : GroundTerm} (h : hook mapConcat vs = some (some v)) :
    ∃ s t a b m, vs = [.map s a, .map t b] ∧ union a b = some m ∧ v = .map Srt.map m := by
  rw [hook_concat_eq] at h
  match vs, h with
  | [.map s a, .map t b], h =>
    simp only [Option.some.injEq, Option.map_eq_some_iff] at h
    obtain ⟨m, hm, rfl⟩ := h
    exact ⟨s, t, a, b, m, rfl, hm, rfl⟩

theorem patternHooks_cases {f : Sym} (h : patternHooks.contains f = true) :
    f = mapUnit ∨ f = mapElem ∨ f = mapConcat := by
  have := List.contains_iff_mem.mp h
  simpa [patternHooks] using this

theorem patternHook_result {f : Sym} {k : CtorSig} (h : patternHooks.contains f = true)
    (hk : lookupSig hookSigs f = some k) : k.result = Srt.map := by
  rcases patternHooks_cases h with rfl | rfl | rfl
  · rw [show lookupSig hookSigs mapUnit = some ⟨mapUnit, [], Srt.map⟩ by decide] at hk; cases hk; rfl
  · rw [show lookupSig hookSigs mapElem = some ⟨mapElem, [Srt.kitem, Srt.kitem], Srt.map⟩ by decide] at hk
    cases hk; rfl
  · rw [show lookupSig hookSigs mapConcat = some ⟨mapConcat, [Srt.map, Srt.map], Srt.map⟩ by decide] at hk
    cases hk; rfl

/-- A map pattern symbol's value is a map. -/
theorem patternHook_map {f : Sym} {vs : List GroundTerm} {v : GroundTerm}
    (h : patternHooks.contains f = true) (hv : hook f vs = some (some v)) : ∃ es, v = .map Srt.map es := by
  rcases patternHooks_cases h with rfl | rfl | rfl
  · exact ⟨[], (hook_unit_inv hv).2⟩
  · obtain ⟨k, w, _, rfl⟩ := hook_elem_inv hv; exact ⟨_, rfl⟩
  · obtain ⟨_, _, _, _, m, _, _, rfl⟩ := hook_concat_inv hv; exact ⟨m, rfl⟩

theorem hook_listUnit_eq (vs : List GroundTerm) :
    hook listUnit vs = some (match vs with | [] => some (.list Srt.list []) | _ => none) := by
  cases vs <;> rfl
theorem hook_listElem_eq (vs : List GroundTerm) :
    hook listElem vs = some (match vs with | [k] => some (.list Srt.list [k]) | _ => none) := by
  match vs with
  | [] => rfl
  | [_] => rfl
  | _ :: _ :: _ => rfl
theorem hook_listConcat_eq (vs : List GroundTerm) :
    hook listConcat vs = some (match vs with
      | [.list _ a, .list _ b] => some (.list Srt.list (a ++ b)) | _ => none) := by
  match vs with
  | [] => rfl
  | [_] => rfl
  | [a, b] => cases a <;> cases b <;> rfl
  | _ :: _ :: _ :: _ => rfl

/-- A list pattern symbol's value is a list. -/
theorem listHook_list {f : Sym} {vs : List GroundTerm} {v : GroundTerm}
    (h : listPatternHooks.contains f = true) (hv : hook f vs = some (some v)) :
    ∃ es, v = .list Srt.list es := by
  have : f = listUnit ∨ f = listElem ∨ f = listConcat := by
    simpa [listPatternHooks] using List.contains_iff_mem.mp h
  rcases this with rfl | rfl | rfl
  · rw [hook_listUnit_eq] at hv; split at hv <;> (first | (cases hv; exact ⟨_, rfl⟩) | cases hv)
  · rw [hook_listElem_eq] at hv; split at hv <;> (first | (cases hv; exact ⟨_, rfl⟩) | cases hv)
  · rw [hook_listConcat_eq] at hv; split at hv <;> (first | (cases hv; exact ⟨_, rfl⟩) | cases hv)

theorem hook_setUnit_eq (vs : List GroundTerm) :
    hook setUnit vs = some (match vs with | [] => some (.set Srt.set []) | _ => none) := by
  cases vs <;> rfl

theorem hook_setElem_eq (vs : List GroundTerm) :
    hook setElem vs = some (match vs with | [k] => some (.set Srt.set [k]) | _ => none) := by
  match vs with
  | [] => rfl
  | [_] => rfl
  | _ :: _ :: _ => rfl

/-- The set's element's value is a set. -/
theorem setElem_set {vs : List GroundTerm} {v : GroundTerm} (hv : hook setElem vs = some (some v)) :
    ∃ es, v = .set Srt.set es := by
  rw [hook_setElem_eq] at hv; split at hv <;> (first | (cases hv; exact ⟨_, rfl⟩) | cases hv)

theorem hook_setConcat_eq (vs : List GroundTerm) :
    hook setConcat vs = some (match vs with | [.set _ a, .set _ b] => (concatS a b).map (.set Srt.set) | _ => none) := by
  match vs with
  | [] => rfl
  | [_] => rfl
  | [a, b] => cases a <;> cases b <;> rfl
  | _ :: _ :: _ :: _ => rfl

/-- The set's concatenation's value is a set. -/
theorem setConcat_set {vs : List GroundTerm} {v : GroundTerm} (hv : hook setConcat vs = some (some v)) :
    ∃ es, v = .set Srt.set es := by
  rw [hook_setConcat_eq] at hv
  split at hv
  · obtain ⟨u, -, rfl⟩ := Option.map_eq_some_iff.mp (Option.some.inj hv); exact ⟨_, rfl⟩
  · cases hv

/-- A set pattern symbol's value is a set. -/
theorem setHook_set {f : Sym} {vs : List GroundTerm} {v : GroundTerm}
    (h : f = setUnit ∨ f = setElem ∨ f = setConcat) (hv : hook f vs = some (some v)) :
    ∃ es, v = .set Srt.set es := by
  rcases h with rfl | rfl | rfl
  · rw [hook_setUnit_eq] at hv; split at hv <;> (first | (cases hv; exact ⟨_, rfl⟩) | cases hv)
  · exact setElem_set hv
  · exact setConcat_set hv

/-- A collection pattern hook's value is a list, or (the set's) a set. -/
theorem collHook_shape {f : Sym} {vs : List GroundTerm} {v : GroundTerm}
    (h : collPatternHooks.contains f = true) (hv : hook f vs = some (some v)) :
    (∃ es, v = .list Srt.list es) ∨ (∃ es, v = .set Srt.set es) := by
  by_cases hs : f = setUnit ∨ f = setElem ∨ f = setConcat
  · exact .inr (setHook_set hs hv)
  · have hl : listPatternHooks.contains f = true := by
      simp only [collPatternHooks, List.contains_cons, Bool.or_eq_true, beq_iff_eq] at h
      rcases h with h | h | h | h
      · exact absurd (.inl h) hs
      · exact absurd (.inr (.inl h)) hs
      · exact absurd (.inr (.inr h)) hs
      · exact h
    exact .inl (listHook_list hl hv)

/-- A collection pattern symbol's value is a map, a list or a set (of some collection sort). -/
theorem collVal_shape {f : Sym} {vs : List GroundTerm} {v : GroundTerm}
    (hp : c.isCollPat f = true) (hv : c.collVal f vs = some v) :
    (∃ s es, v = .map s es) ∨ (∃ s es, v = .list s es) ∨ (∃ s es, v = .set s es) := by
  unfold Semantics.isCollPat at hp
  unfold Semantics.collVal at hv
  simp only [Bool.and_eq_true] at hp
  by_cases hh : isHook f = true
  · rw [if_pos hh] at hv hp
    cases hr : hook f vs with
    | none => rw [hr] at hv; cases hv
    | some r =>
      rw [hr] at hv
      rcases collHook_shape hp.2 (by rw [hr, show r = some v from hv]) with ⟨es, rfl⟩ | ⟨es, rfl⟩
      · exact .inr (.inl ⟨_, _, rfl⟩)
      · exact .inr (.inr ⟨_, _, rfl⟩)
  · rw [if_neg hh] at hv hp
    unfold Semantics.paramVal at hv
    cases hk : c.lookupParam f with
    | none => rw [hk] at hp; simp at hp
    | some k =>
      rw [hk] at hv hp
      simp only at hp hv
      cases hi : k.impl with
      | none => rw [hi] at hp; simp at hp
      | some g =>
        rw [hi] at hp hv
        simp only at hp hv
        have hw := (Option.filter_eq_some_iff.mp hv).1
        obtain ⟨u, hu, rfl⟩ := Option.map_eq_some_iff.mp hw
        have hsg : silentKey g = false := by
          cases hpg : patternHooks.contains g
          · rw [hpg] at hp; exact silentKey_of_collPatternHook (by simpa using hp.2)
          · exact silentKey_of_patternHook hpg
        rw [Semantics.hookRes_of_notKey hsg] at hu
        cases hr : hook g (c.libArgs g vs) with
        | none => rw [hr] at hu; cases hu
        | some r =>
          rw [hr] at hu
          have hgu : hook g (c.libArgs g vs) = some (some u) := by rw [hr, show r = some u from hu]
          cases hpg : patternHooks.contains g with
          | true =>
            obtain ⟨es, rfl⟩ := patternHook_map hpg hgu
            exact .inl ⟨_, _, rfl⟩
          | false =>
            rw [hpg] at hp
            rcases collHook_shape (by simpa using hp.2) hgu with ⟨es, rfl⟩ | ⟨es, rfl⟩
            · exact .inr (.inl ⟨_, _, rfl⟩)
            · exact .inr (.inr ⟨_, _, rfl⟩)

theorem hookPat_inv (hc : MatchCtx c) {τ : Subst} {f : Sym} {ps : List Term} {v : GroundTerm}
    (hf : patternHooks.contains f = true) (h : PatVal c τ (.app f ps) v) :
    ∃ vs, PatVals c τ ps vs ∧ hook f vs = some (some v) := by
  generalize ht : Term.app f ps = t at h
  cases h with
  | ctor hk _ =>
    cases ht
    rw [hc.patHooks f (List.contains_iff_mem.mp hf)] at hk; cases hk
  | hook _ hs hv => cases ht; exact ⟨_, hs, hv⟩
  | coll _ hp _ _ => cases ht; rw [Semantics.isCollPat_of_hook c hf] at hp; cases hp
  | ovl _ ho _ _ => cases ht; rw [c.isOvl_of_patternHook hf] at ho; cases ho
  | _ => cases ht

theorem patCtx_sig (hc : MatchCtx c) {vars : List Srt} {f : Sym} {ps : List Term} {s : Srt}
    (hf : patternHooks.contains f = true) (ht : sortOfTerm c.patCtx vars (.app f ps) = some s) :
    ∃ k, lookupSig hookSigs f = some k ∧ sortsOfTerms c.patCtx vars ps = some k.args ∧ s = k.result := by
  obtain ⟨k, hk', hargs, rfl⟩ := sortOfTerm_app.mp ht
  exact ⟨k, patCtx_hook_lookup hc hf hk', hargs, rfl⟩

theorem sig_unit : lookupSig hookSigs mapUnit = some ⟨mapUnit, [], Srt.map⟩ := by decide
theorem sig_elem : lookupSig hookSigs mapElem = some ⟨mapElem, [Srt.kitem, Srt.kitem], Srt.map⟩ := by decide
theorem sig_concat : lookupSig hookSigs mapConcat = some ⟨mapConcat, [Srt.map, Srt.map], Srt.map⟩ := by decide

/-! ## Splitting a map pattern's denotation -/

/-- The total size of the elements' patterns. -/
def elemsSize : List (Term × Term) → Nat
  | [] => 0
  | q :: E => termSize q.1 + termSize q.2 + elemsSize E

theorem elemsSize_append : ∀ (E1 E2 : List (Term × Term)), elemsSize (E1 ++ E2) = elemsSize E1 + elemsSize E2
  | [], _ => by simp [elemsSize]
  | q :: E1, E2 => by simp [elemsSize, elemsSize_append E1 E2]; omega

theorem Matched.append {τ : Subst} : ∀ {E1 E2 : List (Term × Term)} {P1 P2 : Entries},
    Matched c τ E1 P1 → Matched c τ E2 P2 → Matched c τ (E1 ++ E2) (P1 ++ P2)
  | [], _, [], _, _, h2 => h2
  | _ :: _, _, _ :: _, _, ⟨h, h1⟩, h2 => ⟨h, Matched.append h1 h2⟩
  | [], _, _ :: _, _, h, _ => nomatch h
  | _ :: _, _, [], _, h, _ => nomatch h

theorem Framed.append {τ : Subst} : ∀ {F1 F2 : List Nat} {M1 M2 : List Entries},
    Framed τ F1 M1 → Framed τ F2 M2 → Framed τ (F1 ++ F2) (M1 ++ M2)
  | [], _, [], _, _, h2 => h2
  | _ :: _, _, _ :: _, _, ⟨h, h1⟩, h2 => ⟨h, Framed.append h1 h2⟩
  | [], _, _ :: _, _, h, _ => nomatch h
  | _ :: _, _, [], _, h, _ => nomatch h

theorem Framed.length {τ : Subst} : ∀ {F : List Nat} {Ms : List Entries}, Framed τ F Ms → Ms.length = F.length
  | [], [], _ => rfl
  | _ :: _, _ :: _, ⟨_, h⟩ => by simp [Framed.length h]
  | [], _ :: _, h => nomatch h
  | _ :: _, [], h => nomatch h

theorem Matched.mem {τ : Subst} : ∀ {E : List (Term × Term)} {P : Entries} {q : Term × Term},
    Matched c τ E P → q ∈ E → ∃ e ∈ P, PatVal c τ q.1 e.1 ∧ PatVal c τ q.2 e.2
  | [], [], _, _, h => nomatch h
  | q' :: E, e :: P, q, ⟨h, h'⟩, hq => by
    rcases List.mem_cons.mp hq with rfl | hq
    · exact ⟨e, List.mem_cons_self .., h⟩
    · obtain ⟨e', he', h''⟩ := Matched.mem h' hq
      exact ⟨e', List.mem_cons_of_mem _ he', h''⟩
  | [], _ :: _, _, h, _ => nomatch h
  | _ :: _, [], _, h, _ => nomatch h

/-- What the elements of a map pattern must satisfy for the matcher. -/
abbrev ElemsOK (c : Semantics) (vars : List Srt) (E : List (Term × Term)) : Prop :=
  ∀ q ∈ E, noMapIn q.1 = true ∧ noMapIn q.2 = true ∧
    sortOfTerm c.patCtx vars q.1 = some Srt.kitem ∧ sortOfTerm c.patCtx vars q.2 = some Srt.kitem

theorem mapDecomp (hc : MatchCtx c) {τ : Subst} {vars : List Srt} (hτ : c.WellSorted vars τ) :
    ∀ (p : Term) (k : Nat) (m : Entries) (N : Nat), mapFrames p = some k → termSize p ≤ N →
    PatVal c τ p (.map Srt.map m) → sortOfTerm c.patCtx vars p = some Srt.map → KeysApart m →
    ∃ E F, mapParts N p = some (E, F) ∧ F.length = k ∧ ElemsOK c vars E ∧
      elemsSize E < termSize p ∧
      (∀ i ∈ varOccs p, i ∈ F ∨ ∃ q ∈ E, i ∈ varOccs q.1 ∨ i ∈ varOccs q.2) ∧
      ∃ P Ms, Matched c τ E P ∧ Framed τ F Ms ∧ KeysApart (P ++ Ms.flatten) ∧
        (∀ e, e ∈ m ↔ e ∈ P ++ Ms.flatten)
  | .var i, k, m, N, hk, hN, hp, ht, hap => by
    simp only [mapFrames, Option.some.injEq] at hk
    subst hk
    have hl := PatVal.var_inv hp
    obtain ⟨w, hw, hsw⟩ := hτ i Srt.map (sortOfTerm_var.mp ht)
    rw [hl] at hw; cases hw
    have hs : keysSorted m = true := (sortOf_Map.mp hsw).1
    obtain ⟨N', rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by simp [termSize] at hN; omega⟩
    refine ⟨[], [i], by simp [mapParts], rfl, (fun q hq => nomatch hq), by simp [elemsSize, termSize],
      fun j hj => Or.inl (by simpa [varOccs] using hj), [], [m], trivial, ⟨⟨hl, hs⟩, trivial⟩,
      by simpa using hap, fun e => by simp⟩
  | .app f [], k, m, N, hk, hN, hp, ht, hap => by
    simp only [mapFrames, mapFramesApp] at hk
    split at hk
    · rename_i hf
      rw [beq_iff_eq] at hf
      subst hf
      simp only [Option.some.injEq] at hk
      subst hk
      obtain ⟨vs, _, hv⟩ := hookPat_inv hc patternHooks_unit hp
      obtain ⟨rfl, hm⟩ := hook_unit_inv hv
      cases hm
      obtain ⟨N', rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by simp [termSize] at hN; omega⟩
      refine ⟨[], [], by simp [mapParts], rfl, (fun q hq => nomatch hq), by simp [elemsSize, termSize],
        fun j hj => by simp [varOccs, varOccsList] at hj, [], [], trivial, trivial, List.Pairwise.nil,
        fun e => by simp⟩
    · cases hk
  | .app f [a, b], k, m, N, hk, hN, hp, ht, hap => by
    simp only [mapFrames, mapFramesApp] at hk
    obtain ⟨N', rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by simp [termSize, termSizeList] at hN; omega⟩
    have hsz : termSize a + termSize b + 1 = termSize (.app f [a, b]) := by
      simp [termSize, termSizeList] <;> omega
    split at hk
    · -- `_Map_`
      rename_i hf
      rw [beq_iff_eq] at hf
      subst hf
      have hne : (mapConcat == mapElem) = false := by decide
      cases ha : mapFrames a with
      | none => rw [ha] at hk; cases hk
      | some k1 =>
        cases hb : mapFrames b with
        | none => rw [ha, hb] at hk; cases hk
        | some k2 =>
          rw [ha, hb] at hk
          simp only [Option.some.injEq] at hk
          subst hk
          obtain ⟨vs, hvs, hv⟩ := hookPat_inv hc patternHooks_concat hp
          obtain ⟨_, _, ma, mb, m', rfl, hu, hm⟩ := hook_concat_inv hv
          cases hm
          obtain ⟨va, vs', he1, hpa, hps⟩ := PatVals.cons_inv hvs
          simp only [List.cons.injEq] at he1
          obtain ⟨rfl, rfl⟩ := he1
          obtain ⟨vb, vs'', he2, hpb, _⟩ := PatVals.cons_inv hps
          simp only [List.cons.injEq] at he2
          obtain ⟨rfl, rfl⟩ := he2
          obtain ⟨ksig, hksig, hargs, _⟩ := patCtx_sig hc patternHooks_concat ht
          rw [sig_concat] at hksig
          cases hksig
          obtain ⟨s1, ss1, hta, htb', he⟩ := sortsOfTerms_cons.mp hargs
          simp only [List.cons.injEq] at he
          obtain ⟨rfl, rfl⟩ := he
          obtain ⟨s2, ss2, htb, _, he'⟩ := sortsOfTerms_cons.mp htb'
          simp only [List.cons.injEq] at he'
          obtain ⟨rfl, rfl⟩ := he'
          have hsa := sortOf_map (patVal_sorted hc hτ hpa hta)
          have hsb := sortOf_map (patVal_sorted hc hτ hpb htb)
          subst hsa; subst hsb
          obtain ⟨hmem, hsub, hapa, hcross⟩ := union_spec hu
          have hapb : KeysApart mb := List.Pairwise.sublist hsub hap
          obtain ⟨E1, F1, h1, hl1, hok1, hs1, hc1, P1, M1, hM1, hF1, hap1, hm1⟩ :=
            mapDecomp hc hτ a k1 ma N' ha (by omega) hpa hta hapa
          obtain ⟨E2, F2, h2, hl2, hok2, hs2, hc2, P2, M2, hM2, hF2, hap2, hm2⟩ :=
            mapDecomp hc hτ b k2 mb N' hb (by omega) hpb htb hapb
          refine ⟨E1 ++ E2, F1 ++ F2, ?_, by simp [hl1, hl2], ?_, ?_, ?_, P1 ++ P2, M1 ++ M2,
            Matched.append hM1 hM2, Framed.append hF1 hF2, ?_, ?_⟩
          · simp [mapParts, hne, h1, h2]
          · intro q hq
            rcases List.mem_append.mp hq with hq | hq
            · exact hok1 q hq
            · exact hok2 q hq
          · rw [elemsSize_append]; omega
          · intro i hi
            simp only [varOccs, varOccsList, List.append_nil, List.mem_append] at hi
            rcases hi with hi | hi
            · rcases hc1 i hi with hi | ⟨q, hq, hq'⟩
              · exact Or.inl (List.mem_append_left _ hi)
              · exact Or.inr ⟨q, List.mem_append_left _ hq, hq'⟩
            · rcases hc2 i hi with hi | ⟨q, hq, hq'⟩
              · exact Or.inl (List.mem_append_right _ hi)
              · exact Or.inr ⟨q, List.mem_append_right _ hq, hq'⟩
          · rw [List.flatten_append]
            refine KeysApart.perm ?_ (perm4 P1 M1.flatten P2 M2.flatten)
            rw [KeysApart, List.pairwise_append]
            refine ⟨hap1, hap2, fun e he e' he' => ?_⟩
            exact hcross e ((hm1 e).mpr he) e' ((hm2 e').mpr he')
          · intro e
            rw [hmem, hm1, hm2, List.flatten_append]
            simp only [List.mem_append, or_assoc, or_left_comm]
    · split at hk
      · -- `|->`
        rename_i _ hf
        rw [beq_iff_eq] at hf
        subst hf
        split at hk
        · rename_i hnm
          simp only [Bool.and_eq_true] at hnm
          simp only [Option.some.injEq] at hk
          subst hk
          obtain ⟨vs, hvs, hv⟩ := hookPat_inv hc patternHooks_elem hp
          obtain ⟨kv, wv, rfl, hm⟩ := hook_elem_inv hv
          cases hm
          obtain ⟨_, _, he1, hpa, hps⟩ := PatVals.cons_inv hvs
          cases he1
          obtain ⟨_, _, he2, hpb, _⟩ := PatVals.cons_inv hps
          cases he2
          obtain ⟨ksig, hksig, hargs, _⟩ := patCtx_sig hc patternHooks_elem ht
          rw [sig_elem] at hksig
          cases hksig
          obtain ⟨s1, ss1, hta, htb', he⟩ := sortsOfTerms_cons.mp hargs
          simp only [List.cons.injEq] at he
          obtain ⟨rfl, rfl⟩ := he
          obtain ⟨s2, ss2, htb, _, he'⟩ := sortsOfTerms_cons.mp htb'
          simp only [List.cons.injEq] at he'
          obtain ⟨rfl, rfl⟩ := he'
          have hne : (mapElem == mapConcat) = false := by decide
          refine ⟨[(a, b)], [], by simp [mapParts, hne], rfl, fun q hq => ?_, ?_, ?_,
            [(kv, wv)], [], ⟨⟨hpa, hpb⟩, trivial⟩, trivial, by simpa using hap, fun e => by simp⟩
          · rw [List.mem_singleton.mp hq]; exact ⟨hnm.1, hnm.2, hta, htb⟩
          · simp [elemsSize]; omega
          · intro i hi
            simp only [varOccs, varOccsList, List.append_nil, List.mem_append] at hi
            exact Or.inr ⟨(a, b), List.mem_singleton_self _, hi⟩
        · cases hk
      · cases hk
  | .app _ [_], _, _, _, hk, _, _, _, _ => by simp [mapFrames, mapFramesApp] at hk
  | .app _ (_ :: _ :: _ :: _), _, _, _, hk, _, _, _, _ => by simp [mapFrames, mapFramesApp] at hk
  | .inj _ _ _, _, _, _, hk, _, _, _, _ => by simp [mapFrames] at hk
  | .as _ _, _, _, _, hk, _, _, _, _ => by simp [mapFrames] at hk
  | .dv _ _, _, _, _, hk, _, _, _, _ => by simp [mapFrames] at hk

/-! ## Completeness on rule patterns -/

theorem pick_of_mem {es : Entries} {e : GroundTerm × GroundTerm} (he : e ∈ es) :
    ∃ j ∈ List.range es.length, pick es j = some (e, es.eraseIdx j) := by
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem he
  exact ⟨j, List.mem_range.mpr hj, by simp [pick, hj]⟩

theorem eraseIdx_mem {es : Entries} {j : Nat} {e : GroundTerm × GroundTerm}
    (hp : pick es j = some (e, es.eraseIdx j)) (hap : KeysApart es) :
    ∀ x, x ∈ es.eraseIdx j ↔ x ∈ es ∧ x ≠ e := by
  obtain ⟨hperm, _⟩ := pick_spec hp
  have hap' : KeysApart (e :: es.eraseIdx j) := KeysApart.perm hap hperm.symm
  rw [KeysApart, List.pairwise_cons] at hap'
  intro x
  constructor
  · intro hx
    refine ⟨hperm.mem_iff.mp (List.mem_cons_of_mem _ hx), fun hxe => ?_⟩
    subst hxe
    have := hap'.1 x hx
    rw [cmp_refl] at this
    exact this rfl
  · rintro ⟨hx, hne⟩
    rcases List.mem_cons.mp (hperm.mem_iff.mpr hx) with h | h
    · exact absurd h hne
    · exact h

mutual
  theorem matchP_complete (hc : MatchCtx c) {τ : Subst} {vars : List Srt}
      (hτ : c.WellSorted vars τ) : ∀ (n : Nat) {σ : Subst} {p : Term} {v : GroundTerm} {s : Srt},
      4 * termSize p ≤ n → noMapIn p = true → PatVal c τ p v →
      sortOfTerm c.patCtx vars p = some s → Ext σ τ →
      ∃ σ' ∈ matchP c n σ p v, Ext σ' τ ∧ Ext σ σ' ∧ Binds σ' (varOccs p)
    | 0, _, p, _, _, hn, _, _, _, _ => by have := termSize_pos p; omega
    | n + 1, σ, .var i, v, _, _, _, hp, _, hx => by
      obtain ⟨σ', hb, hx', hx'', hl⟩ := bindVar_complete hx (PatVal.var_inv hp)
      refine ⟨σ', by simp [matchP, hb], hx', hx'', fun j hj => ?_⟩
      simp only [varOccs, List.mem_singleton] at hj
      exact ⟨v, hj ▸ hl⟩
    | n + 1, σ, .dv s l, v, _, _, _, hp, _, hx => by
      cases hp
      exact ⟨σ, by simp [matchP], hx, Ext.refl _, fun j hj => by simp [varOccs] at hj⟩
    | n + 1, σ, .inj a b p, v, s, hn, hnm, hp, ht, hx => by
      simp only [noMapIn] at hnm
      obtain ⟨hab, ht', rfl⟩ := sortOfTerm_inj.mp ht
      have hn' : 4 * termSize p ≤ n := by simp [termSize] at hn; omega
      cases hp with
      | inj hw =>
        rename_i w
        have hsw := patVal_sorted hc hτ hw ht'
        obtain ⟨σ', hm, hx', hx'', hb⟩ := matchP_complete hc hτ n hn' hnm hw ht' hx
        cases w with
        | inj a' y u =>
          obtain ⟨h1, _, _, rfl⟩ := sortOf_inj.mp hsw
          have hne : (a' == a) = false := by
            rw [beq_eq_false_iff_ne]; rintro rfl; exact hc.irrefl _ h1
          exact ⟨σ', by simp [matchP, injNormal, hne, hm], hx', hx'', by simpa [varOccs] using hb⟩
        | ctor f ts => exact ⟨σ', by simp [matchP, injNormal, hm], hx', hx'', by simpa [varOccs] using hb⟩
        | dv s l => exact ⟨σ', by simp [matchP, injNormal, hm], hx', hx'', by simpa [varOccs] using hb⟩
        | map _ es => exact ⟨σ', by simp [matchP, injNormal, hm], hx', hx'', by simpa [varOccs] using hb⟩
        | set _ es => exact ⟨σ', by simp [matchP, injNormal, hm], hx', hx'', by simpa [varOccs] using hb⟩
        | list _ es => exact ⟨σ', by simp [matchP, injNormal, hm], hx', hx'', by simpa [varOccs] using hb⟩
    | n + 1, σ, .as p i, v, s, hn, hnm, hp, ht, hx => by
      simp only [noMapIn] at hnm
      obtain ⟨hp', hi⟩ := PatVal.as_inv hp
      have hn' : 4 * termSize p ≤ n := by simp [termSize] at hn; omega
      obtain ⟨σ1, hm, hx1, hx1', hb1⟩ := matchP_complete hc hτ n hn' hnm hp' (sortOfTerm_as ht).2 hx
      obtain ⟨σ', hbv, hx', hx'', hl⟩ := bindVar_complete hx1 hi
      refine ⟨σ', ?_, hx', hx1'.trans hx'', fun j hj => ?_⟩
      · simp only [matchP, List.mem_filterMap]
        exact ⟨σ1, hm, hbv⟩
      · simp only [varOccs, List.mem_append, List.mem_singleton] at hj
        rcases hj with hj | rfl
        · exact Binds.mono hx'' hb1 j hj
        · exact ⟨v, hl⟩
    | n + 1, σ, .app f ps, v, s, hn, hnm, hp, ht, hx => by
      by_cases hph : patternHooks.contains f = true
      · -- a map pattern
        simp only [noMapIn, hph, ↓reduceIte] at hnm
        have hnc : c.isCtor f = false := hc.patHooks f (List.contains_iff_mem.mp hph)
        obtain ⟨ksig, hksig, _, rfl⟩ := patCtx_sig hc hph ht
        have hres : ksig.result = Srt.map := patternHook_result hph hksig
        rw [hres] at ht
        have hsv := patVal_sorted hc hτ hp ht
        obtain ⟨es, rfl⟩ : ∃ es, v = .map Srt.map es := by
          obtain ⟨vs, _, hv⟩ := hookPat_inv hc hph hp
          exact patternHook_map hph hv
        have hes : keysSorted es = true := (sortOf_Map.mp hsv).1
        split at hnm
        · rename_i k hk
          have hk' : mapFrames (.app f ps) = some k := hk
          obtain ⟨E, F, hmp, hFl, hok, hsz, hcov, P, Ms, hM, hF, hap, hmem⟩ :=
            mapDecomp hc hτ (.app f ps) k es (n + 1) hk' (by omega) hp ht (sorted_apart hes)
          have hPin : ∀ e ∈ P, e ∈ es := fun e he => (hmem e).mpr (List.mem_append_left _ he)
          have hapP : KeysApart P := List.Pairwise.sublist (List.sublist_append_left _ _) hap
          obtain ⟨σ1, rest, hpa, hx1, hx1', hb1, hsub, hrest⟩ :=
            pickAll_complete hc hτ n (by omega) hok hM hPin hapP (sorted_apart hes) hx
          have hrs : keysSorted rest = true := sorted_sublist hsub hes
          have hrm : ∀ e, e ∈ rest ↔ e ∈ Ms.flatten := fun e => by
            rw [hrest, hmem, List.mem_append]
            constructor
            · rintro ⟨h | h, hn⟩
              · exact absurd h hn
              · exact h
            · intro h
              refine ⟨Or.inr h, fun hP => ?_⟩
              rw [KeysApart, List.pairwise_append] at hap
              have := hap.2.2 e hP e h
              rw [cmp_refl] at this
              exact this rfl
          have hbE : ∀ i ∈ varOccs (.app f ps), (∃ q ∈ E, i ∈ varOccs q.1 ∨ i ∈ varOccs q.2) →
              ∃ w, σ1.lookup i = some w := fun i _ h => hb1 i h
          rcases F with _ | ⟨i, _ | ⟨_, _⟩⟩
          · -- no frame: the elements' entries are the whole map
            have hMs : Ms = [] := by have := Framed.length hF; simpa using this
            subst hMs
            have hr : rest = [] := List.eq_nil_iff_forall_not_mem.mpr fun e he => by
              simpa using (hrm e).mp he
            subst hr
            refine ⟨σ1, ?_, hx1, hx1', fun j hj => ?_⟩
            · simp only [matchP, hnc, hph, Bool.false_eq_true, ↓reduceIte, hmp, List.mem_flatMap, beq_self_eq_true]
              exact ⟨(σ1, []), hpa, by simp⟩
            · rcases hcov j hj with hj | hj
              · simp at hj
              · exact hb1 j hj
          · -- one frame: the rest is its map
            match Ms, hF with
            | [M], ⟨⟨hl, hsM⟩, _⟩ =>
              have hrM : rest = M := entries_canon hrs hsM (fun e => by simpa using hrm e)
              subst hrM
              obtain ⟨σ', hbv, hx', hx'', hl'⟩ := bindVar_complete hx1 hl
              refine ⟨σ', ?_, hx', hx1'.trans hx'', fun j hj => ?_⟩
              · simp only [matchP, hnc, hph, Bool.false_eq_true, ↓reduceIte, hmp, List.mem_flatMap, beq_self_eq_true]
                exact ⟨(σ1, rest), hpa, by simp [hbv]⟩
              · rcases hcov j hj with hj | hj
                · simp only [List.mem_singleton] at hj
                  subst hj
                  exact ⟨_, hl'⟩
                · obtain ⟨w, hw⟩ := hb1 j hj
                  exact ⟨w, hx'' j w hw⟩
          · simp at hFl hnm; omega
        · cases hnm
      · -- a constructor pattern
        have hph' : patternHooks.contains f = false := by simpa using hph
        simp only [noMapIn, hph', Bool.false_eq_true, ↓reduceIte] at hnm
        obtain ⟨hk, vs, rfl, hs⟩ := PatVal.app_inv hph' hp (ctor_of_patCtx ht hph')
        obtain ⟨k, hk', hargs, rfl⟩ := sortOfTerm_app.mp ht
        have hn' : 4 * termSizeList ps + 1 ≤ n := by simp [termSize] at hn; omega
        obtain ⟨σ', hm, hx', hx'', hb⟩ := matchL_complete hc hτ n hn' hnm hs hargs hx
        refine ⟨σ', ?_, hx', hx'', by simpa [varOccs] using hb⟩
        simp [matchP, hk, hm]
  theorem matchL_complete (hc : MatchCtx c) {τ : Subst} {vars : List Srt}
      (hτ : c.WellSorted vars τ) : ∀ (n : Nat) {σ : Subst} {ps : List Term} {vs : List GroundTerm}
      {ss : List Srt}, 4 * termSizeList ps + 1 ≤ n → noMapInList ps = true → PatVals c τ ps vs →
      sortsOfTerms c.patCtx vars ps = some ss → Ext σ τ →
      ∃ σ' ∈ matchL c n σ ps vs, Ext σ' τ ∧ Ext σ σ' ∧ Binds σ' (varOccsList ps)
    | 0, _, _, _, _, hn, _, _, _, _ => by omega
    | n + 1, σ, [], vs, _, _, _, hp, _, hx => by
      rw [PatVals.nil_inv hp]
      exact ⟨σ, by simp [matchL], hx, Ext.refl _, fun j hj => by simp [varOccsList] at hj⟩
    | n + 1, σ, p :: ps, vs, ss, hn, hnm, hp, ht, hx => by
      simp only [noMapInList, Bool.and_eq_true] at hnm
      obtain ⟨v, vs', rfl, hp1, hps⟩ := PatVals.cons_inv hp
      obtain ⟨s, ss', h1, h2, rfl⟩ := sortsOfTerms_cons.mp ht
      have hsz := termSize_pos p
      have hn1 : 4 * termSize p ≤ n := by simp [termSizeList] at hn; omega
      have hn2 : 4 * termSizeList ps + 1 ≤ n := by simp [termSizeList] at hn; omega
      obtain ⟨σ1, hm1, hx1, hx1', hb1⟩ := matchP_complete hc hτ n hn1 hnm.1 hp1 h1 hx
      obtain ⟨σ', hm2, hx', hx'', hb2⟩ := matchL_complete hc hτ n hn2 hnm.2 hps h2 hx1
      refine ⟨σ', ?_, hx', hx1'.trans hx'', fun j hj => ?_⟩
      · simp only [matchL, List.mem_flatMap]
        exact ⟨σ1, hm1, hm2⟩
      · simp only [varOccsList, List.mem_append] at hj
        rcases hj with hj | hj
        · exact Binds.mono hx'' hb1 j hj
        · exact hb2 j hj
  theorem pickAll_complete (hc : MatchCtx c) {τ : Subst} {vars : List Srt}
      (hτ : c.WellSorted vars τ) : ∀ (n : Nat) {σ : Subst} {E : List (Term × Term)} {P es : Entries},
      4 * elemsSize E + 1 ≤ n → ElemsOK c vars E → Matched c τ E P → (∀ e ∈ P, e ∈ es) →
      KeysApart P → KeysApart es → Ext σ τ →
      ∃ σ' rest, (σ', rest) ∈ pickAll c n σ E es ∧ Ext σ' τ ∧ Ext σ σ' ∧
        (∀ i, (∃ q ∈ E, i ∈ varOccs q.1 ∨ i ∈ varOccs q.2) → ∃ w, σ'.lookup i = some w) ∧
        rest.Sublist es ∧ ∀ e, e ∈ rest ↔ e ∈ es ∧ e ∉ P
    | 0, _, _, _, _, hn, _, _, _, _, _, _ => by omega
    | n + 1, σ, [], P, es, _, _, hM, _, _, _, hx => by
      match P, hM with
      | [], _ =>
        exact ⟨σ, es, by simp [pickAll], hx, Ext.refl _, (fun i ⟨q, hq, _⟩ => nomatch hq),
          List.Sublist.refl _, fun e => by simp⟩
    | n + 1, σ, (kp, vp) :: E, P, es, hn, hok, hM, hPin, hapP, hes, hx => by
      match P, hM, hPin, hapP with
      | e :: P', ⟨⟨hpk, hpv⟩, hM'⟩, hPin, hapP =>
        obtain ⟨hnk, hnv, htk, htv⟩ := hok (kp, vp) (List.mem_cons_self ..)
        have hok' : ElemsOK c vars E := fun q hq => hok q (List.mem_cons_of_mem _ hq)
        have hsk := termSize_pos kp
        have hsv := termSize_pos vp
        have hn1 : 4 * termSize kp ≤ n := by simp [elemsSize] at hn; omega
        have hn2 : 4 * termSize vp ≤ n := by simp [elemsSize] at hn; omega
        have hn3 : 4 * elemsSize E + 1 ≤ n := by simp [elemsSize] at hn; omega
        obtain ⟨j, hj, hpick⟩ := pick_of_mem (hPin e (List.mem_cons_self ..))
        have hrest0 := eraseIdx_mem hpick hes
        rw [KeysApart, List.pairwise_cons] at hapP
        have hPin' : ∀ e' ∈ P', e' ∈ es.eraseIdx j := fun e' he' =>
          (hrest0 e').mpr ⟨hPin e' (List.mem_cons_of_mem _ he'), fun h => by
            subst h; have := hapP.1 e' he'; rw [cmp_refl] at this; exact this rfl⟩
        have hes0 : KeysApart (es.eraseIdx j) := List.Pairwise.sublist (List.eraseIdx_sublist _ _) hes
        obtain ⟨σ1, hm1, hx1, hx1', hb1⟩ := matchP_complete hc hτ n hn1 hnk hpk htk hx
        obtain ⟨σ2, hm2, hx2, hx2', hb2⟩ := matchP_complete hc hτ n hn2 hnv hpv htv hx1
        obtain ⟨σ', rest, hpa, hx', hx'', hb', hsub, hrest⟩ :=
          pickAll_complete hc hτ n hn3 hok' hM' hPin' hapP.2 hes0 hx2
        refine ⟨σ', rest, ?_, hx', hx1'.trans (hx2'.trans hx''), fun i ⟨q, hq, hi⟩ => ?_,
          hsub.trans (List.eraseIdx_sublist _ _), fun x => ?_⟩
        · simp only [pickAll, List.mem_flatMap]
          refine ⟨j, hj, ?_⟩
          rw [hpick]
          simp only [List.mem_flatMap]
          exact ⟨σ1, hm1, σ2, hm2, hpa⟩
        · rcases List.mem_cons.mp hq with rfl | hq
          · rcases hi with hi | hi
            · exact Binds.mono (hx2'.trans hx'') hb1 i hi
            · exact Binds.mono hx'' hb2 i hi
          · exact hb' i ⟨q, hq, hi⟩
        · rw [hrest, hrest0]
          simp only [List.mem_cons, not_or]
          constructor
          · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h1, h2, h3⟩
          · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h1, h2⟩, h3⟩
end

end KCore.Exec
