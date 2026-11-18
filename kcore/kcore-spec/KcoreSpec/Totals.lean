/-
  KCore. Totality of the functions `totalOK` confirms (checked layer).

  - `covers_sound`: rows `covers` accepts at the sorts `ss` match, as rows (`RowMatch`: a variable
    matches anything, a constructor application a constructor term of that constructor, an
    injection an injection of the same sorts, an alias what its pattern matches), some row at every
    argument list of those sorts. At an enumerable sort a value is a constructor term or an
    injection (`enumerable_value`), each the application of one of the sort's generators, so the
    rows specialised to that generator cover its arguments; elsewhere the variable rows cover.
  - `rowMatches_subst`: a row of a clause's patterns, its variables apart (`coverRows`), that
    matches an argument list of the clause's sorts as a row, matches it as `PatVal` reads it,
    under a substitution of the clause's variable sorts: each variable is bound at its one
    occurrence.
  - `evalTerm_defined`: a term `totalTerm` accepts has a value where its calls of the functions of
    `tot` have one.
  - `total_of_totalOK`: a function `totalOK` confirms is total, given that every function
    terminates and the total functions before it are total; by induction on the size of its
    decreasing argument (`decArg`), as for termination.
  - `totals_of_order`, `CoreObligations.totals`, `Obligations.totals`: every function declared
    `[total]` is total, given the named ones (`totalObligations`); the sort predicates are total
    (`sortPreds_total`). `CoreObligations.totalsDefined` is `TotalsDefined` (LazySound.lean), from
    `coreOK` and `CoreObligations`; `Obligations.totalsDefined`, from `wf` and `Obligations`.
-/
import KcoreSpec.Terminates
import KcoreSpec.LazySound
import KcoreSpec.NICells
import KcoreSpec.HooksApart

set_option autoImplicit false

namespace KCore

variable {c : Semantics}

/-! ## Rows -/

mutual
  /-- A pattern matches a value as a covering row reads it. -/
  inductive RowMatch (c : Semantics) : Term → GroundTerm → Prop where
    | var {i : Nat} {v : GroundTerm} : RowMatch c (.var i) v
    | as {p : Term} {i : Nat} {v : GroundTerm} (h : RowMatch c p v) : RowMatch c (.as p i) v
    | ctor {f : Sym} {qs : List Term} {ws : List GroundTerm} (h : c.isCtor f = true)
        (hs : RowMatches c qs ws) : RowMatch c (.app f qs) (.ctor f ws)
    | inj {a b : Srt} {q : Term} {w : GroundTerm} (h : RowMatch c q w) :
        RowMatch c (.inj a b q) (.inj a b w)
  inductive RowMatches (c : Semantics) : List Term → List GroundTerm → Prop where
    | nil : RowMatches c [] []
    | cons {p : Term} {ps : List Term} {v : GroundTerm} {vs : List GroundTerm}
        (h : RowMatch c p v) (hs : RowMatches c ps vs) : RowMatches c (p :: ps) (v :: vs)
end

theorem rowMatch_of_peel : ∀ {p : Term} {v : GroundTerm}, RowMatch c (peelAs p) v → RowMatch c p v
  | .as p _, _, h => .as (rowMatch_of_peel (p := p) (by simpa [peelAs] using h))
  | .var _, _, h => by simpa [peelAs] using h
  | .app _ _, _, h => by simpa [peelAs] using h
  | .inj _ _ _, _, h => by simpa [peelAs] using h
  | .dv _ _, _, h => by simpa [peelAs] using h

theorem rowMatches_append : ∀ {ps qs : List Term} {vs ws : List GroundTerm},
    ps.length = vs.length → RowMatches c (ps ++ qs) (vs ++ ws) → RowMatches c ps vs ∧ RowMatches c qs ws
  | [], _, [], _, _, h => ⟨.nil, by simpa using h⟩
  | _ :: _, _, _ :: _, _, hl, h => by
    cases h with
    | cons h1 h2 =>
      obtain ⟨a, b⟩ := rowMatches_append (by simpa using hl) h2
      exact ⟨.cons h1 a, b⟩
  | [], _, _ :: _, _, hl, _ => by simp at hl
  | _ :: _, _, [], _, hl, _ => by simp at hl

theorem rowMatches_wild : ∀ (ss : List Srt) {ws : List GroundTerm}, ws.length = ss.length →
    RowMatches c (ss.map fun _ => Term.var 0) ws
  | [], [], _ => .nil
  | _ :: ss, _ :: ws, h => .cons .var (rowMatches_wild ss (by simpa using h))
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

/-- The patterns of a row at the sorts `ss`: each a variable, or of its sort over the clause's
variables in the context of left-hand sides (`patCtxAll`). -/
def RowTyped (c : Semantics) (vars : List Srt) : List Srt → List Term → Prop
  | [], [] => True
  | s :: ss, p :: ps => ((∃ i, p = .var i) ∨ sortOfTerm c.patCtxAll vars p = some s) ∧ RowTyped c vars ss ps
  | _, _ => False

theorem sortOfTerm_peel {vars : List Srt} : ∀ {p : Term} {s : Srt},
    sortOfTerm c.patCtxAll vars p = some s → sortOfTerm c.patCtxAll vars (peelAs p) = some s
  | .as p i, s, h => by
    simp only [peelAs]
    simp only [sortOfTerm] at h
    have hx : c.patCtxAll.asOK = true := rfl
    rw [hx] at h
    cases hv : vars[i]? with
    | none => rw [hv] at h; cases h
    | some u =>
      cases hp : sortOfTerm c.patCtxAll vars p with
      | none => rw [hv, hp] at h; cases h
      | some w =>
        rw [hv, hp] at h
        simp only at h
        split at h
        · cases h; exact sortOfTerm_peel hp
        · cases h
  | .var _, _, h => by simpa [peelAs] using h
  | .app _ _, _, h => by simpa [peelAs] using h
  | .inj _ _ _, _, h => by simpa [peelAs] using h
  | .dv _ _, _, h => by simpa [peelAs] using h

theorem sortsOfTerms_length {x : TermCtx} {vars : List Srt} : ∀ {ts : List Term} {ss : List Srt},
    sortsOfTerms x vars ts = some ss → ts.length = ss.length
  | [], _, h => by rw [sortsOfTerms_nil.mp h]; rfl
  | _ :: _, _, h => by
    obtain ⟨_, _, _, h', rfl⟩ := sortsOfTerms_cons.mp h
    simp [sortsOfTerms_length h']

theorem sortsOf_length : ∀ {vs : List GroundTerm} {ss : List Srt}, c.sortsOf vs = some ss →
    vs.length = ss.length
  | [], _, h => by rw [sortsOf_nil] at h; cases h; rfl
  | _ :: _, _, h => by
    obtain ⟨_, _, _, h', rfl⟩ := sortsOf_cons.mp h
    simp [sortsOf_length h']

theorem sortsOf_append : ∀ {vs ws : List GroundTerm} {ss ts : List Srt}, c.sortsOf vs = some ss →
    c.sortsOf ws = some ts → c.sortsOf (vs ++ ws) = some (ss ++ ts)
  | [], _, _, _, h, h' => by rw [sortsOf_nil] at h; cases h; simpa using h'
  | _ :: _, _, _, _, h, h' => by
    obtain ⟨s, ss', h1, h2, rfl⟩ := sortsOf_cons.mp h
    exact sortsOf_cons.mpr ⟨s, _, h1, sortsOf_append h2 h', rfl⟩

theorem rowTyped_tail {vars : List Srt} {s : Srt} {ss : List Srt} {p : Term} {ps : List Term}
    (h : RowTyped c vars (s :: ss) (p :: ps)) : RowTyped c vars ss ps := h.2

theorem rowTyped_append {vars : List Srt} : ∀ {ss ts : List Srt} {ps qs : List Term},
    RowTyped c vars ss ps → RowTyped c vars ts qs → RowTyped c vars (ss ++ ts) (ps ++ qs)
  | [], _, [], _, _, h => h
  | _ :: _, _, _ :: _, _, h, h' => ⟨h.1, rowTyped_append h.2 h'⟩
  | [], _, _ :: _, _, h, _ => h.elim
  | _ :: _, _, [], _, h, _ => h.elim

theorem rowTyped_wild {vars : List Srt} : ∀ (ss : List Srt), RowTyped c vars ss (ss.map fun _ => Term.var 0)
  | [] => trivial
  | _ :: ss => ⟨Or.inl ⟨0, rfl⟩, rowTyped_wild ss⟩

theorem rowTyped_of_sorts {vars : List Srt} : ∀ {ss : List Srt} {ps : List Term},
    sortsOfTerms c.patCtxAll vars ps = some ss → RowTyped c vars ss ps
  | [], [], _ => trivial
  | _, _ :: _, h => by
    obtain ⟨s, ss', h1, h2, rfl⟩ := sortsOfTerms_cons.mp h
    exact ⟨Or.inr h1, rowTyped_of_sorts h2⟩
  | _ :: _, [], h => by rw [sortsOfTerms_nil] at h; cases h

theorem rowTyped_length {vars : List Srt} : ∀ {ss : List Srt} {ps : List Term},
    RowTyped c vars ss ps → ps.length = ss.length
  | [], [], _ => rfl
  | _ :: _, _ :: _, h => by simp [rowTyped_length h.2]
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim

/-! ## Values of an enumerable sort -/

theorem enumerable_value {s : Srt} {v : GroundTerm} (he : c.enumerable s = true)
    (hv : c.sortOf v = some s) :
    (∃ f ws k, v = .ctor f ws ∧ lookupSig c.ctorSigs f = some k ∧ k.result = s ∧
      c.sortsOf ws = some k.args) ∨
    (∃ a w, v = .inj a s w ∧ (a, s) ∈ c.subsorts ∧ c.sortOf w = some a ∧ w.isInj = false) := by
  have hcs : c.lib.carrier s = s :=
    Lib.carrier_of_not _ (by unfold Semantics.enumerable at he; simp only [Bool.and_eq_true] at he; exact he.1.2)
  simp only [Semantics.enumerable, Bool.and_eq_true, Bool.not_eq_true', Bool.or_eq_false_iff,
    beq_eq_false_iff_ne, Option.isNone_iff_eq_none, List.isEmpty_iff] at he
  obtain ⟨⟨⟨⟨⟨hno, _⟩, hcoll⟩, ⟨⟨⟨⟨⟨⟨⟨hint, hbool⟩, hkc⟩, htok⟩, hbyte⟩, hflt⟩, hstr⟩, hbys⟩⟩, -⟩, hraw⟩ := he
  cases v with
  | ctor f ws =>
    obtain ⟨k, hk, hws, rfl⟩ := (sortOf_ctor hno (fun k hk => by simpa using List.any_eq_false.mp hraw k hk)).mp hv
    exact Or.inl ⟨f, ws, k, rfl, hk, rfl, hws⟩
  | inj a b w =>
    obtain ⟨hab, hi, hw, rfl⟩ := sortOf_inj.mp hv
    exact Or.inr ⟨a, w, rfl, hab, hw, hi⟩
  | dv s' lit =>
    obtain ⟨hok, rfl⟩ := sortOf_dv.mp hv
    cases lit with
    | int _ => simp only [dvOK, hcs, beq_iff_eq] at hok; exact absurd hok hint
    | bool _ => simp only [dvOK, hcs, beq_iff_eq] at hok; exact absurd hok hbool
    | tok _ =>
      simp only [dvOK, hcs, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true] at hok
      rcases hok with ((h | h) | h) | ⟨h | h, -⟩
      · exact absurd h hkc
      · exact absurd h hstr
      · rw [htok] at h; cases h
      · exact absurd h hbys
      · rw [hbyte] at h; cases h
    | float _ _ _ =>
      simp only [dvOK, hcs, Bool.and_eq_true, beq_iff_eq] at hok; exact absurd hok.1 hflt
  | map s' es =>
    obtain ⟨k, _, hk, _, _, _, _, rfl⟩ := sortOf_mapS_fwd hv
    rw [hcoll] at hk; cases hk
  | set s' es =>
    obtain ⟨k, hk, _, _, _, rfl⟩ := sortOf_setS.mp hv
    rw [hcoll] at hk; cases hk
  | list s' es =>
    obtain ⟨k, hk, _, _, rfl⟩ := sortOf_listS.mp hv
    rw [hcoll] at hk; cases hk

theorem mem_insertBy {α β : Type} [LT β] [DecidableRel (α := β) (· < ·)] (key : α → β) (a : α) :
    ∀ (l : List α) (x : α), x ∈ insertBy key a l ↔ x = a ∨ x ∈ l
  | [], x => by simp [insertBy]
  | b :: bs, x => by
    simp only [insertBy]
    split
    · simp
    · simp only [List.mem_cons, mem_insertBy key a bs x]
      constructor
      · rintro (h | h | h) <;> simp [h]
      · rintro (h | h | h) <;> simp [h]

theorem mem_sortBy {α β : Type} [LT β] [DecidableRel (α := β) (· < ·)] (key : α → β) :
    ∀ (l : List α) (x : α), x ∈ sortBy key l ↔ x ∈ l
  | [], x => by simp [sortBy]
  | b :: bs, x => by
    have : sortBy key (b :: bs) = insertBy key b (sortBy key bs) := rfl
    rw [this, mem_insertBy, mem_sortBy key bs x, List.mem_cons]

/-! ## `covers` is sound -/

theorem specialize_cases {g : Gen} {p : Term} {ps r' : List Term} (h : specialize g (p :: ps) = some r') :
    (∃ i, peelAs p = .var i ∧ r' = (g.argSorts.map fun _ => Term.var 0) ++ ps) ∨
    (∃ f qs k, peelAs p = .app f qs ∧ g = .ctor k ∧ f = k.name ∧ r' = qs ++ ps) ∨
    (∃ a b q, peelAs p = .inj a b q ∧ g = .inj a ∧ r' = q :: ps) := by
  simp only [specialize] at h
  split at h
  · rename_i i _
    exact Or.inl ⟨i, by assumption, (Option.some.inj h).symm⟩
  · rename_i f qs k hp
    split at h
    · rename_i hf
      exact Or.inr (Or.inl ⟨f, qs, k, hp, rfl, beq_iff_eq.mp hf, (Option.some.inj h).symm⟩)
    · cases h
  · rename_i a b q a' hp
    split at h
    · rename_i ha
      have := beq_iff_eq.mp ha
      subst this
      exact Or.inr (Or.inr ⟨a, b, q, hp, rfl, (Option.some.inj h).symm⟩)
    · cases h
  · cases h

/-- A constructor that is the first of its name: its patterns are typed by it. -/
theorem lookup_patCtxAll_of_ctor {f : Sym} {k : CtorSig} (hk : lookupSig c.ctorSigs f = some k) :
    lookupSig c.patCtxAll.heads f = some k := by
  simp only [Semantics.patCtxAll, Semantics.patCtx]
  exact lookupSig_append_of_some (lookupSig_append_of_some hk)

theorem covers_sound : ∀ (n : Nat) (ss : List Srt) (rows : List (List Term)),
    c.covers n ss rows = true → (∀ r ∈ rows, ∃ vars, RowTyped c vars ss r) →
    ∀ vs, c.sortsOf vs = some ss → ∃ r ∈ rows, RowMatches c r vs
  | 0, _, _, h, _, _, _ => by simp [Semantics.covers] at h
  | n + 1, [], rows, h, ht, vs, hvs => by
    simp only [Semantics.covers, Bool.not_eq_true', List.isEmpty_eq_false_iff] at h
    obtain ⟨r, hr⟩ := List.exists_mem_of_ne_nil rows h
    obtain ⟨vars, hrt⟩ := ht r hr
    have hr0 : r = [] := by cases r with | nil => rfl | cons _ _ => exact hrt.elim
    have hv0 : vs = [] := by
      cases vs with
      | nil => rfl
      | cons _ _ => obtain ⟨_, _, _, _, he⟩ := sortsOf_cons.mp hvs; cases he
    subst hr0; subst hv0
    exact ⟨[], hr, .nil⟩
  | n + 1, s :: ss, rows, h, ht, vs, hvs => by
    obtain ⟨v, vs', rfl, hv, hvs'⟩ := sortsOf_inv_cons hvs
    simp only [Semantics.covers] at h
    -- the variable rows, read in the second branch
    have hvar : ∀ r' ∈ rows.filterMap (fun r => match r with
        | p :: ps => (match peelAs p with | .var _ => some ps | _ => none)
        | [] => none), ∃ r ∈ rows, ∃ p, r = p :: r' ∧ ∃ i, peelAs p = .var i := by
      intro r' hr'
      obtain ⟨r, hr, he⟩ := List.mem_filterMap.mp hr'
      refine ⟨r, hr, ?_⟩
      cases r with
      | nil => cases he
      | cons p ps =>
        simp only at he
        split at he
        · rename_i i hi
          exact ⟨p, by rw [Option.some.inj he], i, hi⟩
        · cases he
    split at h
    · rename_i hcond
      simp only [Bool.and_eq_true] at hcond
      have hall := List.all_eq_true.mp h
      rcases enumerable_value hcond.1 hv with ⟨f, ws, k, rfl, hk, hres, hws⟩ | ⟨a, w, rfl, hab, hw, hi⟩
      · -- a constructor term: the rows specialised to its constructor
        obtain ⟨hkm, hkn⟩ := lookupSig_spec hk
        have hg : Gen.ctor k ∈ c.gens s := by
          simp only [Semantics.gens, List.mem_append, List.mem_map, List.mem_filter, beq_iff_eq]
          exact Or.inl (Or.inl (Or.inl ⟨k, ⟨hkm, hres⟩, rfl⟩))
        have hcov := hall _ hg
        simp only [Gen.argSorts] at hcov
        have htyped : ∀ r' ∈ rows.filterMap (specialize (.ctor k)), ∃ vars, RowTyped c vars (k.args ++ ss) r' := by
          intro r' hr'
          obtain ⟨r, hr, he⟩ := List.mem_filterMap.mp hr'
          obtain ⟨vars, hrt⟩ := ht r hr
          cases r with
          | nil => simp [specialize] at he
          | cons p ps =>
            refine ⟨vars, ?_⟩
            rcases specialize_cases he with ⟨_, _, rfl⟩ | ⟨f', qs, k', hp, hk', rfl, rfl⟩ | ⟨_, _, _, _, hg', _⟩
            · simp only [Gen.argSorts]
              exact rowTyped_append (rowTyped_wild _) hrt.2
            · cases hk'
              rcases hrt.1 with ⟨i, rfl⟩ | hps
              · simp [peelAs] at hp
              · have hps' := sortOfTerm_peel hps
                rw [hp] at hps'
                obtain ⟨k₀, hk₀, hqs, _⟩ := sortOfTerm_app.mp hps'
                rw [← hkn] at hk
                rw [lookup_patCtxAll_of_ctor hk] at hk₀
                cases hk₀
                exact rowTyped_append (rowTyped_of_sorts hqs) hrt.2
            · cases hg'
        obtain ⟨r', hr', hm⟩ := covers_sound n _ _ hcov htyped (ws ++ vs') (sortsOf_append hws hvs')
        obtain ⟨r, hr, he⟩ := List.mem_filterMap.mp hr'
        obtain ⟨vars, hrt⟩ := ht r hr
        refine ⟨r, hr, ?_⟩
        cases r with
        | nil => simp [specialize] at he
        | cons p ps =>
          rcases specialize_cases he with ⟨i, hp, rfl⟩ | ⟨f', qs, k', hp, hk', rfl, rfl⟩ | ⟨_, _, _, _, hg', _⟩
          · obtain ⟨_, h2⟩ := rowMatches_append (by simp [Gen.argSorts, sortsOf_length hws]) hm
            exact .cons (rowMatch_of_peel (by rw [hp]; exact .var)) h2
          · cases hk'
            rcases hrt.1 with ⟨i, rfl⟩ | hps
            · simp [peelAs] at hp
            · have hps' := sortOfTerm_peel hps
              rw [hp] at hps'
              obtain ⟨k₀, hk₀, hqs, _⟩ := sortOfTerm_app.mp hps'
              have hk2 := hk
              rw [← hkn] at hk2
              rw [lookup_patCtxAll_of_ctor hk2] at hk₀
              cases hk₀
              obtain ⟨h1, h2⟩ := rowMatches_append
                (by rw [sortsOfTerms_length hqs, sortsOf_length hws]) hm
              have hct : c.isCtor k.name = true := by
                simp only [Semantics.isCtor]; rw [hk2]; rfl
              rw [← hkn]
              exact .cons (rowMatch_of_peel (by rw [hp]; exact .ctor hct h1)) h2
          · cases hg'
      · -- an injection: the rows specialised to the injection from its sort
        have hg : Gen.inj a ∈ c.gens s := by
          simp only [Semantics.gens, List.mem_append, List.mem_map]
          refine Or.inr ⟨a, ?_, rfl⟩
          rw [mem_sortBy]
          exact List.mem_map.mpr ⟨(a, s), List.mem_filter.mpr ⟨hab, by simp⟩, rfl⟩
        have hcov := hall _ hg
        simp only [Gen.argSorts] at hcov
        have htyped : ∀ r' ∈ rows.filterMap (specialize (.inj a)), ∃ vars, RowTyped c vars (a :: ss) r' := by
          intro r' hr'
          obtain ⟨r, hr, he⟩ := List.mem_filterMap.mp hr'
          obtain ⟨vars, hrt⟩ := ht r hr
          cases r with
          | nil => simp [specialize] at he
          | cons p ps =>
            refine ⟨vars, ?_⟩
            rcases specialize_cases he with ⟨_, _, rfl⟩ | ⟨_, _, _, _, hg', _⟩ | ⟨a', b', q, hp, hg', rfl⟩
            · exact ⟨Or.inl ⟨0, rfl⟩, hrt.2⟩
            · cases hg'
            · cases hg'
              rcases hrt.1 with ⟨i, rfl⟩ | hps
              · simp [peelAs] at hp
              · have hps' := sortOfTerm_peel hps
                rw [hp] at hps'
                obtain ⟨_, hq, _⟩ := sortOfTerm_inj.mp hps'
                exact ⟨Or.inr hq, hrt.2⟩
        obtain ⟨r', hr', hm⟩ := covers_sound n _ _ hcov htyped (w :: vs') (sortsOf_cons.mpr ⟨a, ss, hw, hvs', rfl⟩)
        obtain ⟨r, hr, he⟩ := List.mem_filterMap.mp hr'
        obtain ⟨vars, hrt⟩ := ht r hr
        refine ⟨r, hr, ?_⟩
        cases r with
        | nil => simp [specialize] at he
        | cons p ps =>
          rcases specialize_cases he with ⟨i, hp, rfl⟩ | ⟨_, _, _, _, hg', _⟩ | ⟨a', b', q, hp, hg', rfl⟩
          · simp only [Gen.argSorts, List.map_cons, List.map_nil, List.cons_append, List.nil_append] at hm
            cases hm with
            | cons _ h2 => exact .cons (rowMatch_of_peel (by rw [hp]; exact .var)) h2
          · cases hg'
          · cases hg'
            rcases hrt.1 with ⟨i, rfl⟩ | hps
            · simp [peelAs] at hp
            · have hps' := sortOfTerm_peel hps
              rw [hp] at hps'
              obtain ⟨_, _, rfl⟩ := sortOfTerm_inj.mp hps'
              cases hm with
              | cons h1 h2 => exact .cons (rowMatch_of_peel (by rw [hp]; exact .inj h1)) h2
    · have hcov := h
      have htyped : ∀ r' ∈ rows.filterMap (fun r => match r with
          | p :: ps => (match peelAs p with | .var _ => some ps | _ => none)
          | [] => none), ∃ vars, RowTyped c vars ss r' := by
        intro r' hr'
        obtain ⟨r, hr, p, rfl, _⟩ := hvar r' hr'
        obtain ⟨vars, hrt⟩ := ht _ hr
        exact ⟨vars, hrt.2⟩
      obtain ⟨r', hr', hm⟩ := covers_sound n ss _ hcov htyped vs' hvs'
      obtain ⟨r, hr, p, rfl, i, hp⟩ := hvar r' hr'
      exact ⟨_, hr, .cons (rowMatch_of_peel (by rw [hp]; exact .var)) hm⟩

/-! ## A row's match is a clause's match -/

theorem lookup_cons_self (j : Nat) (w : GroundTerm) (σ : Subst) :
    ((j, w) :: σ).lookup j = some w := by
  rw [List.lookup_cons, beq_self_eq_true]

theorem lookup_cons_ne {j i : Nat} (w : GroundTerm) (σ : Subst) (h : j ≠ i) :
    ((i, w) :: σ).lookup j = σ.lookup j := by
  have hji : (j == i) = false := by simpa using h
  rw [List.lookup_cons, hji]

theorem lookup_append_of_mem : ∀ (σ₁ σ₂ : Subst) {j : Nat}, j ∈ σ₁.map (·.1) →
    (σ₁ ++ σ₂).lookup j = σ₁.lookup j
  | [], _, _, h => nomatch h
  | (i, w) :: σ₁, σ₂, j, h => by
    rw [List.cons_append]
    by_cases hj : j = i
    · subst hj; rw [lookup_cons_self, lookup_cons_self]
    · rw [lookup_cons_ne _ _ hj, lookup_cons_ne _ _ hj]
      rw [List.map_cons, List.mem_cons] at h
      exact lookup_append_of_mem σ₁ σ₂ (h.resolve_left hj)

theorem lookup_append_of_not_mem : ∀ (σ₁ σ₂ : Subst) {j : Nat}, j ∉ σ₁.map (·.1) →
    (σ₁ ++ σ₂).lookup j = σ₂.lookup j
  | [], _, _, _ => rfl
  | (i, w) :: σ₁, σ₂, j, h => by
    have hj : j ≠ i := fun e => h (by simp [e])
    rw [List.cons_append, lookup_cons_ne _ _ hj]
    exact lookup_append_of_not_mem σ₁ σ₂ (fun h' => h (by simp [h']))

theorem lookup_of_mem_keys : ∀ (σ : Subst) {j : Nat}, j ∈ σ.map (·.1) →
    ∃ w, σ.lookup j = some w ∧ (j, w) ∈ σ
  | [], _, h => nomatch h
  | (i, w) :: σ, j, h => by
    by_cases hj : j = i
    · subst hj; exact ⟨w, lookup_cons_self _ _ _, List.mem_cons_self ..⟩
    · rw [List.map_cons, List.mem_cons] at h
      obtain ⟨w', h1, h2⟩ := lookup_of_mem_keys σ (h.resolve_left hj)
      exact ⟨w', by rw [lookup_cons_ne _ _ hj]; exact h1, List.mem_cons_of_mem _ h2⟩

theorem sortOfTerm_as_all {vars : List Srt} {p : Term} {i : Nat} {s : Srt}
    (h : sortOfTerm c.patCtxAll vars (.as p i) = some s) :
    vars[i]? = some s ∧ sortOfTerm c.patCtxAll vars p = some s := by
  simp only [sortOfTerm] at h
  have hx : c.patCtxAll.asOK = true := rfl
  rw [hx] at h
  cases hv : vars[i]? with
  | none => rw [hv] at h; cases h
  | some u =>
    cases hp : sortOfTerm c.patCtxAll vars p with
    | none => rw [hv, hp] at h; cases h
    | some w =>
      rw [hv, hp] at h
      simp only at h
      split at h
      · rename_i he
        cases h
        exact ⟨by rw [beq_iff_eq.mp he], rfl⟩
      · cases h

theorem injNormal_of_not_inj {a b : Srt} {w : GroundTerm} (h : w.isInj = false) :
    injNormal a b w = .inj a b w := by
  cases w <;> simp_all [GroundTerm.isInj, injNormal]

/-- The variables' sorts a substitution's entries have. -/
def SortedEntries (c : Semantics) (vars : List Srt) (σ : Subst) : Prop :=
  ∀ e ∈ σ, ∃ s', vars[e.1]? = some s' ∧ c.sortOf e.2 = some s'

mutual
  /-- A row's match of a pattern whose variables occur once, at a value of its sort, is a match
  of it under the substitution binding each variable at its occurrence. -/
  theorem rowMatch_subst {vars : List Srt} {p : Term} {v : GroundTerm} (h : RowMatch c p v) {s : Srt}
      (ht : sortOfTerm c.patCtxAll vars p = some s) (hv : c.sortOf v = some s)
      (hnd : (varOccs p).Nodup) :
      ∃ σ : Subst, σ.map (·.1) = varOccs p ∧ PatVal c σ p v ∧ SortedEntries c vars σ :=
    match h with
    | .var (i := i) (v := v) => by
      refine ⟨[(i, v)], by simp [varOccs], .var (lookup_cons_self _ _ _), ?_⟩
      intro e he
      simp only [List.mem_singleton] at he
      subst he
      exact ⟨s, sortOfTerm_var.mp ht, hv⟩
    | .as (p := p) (i := i) h' => by
      obtain ⟨hvi, ht'⟩ := sortOfTerm_as_all ht
      simp only [varOccs] at hnd ⊢
      have hnd' := List.nodup_append.mp hnd
      have hi : i ∉ varOccs p := fun hm => hnd'.2.2 i hm i (List.mem_singleton_self _) rfl
      obtain ⟨σ, hk, hm, hse⟩ := rowMatch_subst h' ht' hv hnd'.1
      refine ⟨σ ++ [(i, v)], by simp [hk], ?_, ?_⟩
      · refine .as (NI.PatVal.congr hm fun j hj => lookup_append_of_mem σ _ (by rw [hk]; exact hj)) ?_
        rw [lookup_append_of_not_mem σ _ (by rw [hk]; exact hi)]
        exact lookup_cons_self _ _ _
      · intro e he
        rcases List.mem_append.mp he with he | he
        · exact hse e he
        · simp only [List.mem_singleton] at he
          subst he
          exact ⟨s, hvi, hv⟩
    | .ctor (f := f) (qs := qs) (ws := ws) hct hs => by
      obtain ⟨k₀, hk₀, hqs, rfl⟩ := sortOfTerm_app.mp ht
      obtain ⟨k, hk, hws, hres⟩ := (sortOf_ctor_of_isCtor hct).mp hv
      rw [lookup_patCtxAll_of_ctor hk] at hk₀
      cases hk₀
      obtain ⟨σ, hkeys, hm, hse⟩ := rowMatches_subst hs hqs hws (by simpa [varOccs] using hnd)
      exact ⟨σ, by simpa [varOccs] using hkeys, .ctor hct hm, hse⟩
    | .inj (a := a) (b := b) (w := w) h' => by
      obtain ⟨_, ht', rfl⟩ := sortOfTerm_inj.mp ht
      obtain ⟨_, hi, hw, _⟩ := sortOf_inj.mp hv
      obtain ⟨σ, hkeys, hm, hse⟩ := rowMatch_subst h' ht' hw (by simpa [varOccs] using hnd)
      refine ⟨σ, by simpa [varOccs] using hkeys, ?_, hse⟩
      rw [← injNormal_of_not_inj hi]
      exact .inj hm
  theorem rowMatches_subst {vars : List Srt} {ps : List Term} {vs : List GroundTerm}
      (h : RowMatches c ps vs) {ss : List Srt} (ht : sortsOfTerms c.patCtxAll vars ps = some ss)
      (hv : c.sortsOf vs = some ss) (hnd : (varOccsList ps).Nodup) :
      ∃ σ : Subst, σ.map (·.1) = varOccsList ps ∧ PatVals c σ ps vs ∧ SortedEntries c vars σ :=
    match h with
    | .nil => ⟨[], by simp [varOccsList], .nil, fun _ he => nomatch he⟩
    | .cons (p := p) (ps := ps) h1 h2 => by
      obtain ⟨s, ss', ht1, ht2, rfl⟩ := sortsOfTerms_cons.mp ht
      obtain ⟨s₀, ss₀, hv1, hv2, he⟩ := sortsOf_cons.mp hv
      simp only [List.cons.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      simp only [varOccsList] at hnd ⊢
      have hnd' := List.nodup_append.mp hnd
      obtain ⟨σ₁, hk1, hm1, hs1⟩ := rowMatch_subst h1 ht1 hv1 hnd'.1
      obtain ⟨σ₂, hk2, hm2, hs2⟩ := rowMatches_subst h2 ht2 hv2 hnd'.2.1
      refine ⟨σ₁ ++ σ₂, by simp [hk1, hk2], .cons ?_ ?_, ?_⟩
      · exact NI.PatVal.congr hm1 fun j hj => lookup_append_of_mem σ₁ σ₂ (by rw [hk1]; exact hj)
      · exact NI.PatVals.congr hm2 fun j hj => lookup_append_of_not_mem σ₁ σ₂ (by
          rw [hk1]; exact fun hj' => hnd'.2.2 j hj' j hj rfl)
      · intro e he
        rcases List.mem_append.mp he with he | he
        · exact hs1 e he
        · exact hs2 e he
end

/-- **A covering row's match is a clause's match**: a clause with no `requires` and a `\top` premise, its pattern
variables apart, whose patterns match an argument list of the function's sorts as a row, applies
there. Each variable is bound at its one occurrence, to a value of its sort; every variable occurs
(`binds`), so the substitution is well sorted. -/
theorem applies_of_row {cl : Clause} {args : List Srt} {vs : List GroundTerm}
    (hpt : sortsOfTerms c.patCtxAll cl.vars cl.pats = some args)
    (hb : binds cl.vars.length (varOccsList cl.pats) = true) (hreq : cl.req = none) (hpre : cl.pre = .top)
    (hnd : (varOccsList cl.pats).Nodup) (hvs : c.sortsOf vs = some args)
    (hm : RowMatches c cl.pats vs) : ∃ σ, cl.AppliesAt c σ vs := by
  obtain ⟨σ, hk, hpv, hse⟩ := rowMatches_subst hm hpt hvs hnd
  refine ⟨σ, fun i _ s hi => ?_, hpv, (fun t ht => by rw [hreq] at ht; cases ht), Clause.holds_preTop hpre σ⟩
  have hlt : i < cl.vars.length := by
    rcases Nat.lt_or_ge i cl.vars.length with h | h
    · exact h
    · rw [List.getElem?_eq_none h] at hi; cases hi
  have hmem : i ∈ varOccsList cl.pats := by
    have := List.all_eq_true.mp hb i (List.mem_range.mpr hlt)
    exact List.contains_iff_mem.mp this
  obtain ⟨w, hw, he⟩ := lookup_of_mem_keys σ (by rw [hk]; exact hmem)
  obtain ⟨s', hs', hsw⟩ := hse _ he
  rw [hi] at hs'
  cases hs'
  exact ⟨w, hw, hsw⟩

/-- **A covering row's match is a clause's match** where each variable outside the patterns is of a
sort with a value: a clause with no `requires` and a `\top` premise, its pattern variables apart,
whose patterns match an argument list of the function's sorts as a row, applies there. Each pattern
variable is bound at its one occurrence, to a value of its sort; the substitution extends to the
other variables (`Clause.appliesAt_extendRH`). -/
theorem applies_of_rowRH {cl : Clause} {args : List Srt} {vs : List GroundTerm}
    (hh : c.HeldAt cl.vars cl.leftVars) (hpt : sortsOfTerms c.patCtxAll cl.vars cl.pats = some args)
    (hreq : cl.req = none) (hpre : cl.pre = .top)
    (hnd : (varOccsList cl.pats).Nodup) (hvs : c.sortsOf vs = some args)
    (hm : RowMatches c cl.pats vs) : ∃ σ, cl.AppliesAt c σ vs := by
  obtain ⟨σ, hk, hpv, hse⟩ := rowMatches_subst hm hpt hvs hnd
  have hcv : cl.condVars = [] := by simp [Clause.condVars, hreq, hpre, varOccsCond]
  have hσ : c.WellSortedAt cl.vars cl.leftVars σ := fun i hi s hs => by
    have hmem : i ∈ varOccsList cl.pats := by simpa [Clause.leftVars, hcv] using hi
    obtain ⟨w, hw, he⟩ := lookup_of_mem_keys σ (by rw [hk]; exact hmem)
    obtain ⟨s', hs', hsw⟩ := hse _ he
    rw [hs] at hs'
    cases hs'
    exact ⟨w, hw, hsw⟩
  obtain ⟨σ', ha, -⟩ := Clause.appliesAt_extendRH hh hσ hpv (fun t ht => by rw [hreq] at ht; cases ht)
    (Clause.holds_preTop hpre σ)
  exact ⟨σ', ha⟩

/-! ## A total term has a value -/

/-- A call `g(ts)` under σ has a value: where the arguments have values `vs` of the argument
sorts of the function `g`, `g` has a value at `vs`. -/
def CallDefined (c : Semantics) (σ : Subst) (g : Sym) (ts : List Term) : Prop :=
  ∀ gfn, c.lookupFn g = some gfn → ∀ vs, EvalTerms c σ ts (vs.map some) →
    c.sortsOf vs = some gfn.args → ∃ v, Eval c g vs (some v)

theorem isParam_false_of {f : Sym} (h : c.params.any (·.sig.name == f) = false) :
    c.isParam f = false := by
  unfold Semantics.isParam
  rw [Semantics.lookupParam_eq]
  cases hf : c.params.find? (·.sig.name == f) with
  | none => rfl
  | some k =>
    have := List.any_eq_true.mpr ⟨k, List.mem_of_find?_eq_some hf, List.find?_some hf⟩
    rw [h] at this; cases this

mutual
  /-- A right-hand side well sorted over the heads `L` that `totalTerm` accepts over `tot` has a
  value under a well-sorted σ, where each of its calls of a function of `tot` has one; the
  interpreted symbols it admits have one at values of their sorts (`hook_total`, `shapesOK`). -/
  theorem evalTerm_defined (hc : SortCtx c) (hs : c.shapesOK = true) {L : List CtorSig}
      (hL : HeadsOK c L) {vars : List Srt} {σ : Subst} (hσ : c.WellSorted vars σ) {tot : List Sym} :
      ∀ (t : Term) {s : Srt}, sortOfTerm (c.rhsCtx L) vars t = some s → c.totalTerm tot t = true →
        (∀ g ts, ts ∈ callsOf g t → tot.contains g = true → CallDefined c σ g ts) →
          ∃ v, EvalTerm c σ t (some v)
    | .var i, s, ht, _, _ => by
      obtain ⟨v, hv, _⟩ := hσ i s (sortOfTerm_var.mp ht)
      exact ⟨v, hv ▸ EvalTerm.var⟩
    | .dv _ _, _, _, _, _ => ⟨_, EvalTerm.dv⟩
    | .inj _ _ t, _, ht, htt, hcall => by
      obtain ⟨_, ht', _⟩ := sortOfTerm_inj.mp ht
      obtain ⟨v, hv⟩ := evalTerm_defined hc hs hL hσ t ht' (by simpa [Semantics.totalTerm] using htt)
        (fun g ts h => hcall g ts (by simpa [callsOf] using h))
      exact ⟨_, EvalTerm.inj hv⟩
    | .as _ _, _, _, htt, _ => by simp [Semantics.totalTerm] at htt
    | .app f ts, _, ht, htt, hcall => by
      simp only [Semantics.totalTerm, Bool.and_eq_true, Bool.or_eq_true] at htt
      obtain ⟨hhead, hargs'⟩ := htt
      obtain ⟨k, hk', hargs, rfl⟩ := sortOfTerm_app.mp ht
      obtain ⟨vs, hts⟩ := evalTerms_defined hc hs hL hσ ts hargs hargs' (fun g us h =>
        hcall g us (by simp only [callsOf, List.mem_append]; exact Or.inr h))
      have hall := allSome_map_some vs
      have hsrt := EvalTerms.sorted hc hts hL hσ hargs hall
      cases hct : c.isCtor f
      · have hnc : lookupSig c.ctorSigs f = none :=
          Option.not_isSome_iff_eq_none.mp (by simpa [Semantics.isCtor] using hct)
        have hnc' : (lookupSig c.ctorSigs f).isSome = false := by rw [hnc]; rfl
        simp only [Semantics.rhsCtx, List.append_assoc] at hk'
        rw [lookupSig_append_of_none hnc] at hk'
        cases hhk : isHook f
        · have hnh : hookSigs.any (·.name == f) = false := by
            cases h : hookSigs.any (·.name == f)
            · rfl
            · rw [← isHook_iff] at h; rw [hhk] at h; cases h
          rcases hhead with (h1 | ⟨h1, _⟩) | ⟨⟨⟨htc, _⟩, hnp⟩, hno⟩
          · rw [hnc'] at h1; cases h1
          · rw [hnh] at h1; cases h1
          have hpar : c.isParam f = false := isParam_false_of (by simpa using hnp)
          cases hov : c.isOvl f with
          | true =>
            -- `totalTerm` admits no overloading symbol as a function of `tot`
            have hsome := (c.isOvl_parts hov).2.2.2.2
            rw [Option.isNone_iff_eq_none.mp hno] at hsome
            exact absurd hsome (by simp)
          | false =>
          rw [lookupSig_append_of_none (lookupSig_hookSigs_of_not_isHook hhk),
            lookupSig_append_of_none (c.lookupSig_params_of_not hpar)] at hk'
          obtain ⟨hkL, hkn⟩ := lookupSig_spec (lookup_drop_ovls (lookupOvl_none_of hc hov) hk')
          obtain ⟨fn, hfn, rfl⟩ := headsOK_preds hL k hkL
          have hlook : c.lookupFn f = some fn := by
            rw [← hkn, Semantics.lookupFn_eq]; exact find?_label hc.nodupFns hfn
          obtain ⟨v, hv⟩ := hcall f ts (by simp [callsOf]) htc fn hlook vs hts hsrt
          exact ⟨v, EvalTerm.call hct hhk hts hall hv hpar⟩
        · have hh : hookSigs.any (·.name == f) = true := (isHook_iff f).mp hhk
          have hhead : partialHooks.contains f = false := by
            rcases hhead with (h1 | ⟨_, hpart⟩) | ⟨⟨⟨_, h1⟩, _⟩, _⟩
            · rw [hnc'] at h1; cases h1
            · simpa using hpart
            · rw [hh] at h1; cases h1
          obtain ⟨k₀, hk₀⟩ := lookupSig_hookSigs_of_isHook hhk
          rw [lookupSig_append_of_some hk₀] at hk'
          have hkk : k₀ = k := Option.some.inj hk'
          subst hkk
          obtain ⟨hmem, hname⟩ := lookupSig_spec hk₀
          obtain ⟨v, hv⟩ := hook_total hs k₀ hmem (by rw [hname]; exact hhead) vs hsrt
          rw [hname] at hv
          exact ⟨v, EvalTerm.hook hct hhk hts (fun ws h => by rw [hall] at h; cases h; exact Semantics.hookRes_of_value hv)
            (fun h => by rw [hall] at h; cases h)⟩
      · have := EvalTerm.ctor (c := c) (σ := σ) hct hts
        rw [hall] at this
        exact ⟨_, this⟩
  theorem evalTerms_defined (hc : SortCtx c) (hs : c.shapesOK = true) {L : List CtorSig}
      (hL : HeadsOK c L) {vars : List Srt} {σ : Subst} (hσ : c.WellSorted vars σ) {tot : List Sym} :
      ∀ (ts : List Term) {ss : List Srt}, sortsOfTerms (c.rhsCtx L) vars ts = some ss →
        c.totalTermList tot ts = true →
        (∀ g us, us ∈ callsOfList g ts → tot.contains g = true → CallDefined c σ g us) →
          ∃ vs : List GroundTerm, EvalTerms c σ ts (vs.map some)
    | [], _, _, _, _ => ⟨[], EvalTerms.nil⟩
    | t :: ts, _, hts, htt, hcall => by
      obtain ⟨_, _, ht, hts', rfl⟩ := sortsOfTerms_cons.mp hts
      simp only [Semantics.totalTermList, Bool.and_eq_true] at htt
      obtain ⟨v, hv⟩ := evalTerm_defined hc hs hL hσ t ht htt.1 (fun g us h =>
        hcall g us (by simp only [callsOfList, List.mem_append]; exact Or.inl h))
      obtain ⟨vs, hvs⟩ := evalTerms_defined hc hs hL hσ ts hts' htt.2 (fun g us h =>
        hcall g us (by simp only [callsOfList, List.mem_append]; exact Or.inr h))
      exact ⟨v :: vs, EvalTerms.cons hv hvs⟩
end

/-! ## A function with total clauses is total -/

/-- As `eval_result`, with values: the right-hand sides of the clauses that apply have values, no
clause has an `ensures`, an existential variable or a right side's predicate other than `\top`,
and a clause without `requires` applies (one that cannot fail), so some clause applies. -/
theorem eval_defined {f : Sym} {fn : Fn} (hfn : c.lookupFn f = some fn) {vs : List GroundTerm}
    (hx : ∀ cl ∈ fn.clauses, cl.exs = [] ∧ cl.post = .top)
    (hh : ∀ cl ∈ fn.clauses, c.HeldAt cl.vars cl.leftVars)
    (hreq : ∀ cl ∈ fn.clauses, ∀ σ, c.WellSorted cl.vars σ → PatVals c σ cl.pats vs →
      (∀ t, cl.req = some t → ∃ r, EvalTerm c σ t r) ∧ ∃ b, Holds c cl.vars.length σ cl.pre b)
    (hrhs : ∀ cl ∈ fn.clauses, ∀ σ, cl.AppliesAt c σ vs → ∃ v, EvalTerm c σ cl.rhs (some v))
    (hcov : ∃ cl ∈ fn.clauses, cl.req = none ∧ ∃ σ, cl.AppliesAt c σ vs)
    (hnoens : ∀ cl ∈ fn.clauses, cl.ens = none) :
    ∃ v, Eval c f vs (some v) := by
  have hfail : ∀ cl ∈ fn.clauses, (¬ ∃ σ, cl.AppliesAt c σ vs) → Fails c vs cl := fun cl hcl hna =>
    Clause.fails_of_not_appliesRH (hh cl hcl) (hreq cl hcl) hna
  have key : ∀ n p, p < n → (∃ cl ∈ fn.clauses, cl.prio = p ∧ ∃ σ, cl.AppliesAt c σ vs) →
      ∃ v, Eval c f vs (some v) := by
    intro n
    induction n with
    | zero => intro p hp; omega
    | succ n ih =>
      intro p hp ⟨cl, hcl, hpr, σ, hσu, hm, hq, hp'⟩
      have hσ : c.WellSorted cl.vars σ := (wellSortedAt_univ (hx cl hcl).1).mp hσu
      by_cases hlow : ∃ cl' ∈ fn.clauses, cl'.prio < p ∧ ∃ σ', cl'.AppliesAt c σ' vs
      · obtain ⟨cl', hcl', hlt, ha⟩ := hlow
        exact ih cl'.prio (by omega) ⟨cl', hcl', rfl, ha⟩
      · obtain ⟨v, hv⟩ := hrhs cl hcl σ ⟨hσu, hm, hq, hp'⟩
        exact ⟨v, Eval.clause hfn hcl hσ hm hq hp' (fun cl' hcl' _ hlt =>
          hfail cl' hcl' fun ha => hlow ⟨cl', hcl', by omega, ha⟩) (hx cl hcl).1 hv
          (fun t ht => by rw [hnoens cl hcl] at ht; cases ht) (Clause.holds_postTop (hx cl hcl).2 σ)⟩
  obtain ⟨cl, hcl, _, ha⟩ := hcov
  exact key (cl.prio + 1) cl.prio (by omega) ⟨cl, hcl, rfl, ha⟩

/-- The `requires` of a clause have a result at each of its matches, every function terminating. -/
theorem req_resultN (hc : EvalCtxN c) (hterm : ∀ g, Terminates c g) {fn : Fn} (hfn : fn ∈ c.allFns)
    {cl : Clause} (hcl : cl ∈ fn.clauses) {σ : Subst} (hσ : c.WellSorted cl.vars σ) {t : Term}
    (ht : cl.req = some t) : ∃ r, EvalTerm c σ t r := by
  obtain ⟨L', hL', hreqs⟩ := hc.reqs fn hfn
  have hq := hreqs cl hcl
  rw [ht] at hq
  simp only [reqOK, beq_iff_eq] at hq
  exact evalTerm_result hc.sort hL' hσ t hq (fun _ _ _ _ kg _ _ => hterm kg.name)
    fun g _ _ gfn hg _ vs' _ _ hsrt => hterm g gfn hg vs' hsrt

/-- The `requires` of a clause have a result at each of its matches, every function terminating. -/
theorem req_result (hc : EvalCtx c) (hterm : ∀ g, Terminates c g) {fn : Fn} (hfn : fn ∈ c.allFns)
    {cl : Clause} (hcl : cl ∈ fn.clauses) {σ : Subst} (hσ : c.WellSorted cl.vars σ) {t : Term}
    (ht : cl.req = some t) : ∃ r, EvalTerm c σ t r :=
  req_resultN hc.toN hterm hfn hcl hσ ht

/-- **The sort predicates are total**: their clauses have no `requires` and Bool literals as
right-hand sides, and each has a clause over a variable of sort K, which applies at every K. -/
theorem sortPreds_totalN (hc : EvalCtxN c) {fn : Fn} (hfn : fn ∈ c.sortPreds) : Total c fn.label := by
  have hmem : fn ∈ c.allFns := List.mem_append_right _ hfn
  intro fn' hfn' vs hvs
  rw [lookupFn_of_memN hc hmem] at hfn'
  cases hfn'
  have hfacts : fn.args = [Srt.k] ∧ (∀ cl ∈ fn.clauses, cl.req = none ∧ ∃ s l, cl.rhs = .dv s l) ∧
      ∃ cl ∈ fn.clauses, cl.vars = [Srt.k] ∧ cl.pats = [.var 0] ∧ cl.req = none := by
    simp only [Semantics.sortPreds, List.cons_append, List.nil_append, List.mem_cons,
      List.mem_filterMap, Option.map_eq_some_iff] at hfn
    rcases hfn with rfl | rfl | ⟨X, _, _, _, rfl⟩
    · refine ⟨rfl, fun cl hcl => ?_, { vars := [Srt.k], pats := [.var 0], req := none, rhs := .dv Srt.bool (.bool true), ens := none, prio := 50 },
        List.mem_singleton_self _, rfl, rfl, rfl⟩
      simp only [List.mem_singleton] at hcl
      subst hcl
      exact ⟨rfl, _, _, rfl⟩
    · refine ⟨rfl, fun cl hcl => ?_, { vars := [Srt.k], pats := [.var 0], req := none, rhs := .dv Srt.bool (.bool false), ens := none, prio := 200 },
        by simp, rfl, rfl, rfl⟩
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hcl
      rcases hcl with rfl | rfl <;> exact ⟨rfl, _, _, rfl⟩
    · refine ⟨rfl, fun cl hcl => ?_, { vars := [Srt.k], pats := [.var 0], req := none, rhs := .dv Srt.bool (.bool false), ens := none, prio := 200 },
        by simp, rfl, rfl, rfl⟩
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hcl
      rcases hcl with rfl | rfl <;> exact ⟨rfl, _, _, rfl⟩
  obtain ⟨hargs, hshape, cl₀, hcl₀, hv₀, hp₀, hr₀⟩ := hfacts
  rw [hargs] at hvs
  obtain ⟨w, rfl, hw⟩ := sortsOf_one hvs
  have hσ : c.WellSorted cl₀.vars [(0, w)] := by
    rw [hv₀]
    intro i s hi
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
      subst hi
      exact ⟨w, lookup_cons_self _ _ _, hw⟩
    | succ i => simp at hi
  refine eval_defined (lookupFn_of_memN hc hmem) (hc.plain fn hmem)
    (fun cl hcl => Semantics.heldAt_of_bindsRH (Semantics.sortPreds_binds hfn cl hcl))
    (fun cl hcl σ _ _ => ⟨(fun t ht => by rw [(hshape cl hcl).1] at ht; cases ht), true,
      Clause.holds_preTop (Semantics.sortPreds_pre hfn cl hcl) σ⟩)
    (fun cl hcl _ _ => by obtain ⟨_, s, l, h⟩ := hshape cl hcl; rw [h]; exact ⟨_, EvalTerm.dv⟩)
    ⟨cl₀, hcl₀, hr₀, [(0, w)], hσ.at _, by rw [hp₀]; exact .cons (.var (lookup_cons_self _ _ _)) .nil,
      (fun t ht => by rw [hr₀] at ht; cases ht), Clause.holds_preTop (Semantics.sortPreds_pre hfn cl₀ hcl₀) _⟩ (sortPreds_ens hfn)

theorem sortPreds_total (hc : EvalCtx c) {fn : Fn} (hfn : fn ∈ c.sortPreds) : Total c fn.label :=
  sortPreds_totalN hc.toN hfn

theorem mem_coverRows {fn : Fn} {r : List Term} (h : r ∈ Semantics.coverRows fn) :
    ∃ cl ∈ fn.clauses, cl.req = none ∧ (varOccsList cl.pats).Nodup ∧ cl.pats = r := by
  simp only [Semantics.coverRows, List.mem_map, List.mem_filter, Bool.and_eq_true, Option.isNone_iff_eq_none] at h
  obtain ⟨cl, ⟨hcl, hreq, hnd⟩, rfl⟩ := h
  exact ⟨cl, hcl, hreq, nodup_of_eq_true hnd, rfl⟩

/-- **A function whose clauses are total is total**: its right-hand sides are total over `tot`,
whose functions but itself are total; its self calls decrease; its covering rows cover its argument
sorts. By induction on the size of the decreasing argument. The held variables are read of this function alone (`hb`). -/
theorem total_of_partsN (hc : EvalCtxN c) (hs : c.shapesOK = true) (hterm : ∀ g, Terminates c g)
    {fn : Fn} (hfn : fn ∈ c.allFns) (hb : c.HeldFn fn)
    (hclk : ∀ cl ∈ fn.clauses, sortsOfTerms c.patCtxAll cl.vars cl.pats = some fn.args ∧ cl.pre = .top)
    {dec : Option Nat} (hdec : decreasingOK c fn dec = true) {n : Nat}
    (hcov : c.covers n fn.args (Semantics.coverRows fn) = true) {tot : List Sym}
    (hrhs : ∀ cl ∈ fn.clauses, c.totalTerm tot cl.rhs = true)
    (hnoens : ∀ cl ∈ fn.clauses, cl.ens = none)
    (htot : ∀ g ∈ tot, g ≠ fn.label → Total c g) : Total c fn.label := by
  have hlook := lookupFn_of_memN hc hfn
  obtain ⟨L, hL, hrs⟩ := hc.sort.fns fn hfn
  intro fn' hfn' vs hvs
  rw [hlook] at hfn'
  cases hfn'
  suffices h : ∀ m vs, c.sortsOf vs = some fn.args → decMeasure dec vs < m →
      ∃ v, Eval c fn.label vs (some v) from h _ vs hvs (Nat.lt_succ_self _)
  intro m
  induction m with
  | zero => intro _ _ h; exact absurd h (Nat.not_lt_zero _)
  | succ m ih =>
    intro vs hvs hlt
    refine eval_defined hlook (hc.plain fn hfn) hb (fun cl hcl σ hσ _ => ⟨fun t ht => req_resultN hc hterm hfn hcl hσ ht, true,
        Clause.holds_preTop (hclk cl hcl).2 σ⟩)
      (fun cl hcl σ ha => ?_) ?_ hnoens
    · refine evalTerm_defined hc.sort hs hL ((wellSortedAt_univ (hc.plain fn hfn cl hcl).1).mp ha.1) cl.rhs (hrs cl hcl) (hrhs cl hcl)
        fun g ts hts hgt gfn hg vs' hts' hsrt => ?_
      by_cases hgl : g = fn.label
      · subst hgl
        rw [hlook] at hg
        cases hg
        obtain ⟨i, j, p, rfl, hti, hpi, hsi⟩ := decreasingOK_clause hdec hcl (Or.inl rfl) hts
        obtain ⟨v, hvi, hpv⟩ := patVals_get ha.2.1 hpi
        obtain ⟨w, hw, hwv⟩ := strictlyIn_size p hpv hsi
        have hvi' : vs'[i]? = some w := (evalTerms_var hts' hti (allSome_map_some vs')).trans hw
        refine ih vs' hsrt ?_
        have h1 : decMeasure (some i) vs' = w.size := by simp [decMeasure, hvi']
        have h2 : decMeasure (some i) vs = v.size := by simp [decMeasure, hvi]
        omega
      · exact htot g (List.contains_iff_mem.mp hgt) hgl gfn hg vs' hsrt
    · have htyped : ∀ r ∈ Semantics.coverRows fn, ∃ vars, RowTyped c vars fn.args r := by
        intro r hr
        obtain ⟨cl, hcl, _, _, rfl⟩ := mem_coverRows hr
        exact ⟨cl.vars, rowTyped_of_sorts (hclk cl hcl).1⟩
      obtain ⟨r, hr, hm⟩ := covers_sound n fn.args _ hcov htyped vs hvs
      obtain ⟨cl, hcl, hreq, hnd, rfl⟩ := mem_coverRows hr
      exact ⟨cl, hcl, hreq, applies_of_rowRH (hb cl hcl) (hclk cl hcl).1 hreq (hclk cl hcl).2 hnd hvs hm⟩

/-- **A function whose clauses are total is total**: its right-hand sides are total over `tot`,
whose functions but itself are total; its self calls decrease; its covering rows cover its argument
sorts. By induction on the size of the decreasing argument. -/
theorem total_of_parts (hc : EvalCtx c) (hs : c.shapesOK = true) (hterm : ∀ g, Terminates c g)
    {fn : Fn} (hfn : fn ∈ c.allFns)
    (hclk : ∀ cl ∈ fn.clauses, sortsOfTerms c.patCtxAll cl.vars cl.pats = some fn.args ∧ cl.pre = .top)
    {dec : Option Nat} (hdec : decreasingOK c fn dec = true) {n : Nat}
    (hcov : c.covers n fn.args (Semantics.coverRows fn) = true) {tot : List Sym}
    (hrhs : ∀ cl ∈ fn.clauses, c.totalTerm tot cl.rhs = true)
    (hnoens : ∀ cl ∈ fn.clauses, cl.ens = none)
    (htot : ∀ g ∈ tot, g ≠ fn.label → Total c g) : Total c fn.label :=
  total_of_partsN hc.toN hs hterm hfn (hc.binds fn hfn) hclk hdec hcov hrhs hnoens htot

/-- **A function `totalOK` confirms is total**, in a core that `sortedOK` and `srReady` accept
whose clauses' variables are held (`RightHeld`), every function terminating and the total functions before it total. -/
theorem total_of_totalOK (hpreTop : c.clausesPreTop = true) (hok : c.sortedOK = true) (hsr : c.srReady = true) (hov : c.OvlCase)
    (hrh : c.RightHeld)
    (hterm : ∀ g, Terminates c g) {fn : Fn} (hfn : fn ∈ c.fns) (hT : c.totalOK fn = true)
    (htot : ∀ g ∈ c.totalBefore fn, Total c g) : Total c fn.label := by
  have hc := evalCtx_of_all (hpreTop := hpreTop) hok hsr hov hrh
  simp only [Semantics.totalOK, Bool.and_eq_true, Bool.or_eq_true, List.all_eq_true] at hT
  obtain ⟨⟨⟨⟨hs, hdec⟩, hcov⟩, hrhs⟩, hne⟩ := hT
  have hfok : ∀ cl ∈ fn.clauses, c.clauseSorted fn (c.fns.map Fn.sig) cl = true := by
    replace hok := Semantics.sortedOK_sorted hok
    simp only [Bool.and_eq_true, List.all_eq_true] at hok
    exact hok.1.2 fn hfn
  refine total_of_parts hc hs hterm (List.mem_append_left _ hfn) (fun cl hcl => ?_) hdec
    (n := Semantics.coverFuel fn) hcov hrhs (fun cl hcl => by simpa using hne cl hcl) (fun g hg hgl => ?_)
  · have := hfok cl hcl
    simp only [Semantics.clauseSorted, Bool.and_eq_true, beq_iff_eq] at this
    replace this := this.1
    exact ⟨this.1.1.1.1.1, Semantics.clausesPreTop_spec hpreTop hfn hcl⟩
  · simp only [List.mem_append, List.mem_map, List.mem_singleton] at hg
    rcases hg with (hg | ⟨p, hp, rfl⟩) | hg
    · exact htot g hg
    · exact sortPreds_total hc hp
    · exact absurd hg hgl

theorem mem_takeWhile_lt {α : Type} {p : α → Bool} : ∀ {l : List α} {n : Nat} {y x : α},
    l[n]? = some y → p y = false → x ∈ l.takeWhile p → ∃ m < n, l[m]? = some x
  | [], _, _, _, h, _, _ => by simp at h
  | a :: l, 0, y, x, h, hp, hx => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    simp [List.takeWhile, hp] at hx
  | a :: l, n + 1, y, x, h, hp, hx => by
    simp only [List.takeWhile] at hx
    split at hx
    · rcases List.mem_cons.mp hx with rfl | hx
      · exact ⟨0, by omega, rfl⟩
      · obtain ⟨m, hm, hl⟩ := mem_takeWhile_lt (l := l) (by simpa using h) hp hx
        exact ⟨m + 1, by omega, by simpa using hl⟩
    · cases hx

/-- **Every function declared `[total]` is total**, in a core that `sortedOK` and `srReady` accept
whose clauses' variables are held (`RightHeld`), every function terminating, given the named ones
(`totalObligations`): by induction on the position in the declaration order, a function `totalOK`
confirms is total where the total functions before it are (`total_of_totalOK`); the sort predicates
are total. -/
theorem totals_of_order_core (hpreTop : c.clausesPreTop = true) (hok : c.sortedOK = true) (hsr : c.srReady = true) (hov : c.OvlCase)
    (hrh : c.RightHeld) (hterm : ∀ g, Terminates c g)
    (hnamed : ∀ g ∈ c.totalObligations, Total c g) :
    ∀ f fn, c.lookupFn f = some fn → fn.total = true → Total c f := by
  have hc := evalCtx_of_all (hpreTop := hpreTop) hok hsr hov hrh
  have pos : ∀ (n : Nat) (fn : Fn), c.fns[n]? = some fn → fn.total = true → Total c fn.label := by
    intro n
    induction n using Nat.strongRecOn with
    | _ n ih =>
      intro fn hn htot
      have hmem : fn ∈ c.fns := List.mem_of_getElem? hn
      by_cases hN : fn.label ∈ c.totalObligations
      · exact hnamed _ hN
      have hT : c.totalOK fn = true := by
        cases h : c.totalOK fn
        · exact absurd (List.mem_map.mpr ⟨fn, List.mem_filter.mpr ⟨hmem, by simp [htot, h]⟩, rfl⟩) hN
        · rfl
      refine total_of_totalOK (hpreTop := hpreTop) hok hsr hov hrh hterm hmem hT fun g hg => ?_
      simp only [Semantics.totalBefore, List.mem_map, List.mem_filter] at hg
      obtain ⟨gfn, ⟨hgw, hgt⟩, rfl⟩ := hg
      obtain ⟨m, hm, hgm⟩ := mem_takeWhile_lt hn (by simp) hgw
      exact ih m hm gfn hgm hgt
  intro f fn hfn htot
  obtain ⟨hgm, hlab⟩ := lookupFn_spec hfn
  subst hlab
  rcases List.mem_append.mp hgm with hu | hp
  · obtain ⟨n, hn, rfl⟩ := List.getElem_of_mem hu
    exact pos n _ (List.getElem?_eq_getElem hn) htot
  · exact sortPreds_total hc hp

/-- `totals_of_order_core` in a core that `okAll` accepts. -/
theorem totals_of_order (hok : c.okAll = true) (hsr : c.srReady = true) (hov : c.OvlCase)
    (hterm : ∀ g, Terminates c g) (hnamed : ∀ g ∈ c.totalObligations, Total c g)
    (hrh : c.RightHeld := by exact Semantics.rightHeld_of_valued (by decide +kernel)) :
    ∀ f fn, c.lookupFn f = some fn → fn.total = true → Total c f :=
  have hpreTop := Semantics.preTop_of_okAll hok
  totals_of_order_core (hpreTop := hpreTop) (Semantics.sortedOK_of_okAll hok) hsr hov hrh hterm hnamed

/-- With no `[total]` function named, every one is total. -/
theorem totals_of_nil (hok : c.okAll = true) (hsr : c.srReady = true) (hov : c.OvlCase)
    (hterm : ∀ g, Terminates c g) (h : c.totalObligations = []) (hrh : c.RightHeld := by exact Semantics.rightHeld_of_valued (by decide +kernel)) :
    ∀ f fn, c.lookupFn f = some fn → fn.total = true → Total c f :=
  have hpreTop := Semantics.preTop_of_okAll hok
  totals_of_order hok hsr hov hterm (fun g hg => by rw [h] at hg; exact absurd hg List.not_mem_nil) hrh

kernel_rfl Semantics.totalObligations_withHooks :
  ∀ (c : Semantics) (H : HookParams), (c.withHooks H).totalObligations = c.totalObligations

/-- `totals_of_order` for every interpretation of the parameters, of a semantics without an open
generator (`hr`). -/
theorem totals_of_order_withHooks (hok : c.okAll = true) (hsr : c.srReady = true) (hov : c.OvlCase)
    (H : HookParams)
    (hterm : ∀ g, Terminates (c.withHooks H) g)
    (hnamed : ∀ g ∈ c.totalObligations, Total (c.withHooks H) g)
    (hrh : c.RightHeld := by exact Semantics.rightHeld_of_valued (by decide +kernel))
    (hr : ∀ k ∈ c.params, k.raw = false := by decide +kernel) :
    ∀ f fn, (c.withHooks H).lookupFn f = some fn → fn.total = true → Total (c.withHooks H) f :=
  have hpreTop := Semantics.preTop_of_okAll hok
  totals_of_order ((Semantics.okAll_withHooks c H).trans hok) ((Semantics.srReady_withHooks c H).trans hsr)
    (Semantics.ovlCase_withHooks hov H) hterm (by rw [Semantics.totalObligations_withHooks]; exact hnamed)
    (Semantics.rightHeld_withHooks hrh H hr)

/-- `totals_of_nil` for every interpretation of the parameters, of a semantics without an open
generator (`hr`). -/
theorem totals_of_nil_withHooks (hok : c.okAll = true) (hsr : c.srReady = true) (hov : c.OvlCase)
    (H : HookParams)
    (hterm : ∀ g, Terminates (c.withHooks H) g) (h : c.totalObligations = [])
    (hrh : c.RightHeld := by exact Semantics.rightHeld_of_valued (by decide +kernel))
    (hr : ∀ k ∈ c.params, k.raw = false := by decide +kernel) :
    ∀ f fn, (c.withHooks H).lookupFn f = some fn → fn.total = true → Total (c.withHooks H) f :=
  have hpreTop := Semantics.preTop_of_okAll hok
  totals_of_order_withHooks hok hsr hov H hterm (fun g hg => by rw [h] at hg; exact absurd hg List.not_mem_nil) hrh hr

/-! ## For a semantics: from `coreOK` and `CoreObligations` -/

section Core

variable {t : Certificates}

/-- **Every function declared `[total]` is total**, under `coreOK`, `RightHeld` (each clause's
variables in its patterns or conditions or of a sort with a value) and `CoreObligations` (its first
two conjuncts: the named functions terminate, the named `[total]` functions are total). Stated for
every function `lookupFn` finds, the sort predicates among them. -/
theorem CoreObligations.totals (hpreTop : c.clausesPreTop = true) (h : c.coreOK = true) (hrh : c.RightHeld) (hob : CoreObligations c t) :
    ∀ f fn, c.lookupFn f = some fn → fn.total = true → Total c f := by
  obtain ⟨hok, -, -, hp, hids⟩ := Semantics.coreOK_parts h
  exact totals_of_order_core (hpreTop := hpreTop) hok (NamesApart.srReady_of hp hids hok
    (NamesApart.rangeKeys_genWf_of_faithCore (Semantics.coreOK_parts h).2.1) (Semantics.coreOK_ovls h)) (Semantics.ovlCase_of_core h) hrh
    (CoreObligations.terminates (hpreTop := hpreTop) h hrh hob) hob.2.1

/-- `TotalsDefined` (LazySound.lean), from `coreOK` and `CoreObligations`. -/
theorem CoreObligations.totalsDefined (hpreTop : c.clausesPreTop = true) (h : c.coreOK = true) (hrh : c.RightHeld) (hob : CoreObligations c t) :
    c.TotalsDefined :=
  fun f fn hfn ht vs hvs => CoreObligations.totals (hpreTop := hpreTop) h hrh hob
    f fn hfn ht fn hfn vs hvs

/-- `definedArg_sound` from `coreOK` and `CoreObligations`. -/
theorem CoreObligations.definedArg_sound (hpreTop : c.clausesPreTop = true) (h : c.coreOK = true) (hrh : c.RightHeld) (hob : CoreObligations c t)
    {vars : List Srt} {u : Term} (hd : c.definedArg vars u = true) {σ : Subst}
    (hσ : c.WellSorted vars σ) : ∃ v, EvalTerm c σ u (some v) := by
  obtain ⟨hok, -, -, hp, hids⟩ := Semantics.coreOK_parts h
  exact c.definedArg_sound hok (NamesApart.srReady_of hp hids hok
    (NamesApart.rangeKeys_genWf_of_faithCore (Semantics.coreOK_parts h).2.1) (Semantics.coreOK_ovls h)) (Semantics.ovlCase_of_core h)
    (CoreObligations.totalsDefined (hpreTop := hpreTop) h hrh hob) hd hσ

/-- `LazyOcc.holds_of_definedArg` from `coreOK` and `CoreObligations`. -/
theorem CoreObligations.holds_of_definedArg (hpreTop : c.clausesPreTop = true) (h : c.coreOK = true) (hrh : c.RightHeld) (hob : CoreObligations c t)
    {o : LazyOcc} (ho : o ∈ c.lazyOccs) (hd : c.definedArg o.vars o.skipped = true) : o.Holds c := by
  obtain ⟨hok, -, -, hp, hids⟩ := Semantics.coreOK_parts h
  exact LazyOcc.holds_of_definedArg hok (NamesApart.srReady_of hp hids hok
    (NamesApart.rangeKeys_genWf_of_faithCore (Semantics.coreOK_parts h).2.1) (Semantics.coreOK_ovls h)) (Semantics.ovlCase_of_core h)
    (CoreObligations.totalsDefined (hpreTop := hpreTop) h hrh hob) ho hd

/-- `lazyOccs_hold` from `coreOK` and `CoreObligations`: every occurrence meets its obligation. -/
theorem CoreObligations.lazyOccs_hold (hpreTop : c.clausesPreTop = true) (h : c.coreOK = true) (hrh : c.RightHeld) (hob : CoreObligations c t) :
    ∀ o ∈ c.lazyOccs, o.Holds c := by
  obtain ⟨hok, -, -, hp, hids⟩ := Semantics.coreOK_parts h
  exact KCore.lazyOccs_hold hok (NamesApart.srReady_of hp hids hok
    (NamesApart.rangeKeys_genWf_of_faithCore (Semantics.coreOK_parts h).2.1) (Semantics.coreOK_ovls h)) (Semantics.ovlCase_of_core h)
    (CoreObligations.totalsDefined (hpreTop := hpreTop) h hrh hob) hob.2.2.2.2.1

end Core

/-! ## For a definition: from `wf` and `Obligations` -/

/-- **Every function declared `[total]` is total**, under `wf` and `Obligations` (its first two
conjuncts: the named functions terminate, the named `[total]` functions are total). Stated for
every function `lookupFn` finds, the sort predicates among them. -/
theorem Obligations.totals {d : Definition} (hwf : wf d = true) (hrh : d.sem.RightHeld) (hob : Obligations d) :
    ∀ f fn, d.sem.lookupFn f = some fn → fn.total = true → Total d.sem f :=
  have hpreTop := Semantics.preTop_of_okAll (NamesApart.wf_parts hwf).2.2.2
  CoreObligations.totals (hpreTop := hpreTop) (Definition.coreOK_of_wf hwf) hrh hob

/-- `TotalsDefined` (LazySound.lean), from `wf` and `Obligations`. -/
theorem Obligations.totalsDefined {d : Definition} (hwf : wf d = true) (hrh : d.sem.RightHeld) (hob : Obligations d) :
    d.sem.TotalsDefined :=
  have hpreTop := Semantics.preTop_of_okAll (NamesApart.wf_parts hwf).2.2.2
  CoreObligations.totalsDefined (hpreTop := hpreTop) (Definition.coreOK_of_wf hwf) hrh hob

/-- `definedArg_sound` from `wf` and `Obligations`. -/
theorem Obligations.definedArg_sound {d : Definition} (hwf : wf d = true) (hrh : d.sem.RightHeld) (hob : Obligations d)
    {vars : List Srt} {t : Term} (hd : d.sem.definedArg vars t = true) {σ : Subst}
    (hσ : d.sem.WellSorted vars σ) : ∃ v, EvalTerm d.sem σ t (some v) :=
  have hpreTop := Semantics.preTop_of_okAll (NamesApart.wf_parts hwf).2.2.2
  CoreObligations.definedArg_sound (hpreTop := hpreTop) (Definition.coreOK_of_wf hwf) hrh hob hd hσ

/-- `LazyOcc.holds_of_definedArg` from `wf` and `Obligations`. -/
theorem Obligations.holds_of_definedArg {d : Definition} (hwf : wf d = true) (hrh : d.sem.RightHeld) (hob : Obligations d)
    {o : LazyOcc} (ho : o ∈ d.sem.lazyOccs) (hd : d.sem.definedArg o.vars o.skipped = true) :
    o.Holds d.sem :=
  have hpreTop := Semantics.preTop_of_okAll (NamesApart.wf_parts hwf).2.2.2
  CoreObligations.holds_of_definedArg (hpreTop := hpreTop) (Definition.coreOK_of_wf hwf) hrh hob ho hd

/-- `lazyOccs_hold` from `wf` and `Obligations`: every occurrence meets its obligation. -/
theorem Obligations.lazyOccs_hold {d : Definition} (hwf : wf d = true) (hrh : d.sem.RightHeld) (hob : Obligations d) :
    ∀ o ∈ d.sem.lazyOccs, o.Holds d.sem :=
  have hpreTop := Semantics.preTop_of_okAll (NamesApart.wf_parts hwf).2.2.2
  CoreObligations.lazyOccs_hold (hpreTop := hpreTop) (Definition.coreOK_of_wf hwf) hrh hob

end KCore
