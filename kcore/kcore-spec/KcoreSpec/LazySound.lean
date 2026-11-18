/-
  KCore. What the lazy decider and the lazy obligation mean (checked layer; Lazy.lean).

  - `definedArg_sound`: a term `definedArg` accepts evaluates to a value under every well-sorted
    substitution, in a core that `sortedOK` and `srReady` accept, given that the functions declared
    `[total]` are defined at every argument list of their sorts (`TotalsDefined`). The interpreted
    symbols it admits are defined at every argument list of their sorts (`hook_total`): at the
    sorts they read (Int, Bool, Map, Set, List, RangeMap, String, Bytes) a value is a literal or a
    collection of that sort (`shapesOK`, `shape_int` …, `shape_rangeMap`, `shape_string`, `shape_bytes`), which every hook but
    `partialHooks` maps to a value.
  - `lazyOccs_hold`: with the lazy obligations, every occurrence's obligation holds, those
    `definedArg` confirms by `definedArg_sound` (`holds_of_definedArg`).
  - What an obligation gives at its occurrence: the strict result is the short-circuit one.
    `iteParam_true`: `ite{S}(C, A, B)` with C true has A's result when B has a value, although B is
    evaluated; `iteParam_false` the same for A when C is false; `andBool_false`, `orBool_true`; with
    `EvalTerm.functional`, every result of the occurrence is that one (`iteParam_true_eq`,
    `andBool_false_eq`). Where the skipped argument is undefined the strict result is undefined
    (`iteParam_skipped_undef`, `andBool_skipped_undef`): there the two readings differ.
-/
import KcoreSpec.Lazy
import KcoreSpec.SubjectReduction
import KcoreSpec.EvalFunctional

set_option autoImplicit false

namespace KCore

variable {c : Semantics}

/-! ## Values of the sorts the interpreted symbols read -/

theorem sortsOf_inv_cons {ws : List GroundTerm} {s : Srt} {ss : List Srt}
    (h : c.sortsOf ws = some (s :: ss)) :
    ∃ w ws', ws = w :: ws' ∧ c.sortOf w = some s ∧ c.sortsOf ws' = some ss := by
  cases ws with
  | nil => simp [Semantics.sortsOf] at h
  | cons w ws' => exact ⟨w, ws', rfl, (sortsOf_eq_cons.mp h).1, (sortsOf_eq_cons.mp h).2⟩

theorem sortsOf_inv_nil {ws : List GroundTerm} (h : c.sortsOf ws = some []) : ws = [] := by
  cases ws with
  | nil => rfl
  | cons w ws' =>
    obtain ⟨_, _, _, _, he⟩ := sortsOf_cons.mp h
    cases he

theorem sortsOf_one {ws : List GroundTerm} {a : Srt} (h : c.sortsOf ws = some [a]) :
    ∃ w₁, ws = [w₁] ∧ c.sortOf w₁ = some a := by
  obtain ⟨w₁, ws, rfl, h₁, h⟩ := sortsOf_inv_cons h
  obtain rfl := sortsOf_inv_nil h
  exact ⟨w₁, rfl, h₁⟩

theorem sortsOf_two {ws : List GroundTerm} {a b : Srt} (h : c.sortsOf ws = some [a, b]) :
    ∃ w₁ w₂, ws = [w₁, w₂] ∧ c.sortOf w₁ = some a ∧ c.sortOf w₂ = some b := by
  obtain ⟨w₁, ws, rfl, h₁, h⟩ := sortsOf_inv_cons h
  obtain ⟨w₂, rfl, h₂⟩ := sortsOf_one h
  exact ⟨w₁, w₂, rfl, h₁, h₂⟩

theorem sortsOf_three {ws : List GroundTerm} {a b d : Srt} (h : c.sortsOf ws = some [a, b, d]) :
    ∃ w₁ w₂ w₃, ws = [w₁, w₂, w₃] ∧ c.sortOf w₁ = some a ∧ c.sortOf w₂ = some b ∧
      c.sortOf w₃ = some d := by
  obtain ⟨w₁, ws, rfl, h₁, h⟩ := sortsOf_inv_cons h
  obtain ⟨w₂, w₃, rfl, h₂, h₃⟩ := sortsOf_two h
  exact ⟨w₁, w₂, w₃, rfl, h₁, h₂, h₃⟩

/-- Endianness and Signedness are no collection sort, where no collection of the definition's own
has either as its sort. -/
theorem collOf_enum (hcoll : ∀ k ∈ c.colls, (k.sort != Srt.endianness) = true ∧ (k.sort != Srt.signedness) = true)
    {s : Srt} (hS : s = Srt.endianness ∨ s = Srt.signedness) {k : CollSig} (h : c.collOf s = some k) : False := by
  unfold Semantics.collOf Semantics.allColls at h
  rw [List.find?_append] at h
  have hb : builtinColls.find? (·.sort == s) = none := by
    rcases hS with rfl | rfl <;> rfl
  rw [hb, Option.none_or] at h
  have hk := List.mem_of_find?_eq_some h
  have he : k.sort = s := by simpa using List.find?_some h
  have := hcoll k hk
  simp only [bne_iff_ne, ne_eq] at this
  rw [he] at this
  rcases hS with rfl | rfl
  · exact this.1 rfl
  · exact this.2 rfl

section Shapes
variable (hs : c.shapesOK = true)
include hs

theorem shapes_ctor' {k : CtorSig} (hk : k ∈ c.ctorSigs) : (shapeSorts ++ litShapeSorts).contains k.result = false := by
  unfold Semantics.shapesOK at hs
  simp only [Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true'] at hs
  exact hs.1.1.1.1.1.1 k hk

theorem shapes_sub' {p : Srt × Srt} (hp : p ∈ c.subsorts) : (shapeSorts ++ litShapeSorts).contains p.2 = false := by
  unfold Semantics.shapesOK at hs
  simp only [Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true'] at hs
  exact hs.1.1.1.1.1.2 p hp

theorem shapes_coll' {k : CollSig} (hk : k ∈ c.colls) : (shapeSorts ++ litShapeSorts).contains k.sort = false := by
  unfold Semantics.shapesOK at hs
  simp only [Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true'] at hs
  exact hs.1.1.1.2 k hk

theorem shapes_ovl' {k : CtorSig} (hk : k ∈ c.ovlSigs) : (shapeSorts ++ litShapeSorts).contains k.result = false := by
  unfold Semantics.shapesOK at hs
  simp only [Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true'] at hs
  exact hs.1.1.2 k hk

/-- No open generator has a sort of `shapeSorts ++ litShapeSorts`. -/
theorem shapes_open' {k : ParamSig} (hk : k ∈ c.params) (hraw : k.raw = true) :
    (shapeSorts ++ litShapeSorts).contains k.sig.result = false := by
  unfold Semantics.shapesOK at hs
  simp only [Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true'] at hs
  have := hs.1.2 k hk
  rw [hraw] at this
  exact this

theorem shapes_ctor {k : CtorSig} (hk : k ∈ c.ctorSigs) : shapeSorts.contains k.result = false := by
  have := shapes_ctor' hs hk
  simp only [List.contains_append, Bool.or_eq_false_iff] at this
  exact this.1

theorem shapes_sub {p : Srt × Srt} (hp : p ∈ c.subsorts) : shapeSorts.contains p.2 = false := by
  have := shapes_sub' hs hp
  simp only [List.contains_append, Bool.or_eq_false_iff] at this
  exact this.1

theorem shapes_coll {k : CollSig} (hk : k ∈ c.colls) : shapeSorts.contains k.sort = false := by
  have := shapes_coll' hs hk
  simp only [List.contains_append, Bool.or_eq_false_iff] at this
  exact this.1

theorem shapes_ovl {k : CtorSig} (hk : k ∈ c.ovlSigs) : shapeSorts.contains k.result = false := by
  have := shapes_ovl' hs hk
  simp only [List.contains_append, Bool.or_eq_false_iff] at this
  exact this.1

theorem shapes_ctor_lit {k : CtorSig} (hk : k ∈ c.ctorSigs) : litShapeSorts.contains k.result = false := by
  have := shapes_ctor' hs hk
  simp only [List.contains_append, Bool.or_eq_false_iff] at this
  exact this.2

theorem shapes_sub_lit {p : Srt × Srt} (hp : p ∈ c.subsorts) : litShapeSorts.contains p.2 = false := by
  have := shapes_sub' hs hp
  simp only [List.contains_append, Bool.or_eq_false_iff] at this
  exact this.2

theorem shapes_coll_lit {k : CollSig} (hk : k ∈ c.colls) : litShapeSorts.contains k.sort = false := by
  have := shapes_coll' hs hk
  simp only [List.contains_append, Bool.or_eq_false_iff] at this
  exact this.2

theorem shapes_ovl_lit {k : CtorSig} (hk : k ∈ c.ovlSigs) : litShapeSorts.contains k.result = false := by
  have := shapes_ovl' hs hk
  simp only [List.contains_append, Bool.or_eq_false_iff] at this
  exact this.2

/-- A token literal has no sort of `shapeSorts`. -/
theorem shapes_tok {s : Srt} (hS : shapeSorts.contains s = true) (t : String) :
    dvOK c.lib s (.tok t) = false := by
  unfold Semantics.shapesOK at hs
  simp only [Bool.and_eq_true, Bool.not_eq_true', List.any_eq_false] at hs
  have hn := hs.1.1.1.1.2
  have hk : (s == Srt.kconfigVar) = false ∧ (s == Srt.string) = false ∧ (s == Srt.bytes) = false := by
    simp only [shapeSorts, List.contains_cons, List.contains_nil, Bool.or_false,
      Bool.or_eq_true, beq_iff_eq] at hS
    rcases hS with rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨rfl, rfl, rfl⟩
  have ht : c.lib.tokenSorts.contains s = false := by
    cases h : c.lib.tokenSorts.contains s
    · rfl
    · exact (hn s (List.mem_append_left _ (List.contains_iff_mem.mp h)) hS).elim
  have hb : c.lib.byteSorts.contains s = false := by
    cases h : c.lib.byteSorts.contains s
    · rfl
    · exact (hn s (List.mem_append_right _ (List.contains_iff_mem.mp h)) hS).elim
  have hcs : c.lib.carrier s = s := by
    simp only [shapeSorts, List.contains_cons, List.contains_nil, Bool.or_false, Bool.or_eq_true, beq_iff_eq] at hS
    rcases hS with rfl | rfl | rfl | rfl | rfl | rfl <;> exact Lib.carrier_of_lt _ (by decide)
  simp only [dvOK, hcs, hk.1, hk.2.1, hk.2.2, ht, hb, Bool.false_or, Bool.false_and]

/-- A value of a sort of `shapeSorts` is a domain value or a collection of that sort. -/
theorem shape_of_sortOf {v : GroundTerm} {s : Srt} (hS : shapeSorts.contains s = true)
    (h : c.sortOf v = some s) :
    (∃ lit, v = .dv s lit ∧ dvOK c.lib s lit = true) ∨
    (∃ es k, v = .map s es ∧ c.collOf s = some k ∧ (k.kind = .map ∨ k.kind = .rangeMap)) ∨
    (∃ es k, v = .set s es ∧ c.collOf s = some k ∧ k.kind = .set) ∨
    (∃ es k, v = .list s es ∧ c.collOf s = some k ∧ k.kind = .list) := by
  cases v with
  | ctor f ts =>
    rcases c.sortOf_ctor_iff.mp h with ⟨k, hk, _, rfl⟩ | ⟨-, o, ho, _, _, rfl⟩ | ⟨-, -, k, hk, _, _, rfl⟩
    rotate_right
    · obtain ⟨hm, hraw, -, -⟩ := c.lookupOpen_spec hk
      have := shapes_open' hs hm hraw
      simp only [List.contains_append, Bool.or_eq_false_iff] at this
      rw [this.1] at hS; cases hS
    · have := shapes_ctor hs (lookupSig_spec hk).1
      rw [this] at hS; cases hS
    · have hom : o ∈ c.ovls := List.mem_of_find?_eq_some ho
      have := shapes_ovl hs (List.mem_map_of_mem (f := (·.sig)) hom)
      rw [this] at hS; cases hS
  | inj a b t =>
    obtain ⟨hab, _, _, rfl⟩ := sortOf_inj.mp h
    have := shapes_sub hs hab
    rw [this] at hS; cases hS
  | dv s' lit =>
    obtain ⟨hok, rfl⟩ := sortOf_dv.mp h
    exact Or.inl ⟨lit, rfl, hok⟩
  | map s' es =>
    obtain ⟨k, _, hk, hkind, _, _, _, rfl⟩ := sortOf_mapS_fwd h
    exact Or.inr (Or.inl ⟨es, k, rfl, hk, hkind⟩)
  | set s' es =>
    obtain ⟨k, hk, hkind, _, _, rfl⟩ := sortOf_setS.mp h
    exact Or.inr (Or.inr (Or.inl ⟨es, k, rfl, hk, hkind⟩))
  | list s' es =>
    obtain ⟨k, hk, hkind, _, rfl⟩ := sortOf_listS.mp h
    exact Or.inr (Or.inr (Or.inr ⟨es, k, rfl, hk, hkind⟩))

/-- Int and Bool are no collection sort. -/
theorem collOf_scalar {s : Srt} (hS : s = Srt.int ∨ s = Srt.bool) {k : CollSig}
    (h : c.collOf s = some k) : False := by
  unfold Semantics.collOf Semantics.allColls at h
  rw [List.find?_append] at h
  have hb : builtinColls.find? (·.sort == s) = none := by
    rcases hS with rfl | rfl <;> rfl
  rw [hb, Option.none_or] at h
  have hk := List.mem_of_find?_eq_some h
  have he : k.sort = s := by simpa using List.find?_some h
  have := shapes_coll hs hk
  rw [he] at this
  rcases hS with rfl | rfl <;> exact absurd this (by decide)

theorem shape_int {v : GroundTerm} (h : c.sortOf v = some Srt.int) : ∃ i, v = int i := by
  rcases shape_of_sortOf hs (by decide) h with ⟨lit, rfl, hok⟩ | ⟨_, _, _, hk, _⟩ | ⟨_, _, _, hk, _⟩ |
      ⟨_, _, _, hk, _⟩
  · cases lit with
    | int i => exact ⟨i, rfl⟩
    | bool b => simp only [dvOK, Lib.carrier_of_lt c.lib (by decide : Srt.int < nRegSorts), beq_iff_eq] at hok; exact absurd hok (by decide)
    | tok t => rw [shapes_tok hs (by decide) t] at hok; cases hok
    | float _ _ _ => simp only [dvOK, Lib.carrier_of_lt c.lib (by decide : Srt.int < nRegSorts), Bool.and_eq_true, beq_iff_eq] at hok; exact absurd hok.1 (by decide)
  all_goals exact (collOf_scalar hs (Or.inl rfl) hk).elim

theorem shape_bool {v : GroundTerm} (h : c.sortOf v = some Srt.bool) : ∃ b, v = bool b := by
  rcases shape_of_sortOf hs (by decide) h with ⟨lit, rfl, hok⟩ | ⟨_, _, _, hk, _⟩ | ⟨_, _, _, hk, _⟩ |
      ⟨_, _, _, hk, _⟩
  · cases lit with
    | int i => simp only [dvOK, Lib.carrier_of_lt c.lib (by decide : Srt.bool < nRegSorts), beq_iff_eq] at hok; exact absurd hok (by decide)
    | bool b => exact ⟨b, rfl⟩
    | tok t => rw [shapes_tok hs (by decide) t] at hok; cases hok
    | float _ _ _ => simp only [dvOK, Lib.carrier_of_lt c.lib (by decide : Srt.bool < nRegSorts), Bool.and_eq_true, beq_iff_eq] at hok; exact absurd hok.1 (by decide)
  all_goals exact (collOf_scalar hs (Or.inr rfl) hk).elim

theorem shape_map {v : GroundTerm} (h : c.sortOf v = some Srt.map) : ∃ es, v = .map Srt.map es := by
  rcases shape_of_sortOf hs (by decide) h with ⟨lit, rfl, hok⟩ | ⟨es, _, rfl, _, _⟩ |
      ⟨_, _, _, hk, hkind⟩ | ⟨_, _, _, hk, hkind⟩
  · cases lit with
    | int i => simp only [dvOK, Lib.carrier_of_lt c.lib (by decide : Srt.map < nRegSorts), beq_iff_eq] at hok; exact absurd hok (by decide)
    | bool b => simp only [dvOK, Lib.carrier_of_lt c.lib (by decide : Srt.map < nRegSorts), beq_iff_eq] at hok; exact absurd hok (by decide)
    | tok t => rw [shapes_tok hs (by decide) t] at hok; cases hok
    | float _ _ _ => simp only [dvOK, Lib.carrier_of_lt c.lib (by decide : Srt.map < nRegSorts), Bool.and_eq_true, beq_iff_eq] at hok; exact absurd hok.1 (by decide)
  · exact ⟨es, rfl⟩
  all_goals rw [collOf_map] at hk; cases hk; exact absurd hkind (by decide)

theorem shape_set {v : GroundTerm} (h : c.sortOf v = some Srt.set) : ∃ es, v = .set Srt.set es := by
  rcases shape_of_sortOf hs (by decide) h with ⟨lit, rfl, hok⟩ | ⟨_, _, _, hk, hkind⟩ |
      ⟨es, _, rfl, _, _⟩ | ⟨_, _, _, hk, hkind⟩
  · cases lit with
    | int i => simp only [dvOK, Lib.carrier_of_lt c.lib (by decide : Srt.set < nRegSorts), beq_iff_eq] at hok; exact absurd hok (by decide)
    | bool b => simp only [dvOK, Lib.carrier_of_lt c.lib (by decide : Srt.set < nRegSorts), beq_iff_eq] at hok; exact absurd hok (by decide)
    | tok t => rw [shapes_tok hs (by decide) t] at hok; cases hok
    | float _ _ _ => simp only [dvOK, Lib.carrier_of_lt c.lib (by decide : Srt.set < nRegSorts), Bool.and_eq_true, beq_iff_eq] at hok; exact absurd hok.1 (by decide)
  · rw [collOf_set] at hk; cases hk; exact absurd hkind (by decide)
  · exact ⟨es, rfl⟩
  · rw [collOf_set] at hk; cases hk; exact absurd hkind (by decide)

theorem shape_list {v : GroundTerm} (h : c.sortOf v = some Srt.list) : ∃ es, v = .list Srt.list es := by
  rcases shape_of_sortOf hs (by decide) h with ⟨lit, rfl, hok⟩ | ⟨_, _, _, hk, hkind⟩ |
      ⟨_, _, _, hk, hkind⟩ | ⟨es, _, rfl, _, _⟩
  · cases lit with
    | int i => simp only [dvOK, Lib.carrier_of_lt c.lib (by decide : Srt.list < nRegSorts), beq_iff_eq] at hok; exact absurd hok (by decide)
    | bool b => simp only [dvOK, Lib.carrier_of_lt c.lib (by decide : Srt.list < nRegSorts), beq_iff_eq] at hok; exact absurd hok (by decide)
    | tok t => rw [shapes_tok hs (by decide) t] at hok; cases hok
    | float _ _ _ => simp only [dvOK, Lib.carrier_of_lt c.lib (by decide : Srt.list < nRegSorts), Bool.and_eq_true, beq_iff_eq] at hok; exact absurd hok.1 (by decide)
  all_goals first
    | exact ⟨es, rfl⟩
    | (rw [collOf_list] at hk; cases hk; exact absurd hkind (by decide))

/-- A value of sort RangeMap is a range map of that sort whose entries are triples (every key a
proper range). -/
theorem shape_rangeMap {v : GroundTerm} (h : c.sortOf v = some Srt.rangeMap) :
    ∃ es ts, v = .map Srt.rangeMap es ∧ rmTriples es = some ts := by
  rcases shape_of_sortOf hs (by decide) h with ⟨lit, rfl, hok⟩ | ⟨es, _, rfl, _, _⟩ |
      ⟨_, _, _, hk, hkind⟩ | ⟨_, _, _, hk, hkind⟩
  · cases lit with
    | int i => simp only [dvOK, Lib.carrier_of_lt c.lib (by decide : Srt.rangeMap < nRegSorts), beq_iff_eq] at hok; exact absurd hok (by decide)
    | bool b => simp only [dvOK, Lib.carrier_of_lt c.lib (by decide : Srt.rangeMap < nRegSorts), beq_iff_eq] at hok; exact absurd hok (by decide)
    | tok t => rw [shapes_tok hs (by decide) t] at hok; cases hok
    | float _ _ _ => simp only [dvOK, Lib.carrier_of_lt c.lib (by decide : Srt.rangeMap < nRegSorts), Bool.and_eq_true, beq_iff_eq] at hok; exact absurd hok.1 (by decide)
  · obtain ⟨-, hr, -⟩ := (rmS_sortOf_map collOf_rangeMap).mp h
    obtain ⟨ts, hts⟩ := Option.isSome_iff_exists.mp (rmTriples_of_rangesOK hr)
    exact ⟨es, ts, rfl, hts⟩
  all_goals (rw [collOf_rangeMap] at hk; cases hk; exact absurd hkind (by decide))

/-- String and Bytes are no collection sort. -/
theorem collOf_lit {s : Srt} (hS : litShapeSorts.contains s = true) {k : CollSig}
    (h : c.collOf s = some k) : False := by
  unfold Semantics.collOf Semantics.allColls at h
  rw [List.find?_append] at h
  have hS' : s = Srt.string ∨ s = Srt.bytes := by
    simp only [litShapeSorts, List.contains_cons, List.contains_nil, Bool.or_false, Bool.or_eq_true,
      beq_iff_eq] at hS
    exact hS
  have hb : builtinColls.find? (·.sort == s) = none := by
    rcases hS' with rfl | rfl <;> rfl
  rw [hb, Option.none_or] at h
  have hk := List.mem_of_find?_eq_some h
  have he : k.sort = s := by simpa using List.find?_some h
  have := shapes_coll_lit hs hk
  rw [he, hS] at this
  cases this

/-- A value of a sort of `litShapeSorts` is a token literal of that sort. -/
theorem shape_lit {v : GroundTerm} {s : Srt} (hS : litShapeSorts.contains s = true)
    (h : c.sortOf v = some s) : ∃ t, v = .dv s (.tok t) := by
  cases v with
  | ctor f ts =>
    rcases c.sortOf_ctor_iff.mp h with ⟨k, hk, _, rfl⟩ | ⟨-, o, ho, _, _, rfl⟩ | ⟨-, -, k, hk, _, _, rfl⟩
    rotate_right
    · obtain ⟨hm, hraw, -, -⟩ := c.lookupOpen_spec hk
      have := shapes_open' hs hm hraw
      simp only [List.contains_append, Bool.or_eq_false_iff] at this
      rw [this.2] at hS; cases hS
    · have := shapes_ctor_lit hs (lookupSig_spec hk).1
      rw [this] at hS; cases hS
    · have hom : o ∈ c.ovls := List.mem_of_find?_eq_some ho
      have := shapes_ovl_lit hs (List.mem_map_of_mem (f := (·.sig)) hom)
      rw [this] at hS; cases hS
  | inj a b t =>
    obtain ⟨hab, _, _, rfl⟩ := sortOf_inj.mp h
    have := shapes_sub_lit hs hab
    rw [this] at hS; cases hS
  | dv s' lit =>
    obtain ⟨hok, rfl⟩ := sortOf_dv.mp h
    have hcs : c.lib.carrier s = s := by
      simp only [litShapeSorts, List.contains_cons, List.contains_nil, Bool.or_false, Bool.or_eq_true, beq_iff_eq] at hS
      rcases hS with rfl | rfl <;> exact Lib.carrier_of_lt _ (by decide)
    cases lit with
    | tok t => exact ⟨t, rfl⟩
    | int i => simp only [dvOK, hcs, beq_iff_eq] at hok; subst hok; exact absurd hS (by decide)
    | bool b => simp only [dvOK, hcs, beq_iff_eq] at hok; subst hok; exact absurd hS (by decide)
    | float _ _ _ =>
      simp only [dvOK, hcs, Bool.and_eq_true, beq_iff_eq] at hok; rw [hok.1] at hS; exact absurd hS (by decide)
  | map s' es =>
    obtain ⟨k, _, hk, _, _, _, _, rfl⟩ := sortOf_mapS_fwd h
    exact (collOf_lit hs hS hk).elim
  | set s' es =>
    obtain ⟨k, hk, _, _, _, rfl⟩ := sortOf_setS.mp h
    exact (collOf_lit hs hS hk).elim
  | list s' es =>
    obtain ⟨k, hk, _, _, rfl⟩ := sortOf_listS.mp h
    exact (collOf_lit hs hS hk).elim

theorem shape_string {v : GroundTerm} (h : c.sortOf v = some Srt.string) : ∃ t, v = .dv Srt.string (.tok t) :=
  shape_lit hs (by decide) h

theorem shape_bytes {v : GroundTerm} (h : c.sortOf v = some Srt.bytes) : ∃ t, v = .dv Srt.bytes (.tok t) :=
  shape_lit hs (by decide) h

theorem shapes_enum : c.enumShapesOK = true := by
  unfold Semantics.shapesOK at hs
  simp only [Bool.and_eq_true] at hs
  exact hs.2

/-- A value of Endianness or Signedness is a constructor of BYTES of that sort without arguments
(`enumShapesOK`). -/
theorem shape_enum {v : GroundTerm} {s : Srt} (hS : s = Srt.endianness ∨ s = Srt.signedness)
    (h : c.sortOf v = some s) :
    ∃ f, v = .ctor f [] ∧ (s = Srt.endianness → f = littleEndianBytes ∨ f = bigEndianBytes) ∧
      (s = Srt.signedness → f = signedBytes ∨ f = unsignedBytes) := by
  have he := shapes_enum hs
  unfold Semantics.enumShapesOK at he
  simp only [Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true'] at he
  obtain ⟨⟨⟨⟨⟨hc, hsub⟩, hcoll⟩, htok⟩, hovl⟩, hrw⟩ := he
  have hS' : s ≠ Srt.endianness ∨ s ≠ Srt.signedness := by
    rcases hS with rfl | rfl
    · exact Or.inr (by decide)
    · exact Or.inl (by decide)
  cases v with
  | ctor f ts =>
    rcases c.sortOf_ctor_iff.mp h with ⟨k, hk, hts, rfl⟩ | ⟨-, o, ho, _, _, rfl⟩ | ⟨-, -, kp, hkp, _, _, rfl⟩
    rotate_right
    · obtain ⟨hm, hr, -, -⟩ := c.lookupOpen_spec hkp
      have := hrw kp hm
      rw [hr] at this
      simp only [Bool.true_and, Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq, Bool.not_eq_true'] at this
      rcases hS with hS | hS
      · exact absurd hS this.1
      · exact absurd hS this.2
    rotate_left
    · have hom : o ∈ c.ovls := List.mem_of_find?_eq_some ho
      have := hovl _ (List.mem_map_of_mem (f := (·.sig)) hom)
      simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at this
      rcases hS with hS | hS
      · exact absurd hS this.1
      · exact absurd hS this.2
    obtain ⟨hkm, rfl⟩ := lookupSig_spec hk
    have := hc k hkm
    simp only [Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq, beq_iff_eq, List.isEmpty_iff] at this
    obtain ⟨h1, h2⟩ := this
    rcases hS with hS | hS
    · rcases h1 with h1 | ⟨h1, ha⟩
      · exact absurd hS h1
      · rw [ha] at hts
        refine ⟨k.name, by rw [sortsOf_inv_nil hts], fun _ => h1, fun h' => ?_⟩
        rw [hS] at h'; exact absurd h' (by decide)
    · rcases h2 with h2 | ⟨h2, ha⟩
      · exact absurd hS h2
      · rw [ha] at hts
        refine ⟨k.name, by rw [sortsOf_inv_nil hts], fun h' => ?_, fun _ => h2⟩
        rw [hS] at h'; exact absurd h' (by decide)
  | inj a b t =>
    obtain ⟨hab, _, _, rfl⟩ := sortOf_inj.mp h
    have := hsub _ hab
    simp only [bne_iff_ne, ne_eq] at this
    rcases hS with hS | hS
    · exact absurd hS this.1
    · exact absurd hS this.2
  | dv s' lit =>
    obtain ⟨hok, hss⟩ := sortOf_dv.mp h
    rw [← hss] at hok
    have hcs : c.lib.carrier s = s := by rcases hS with rfl | rfl <;> exact Lib.carrier_of_lt _ (by decide)
    have hnt : ∀ x, x ∈ c.lib.tokenSorts ++ c.lib.byteSorts → x ≠ s := by
      intro x hx hxs
      have h1 := List.any_eq_false.mp htok x hx
      rw [hxs] at h1
      rcases hS with hS | hS <;> rw [hS] at h1 <;> exact h1 (by decide)
    cases lit with
    | int i => simp only [dvOK, hcs, beq_iff_eq] at hok; subst hok; rcases hS with h | h <;> exact absurd h (by decide)
    | bool b => simp only [dvOK, hcs, beq_iff_eq] at hok; subst hok; rcases hS with h | h <;> exact absurd h (by decide)
    | float _ _ _ =>
      simp only [dvOK, hcs, Bool.and_eq_true, beq_iff_eq] at hok
      rw [hok.1] at hS; rcases hS with h | h <;> exact absurd h (by decide)
    | tok t =>
      simp only [dvOK, hcs, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hok
      rcases hok with ((hk | hk) | hk) | ⟨hk | hk, -⟩
      · subst hk; rcases hS with h | h <;> exact absurd h (by decide)
      · subst hk; rcases hS with h | h <;> exact absurd h (by decide)
      · exact absurd rfl (hnt s (List.mem_append_left _ (List.contains_iff_mem.mp hk)))
      · subst hk; rcases hS with h | h <;> exact absurd h (by decide)
      · exact absurd rfl (hnt s (List.mem_append_right _ (List.contains_iff_mem.mp hk)))
  | map s' es =>
    obtain ⟨k, _, hk, _, _, _, _, rfl⟩ := sortOf_mapS_fwd h
    exact (collOf_enum hcoll hS hk).elim
  | set s' es =>
    obtain ⟨k, hk, _, _, _, rfl⟩ := sortOf_setS.mp h
    exact (collOf_enum hcoll hS hk).elim
  | list s' es =>
    obtain ⟨k, hk, _, _, rfl⟩ := sortOf_listS.mp h
    exact (collOf_enum hcoll hS hk).elim

theorem shape_endian {v : GroundTerm} (h : c.sortOf v = some Srt.endianness) :
    v = .ctor littleEndianBytes [] ∨ v = .ctor bigEndianBytes [] := by
  obtain ⟨f, rfl, h1, -⟩ := shape_enum hs (Or.inl rfl) h
  rcases h1 rfl with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem shape_signed {v : GroundTerm} (h : c.sortOf v = some Srt.signedness) :
    v = .ctor signedBytes [] ∨ v = .ctor unsignedBytes [] := by
  obtain ⟨f, rfl, -, h2⟩ := shape_enum hs (Or.inr rfl) h
  rcases h2 rfl with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- `Bytes2Int` has a value at every argument list of its sorts. -/
theorem bytes2Int_total {ws : List GroundTerm}
    (hws : c.sortsOf ws = some [Srt.bytes, Srt.endianness, Srt.signedness]) :
    ∃ v, hook bytes2Int ws = some (some v) := by
  obtain ⟨_, _, _, rfl, h₁, h₂, h₃⟩ := sortsOf_three hws
  obtain ⟨_, rfl⟩ := shape_bytes hs h₁
  rcases shape_endian hs h₂ with rfl | rfl <;> rcases shape_signed hs h₃ with rfl | rfl <;> exact ⟨_, rfl⟩

/-- **RANGEMAP's interpreted symbols but `partialHooks` have a value at every argument list of
their sorts** (unit, `orDefault`, `-RangeMap`, `updateRangeMap`, `in_keys`, `size`, `<=RangeMap`):
an argument of sort RangeMap is a range map whose keys are proper ranges (`shape_rangeMap`). -/
theorem rangeMapHook_total : ∀ k ∈ rangeMapSigs, partialHooks.contains k.name = false →
    ∀ ws, c.sortsOf ws = some k.args → ∃ v, hook k.name ws = some (some v) := by
  intro k hk hp ws hws
  simp only [rangeMapSigs, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | exact absurd hp (by decide)
    | skip
  · obtain rfl := sortsOf_inv_nil hws
    exact ⟨_, rfl⟩
  · obtain ⟨_, _, _, rfl, h₁, -, -⟩ := sortsOf_three hws
    obtain ⟨es, ts, rfl, hts⟩ := shape_rangeMap hs h₁
    have e : ∀ k d, hook rmLookupOrDefault [.map Srt.rangeMap es, k, d] =
        some ((rmTriples es).map fun ts => (((asKInt k).bind fun i => rmFind i ts).map (·.2.2)).getD d) :=
      fun _ _ => rfl
    simp only [e, hts, Option.map_some]
    exact ⟨_, rfl⟩
  · obtain ⟨_, _, rfl, h₁, h₂⟩ := sortsOf_two hws
    obtain ⟨es, ts, rfl, hts⟩ := shape_rangeMap hs h₁
    obtain ⟨es', us, rfl, hus⟩ := shape_rangeMap hs h₂
    have e : hook rmDifference [.map Srt.rangeMap es, .map Srt.rangeMap es'] =
        some ((rmTriples es).bind fun ts => (rmTriples es').map fun us => rmV (rmCanon (rmDiffT ts us))) := rfl
    simp only [e, hts, hus, Option.map_some, Option.bind_some]
    exact ⟨_, rfl⟩
  · obtain ⟨_, _, rfl, h₁, h₂⟩ := sortsOf_two hws
    obtain ⟨es, ts, rfl, hts⟩ := shape_rangeMap hs h₁
    obtain ⟨es', us, rfl, hus⟩ := shape_rangeMap hs h₂
    have e : hook rmUpdateAll [.map Srt.rangeMap es, .map Srt.rangeMap es'] =
        some ((rmTriples es).bind fun ts => (rmTriples es').map fun us => rmV (rmCanon (rmOverT ts us))) := rfl
    simp only [e, hts, hus, Option.map_some, Option.bind_some]
    exact ⟨_, rfl⟩
  · obtain ⟨_, _, rfl, -, h₂⟩ := sortsOf_two hws
    obtain ⟨es, ts, rfl, hts⟩ := shape_rangeMap hs h₂
    have e : ∀ k, hook rmInKeys [k, .map Srt.rangeMap es] =
        some ((rmTriples es).map fun ts => bool (((asKInt k).bind fun i => rmFind i ts).isSome)) := fun _ => rfl
    simp only [e, hts, Option.map_some]
    exact ⟨_, rfl⟩
  · obtain ⟨_, rfl, h₁⟩ := sortsOf_one hws
    obtain ⟨es, ts, rfl, -⟩ := shape_rangeMap hs h₁
    exact ⟨_, rfl⟩
  · obtain ⟨_, _, rfl, h₁, h₂⟩ := sortsOf_two hws
    obtain ⟨es, ts, rfl, hts⟩ := shape_rangeMap hs h₁
    obtain ⟨es', us, rfl, hus⟩ := shape_rangeMap hs h₂
    have e : hook rmInclusion [.map Srt.rangeMap es, .map Srt.rangeMap es'] =
        some ((rmTriples es).bind fun ts => (rmTriples es').map fun us => bool (rmIncluded ts us)) := rfl
    simp only [e, hts, hus, Option.map_some, Option.bind_some]
    exact ⟨_, rfl⟩

/-- **RANGEMAP's `keys` has a value at every range map value**: an argument of sort RangeMap is a
range map (`shape_rangeMap`). -/
theorem rmKeysHook_total {ws : List GroundTerm} (hws : c.sortsOf ws = some [Srt.rangeMap]) :
    ∃ v, hook rmKeys ws = some (some v) := by
  obtain ⟨_, rfl, h₁⟩ := sortsOf_one hws
  obtain ⟨es, ts, rfl, -⟩ := shape_rangeMap hs h₁
  exact ⟨_, rfl⟩

set_option hygiene false in
/-- A value of Int, Bool, Map, Set, List, String or Bytes sort replaced by its shape. -/
local macro "shapeAt " hs:term:max h:term:max : tactic => `(tactic| first
  | obtain ⟨_, rfl⟩ := shape_int $hs $h
  | obtain ⟨_, rfl⟩ := shape_bool $hs $h
  | obtain ⟨_, rfl⟩ := shape_map $hs $h
  | obtain ⟨_, rfl⟩ := shape_set $hs $h
  | obtain ⟨_, rfl⟩ := shape_list $hs $h
  | obtain ⟨_, rfl⟩ := shape_string $hs $h
  | obtain ⟨_, rfl⟩ := shape_bytes $hs $h)

/-! ## The interpreted symbols but `partialHooks` are defined at every argument list of their sorts -/

theorem hook_total : ∀ k ∈ hookSigs, partialHooks.contains k.name = false →
    ∀ ws, c.sortsOf ws = some k.args → ∃ v, hook k.name ws = some (some v) := by
  intro k hk hp ws hws
  by_cases hb : k = ⟨bytes2Int, [Srt.bytes, Srt.endianness, Srt.signedness], Srt.int⟩
  · subst hb; exact bytes2Int_total hs hws
  rw [hookSigs, List.mem_append] at hk
  rcases hk with hk | hk
  rotate_left
  · rw [List.mem_singleton] at hk
    subst hk
    exact rmKeysHook_total hs hws
  rw [List.mem_append] at hk
  rcases hk with hk | hk
  rotate_left
  · exact rangeMapHook_total hs k hk hp ws hws
  simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  all_goals first
    | exact absurd hp (by decide)
    | exact absurd rfl hb
    | skip
  all_goals first
    | (obtain ⟨_, _, _, rfl, h₁, h₂, h₃⟩ := sortsOf_three hws
       try shapeAt hs h₁
       try shapeAt hs h₂
       try shapeAt hs h₃)
    | (obtain ⟨_, _, rfl, h₁, h₂⟩ := sortsOf_two hws
       try shapeAt hs h₁
       try shapeAt hs h₂)
    | (obtain ⟨_, rfl, h₁⟩ := sortsOf_one hws
       try shapeAt hs h₁)
    | (obtain rfl := sortsOf_inv_nil hws)
  all_goals exact ⟨_, rfl⟩

end Shapes

/-! ## `definedArg` is sound -/

theorem allSome_map_some : ∀ (vs : List GroundTerm), allSome (vs.map some) = some vs
  | [] => rfl
  | v :: vs => by simp [allSome, allSome_map_some vs]

/-- A value of its sort is its own `withSort`. -/
theorem withSort_of_sortOf {z : GroundTerm} {S : Srt} (h : c.sortOf z = some S) : z.withSort S = z := by
  cases z with
  | map s es => obtain ⟨_, _, _, _, _, _, _, rfl⟩ := sortOf_mapS_fwd h; rfl
  | set s es => obtain ⟨_, _, _, _, _, rfl⟩ := sortOf_setS.mp h; rfl
  | list s es => obtain ⟨_, _, _, _, rfl⟩ := sortOf_listS.mp h; rfl
  | ctor _ _ => rfl
  | inj _ _ _ => rfl
  | dv _ _ => rfl

/-- `ite{S}(b, x, y)`, a parameter implemented by `kIte`, is x or y, when that value has sort S. -/
theorem paramVal_ite {f : Sym} {k : ParamSig} (hp : c.lookupParam f = some k) (hk : k.impl = some kIte)
    (b : Bool) {x y : GroundTerm} (hz : c.sortOf (if b then x else y) = some k.sig.result) :
    c.paramVal f [bool b, x, y] = some (if b then x else y) := by
  unfold Semantics.paramVal
  rw [hp]
  simp only [hk]
  rw [Semantics.libArgs_coll c (by decide)]
  have hh : hook kIte [bool b, x, y] = some (some (if b then x else y)) := rfl
  rw [Semantics.hookRes_of_value hh]
  have ha : (if b then x else y).asSort c.lib k.sig.result = if b then x else y := by
    generalize hv : (if b then x else y) = v at hz ⊢
    cases v with
    | dv s lit => obtain ⟨-, rfl⟩ := sortOf_dv.mp hz; simp [GroundTerm.asSort]
    | _ => exact withSort_of_sortOf hz
  simp [Option.filter, ha, hz]

/-- An application of a `definedHead` to arguments with values of its argument sorts has a value. -/
theorem app_defined (hc : SortCtx c) (htot : c.TotalsDefined) (hs : c.shapesOK = true)
    {L : List CtorSig} (hL : HeadsOK c L) {σ : Subst} {f : Sym} {ts : List Term} {k : CtorSig}
    {vs : List GroundTerm} (hk' : lookupSig (c.rhsCtx L).heads f = some k)
    (hts : EvalTerms c σ ts (vs.map some)) (hsrt : c.sortsOf vs = some k.args)
    (hd : c.definedHead f = true) : ∃ v, EvalTerm c σ (.app f ts) (some v) := by
  have hall := allSome_map_some vs
  cases hct : c.isCtor f
  · have hnc : lookupSig c.ctorSigs f = none :=
      Option.not_isSome_iff_eq_none.mp (by simpa [Semantics.isCtor] using hct)
    simp only [Semantics.rhsCtx, List.append_assoc] at hk'
    rw [lookupSig_append_of_none hnc] at hk'
    cases hhk : isHook f
    · rw [lookupSig_append_of_none (lookupSig_hookSigs_of_not_isHook hhk)] at hk'
      cases hpar : c.lookupParam f with
      | some kp =>
        have hp : c.isParam f = true := by simp [Semantics.isParam, hpar]
        rw [lookupSig_append_of_some (l' := c.sortPreds.map Fn.sig ++ (L ++ c.ovlSigs)) (k := kp.sig)
          (by rw [c.lookupSig_params, hpar]; rfl)] at hk'
        cases hk'
        simp only [Semantics.definedHead, Semantics.iteSig, hct, hhk, hpar, Bool.false_or,
          Bool.false_and, Bool.not_false, Bool.true_and, Bool.and_eq_true, beq_iff_eq] at hd
        obtain ⟨himpl, hA⟩ := hd
        rw [hA] at hsrt
        obtain ⟨w₀, w₁, w₂, rfl, h0, h1, h2⟩ := sortsOf_three hsrt
        obtain ⟨bb, rfl⟩ := shape_bool hs h0
        refine ⟨if bb then w₁ else w₂, EvalTerm.param hct hhk hp hts ?_⟩
        rw [hall, Option.bind_some, paramVal_ite hpar himpl bb (by cases bb <;> assumption)]
      | none =>
        have hp : c.isParam f = false := by simp [Semantics.isParam, hpar]
        rw [lookupSig_append_of_none (c.lookupSig_params_of_not hp)] at hk'
        have hfn0 : ∃ fn0, c.lookupFn f = some fn0 := by
          cases h0 : c.lookupFn f with
          | none => simp [Semantics.definedHead, hct, hhk, hpar, h0] at hd
          | some fn0 => exact ⟨fn0, rfl⟩
        obtain ⟨hkL, hkn⟩ := lookupSig_spec (rhs_lookup_fn hc hfn0.choose_spec hk')
        obtain ⟨fn, hfn, rfl⟩ := headsOK_preds hL k hkL
        have hlook : c.lookupFn f = some fn := by
          rw [← hkn, Semantics.lookupFn_eq]; exact find?_label hc.nodupFns hfn
        simp only [Semantics.definedHead, hct, hhk, hpar, hlook, Bool.false_or, Bool.false_and,
          Bool.not_false, Bool.true_and, Option.any_some] at hd
        obtain ⟨v, hv⟩ := htot f fn hlook hd vs hsrt
        exact ⟨v, EvalTerm.call hct hhk hts hall hv hp⟩
    · obtain ⟨k₀, hk₀⟩ := lookupSig_hookSigs_of_isHook hhk
      rw [lookupSig_append_of_some hk₀] at hk'
      have hkk : k₀ = k := Option.some.inj hk'
      subst hkk
      have hpart : partialHooks.contains f = false := by
        simpa [Semantics.definedHead, hct, hhk] using hd
      obtain ⟨hmem, hname⟩ := lookupSig_spec hk₀
      obtain ⟨v, hv⟩ := hook_total hs k₀ hmem (hname ▸ hpart) vs hsrt
      rw [hname] at hv
      exact ⟨v, EvalTerm.hook hct hhk hts (fun ws h => by rw [hall] at h; cases h; exact Semantics.hookRes_of_value hv)
        (fun h => by rw [hall] at h; cases h)⟩
  · have := EvalTerm.ctor (c := c) (σ := σ) hct hts
    rw [hall] at this
    exact ⟨_, this⟩

mutual
  theorem definedTerm_sound (hc : SortCtx c) (htot : c.TotalsDefined) (hs : c.shapesOK = true)
      {L : List CtorSig} (hL : HeadsOK c L) {vars : List Srt} {σ : Subst}
      (hσ : c.WellSorted vars σ) : ∀ (t : Term) {s : Srt},
      sortOfTerm (c.rhsCtx L) vars t = some s → c.definedTerm t = true →
        ∃ v, EvalTerm c σ t (some v)
    | .var i, s, ht, _ => by
      obtain ⟨v, hv, _⟩ := hσ i s (sortOfTerm_var.mp ht)
      exact ⟨v, hv ▸ EvalTerm.var⟩
    | .dv _ _, _, _, _ => ⟨_, EvalTerm.dv⟩
    | .inj a b t, s, ht, hd => by
      obtain ⟨_, ht', _⟩ := sortOfTerm_inj.mp ht
      obtain ⟨v, hv⟩ := definedTerm_sound hc htot hs hL hσ t ht'
        (by simpa [Semantics.definedTerm] using hd)
      exact ⟨_, EvalTerm.inj hv⟩
    | .as _ _, _, _, hd => by simp [Semantics.definedTerm] at hd
    | .app f ts, s, ht, hd => by
      simp only [Semantics.definedTerm, Bool.and_eq_true] at hd
      obtain ⟨k, hk', hargs, rfl⟩ := sortOfTerm_app.mp ht
      obtain ⟨vs, hts⟩ := definedTerms_sound hc htot hs hL hσ ts hargs hd.2
      exact app_defined hc htot hs hL hk' hts
        (EvalTerms.sorted hc hts hL hσ hargs (allSome_map_some vs)) hd.1
  theorem definedTerms_sound (hc : SortCtx c) (htot : c.TotalsDefined) (hs : c.shapesOK = true)
      {L : List CtorSig} (hL : HeadsOK c L) {vars : List Srt} {σ : Subst}
      (hσ : c.WellSorted vars σ) : ∀ (ts : List Term) {ss : List Srt},
      sortsOfTerms (c.rhsCtx L) vars ts = some ss → c.definedTerms ts = true →
        ∃ vs : List GroundTerm, EvalTerms c σ ts (vs.map some)
    | [], _, _, _ => ⟨[], EvalTerms.nil⟩
    | t :: ts, _, hts, hd => by
      obtain ⟨s, ss', ht, hts', rfl⟩ := sortsOfTerms_cons.mp hts
      simp only [Semantics.definedTerms, Bool.and_eq_true] at hd
      obtain ⟨v, hv⟩ := definedTerm_sound hc htot hs hL hσ t ht hd.1
      obtain ⟨vs, hvs⟩ := definedTerms_sound hc htot hs hL hσ ts hts' hd.2
      exact ⟨v :: vs, EvalTerms.cons hv hvs⟩
end

/-- The functions of the definition's own, with the sort predicates, are the heads a right-hand
side may call. -/
theorem headsOK_fns (c : Semantics) : HeadsOK c (c.fns.map Fn.sig) := fun k hk => by
  obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hk
  exact ⟨g, List.mem_append_left _ hg, rfl⟩

/-- **The decider is sound**: in a core that `sortedOK` and `srReady` accept, where the functions
declared `[total]` are defined at every argument list of their sorts, a term `definedArg` accepts
evaluates to a value under every well-sorted substitution of its variables. -/
theorem Semantics.definedArg_sound {c : Semantics} (hok : c.sortedOK = true) (hsr : c.srReady = true) (hov : c.OvlCase)
    (htot : c.TotalsDefined) {vars : List Srt} {t : Term} (hd : c.definedArg vars t = true)
    {σ : Subst} (hσ : c.WellSorted vars σ) : ∃ v, EvalTerm c σ t (some v) := by
  simp only [Semantics.definedArg, Bool.and_eq_true] at hd
  obtain ⟨⟨hsort, hs⟩, hdt⟩ := hd
  obtain ⟨s, hs'⟩ := Option.isSome_iff_exists.mp hsort
  exact definedTerm_sound (sortCtx_of_all hok hsr hov) htot hs (headsOK_fns c) hσ t hs' hdt

/-! ## Every occurrence's obligation holds -/

mutual
  theorem occsOf_mem {site : LazySite} {vars : List Srt} {o : LazyOcc} :
      ∀ {path : List Nat} (t : Term), o ∈ c.occsOf site vars path t → o.site = site ∧ o.vars = vars
    | path, .app f ts, h => by
      simp only [Semantics.occsOf, List.mem_append] at h
      rcases h with h | h
      · cases hl : c.lazyHookOf f with
        | none => rw [hl] at h; cases h
        | some g =>
          rw [hl] at h
          obtain ⟨⟨gd, w, i, t⟩, _, rfl⟩ := List.mem_map.mp h
          exact ⟨rfl, rfl⟩
      · exact occsOfList_mem 0 ts h
    | path, .inj _ _ t, h => by
      simp only [Semantics.occsOf] at h
      exact occsOf_mem t h
    | path, .as t _, h => by
      simp only [Semantics.occsOf] at h
      exact occsOf_mem t h
    | _, .var _, h => by simp [Semantics.occsOf] at h
    | _, .dv _ _, h => by simp [Semantics.occsOf] at h
  theorem occsOfList_mem {site : LazySite} {vars : List Srt} {o : LazyOcc} :
      ∀ {path : List Nat} (i : Nat) (ts : List Term), o ∈ c.occsOfList site vars path i ts →
        o.site = site ∧ o.vars = vars
    | _, _, [], h => by simp [Semantics.occsOfList] at h
    | path, i, t :: ts, h => by
      simp only [Semantics.occsOfList, List.mem_append] at h
      rcases h with h | h
      · exact occsOf_mem t h
      · exact occsOfList_mem (i + 1) ts h
end

theorem occsOfReq_mem {site : LazySite} {vars : List Srt} {o : LazyOcc} {req : Option Term}
    (h : o ∈ c.occsOfReq site vars req) : o.site = site ∧ o.vars = vars := by
  cases req with
  | none => simp [Semantics.occsOfReq] at h
  | some t => exact occsOf_mem t h

/-- An occurrence lies in a rule or a clause of the definition, and its variable sorts are that
rule's or clause's. -/
theorem lazyOccs_mem {o : LazyOcc} (h : o ∈ c.lazyOccs) :
    (∃ i r, c.rules[i]? = some r ∧ (o.site = .ruleReq i ∨ o.site = .ruleRhs i ∨ o.site = .ruleEns i) ∧
      o.vars = r.vars) ∨
    (∃ fn ∈ c.fns, ∃ j cl, fn.clauses[j]? = some cl ∧
      (o.site = .clauseReq fn.label j ∨ o.site = .clauseRhs fn.label j ∨ o.site = .clauseEns fn.label j) ∧
        o.vars = cl.vars) := by
  simp only [Semantics.lazyOccs, List.mem_append, List.mem_flatMap] at h
  rcases h with ⟨⟨r, i⟩, hri, h⟩ | ⟨fn, hfn, h⟩
  · have hr : c.rules[i]? = some r := List.mem_zipIdx_iff_getElem?.mp hri
    simp only at h
    rcases h with h | h | h
    · obtain ⟨h1, h2⟩ := occsOfReq_mem h
      exact Or.inl ⟨i, r, hr, Or.inl h1, h2⟩
    · obtain ⟨h1, h2⟩ := occsOf_mem _ h
      exact Or.inl ⟨i, r, hr, Or.inr (Or.inl h1), h2⟩
    · obtain ⟨h1, h2⟩ := occsOfReq_mem h
      exact Or.inl ⟨i, r, hr, Or.inr (Or.inr h1), h2⟩
  · obtain ⟨⟨cl, j⟩, hcj, h⟩ := h
    have hcl : fn.clauses[j]? = some cl := List.mem_zipIdx_iff_getElem?.mp hcj
    simp only at h
    rcases h with h | h | h
    · obtain ⟨h1, h2⟩ := occsOfReq_mem h
      exact Or.inr ⟨fn, hfn, j, cl, hcl, Or.inl h1, h2⟩
    · obtain ⟨h1, h2⟩ := occsOf_mem _ h
      exact Or.inr ⟨fn, hfn, j, cl, hcl, Or.inr (Or.inl h1), h2⟩
    · obtain ⟨h1, h2⟩ := occsOfReq_mem h
      exact Or.inr ⟨fn, hfn, j, cl, hcl, Or.inr (Or.inr h1), h2⟩

/-- Where an occurrence is reached, σ is well sorted for its variables. -/
theorem Semantics.Reached.wellSorted {c : Semantics} (hok : c.sortedOK = true) (hsr : c.srReady = true) (hov : c.OvlCase)
    {o : LazyOcc} (ho : o ∈ c.lazyOccs) {σ : Subst} (hR : c.Reached o.site σ) :
    c.WellSorted o.vars σ := by
  have hc := sortCtx_of_all hok hsr hov
  have hlook : ∀ fn ∈ c.fns, c.lookupFn fn.label = some fn := fun fn hfn => by
    rw [Semantics.lookupFn_eq]; exact find?_label hc.nodupFns (List.mem_append_left _ hfn)
  rcases lazyOccs_mem ho with ⟨i, r, hr, hs, hv⟩ | ⟨fn, hfn, j, cl, hcl, hs, hv⟩
  · rw [hv]
    rcases hs with hs | hs | hs <;> rw [hs] at hR <;> obtain ⟨r', hr', hσ, _⟩ := hR <;>
      (rw [hr] at hr'; cases hr'; exact hσ)
  · rw [hv]
    rcases hs with hs | hs | hs <;> rw [hs] at hR <;> obtain ⟨fn', cl', hfn', hcl', hσ, _⟩ := hR <;>
      (rw [hlook fn hfn] at hfn'; cases hfn'; rw [hcl] at hcl'; cases hcl'; exact hσ)

/-- An occurrence whose skipped argument `definedArg` confirms meets its obligation. -/
theorem LazyOcc.holds_of_definedArg {c : Semantics} (hok : c.sortedOK = true) (hsr : c.srReady = true)
    (hov : c.OvlCase) (htot : c.TotalsDefined) {o : LazyOcc} (ho : o ∈ c.lazyOccs)
    (hd : c.definedArg o.vars o.skipped = true) : o.Holds c :=
  fun _ hR _ => c.definedArg_sound hok hsr hov htot hd (hR.wellSorted hok hsr hov ho)

/-- With the lazy obligations (`Obligations`' last conjunct), every occurrence meets its
obligation. -/
theorem lazyOccs_hold {c : Semantics} (hok : c.sortedOK = true) (hsr : c.srReady = true)
    (hov : c.OvlCase) (htot : c.TotalsDefined) (hob : ∀ o ∈ c.lazyObligations, o.Holds c) :
    ∀ o ∈ c.lazyOccs, o.Holds c := fun o ho => by
  cases hd : c.definedArg o.vars o.skipped
  · exact hob o (List.mem_filter.mpr ⟨ho, by simp [hd]⟩)
  · exact LazyOcc.holds_of_definedArg hok hsr hov htot ho hd

/-! ## What an obligation gives: the strict result is the short-circuit one -/

section Agree
variable {σ : Subst} {f : Sym} {k : ParamSig} {C A B : Term}

/-- `ite{S}(C, A, B)` with C true: the strict result is A's, B evaluated to a value. -/
theorem iteParam_true (hp : c.lookupParam f = some k) (hk : k.impl = some kIte)
    (hc : c.isCtor f = false) (hh : isHook f = false)
    {rA : Option GroundTerm} {w : GroundTerm}
    (hC : EvalTerm c σ C (some (bool true))) (hA : EvalTerm c σ A rA)
    (hAs : ∀ a, rA = some a → c.sortOf a = some k.sig.result)
    (hB : EvalTerm c σ B (some w)) : EvalTerm c σ (.app f [C, A, B]) rA := by
  have hpar : c.isParam f = true := by simp [Semantics.isParam, hp]
  refine EvalTerm.param hc hh hpar (.cons hC (.cons hA (.cons hB .nil))) ?_
  cases rA with
  | none => rfl
  | some a =>
    show some a = c.paramVal f [bool true, a, w]
    rw [paramVal_ite hp hk true (by simpa using hAs a rfl)]
    rfl

/-- `ite{S}(C, A, B)` with C false: the strict result is B's, A evaluated to a value. -/
theorem iteParam_false (hp : c.lookupParam f = some k) (hk : k.impl = some kIte)
    (hc : c.isCtor f = false) (hh : isHook f = false)
    {rB : Option GroundTerm} {w : GroundTerm}
    (hC : EvalTerm c σ C (some (bool false))) (hA : EvalTerm c σ A (some w))
    (hB : EvalTerm c σ B rB) (hBs : ∀ b, rB = some b → c.sortOf b = some k.sig.result) :
    EvalTerm c σ (.app f [C, A, B]) rB := by
  have hpar : c.isParam f = true := by simp [Semantics.isParam, hp]
  refine EvalTerm.param hc hh hpar (.cons hC (.cons hA (.cons hB .nil))) ?_
  cases rB with
  | none => rfl
  | some b =>
    show some b = c.paramVal f [bool false, w, b]
    rw [paramVal_ite hp hk false (by simpa using hBs b rfl)]
    rfl

/-- Strictness: where the skipped argument is undefined, so is `ite{S}(C, A, B)`, whatever C. -/
theorem iteParam_skipped_undef (hp : c.lookupParam f = some k) (hc : c.isCtor f = false)
    (hh : isHook f = false) {rC rA : Option GroundTerm}
    (hC : EvalTerm c σ C rC) (hA : EvalTerm c σ A rA) (hB : EvalTerm c σ B none) :
    EvalTerm c σ (.app f [C, A, B]) none := by
  have hpar : c.isParam f = true := by simp [Semantics.isParam, hp]
  refine EvalTerm.param hc hh hpar (.cons hC (.cons hA (.cons hB .nil))) ?_
  cases rC <;> cases rA <;> rfl

/-- With evaluation functional (`CoherentAll`), every strict result of `ite{S}(C, A, B)`
with C true is A's, B evaluated to a value. -/
theorem iteParam_true_eq (hmi : CoherentAll c) (hp : c.lookupParam f = some k)
    (hk : k.impl = some kIte) (hc : c.isCtor f = false) (hh : isHook f = false)
    {rA r : Option GroundTerm} {w : GroundTerm}
    (hC : EvalTerm c σ C (some (bool true))) (hA : EvalTerm c σ A rA)
    (hAs : ∀ a, rA = some a → c.sortOf a = some k.sig.result)
    (hB : EvalTerm c σ B (some w)) (h : EvalTerm c σ (.app f [C, A, B]) r) : r = rA :=
  EvalTerm.functional hmi h (iteParam_true hp hk hc hh hC hA hAs hB)

/-- `A andBool B` with A false: the strict result is false, B evaluated to a Bool. -/
theorem andBool_false (hc : c.isCtor boolAnd = false) {b : Bool}
    (hA : EvalTerm c σ A (some (bool false))) (hB : EvalTerm c σ B (some (bool b))) :
    EvalTerm c σ (.app boolAnd [A, B]) (some (bool false)) :=
  EvalTerm.hook hc rfl (.cons hA (.cons hB .nil))
    (fun vs h => by
      simp only [allSome, Option.bind_some, Option.map_some, Option.some.injEq] at h; subst h
      exact Semantics.hookRes_of_value rfl)
    (fun h => by cases h)

/-- `A orBool B` with A true: the strict result is true, B evaluated to a Bool. -/
theorem orBool_true (hc : c.isCtor boolOr = false) {b : Bool}
    (hA : EvalTerm c σ A (some (bool true))) (hB : EvalTerm c σ B (some (bool b))) :
    EvalTerm c σ (.app boolOr [A, B]) (some (bool true)) :=
  EvalTerm.hook hc rfl (.cons hA (.cons hB .nil))
    (fun vs h => by
      simp only [allSome, Option.bind_some, Option.map_some, Option.some.injEq] at h; subst h
      exact Semantics.hookRes_of_value rfl)
    (fun h => by cases h)

/-- Strictness: where B is undefined, so is `A andBool B`, whatever A. -/
theorem andBool_skipped_undef (hc : c.isCtor boolAnd = false) {rA : Option GroundTerm}
    (hA : EvalTerm c σ A rA) (hB : EvalTerm c σ B none) :
    EvalTerm c σ (.app boolAnd [A, B]) none :=
  EvalTerm.hook hc rfl (.cons hA (.cons hB .nil))
    (fun vs h => by cases rA <;> simp [allSome] at h)
    (fun _ => rfl)

/-- With evaluation functional, every strict result of `A andBool B` with A false is false, B
evaluated to a Bool. -/
theorem andBool_false_eq (hmi : CoherentAll c) (hc : c.isCtor boolAnd = false) {b : Bool}
    {r : Option GroundTerm} (hA : EvalTerm c σ A (some (bool false)))
    (hB : EvalTerm c σ B (some (bool b))) (h : EvalTerm c σ (.app boolAnd [A, B]) r) :
    r = some (bool false) :=
  EvalTerm.functional hmi h (andBool_false hc hA hB)

end Agree

/-- **What the obligation buys**, for `ite{S}`: at an occurrence of `ite{S}(C, A, B)` that is
skipped when C is true and whose obligation holds, reached under σ with C true, the strict result is
A's, in a core `sortedOK` and `srReady` accept, A well sorted at S. -/
theorem LazyOcc.iteParam_true {c : Semantics} (hok : c.sortedOK = true) (hsr : c.srReady = true) (hov : c.OvlCase)
    {o : LazyOcc} (hO : o.Holds c) {σ : Subst} (hR : c.Reached o.site σ)
    (hσ : c.WellSorted o.vars σ) {f : Sym} {k : ParamSig} {C A B : Term}
    (hp : c.lookupParam f = some k) (hk : k.impl = some kIte) (hc : c.isCtor f = false)
    (hh : isHook f = false) (hg : o.guard = C) (hw : o.skipWhen = true) (hsk : o.skipped = B)
    (hAs : sortOfTerm (c.rhsCtx (c.fns.map Fn.sig)) o.vars A = some k.sig.result)
    {rA : Option GroundTerm} (hC : EvalTerm c σ C (some (bool true))) (hA : EvalTerm c σ A rA) :
    EvalTerm c σ (.app f [C, A, B]) rA := by
  obtain ⟨w, hB⟩ := hO σ hR (by rw [hg, hw]; exact hC)
  rw [hsk] at hB
  exact KCore.iteParam_true hp hk hc hh hC hA
    (fun a ha => EvalTerm.sorted (sortCtx_of_all hok hsr hov) hA (headsOK_fns c) hσ hAs ha) hB

/-- **What the obligation buys**, for `_andBool_`: at an occurrence of `A andBool B` whose
obligation holds, reached under σ with A false, the strict result is false, in a core `sortedOK` and
`srReady` accept whose Bool values are literals (`shapesOK`), B well sorted at Bool. -/
theorem LazyOcc.andBool_false {c : Semantics} (hok : c.sortedOK = true) (hsr : c.srReady = true) (hov : c.OvlCase)
    (hs : c.shapesOK = true) {o : LazyOcc} (hO : o.Holds c) {σ : Subst} (hR : c.Reached o.site σ)
    (hσ : c.WellSorted o.vars σ) {A B : Term} (hc : c.isCtor boolAnd = false)
    (hg : o.guard = A) (hw : o.skipWhen = false) (hsk : o.skipped = B)
    (hBs : sortOfTerm (c.rhsCtx (c.fns.map Fn.sig)) o.vars B = some Srt.bool)
    (hA : EvalTerm c σ A (some (bool false))) :
    EvalTerm c σ (.app boolAnd [A, B]) (some (bool false)) := by
  obtain ⟨w, hB⟩ := hO σ hR (by rw [hg, hw]; exact hA)
  rw [hsk] at hB
  obtain ⟨b, rfl⟩ := shape_bool hs
    (EvalTerm.sorted (sortCtx_of_all hok hsr hov) hB (headsOK_fns c) hσ hBs rfl)
  exact KCore.andBool_false hc hA hB

end KCore
