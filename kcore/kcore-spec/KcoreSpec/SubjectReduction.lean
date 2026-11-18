/-
  Subject reduction (checked layer; no statement reads it).

  `Step c x y` takes `y : Config c`, so a rule application whose right-hand side evaluated to a
  non-configuration would be lost. This module proves it never is, for a core that
  `Semantics.sortedOK` accepts and that passes two decidable checks on its data
  (`Semantics.srReady`: function labels distinct, subsort pairs closed under composition, every
  Range value a KItem):
  - `Eval.sorted`: a function at arguments of its argument sorts, when defined, has a value of
    its result sort;
  - `rhs_sorted_core`: a rule's right-hand side, evaluated under a well-sorted σ, is a configuration
    when defined; so every application is a step (`step_of_apply_core`).
  The argument reads the right-hand sides of rules and clauses, all sorted in `rhsCtx`, never a left-hand side: σ's sorts are a premise of `Step`, not derived from
  the match. So it holds alike for left-hand sides with collection patterns (`patCtxAll`), and the
  forms over `Semantics.okAll` (`rhs_sorted_all`, `step_of_apply_all`) and `Semantics.ok`
  (`rhs_sorted`, `step_of_apply`, `Eval.sorted_of`) are corollaries (`sortedOK_of_okAll`,
  `okAll_of_ok`).
  An interpreted hook returns a value of its declared result sort (`hook_sorted`; RANGEMAP's `keys`
  where every Range value is a KItem, `RangeBelow`, which `SortCtx` holds; a Float result is
  an encoding of its format, `KFloat.validBits_pack`; a String or Bytes result is made of its
  arguments' characters, `dvOK_tok_of`): Bool and Int
  results are canonical literals (`intLit?_intRepr`), the map and set operations keep keys sorted
  and entries of sort KItem (OrderLaws.lean, SetLaws.lean); the generated sort predicates are
  well-formed functions (`sortPreds_ctx`). `srReady` follows from `wf` (`srReady_of_wf`,
  NamesApart.lean).
-/
import KcoreSpec.SetLaws
import KcoreSpec.Step
import KcoreSpec.Tie
import KcoreSpec.OvlLawsFn
import KcoreSpec.RangeMapSorted

set_option autoImplicit false

namespace KCore

theorem digitVal_digitChar : ∀ d < 10, digitVal (Nat.digitChar d) = some d := by decide

theorem digitChar_props : ∀ d < 10, (d ≠ 0 → Nat.digitChar d ≠ '0') ∧ Nat.digitChar d ≠ '-' := by decide

theorem digitsVal_append : ∀ (l l' : List Char) (acc : Nat),
    digitsVal (l ++ l') acc = (digitsVal l acc).bind (digitsVal l')
  | [], l', acc => by simp [digitsVal]
  | ch :: l, l', acc => by
    simp only [List.cons_append, digitsVal]
    cases digitVal ch with
    | none => rfl
    | some d => simp only [Option.bind_some]; exact digitsVal_append l l' _

theorem digitsVal_toDigits : ∀ n : Nat, digitsVal (Nat.toDigits 10 n) 0 = some n := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases hn : n < 10
    · rw [Nat.toDigits_of_lt_base hn]
      simp [digitsVal, digitVal_digitChar n hn]
    · rw [Nat.toDigits_of_base_le (by decide) (by omega), digitsVal_append,
        ih (n / 10) (by omega), Option.bind_some]
      simp only [digitsVal, digitVal_digitChar (n % 10) (Nat.mod_lt _ (by decide)), Option.bind_some]
      congr 1
      omega

theorem toDigits_head : ∀ n : Nat, ∃ d ds, Nat.toDigits 10 n = d :: ds ∧ (n ≠ 0 → d ≠ '0') ∧ d ≠ '-' := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases hn : n < 10
    · rw [Nat.toDigits_of_lt_base hn]
      exact ⟨_, [], rfl, (digitChar_props n hn).1, (digitChar_props n hn).2⟩
    · obtain ⟨d, ds, he, h1, h2⟩ := ih (n / 10) (by omega)
      rw [Nat.toDigits_of_base_le (by decide) (by omega), he]
      exact ⟨d, ds ++ _, rfl, fun _ => h1 (by omega), h2⟩

theorem intLit?_intRepr (i : Int) : intLit? (intRepr i) = some i := by
  cases i with
  | ofNat n =>
    simp only [intRepr, intLit?, Nat.repr_eq_ofList_toDigits, String.toList_ofList]
    obtain ⟨d, ds, he, h1, h2⟩ := toDigits_head n
    by_cases hn : n = 0
    · subst hn; simp [Nat.toDigits_zero]
    · have hval := digitsVal_toDigits n
      rw [he] at hval ⊢
      have hd : d ≠ '0' := h1 hn
      split
      · rename_i heq; cases heq; exact absurd rfl hd
      · rename_i d' ds' heq; cases heq; exact absurd rfl h2
      · rename_i d' ds' _ _ heq; cases heq; simp [hd, hval]
      · rename_i heq; cases heq
  | negSucc n =>
    simp only [intRepr, intLit?, String.toList_append, Nat.repr_eq_ofList_toDigits, String.toList_ofList]
    obtain ⟨d, ds, he, h1, h2⟩ := toDigits_head (n + 1)
    have hval := digitsVal_toDigits (n + 1)
    rw [he] at hval ⊢
    have hd : d ≠ '0' := h1 (by omega)
    simp [hd, hval]
    rfl

variable {c : Semantics}

/-! ## Inversion of `sortOf` -/

/-- A constructor applied to values of its argument sorts is a value of its result sort. -/
theorem sortOf_ctor_intro {f : Sym} {ts : List GroundTerm} {s : Srt}
    (h : ∃ k, lookupSig c.ctorSigs f = some k ∧ c.sortsOf ts = some k.args ∧ s = k.result) :
    c.sortOf (.ctor f ts) = some s :=
  c.sortOf_ctor_iff.mpr (.inl h)

/-- Without overloading symbols and raw parameters, a constructor term's sort is its constructor's
(the second hypothesis is decided where `c` is closed). -/
theorem sortOf_ctor (hno : c.ovls = []) {f : Sym} {ts : List GroundTerm} {s : Srt}
    (hr : ∀ k ∈ c.params, k.raw = false := by decide +kernel) :
    c.sortOf (.ctor f ts) = some s ↔
      ∃ k, lookupSig c.ctorSigs f = some k ∧ c.sortsOf ts = some k.args ∧ s = k.result :=
  c.sortOf_ctor_of_none hno hr

/-- The sort of a constructor's term is its result sort. -/
theorem sortOf_ctor_of_isCtor {f : Sym} {ts : List GroundTerm} {s : Srt} (hf : c.isCtor f = true) :
    c.sortOf (.ctor f ts) = some s ↔
      ∃ k, lookupSig c.ctorSigs f = some k ∧ c.sortsOf ts = some k.args ∧ s = k.result := by
  refine ⟨fun h => ?_, sortOf_ctor_intro⟩
  rcases c.sortOf_ctor_iff.mp h with h | ⟨hk, -⟩ | ⟨hk, -⟩
  · exact h
  · simp [Semantics.isCtor, hk] at hf
  · simp [Semantics.isCtor, hk] at hf

theorem sortOf_inj {a b : Srt} {t : GroundTerm} {s : Srt} :
    c.sortOf (.inj a b t) = some s ↔
      (a, b) ∈ c.subsorts ∧ t.isInj = false ∧ c.sortOf t = some a ∧ s = b := by
  simp only [Semantics.sortOf]
  constructor
  · intro h
    split at h
    · rename_i hc
      simp only [Bool.and_eq_true, List.contains_iff_mem, Bool.not_eq_true', beq_iff_eq] at hc
      exact ⟨hc.1.1, hc.1.2, hc.2, (Option.some.inj h).symm⟩
    · cases h
  · rintro ⟨h1, h2, h3, rfl⟩
    simp [h1, h2, h3]

theorem sortsOf_nil : c.sortsOf [] = some [] := by simp [Semantics.sortsOf]

theorem sortsOf_cons {t : GroundTerm} {ts : List GroundTerm} {ss : List Srt} :
    c.sortsOf (t :: ts) = some ss ↔
      ∃ s ss', c.sortOf t = some s ∧ c.sortsOf ts = some ss' ∧ ss = s :: ss' := by
  simp only [Semantics.sortsOf]
  cases h1 : c.sortOf t <;> cases h2 : c.sortsOf ts <;> simp [eq_comm]

theorem entriesOK_iff {ks vs : Srt} {es : Entries} :
    c.entriesOK ks vs es = true ↔ ∀ e ∈ es, c.sortOf e.1 = some ks ∧ c.sortOf e.2 = some vs := by
  induction es with
  | nil => simp [Semantics.entriesOK]
  | cons e es ih =>
    obtain ⟨k, v⟩ := e
    simp only [Semantics.entriesOK, Semantics.entryOK, Bool.and_eq_true, beq_iff_eq, ih,
      List.forall_mem_cons]

/-- The library's collection sorts are found first. -/
theorem collOf_map : c.collOf Srt.map = some builtinColls[0] := rfl
theorem collOf_set : c.collOf Srt.set = some builtinColls[1] := rfl
theorem collOf_list : c.collOf Srt.list = some builtinColls[2] := rfl
theorem collOf_rangeMap : c.collOf Srt.rangeMap = some (builtinColl .rangeMap) := rfl

theorem sortOf_mapS_iff {s : Srt} {es : Entries} {t : Srt} :
    c.sortOf (.map s es) = some t ↔ ∃ k vs, c.collOf s = some k ∧ k.val = some vs ∧
      (match k.kind with | .map => keysSorted es | .rangeMap => rangesOK es | _ => false) = true ∧
      c.entriesOK k.key vs es = true ∧ t = s := by
  constructor
  · exact c.sortOf_map_inv
  · rintro ⟨k, vs, hk, hv, h1, h2, rfl⟩
    simp only [Semantics.sortOf, hk, hv]
    simp only [h2, Bool.and_true]
    exact if_pos h1

/-- A map value of a collection sort: the collection is a map or a range map, and either way its
keys are sorted. -/
theorem sortOf_mapS_fwd {s : Srt} {es : Entries} {t : Srt} (h : c.sortOf (.map s es) = some t) :
    ∃ k vs, c.collOf s = some k ∧ (k.kind = .map ∨ k.kind = .rangeMap) ∧ k.val = some vs ∧
      keysSorted es = true ∧ c.entriesOK k.key vs es = true ∧ t = s := by
  obtain ⟨k, vs, hk, hv, h1, h2, rfl⟩ := sortOf_mapS_iff.mp h
  exact ⟨k, vs, hk, (mapKeys_sorted h1).1, hv, (mapKeys_sorted h1).2, h2, rfl⟩

/-- At a collection of kind `.map`, the map values are the maps with sorted keys and entries of
its sorts. -/
theorem sortOf_mapS_map {s : Srt} {es : Entries} {t : Srt} {k : CollSig} (hk : c.collOf s = some k)
    (hkind : k.kind = .map) :
    c.sortOf (.map s es) = some t ↔ ∃ vs, k.val = some vs ∧ keysSorted es = true ∧
      c.entriesOK k.key vs es = true ∧ t = s := by
  rw [sortOf_mapS_iff]
  constructor
  · rintro ⟨k', vs, hk', hv, h1, h2, rfl⟩
    rw [hk] at hk'; cases hk'
    rw [hkind] at h1
    exact ⟨vs, hv, h1, h2, rfl⟩
  · rintro ⟨vs, hv, h1, h2, rfl⟩
    exact ⟨k, vs, hk, hv, by rw [hkind]; exact h1, h2, rfl⟩

theorem sortOf_map {es : Entries} {s t : Srt} :
    c.sortOf (.map s es) = some t → s = t := by
  intro h; obtain ⟨_, _, _, _, _, _, _, rfl⟩ := sortOf_mapS_fwd h; rfl

/-- A map of the library's sort `Map`: sorted keys, entries of sort KItem. -/
theorem sortOf_Map {es : Entries} :
    c.sortOf (.map Srt.map es) = some Srt.map ↔
      keysSorted es = true ∧ c.entriesOK Srt.kitem Srt.kitem es = true := by
  rw [sortOf_mapS_map collOf_map rfl]
  constructor
  · rintro ⟨vs, hv, h1, h2, _⟩; cases hv; exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨_, rfl, h1, h2, rfl⟩

theorem sortOf_bool (b : Bool) : c.sortOf (bool b) = some Srt.bool := by
  cases b <;> rfl

theorem sortOf_int (i : Int) : c.sortOf (int i) = some Srt.int := by
  simp [int, Semantics.sortOf, dvOK]

theorem sortOf_dv {s t : Srt} {lit : Lit} : c.sortOf (.dv s lit) = some t ↔ dvOK c.lib s lit = true ∧ t = s := by
  simp only [Semantics.sortOf]
  by_cases h : dvOK c.lib s lit = true <;> simp [h, eq_comm]

theorem sortsOf_all {es : List GroundTerm} {ss : List Srt} {s : Srt} (h : c.sortsOf es = some ss) :
    ss.all (· == s) = true ↔ ∀ e ∈ es, c.sortOf e = some s := by
  induction es generalizing ss with
  | nil => rw [sortsOf_nil] at h; cases h; simp
  | cons e es ih =>
    obtain ⟨s₀, ss', h1, h2, rfl⟩ := sortsOf_cons.mp h
    simp only [List.all_cons, Bool.and_eq_true, beq_iff_eq, ih h2, List.forall_mem_cons, h1,
      Option.some.injEq]

theorem sortsOf_const {es : List GroundTerm} {s : Srt} (h : ∀ e ∈ es, c.sortOf e = some s) :
    c.sortsOf es = some (es.map fun _ => s) := by
  induction es with
  | nil => exact sortsOf_nil
  | cons e es ih =>
    exact sortsOf_cons.mpr ⟨_, _, h e (List.mem_cons_self ..),
      ih (fun e' he' => h e' (List.mem_cons_of_mem _ he')), rfl⟩

theorem sortOf_setS {s : Srt} {es : List GroundTerm} {t : Srt} :
    c.sortOf (.set s es) = some t ↔ ∃ k, c.collOf s = some k ∧ k.kind = .set ∧
      elemsSorted es = true ∧ (∀ e ∈ es, c.sortOf e = some k.key) ∧ t = s := by
  simp only [Semantics.sortOf]
  constructor
  · intro h
    split at h
    · rename_i k ss hk hss
      split at h
      · rename_i hc
        simp only [Bool.and_eq_true, beq_iff_eq] at hc
        exact ⟨k, hk, hc.1.1, hc.1.2, (sortsOf_all hss).mp hc.2, (Option.some.inj h).symm⟩
      · cases h
    · cases h
  · rintro ⟨k, hk, h0, h1, h2, rfl⟩
    rw [hk, sortsOf_const h2]
    simp only [h0, h1, beq_self_eq_true, Bool.true_and]
    rw [if_pos ((sortsOf_all (sortsOf_const h2)).mpr h2)]

theorem sortOf_listS {s : Srt} {es : List GroundTerm} {t : Srt} :
    c.sortOf (.list s es) = some t ↔ ∃ k, c.collOf s = some k ∧ k.kind = .list ∧
      (∀ e ∈ es, c.sortOf e = some k.key) ∧ t = s := by
  simp only [Semantics.sortOf]
  constructor
  · intro h
    split at h
    · rename_i k ss hk hss
      split at h
      · rename_i hc
        simp only [Bool.and_eq_true, beq_iff_eq] at hc
        exact ⟨k, hk, hc.1, (sortsOf_all hss).mp hc.2, (Option.some.inj h).symm⟩
      · cases h
    · cases h
  · rintro ⟨k, hk, h0, h2, rfl⟩
    rw [hk, sortsOf_const h2]
    simp only [h0, beq_self_eq_true, Bool.true_and]
    rw [if_pos ((sortsOf_all (sortsOf_const h2)).mpr h2)]

theorem sortOf_set_of {es : List GroundTerm} (h1 : es.Pairwise fun a b => GroundTerm.cmp a b = .lt)
    (h2 : ∀ e ∈ es, c.sortOf e = some Srt.kitem) : c.sortOf (.set Srt.set es) = some Srt.set :=
  sortOf_setS.mpr ⟨_, collOf_set, rfl, elemsSorted_iff.mpr h1, h2, rfl⟩

theorem setOK_of {s : Srt} {es : List GroundTerm} (h : c.sortOf (.set s es) = some Srt.set) :
    (es.Pairwise fun a b => GroundTerm.cmp a b = .lt) ∧ ∀ e ∈ es, c.sortOf e = some Srt.kitem := by
  obtain ⟨k, hk, _, h1, h2, rfl⟩ := sortOf_setS.mp h
  rw [collOf_set] at hk; cases hk
  exact ⟨elemsSorted_iff.mp h1, h2⟩

theorem sortOf_list_of {es : List GroundTerm} (h2 : ∀ e ∈ es, c.sortOf e = some Srt.kitem) :
    c.sortOf (.list Srt.list es) = some Srt.list :=
  sortOf_listS.mpr ⟨_, collOf_list, rfl, h2, rfl⟩

theorem listOK_of {s : Srt} {es : List GroundTerm} (h : c.sortOf (.list s es) = some Srt.list) :
    ∀ e ∈ es, c.sortOf e = some Srt.kitem := by
  obtain ⟨k, hk, _, h2, rfl⟩ := sortOf_listS.mp h
  rw [collOf_list] at hk; cases hk
  exact h2

/-! ## Hooks return values of their declared result sort -/

theorem sortsOf_eq_cons {t : GroundTerm} {ts : List GroundTerm} {s : Srt} {ss : List Srt} :
    c.sortsOf (t :: ts) = some (s :: ss) ↔ c.sortOf t = some s ∧ c.sortsOf ts = some ss := by
  rw [sortsOf_cons]
  constructor
  · rintro ⟨s', ss', h1, h2, he⟩; cases he; exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨s, ss, h1, h2, rfl⟩

theorem entriesOK_of {s : Srt} {es : Entries} (h : c.sortOf (.map s es) = some Srt.map) :
    keysSorted es = true ∧ ∀ e ∈ es, c.sortOf e.1 = some Srt.kitem ∧ c.sortOf e.2 = some Srt.kitem := by
  have hs := sortOf_map h; subst hs
  obtain ⟨h1, h2⟩ := sortOf_Map.mp h
  exact ⟨h1, entriesOK_iff.mp h2⟩

theorem sortOf_map_of {es : Entries} (h1 : keysSorted es = true)
    (h2 : ∀ e ∈ es, c.sortOf e.1 = some Srt.kitem ∧ c.sortOf e.2 = some Srt.kitem) :
    c.sortOf (.map Srt.map es) = some Srt.map :=
  sortOf_Map.mpr ⟨h1, entriesOK_iff.mpr h2⟩


theorem bool2_some {vs : List GroundTerm} {g : Bool → Bool → Bool} {v : GroundTerm}
    (h : bool2 vs g = some v) : ∃ b, v = bool b := by
  unfold bool2 at h
  split at h
  · simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨_, _, _, _, rfl⟩ := h
    exact ⟨_, rfl⟩
  · cases h

theorem int2_some {vs : List GroundTerm} {g : Int → Int → Option GroundTerm} {v : GroundTerm}
    (h : int2 vs g = some v) : ∃ x y, g x y = some v := by
  unfold int2 at h
  split at h
  · simp only [Option.bind_eq_some_iff] at h
    obtain ⟨x, _, y, _, h⟩ := h
    exact ⟨x, y, h⟩
  · cases h

theorem nonzero_some {y r : Int} {v : GroundTerm} (h : nonzero y r = some v) : v = int r := by
  unfold nonzero at h
  split at h
  · cases h
  · exact (Option.some.inj h).symm

/-- The hooked symbols are those with a signature, and conversely (decided on the tables). -/
theorem hookSigs_hooked : ∀ k ∈ hookSigs, isHook k.name = true := by decide +kernel

theorem hookTable_sig : ∀ e ∈ hookTable, (lookupSig hookSigs e.1).isSome = true := by decide +kernel

theorem lookupSig_spec {heads : List CtorSig} {g : Sym} {sig : CtorSig}
    (h : lookupSig heads g = some sig) : sig ∈ heads ∧ sig.name = g := by
  rw [lookupSig_eq] at h
  exact ⟨List.mem_of_find?_eq_some h, by simpa using List.find?_some h⟩

theorem listIndex_lt {n : Nat} {i : Int} {j : Nat} (h : listIndex n i = some j) : j < n := by
  unfold listIndex at h
  split at h
  · split at h
    · cases h; omega
    · cases h
  · split at h
    · cases h; omega
    · cases h

theorem listRangeOf_mem {es : List GroundTerm} {a b : Int} {r : List GroundTerm}
    (h : listRangeOf es a b = some r) : ∀ e ∈ r, e ∈ es := by
  unfold listRangeOf at h
  split at h
  · cases h
    intro e he
    exact List.mem_of_mem_drop (List.mem_of_mem_take he)
  · cases h

/-- `ite` returns one of its last two arguments, of sort KItem. -/
theorem iteHook_sorted {f : Sym} {g : List GroundTerm → Option GroundTerm} {k : CtorSig}
    {ws : List GroundTerm} {v : GroundTerm} (hmem : (f, g) ∈ iteHooks)
    (hk : lookupSig hookSigs f = some k) (hws : c.sortsOf ws = some k.args)
    (hev : g ws = some v) : c.sortOf v = some k.result := by
  simp only [iteHooks, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hmem
  obtain ⟨rfl, rfl⟩ := hmem
  rw [show lookupSig hookSigs kIte = some ⟨kIte, [Srt.bool, Srt.kitem, Srt.kitem], Srt.kitem⟩ by
    decide] at hk
  cases hk
  dsimp only at hws hev ⊢
  split at hev
  · obtain ⟨b, -, rfl⟩ := Option.map_eq_some_iff.mp hev
    simp only [sortsOf_eq_cons] at hws
    cases b
    · exact hws.2.2.1
    · exact hws.2.1
  · cases hev

/-- The interpreted List symbols return values of their declared result sort. -/
theorem listHook_sorted {f : Sym} {g : List GroundTerm → Option GroundTerm} {k : CtorSig}
    {ws : List GroundTerm} {v : GroundTerm} (hmem : (f, g) ∈ listHooks)
    (hk : lookupSig hookSigs f = some k) (hws : c.sortsOf ws = some k.args)
    (hev : g ws = some v) : c.sortOf v = some k.result := by
  simp only [listHooks, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hmem
  rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rw [show lookupSig hookSigs listConcat = some ⟨listConcat, [Srt.list, Srt.list], Srt.list⟩ by
      decide] at hk
    cases hk
    dsimp only at hws hev ⊢
    split at hev
    · obtain rfl := Option.some.inj hev
      simp only [sortsOf_eq_cons] at hws
      have ha := listOK_of hws.1
      have hb := listOK_of hws.2.1
      exact sortOf_list_of fun e he => (List.mem_append.mp he).elim (ha e) (hb e)
    · cases hev
  · rw [show lookupSig hookSigs listUnit = some ⟨listUnit, [], Srt.list⟩ by decide] at hk
    cases hk
    dsimp only at hws hev ⊢
    split at hev
    · obtain rfl := Option.some.inj hev
      exact sortOf_list_of fun _ h => nomatch h
    · cases hev
  · rw [show lookupSig hookSigs listElem = some ⟨listElem, [Srt.kitem], Srt.list⟩ by decide] at hk
    cases hk
    dsimp only at hws hev ⊢
    split at hev
    · obtain rfl := Option.some.inj hev
      simp only [sortsOf_eq_cons] at hws
      exact sortOf_list_of fun e he => by
        simp only [List.mem_singleton] at he; subst he; exact hws.1
    · cases hev
  · rw [show lookupSig hookSigs listPush = some ⟨listPush, [Srt.kitem, Srt.list], Srt.list⟩ by
      decide] at hk
    cases hk
    dsimp only at hws hev ⊢
    split at hev
    · obtain rfl := Option.some.inj hev
      simp only [sortsOf_eq_cons] at hws
      have hb := listOK_of hws.2.1
      exact sortOf_list_of fun e he => (List.mem_cons.mp he).elim (fun h => h ▸ hws.1) (hb e)
    · cases hev
  · rw [show lookupSig hookSigs listGet = some ⟨listGet, [Srt.list, Srt.int], Srt.kitem⟩ by
      decide] at hk
    cases hk
    dsimp only at hws hev ⊢
    split at hev
    · simp only [sortsOf_eq_cons] at hws
      have ha := listOK_of hws.1
      simp only [Option.bind_eq_some_iff] at hev
      obtain ⟨_, _, j, _, hj⟩ := hev
      exact ha v (List.mem_of_getElem? hj)
    · cases hev
  · rw [show lookupSig hookSigs listRange = some ⟨listRange, [Srt.list, Srt.int, Srt.int], Srt.list⟩ by
      decide] at hk
    cases hk
    dsimp only at hws hev ⊢
    split at hev
    · simp only [sortsOf_eq_cons] at hws
      have ha := listOK_of hws.1
      simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at hev
      obtain ⟨_, _, _, _, r, hr, rfl⟩ := hev
      exact sortOf_list_of fun e he => ha e (listRangeOf_mem hr e he)
    · cases hev
  · rw [show lookupSig hookSigs listIn = some ⟨listIn, [Srt.kitem, Srt.list], Srt.bool⟩ by
      decide] at hk
    cases hk
    dsimp only at hws hev ⊢
    split at hev
    · obtain rfl := Option.some.inj hev; exact sortOf_bool _
    · cases hev
  · rw [show lookupSig hookSigs listSize = some ⟨listSize, [Srt.list], Srt.int⟩ by decide] at hk
    cases hk
    dsimp only at hws hev ⊢
    split at hev
    · obtain rfl := Option.some.inj hev; exact sortOf_int _
    · cases hev

/-! ## The interpreted Float symbols return values of their declared result sort -/

theorem floatV_sorted {p e : Nat} {sp : Float.Model.Format} (h : KFloat.spec? p e = some sp)
    (u : Float.Model.UnpackedFloat) : c.sortOf (floatV p e sp u) = some Srt.float := by
  rw [floatV, Semantics.sortOf]
  simp [dvOK, KFloat.ok, h, KFloat.validBits_pack]

theorem asFloat_spec {v : GroundTerm} {p e : Nat} {sp : Float.Model.Format} {u : Float.Model.UnpackedFloat}
    (h : asFloat v = some (p, e, sp, u)) : KFloat.spec? p e = some sp := by
  cases v with
  | dv s lit =>
    cases lit with
    | float p' e' b =>
      simp only [asFloat] at h
      split at h
      · obtain ⟨sp', hs, he⟩ := Option.map_eq_some_iff.mp h
        simp only [Prod.mk.injEq] at he
        obtain ⟨rfl, rfl, rfl, -⟩ := he
        exact hs
      · cases h
    | _ => simp [asFloat] at h
  | _ => simp [asFloat] at h

theorem fl1_sorted {op} {vs : List GroundTerm} {v : GroundTerm} (h : fl1 op vs = some v) :
    c.sortOf v = some Srt.float := by
  unfold fl1 at h
  split at h
  · obtain ⟨⟨p, e, sp, u⟩, ha, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨_, -, rfl⟩ := Option.map_eq_some_iff.mp h
    exact floatV_sorted (asFloat_spec ha) _
  · cases h

theorem fl2_sorted {op} {vs : List GroundTerm} {v : GroundTerm} (h : fl2 op vs = some v) :
    c.sortOf v = some Srt.float := by
  unfold fl2 at h
  split at h
  · obtain ⟨⟨p, e, sp, u⟩, ha, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨⟨p', e', sp', u'⟩, -, h⟩ := Option.bind_eq_some_iff.mp h
    dsimp only at h
    by_cases hpe : p = p' ∧ e = e'
    · rw [if_pos hpe] at h
      obtain ⟨_, -, rfl⟩ := Option.map_eq_some_iff.mp h
      exact floatV_sorted (asFloat_spec ha) _
    · rw [if_neg hpe] at h; cases h
  · cases h

theorem flTo_sorted {op} {vs : List GroundTerm} {v : GroundTerm} (h : flTo op vs = some v) :
    c.sortOf v = some Srt.float := by
  unfold flTo at h
  split at h
  · obtain ⟨_, -, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨p, -, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨e, -, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨sp, hs, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨_, -, rfl⟩ := Option.map_eq_some_iff.mp h
    exact floatV_sorted hs _
  · cases h

theorem flOfInt_sorted {vs : List GroundTerm} {v : GroundTerm} (h : flOfInt vs = some v) :
    c.sortOf v = some Srt.float := by
  unfold flOfInt at h
  split at h
  · obtain ⟨_, -, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨p, -, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨e, -, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨sp, hs, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨_, -, rfl⟩ := Option.map_eq_some_iff.mp h
    exact floatV_sorted hs _
  · cases h

theorem flAt_sorted {op} {vs : List GroundTerm} {v : GroundTerm} (h : flAt op vs = some v) :
    c.sortOf v = some Srt.float := by
  unfold flAt at h
  split at h
  · obtain ⟨p, -, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨e, -, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨sp, hs, rfl⟩ := Option.map_eq_some_iff.mp h
    exact floatV_sorted hs _
  · cases h

theorem flTest_sorted {t} {vs : List GroundTerm} {v : GroundTerm} (h : flTest t vs = some v) :
    c.sortOf v = some Srt.bool := by
  unfold flTest at h
  split at h
  · obtain ⟨_, -, rfl⟩ := Option.map_eq_some_iff.mp h; exact sortOf_bool _
  · cases h

theorem flTestM_sorted {t} {vs : List GroundTerm} {v : GroundTerm} (h : flTestM t vs = some v) :
    c.sortOf v = some Srt.bool := by
  unfold flTestM at h
  split at h
  · obtain ⟨_, -, rfl⟩ := Option.map_eq_some_iff.mp h; exact sortOf_bool _
  · cases h

theorem flCmp_sorted {t} {vs : List GroundTerm} {v : GroundTerm} (h : flCmp t vs = some v) :
    c.sortOf v = some Srt.bool := by
  unfold flCmp at h
  split at h
  · obtain ⟨_, -, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨_, -, rfl⟩ := Option.map_eq_some_iff.mp h; exact sortOf_bool _
  · cases h

theorem flFmt_sorted {f} {vs : List GroundTerm} {v : GroundTerm} (h : flFmt f vs = some v) :
    c.sortOf v = some Srt.int := by
  unfold flFmt at h
  split at h
  · split at h
    · cases h; exact sortOf_int _
    · cases h
  · cases h

theorem floatSigs_result : ∀ k ∈ hookSigs, (floatResFloat.contains k.name → k.result = Srt.float) ∧
    (floatResBool.contains k.name → k.result = Srt.bool) ∧ (floatResInt.contains k.name → k.result = Srt.int) := by
  decide +kernel

/-- The interpreted Float symbols by the sort of their result. -/
theorem floatHook_result {f : Sym} {k : CtorSig} (hk : lookupSig hookSigs f = some k) :
    ((floatResFloat.contains f → k.result = Srt.float) ∧ (floatResBool.contains f → k.result = Srt.bool) ∧
      (floatResInt.contains f → k.result = Srt.int)) := by
  obtain ⟨hm, rfl⟩ := lookupSig_spec hk
  have := floatSigs_result k hm
  exact this

/-- The interpreted Float symbols return values of their declared result sort. -/
theorem floatHook_sorted {f : Sym} {g : List GroundTerm → Option GroundTerm} {k : CtorSig}
    {ws : List GroundTerm} {v : GroundTerm} (hmem : (f, g) ∈ floatHooks)
    (hk : lookupSig hookSigs f = some k) (hev : g ws = some v) : c.sortOf v = some k.result := by
  obtain ⟨hF, hB, hI⟩ := floatHook_result hk
  simp only [floatHooks, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hmem
  rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals first
    | (rw [hF (by decide)]; first | exact fl1_sorted hev | exact fl2_sorted hev | exact flTo_sorted hev | exact flOfInt_sorted hev | exact flAt_sorted hev)
    | (rw [hF (by decide)]
       dsimp only at hev
       split at hev
       · obtain ⟨⟨p, e, sp, u⟩, ha, h⟩ := Option.bind_eq_some_iff.mp hev
         obtain ⟨_, -, rfl⟩ := Option.map_eq_some_iff.mp h
         exact floatV_sorted (asFloat_spec ha) _
       · cases hev)
    | (rw [hB (by decide)]; first | exact flTest_sorted hev | exact flTestM_sorted hev | exact flCmp_sorted hev)
    | (rw [hI (by decide)]; exact flFmt_sorted hev)

/-! ## The interpreted String and Bytes symbols return values of their declared result sort

A String (Bytes) result is made of characters of its String (Bytes) arguments, and for Bytes of
bytes below 256: where its arguments are literals of their sort, so is it (`dvOK_tok_of`). -/

/-- A token literal at `s` whose characters are characters of literals admitted at `s`, or below 256, is
admitted at `s`. -/
theorem dvOK_tok_of {l : Lib} {s : Srt} {ts : List String} {t₀ : String} (h₀ : t₀ ∈ ts)
    (hts : ∀ t ∈ ts, dvOK l s (.tok t) = true) {r : List Char}
    (hr : ∀ ch ∈ r, (∃ t ∈ ts, ch ∈ t.toList) ∨ ch.toNat < 256) :
    dvOK l s (.tok (String.ofList r)) = true := by
  have key : ∀ t ∈ ts, (((l.carrier s == Srt.kconfigVar) = true ∨ (l.carrier s == Srt.string) = true) ∨ l.tokenSorts.contains (l.carrier s) = true) ∨
      (((l.carrier s == Srt.bytes) = true ∨ l.byteSorts.contains (l.carrier s) = true) ∧ ∀ ch ∈ t.toList, ch.toNat < 256) := by
    intro t ht
    have := hts t ht
    simp only [dvOK, Bool.or_eq_true, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at this
    exact this
  simp only [dvOK, Bool.or_eq_true, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, String.toList_ofList]
  rcases key t₀ h₀ with h | ⟨hb, -⟩
  · exact Or.inl h
  · by_cases hA : ((l.carrier s == Srt.kconfigVar) = true ∨ (l.carrier s == Srt.string) = true) ∨ l.tokenSorts.contains (l.carrier s) = true
    · exact Or.inl hA
    · refine Or.inr ⟨hb, fun ch hch => ?_⟩
      rcases hr ch hch with ⟨t, ht, hct⟩ | hlt
      · rcases key t ht with h | ⟨_, hall⟩
        · exact absurd h hA
        · exact hall ch hct
      · exact hlt

theorem asStr_some {w : GroundTerm} {x : List Char} (h : asStr w = some x) :
    ∃ t, w = .dv Srt.string (.tok t) ∧ x = t.toList := by
  unfold asStr at h
  split at h
  · rename_i s t
    split at h
    · rename_i hs
      cases h; exact ⟨t, by rw [beq_iff_eq.mp hs], rfl⟩
    · cases h
  · cases h

theorem asBytes_some {w : GroundTerm} {x : List Char} (h : asBytes w = some x) :
    ∃ t, w = .dv Srt.bytes (.tok t) ∧ x = t.toList := by
  unfold asBytes at h
  split at h
  · rename_i s t
    split at h
    · rename_i hs
      cases h; exact ⟨t, by rw [beq_iff_eq.mp hs], rfl⟩
    · cases h
  · cases h

/-- A String made of characters of String values is a String value. -/
theorem strV_sorted {ts : List String} {t₀ : String} (h₀ : t₀ ∈ ts)
    (hts : ∀ t ∈ ts, c.sortOf (.dv Srt.string (.tok t)) = some Srt.string) {r : List Char}
    (hr : ∀ ch ∈ r, ∃ t ∈ ts, ch ∈ t.toList) : c.sortOf (strV r) = some Srt.string :=
  sortOf_dv.mpr ⟨dvOK_tok_of h₀ (fun t ht => (sortOf_dv.mp (hts t ht)).1) fun ch hc => Or.inl (hr ch hc), rfl⟩

/-- A Bytes made of bytes of Bytes values and bytes below 256 is a Bytes value. -/
theorem bytesV_sorted {ts : List String} {t₀ : String} (h₀ : t₀ ∈ ts)
    (hts : ∀ t ∈ ts, c.sortOf (.dv Srt.bytes (.tok t)) = some Srt.bytes) {r : List Char}
    (hr : ∀ ch ∈ r, (∃ t ∈ ts, ch ∈ t.toList) ∨ ch.toNat < 256) : c.sortOf (bytesV r) = some Srt.bytes :=
  sortOf_dv.mpr ⟨dvOK_tok_of h₀ (fun t ht => (sortOf_dv.mp (hts t ht)).1) hr, rfl⟩

/-- Every String literal is a String value. -/
theorem sortOf_strV (r : List Char) : c.sortOf (strV r) = some Srt.string :=
  sortOf_dv.mpr ⟨by simp [dvOK], rfl⟩

/-- A Bytes literal of bytes below 256 is a Bytes value. -/
theorem sortOf_bytesV {r : List Char} (hr : ∀ ch ∈ r, ch.toNat < 256) : c.sortOf (bytesV r) = some Srt.bytes :=
  sortOf_dv.mpr ⟨by simp only [dvOK, Lib.carrier_bytes, Bool.or_eq_true, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq,
    String.toList_ofList, beq_self_eq_true, true_or, true_and]; exact Or.inr hr, rfl⟩

/-- The interpreted String symbols return values of their declared result sort. -/
theorem stringHook_sorted {f : Sym} {g : List GroundTerm → Option GroundTerm} {k : CtorSig}
    {ws : List GroundTerm} {v : GroundTerm} (hmem : (f, g) ∈ stringHooks)
    (hk : lookupSig hookSigs f = some k) (hws : c.sortsOf ws = some k.args)
    (hev : g ws = some v) : c.sortOf v = some k.result := by
  simp only [stringHooks, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hmem
  rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rw [show lookupSig hookSigs stringConcat = some ⟨stringConcat, [Srt.string, Srt.string], Srt.string⟩ by decide] at hk
    cases hk
    dsimp only at hws hev ⊢
    split at hev
    · simp only [sortsOf_eq_cons] at hws
      simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at hev
      obtain ⟨x, hx, y, hy, rfl⟩ := hev
      obtain ⟨ta, rfl, rfl⟩ := asStr_some hx
      obtain ⟨tb, rfl, rfl⟩ := asStr_some hy
      exact strV_sorted (ts := [ta, tb]) (List.mem_cons_self ..) (fun t ht => by rcases List.mem_cons.mp ht with rfl | ht; exact hws.1; rw [List.mem_singleton.mp ht]; exact hws.2.1)
        fun ch hc => (List.mem_append.mp hc).elim (fun h => ⟨ta, List.mem_cons_self .., h⟩) (fun h => ⟨tb, List.mem_cons_of_mem _ (List.mem_singleton_self _), h⟩)
    · cases hev
  · rw [show lookupSig hookSigs stringLength = some ⟨stringLength, [Srt.string], Srt.int⟩ by decide] at hk
    cases hk
    dsimp only at hws hev ⊢
    split at hev
    · simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at hev
      repeat' obtain ⟨_, _, hev⟩ := hev
      exact sortOf_int _
    · cases hev
  · rw [show lookupSig hookSigs stringOrd = some ⟨stringOrd, [Srt.string], Srt.int⟩ by decide] at hk
    cases hk
    dsimp only at hws hev ⊢
    split at hev
    · simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at hev
      repeat' obtain ⟨_, _, hev⟩ := hev
      exact sortOf_int _
    · cases hev
  · rw [show lookupSig hookSigs stringSubstr = some ⟨stringSubstr, [Srt.string, Srt.int, Srt.int], Srt.string⟩ by decide] at hk
    cases hk
    dsimp only at hws hev ⊢
    split at hev
    · simp only [sortsOf_eq_cons] at hws
      simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at hev
      obtain ⟨x, hx, _, _, _, _, r, hr, rfl⟩ := hev
      obtain ⟨ta, rfl, rfl⟩ := asStr_some hx
      exact strV_sorted (ts := [ta]) (List.mem_cons_self ..) (fun t ht => by rw [List.mem_singleton.mp ht]; exact hws.1)
        fun ch hc => ⟨ta, List.mem_cons_self .., KStr.substrString_mem hr hc⟩
    · cases hev
  · rw [show lookupSig hookSigs stringFind = some ⟨stringFind, [Srt.string, Srt.string, Srt.int], Srt.int⟩ by decide] at hk
    cases hk
    dsimp only at hws hev ⊢
    split at hev
    · simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at hev
      repeat' obtain ⟨_, _, hev⟩ := hev
      exact sortOf_int _
    · cases hev
  · rw [show lookupSig hookSigs stringRfind = some ⟨stringRfind, [Srt.string, Srt.string, Srt.int], Srt.int⟩ by decide] at hk
    cases hk
    dsimp only at hws hev ⊢
    split at hev
    · simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at hev
      repeat' obtain ⟨_, _, hev⟩ := hev
      exact sortOf_int _
    · cases hev
  · rw [show lookupSig hookSigs stringFindChar = some ⟨stringFindChar, [Srt.string, Srt.string, Srt.int], Srt.int⟩ by decide] at hk
    cases hk
    dsimp only at hws hev ⊢
    split at hev
    · simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at hev
      repeat' obtain ⟨_, _, hev⟩ := hev
      exact sortOf_int _
    · cases hev
  · rw [show lookupSig hookSigs stringRfindChar = some ⟨stringRfindChar, [Srt.string, Srt.string, Srt.int], Srt.int⟩ by decide] at hk
    cases hk
    dsimp only at hws hev ⊢
    split at hev
    · simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at hev
      repeat' obtain ⟨_, _, hev⟩ := hev
      exact sortOf_int _
    · cases hev
  · rw [show lookupSig hookSigs string2Bool = some ⟨string2Bool, [Srt.string], Srt.bool⟩ by decide] at hk
    cases hk
    dsimp only at hws hev ⊢
    split at hev
    · simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at hev
      repeat' obtain ⟨_, _, hev⟩ := hev
      exact sortOf_bool _
    · cases hev
  · rw [show lookupSig hookSigs string2Int = some ⟨string2Int, [Srt.string], Srt.int⟩ by decide] at hk
    cases hk
    dsimp only at hws hev ⊢
    split at hev
    · simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at hev
      repeat' obtain ⟨_, _, hev⟩ := hev
      exact sortOf_int _
    · cases hev
  · rw [show lookupSig hookSigs string2Base = some ⟨string2Base, [Srt.string, Srt.int], Srt.int⟩ by decide] at hk
    cases hk
    dsimp only at hws hev ⊢
    split at hev
    · simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at hev
      repeat' obtain ⟨_, _, hev⟩ := hev
      exact sortOf_int _
    · cases hev
  · rw [show lookupSig hookSigs stringReplace = some ⟨stringReplace, [Srt.string, Srt.string, Srt.string, Srt.int], Srt.string⟩ by decide] at hk
    cases hk
    dsimp only at hws hev ⊢
    split at hev
    · simp only [sortsOf_eq_cons] at hws
      simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at hev
      obtain ⟨x, hx, y, -, z, hz, _, _, r, hr, rfl⟩ := hev
      obtain ⟨ta, rfl, rfl⟩ := asStr_some hx
      obtain ⟨tc, rfl, rfl⟩ := asStr_some hz
      exact strV_sorted (ts := [ta, tc]) (List.mem_cons_self ..) (fun t ht => by rcases List.mem_cons.mp ht with rfl | ht; exact hws.1; rw [List.mem_singleton.mp ht]; exact hws.2.2.1)
        fun ch hc => (KStr.replace_mem hr hc).elim (fun h => ⟨ta, List.mem_cons_self .., h⟩) (fun h => ⟨tc, List.mem_cons_of_mem _ (List.mem_singleton_self _), h⟩)
    · cases hev
  · rw [show lookupSig hookSigs stringReplaceFirst = some ⟨stringReplaceFirst, [Srt.string, Srt.string, Srt.string], Srt.string⟩ by decide] at hk
    cases hk
    dsimp only at hws hev ⊢
    split at hev
    · simp only [sortsOf_eq_cons] at hws
      simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at hev
      obtain ⟨x, hx, y, -, z, hz, rfl⟩ := hev
      obtain ⟨ta, rfl, rfl⟩ := asStr_some hx
      obtain ⟨tc, rfl, rfl⟩ := asStr_some hz
      exact strV_sorted (ts := [ta, tc]) (List.mem_cons_self ..) (fun t ht => by rcases List.mem_cons.mp ht with rfl | ht; exact hws.1; rw [List.mem_singleton.mp ht]; exact hws.2.2.1)
        fun ch hc => (KStr.replaceFirst_mem hc).elim (fun h => ⟨ta, List.mem_cons_self .., h⟩) (fun h => ⟨tc, List.mem_cons_of_mem _ (List.mem_singleton_self _), h⟩)
    · cases hev
  · rw [show lookupSig hookSigs stringCountAll = some ⟨stringCountAll, [Srt.string, Srt.string], Srt.int⟩ by decide] at hk
    cases hk
    dsimp only at hws hev ⊢
    split at hev
    · simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at hev
      repeat' obtain ⟨_, _, hev⟩ := hev
      exact sortOf_int _
    · cases hev
  · rw [show lookupSig hookSigs stringReplaceAll = some ⟨stringReplaceAll, [Srt.string, Srt.string, Srt.string], Srt.string⟩ by decide] at hk
    cases hk
    dsimp only at hws hev ⊢
    split at hev
    · simp only [sortsOf_eq_cons] at hws
      simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at hev
      obtain ⟨x, hx, y, -, z, hz, r, hr, rfl⟩ := hev
      obtain ⟨ta, rfl, rfl⟩ := asStr_some hx
      obtain ⟨tc, rfl, rfl⟩ := asStr_some hz
      exact strV_sorted (ts := [ta, tc]) (List.mem_cons_self ..) (fun t ht => by rcases List.mem_cons.mp ht with rfl | ht; exact hws.1; rw [List.mem_singleton.mp ht]; exact hws.2.2.1)
        fun ch hc => (KStr.replaceAll_mem hr hc).elim (fun h => ⟨ta, List.mem_cons_self .., h⟩) (fun h => ⟨tc, List.mem_cons_of_mem _ (List.mem_singleton_self _), h⟩)
    · cases hev
  · rw [show lookupSig hookSigs stringEq = some ⟨stringEq, [Srt.string, Srt.string], Srt.bool⟩ by decide] at hk
    cases hk
    dsimp only at hws hev ⊢
    unfold str2 at hev
    split at hev
    · simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at hev
      repeat' obtain ⟨_, _, hev⟩ := hev
      exact sortOf_bool _
    · cases hev
  · rw [show lookupSig hookSigs stringNe = some ⟨stringNe, [Srt.string, Srt.string], Srt.bool⟩ by decide] at hk
    cases hk
    dsimp only at hws hev ⊢
    unfold str2 at hev
    split at hev
    · simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at hev
      repeat' obtain ⟨_, _, hev⟩ := hev
      exact sortOf_bool _
    · cases hev
  · rw [show lookupSig hookSigs stringLt = some ⟨stringLt, [Srt.string, Srt.string], Srt.bool⟩ by decide] at hk
    cases hk
    dsimp only at hws hev ⊢
    unfold str2 at hev
    split at hev
    · simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at hev
      repeat' obtain ⟨_, _, hev⟩ := hev
      exact sortOf_bool _
    · cases hev
  · rw [show lookupSig hookSigs stringLe = some ⟨stringLe, [Srt.string, Srt.string], Srt.bool⟩ by decide] at hk
    cases hk
    dsimp only at hws hev ⊢
    unfold str2 at hev
    split at hev
    · simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at hev
      repeat' obtain ⟨_, _, hev⟩ := hev
      exact sortOf_bool _
    · cases hev
  · rw [show lookupSig hookSigs stringGt = some ⟨stringGt, [Srt.string, Srt.string], Srt.bool⟩ by decide] at hk
    cases hk
    dsimp only at hws hev ⊢
    unfold str2 at hev
    split at hev
    · simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at hev
      repeat' obtain ⟨_, _, hev⟩ := hev
      exact sortOf_bool _
    · cases hev
  · rw [show lookupSig hookSigs stringGe = some ⟨stringGe, [Srt.string, Srt.string], Srt.bool⟩ by decide] at hk
    cases hk
    dsimp only at hws hev ⊢
    unfold str2 at hev
    split at hev
    · simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at hev
      repeat' obtain ⟨_, _, hev⟩ := hev
      exact sortOf_bool _
    · cases hev
  all_goals
    first
      | rw [show lookupSig hookSigs stringChr = some ⟨stringChr, [Srt.int], Srt.string⟩ by decide] at hk
      | rw [show lookupSig hookSigs int2String = some ⟨int2String, [Srt.int], Srt.string⟩ by decide] at hk
      | rw [show lookupSig hookSigs bool2String = some ⟨bool2String, [Srt.bool], Srt.string⟩ by decide] at hk
    cases hk
    dsimp only at hws hev ⊢
    split at hev
    · simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at hev
      repeat' obtain ⟨_, _, hev⟩ := hev
      exact sortOf_strV _
    · cases hev

/-- The interpreted Bytes symbols return values of their declared result sort. -/
theorem bytesHook_sorted {f : Sym} {g : List GroundTerm → Option GroundTerm} {k : CtorSig}
    {ws : List GroundTerm} {v : GroundTerm} (hmem : (f, g) ∈ bytesHooks)
    (hk : lookupSig hookSigs f = some k) (hws : c.sortsOf ws = some k.args)
    (hev : g ws = some v) : c.sortOf v = some k.result := by
  simp only [bytesHooks, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hmem
  rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rw [show lookupSig hookSigs bytes2Int = some ⟨bytes2Int, [Srt.bytes, Srt.endianness, Srt.signedness], Srt.int⟩ by decide] at hk
    cases hk
    dsimp only at hws hev ⊢
    split at hev
    · simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at hev
      repeat' obtain ⟨_, _, hev⟩ := hev
      exact sortOf_int _
    · cases hev
  · rw [show lookupSig hookSigs bytesUpdate = some ⟨bytesUpdate, [Srt.bytes, Srt.int, Srt.int], Srt.bytes⟩ by decide] at hk
    cases hk
    dsimp only at hws hev ⊢
    split at hev
    · simp only [sortsOf_eq_cons] at hws
      simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at hev
      obtain ⟨x, hx, _, _, _, _, r, hr, rfl⟩ := hev
      obtain ⟨ta, rfl, rfl⟩ := asBytes_some hx
      exact bytesV_sorted (ts := [ta]) (List.mem_cons_self ..)
        (fun t ht => by rw [List.mem_singleton.mp ht]; exact hws.1)
        fun ch hc => (KBytes.update_mem hr hc).imp_left fun h => ⟨ta, List.mem_cons_self .., h⟩
    · cases hev
  · rw [show lookupSig hookSigs bytesGet = some ⟨bytesGet, [Srt.bytes, Srt.int], Srt.int⟩ by decide] at hk
    cases hk
    dsimp only at hws hev ⊢
    split at hev
    · simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at hev
      repeat' obtain ⟨_, _, hev⟩ := hev
      exact sortOf_int _
    · cases hev
  · rw [show lookupSig hookSigs bytesSubstr = some ⟨bytesSubstr, [Srt.bytes, Srt.int, Srt.int], Srt.bytes⟩ by decide] at hk
    cases hk
    dsimp only at hws hev ⊢
    split at hev
    · simp only [sortsOf_eq_cons] at hws
      simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at hev
      obtain ⟨x, hx, _, _, _, _, r, hr, rfl⟩ := hev
      obtain ⟨ta, rfl, rfl⟩ := asBytes_some hx
      exact bytesV_sorted (ts := [ta]) (List.mem_cons_self ..)
        (fun t ht => by rw [List.mem_singleton.mp ht]; exact hws.1)
        fun ch hc => Or.inl ⟨ta, List.mem_cons_self .., KStr.substr_mem hr hc⟩
    · cases hev
  · rw [show lookupSig hookSigs bytesReplaceAt = some ⟨bytesReplaceAt, [Srt.bytes, Srt.int, Srt.bytes], Srt.bytes⟩ by decide] at hk
    cases hk
    dsimp only at hws hev ⊢
    split at hev
    · simp only [sortsOf_eq_cons] at hws
      simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at hev
      obtain ⟨x, hx, _, _, y, hy, r, hr, rfl⟩ := hev
      obtain ⟨ta, rfl, rfl⟩ := asBytes_some hx
      obtain ⟨tb, rfl, rfl⟩ := asBytes_some hy
      exact bytesV_sorted (ts := [ta, tb]) (List.mem_cons_self ..)
        (fun t ht => by rcases List.mem_cons.mp ht with rfl | ht; exact hws.1; rw [List.mem_singleton.mp ht]; exact hws.2.2.1)
        fun ch hc => Or.inl ((KBytes.replaceAt_mem hr hc).elim (fun h => ⟨ta, List.mem_cons_self .., h⟩) (fun h => ⟨tb, List.mem_cons_of_mem _ (List.mem_singleton_self _), h⟩))
    · cases hev
  · rw [show lookupSig hookSigs bytesMemset = some ⟨bytesMemset, [Srt.bytes, Srt.int, Srt.int, Srt.int], Srt.bytes⟩ by decide] at hk
    cases hk
    dsimp only at hws hev ⊢
    split at hev
    · simp only [sortsOf_eq_cons] at hws
      simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at hev
      obtain ⟨x, hx, _, _, _, _, _, _, r, hr, rfl⟩ := hev
      obtain ⟨ta, rfl, rfl⟩ := asBytes_some hx
      exact bytesV_sorted (ts := [ta]) (List.mem_cons_self ..)
        (fun t ht => by rw [List.mem_singleton.mp ht]; exact hws.1)
        fun ch hc => (KBytes.memset_mem hr hc).imp_left fun h => ⟨ta, List.mem_cons_self .., h⟩
    · cases hev
  · rw [show lookupSig hookSigs bytesPadRight = some ⟨bytesPadRight, [Srt.bytes, Srt.int, Srt.int], Srt.bytes⟩ by decide] at hk
    cases hk
    dsimp only at hws hev ⊢
    split at hev
    · simp only [sortsOf_eq_cons] at hws
      simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at hev
      obtain ⟨x, hx, _, _, _, _, r, hr, rfl⟩ := hev
      obtain ⟨ta, rfl, rfl⟩ := asBytes_some hx
      exact bytesV_sorted (ts := [ta]) (List.mem_cons_self ..)
        (fun t ht => by rw [List.mem_singleton.mp ht]; exact hws.1)
        fun ch hc => (KBytes.padRight_mem hr hc).imp_left fun h => ⟨ta, List.mem_cons_self .., h⟩
    · cases hev
  · rw [show lookupSig hookSigs bytesPadLeft = some ⟨bytesPadLeft, [Srt.bytes, Srt.int, Srt.int], Srt.bytes⟩ by decide] at hk
    cases hk
    dsimp only at hws hev ⊢
    split at hev
    · simp only [sortsOf_eq_cons] at hws
      simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at hev
      obtain ⟨x, hx, _, _, _, _, r, hr, rfl⟩ := hev
      obtain ⟨ta, rfl, rfl⟩ := asBytes_some hx
      exact bytesV_sorted (ts := [ta]) (List.mem_cons_self ..)
        (fun t ht => by rw [List.mem_singleton.mp ht]; exact hws.1)
        fun ch hc => (KBytes.padLeft_mem hr hc).imp_left fun h => ⟨ta, List.mem_cons_self .., h⟩
    · cases hev
  · rw [show lookupSig hookSigs bytesReverse = some ⟨bytesReverse, [Srt.bytes], Srt.bytes⟩ by decide] at hk
    cases hk
    dsimp only at hws hev ⊢
    split at hev
    · simp only [sortsOf_eq_cons] at hws
      obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.mp hev
      obtain ⟨ta, rfl, rfl⟩ := asBytes_some hx
      exact bytesV_sorted (ts := [ta]) (List.mem_cons_self ..) (fun t ht => by rw [List.mem_singleton.mp ht]; exact hws.1)
        fun ch hc => Or.inl ⟨ta, List.mem_cons_self .., List.mem_reverse.mp hc⟩
    · cases hev
  · rw [show lookupSig hookSigs bytesLength = some ⟨bytesLength, [Srt.bytes], Srt.int⟩ by decide] at hk
    cases hk
    dsimp only at hws hev ⊢
    split at hev
    · simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at hev
      repeat' obtain ⟨_, _, hev⟩ := hev
      exact sortOf_int _
    · cases hev
  · rw [show lookupSig hookSigs bytesConcat = some ⟨bytesConcat, [Srt.bytes, Srt.bytes], Srt.bytes⟩ by decide] at hk
    cases hk
    dsimp only at hws hev ⊢
    split at hev
    · simp only [sortsOf_eq_cons] at hws
      simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at hev
      obtain ⟨x, hx, y, hy, rfl⟩ := hev
      obtain ⟨ta, rfl, rfl⟩ := asBytes_some hx
      obtain ⟨tb, rfl, rfl⟩ := asBytes_some hy
      exact bytesV_sorted (ts := [ta, tb]) (List.mem_cons_self ..) (fun t ht => by rcases List.mem_cons.mp ht with rfl | ht; exact hws.1; rw [List.mem_singleton.mp ht]; exact hws.2.1)
        fun ch hc => Or.inl ((List.mem_append.mp hc).elim (fun h => ⟨ta, List.mem_cons_self .., h⟩) (fun h => ⟨tb, List.mem_cons_of_mem _ (List.mem_singleton_self _), h⟩))
    · cases hev
  · rw [show lookupSig hookSigs bytesEmpty = some ⟨bytesEmpty, [], Srt.bytes⟩ by decide] at hk
    cases hk
    dsimp only at hws hev ⊢
    split at hev
    · cases hev; exact sortOf_bytesV (fun _ h => absurd h List.not_mem_nil)
    · cases hev
  · rw [show lookupSig hookSigs int2Bytes = some ⟨int2Bytes, [Srt.int, Srt.int, Srt.endianness], Srt.bytes⟩ by decide] at hk
    cases hk
    dsimp only at hws hev ⊢
    split at hev
    · simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at hev
      obtain ⟨_, _, _, _, _, _, r, hr, rfl⟩ := hev
      exact sortOf_bytesV (KBytes.ofInt_lt hr)
    · cases hev

/-! ## RANGEMAP's `keys` -/

/-- Every Range value of `c` is a KItem: a range term of sort Range puts Range below KItem. A
semantics with no Range value has it whatever its subsorts. -/
def RangeBelow (c : Semantics) : Prop :=
  ∀ a b : Int, c.sortOf (rangeT a b) = some Srt.range → (Srt.range, Srt.kitem) ∈ c.subsorts

/-- The members `rmKeysHook` builds: in order, each the injection of a key. -/
theorem rmK_keys_set : ∀ m : Entries,
    (m.foldr (fun (k, _) s => insertS (.inj Srt.range Srt.kitem k) s) []).Pairwise (fun a b => GroundTerm.cmp a b = .lt) ∧
    ∀ e ∈ m.foldr (fun (k, _) s => insertS (.inj Srt.range Srt.kitem k) s) [], ∃ p ∈ m, e = .inj Srt.range Srt.kitem p.1
  | [] => ⟨.nil, fun _ h => nomatch h⟩
  | (k, w) :: m => by
    obtain ⟨ih1, ih2⟩ := rmK_keys_set m
    refine ⟨insertS_sorted ih1, fun e he => ?_⟩
    rcases insertS_mem he with rfl | he
    · exact ⟨(k, w), List.mem_cons_self .., rfl⟩
    · obtain ⟨p, hp, rfl⟩ := ih2 e he
      exact ⟨p, List.mem_cons_of_mem _ hp, rfl⟩

/-- The keys of a range map value are a Set value where each range term of sort Range is a KItem. -/
theorem rmK_keys_sorted {c : Semantics} (hco : c.collOf Srt.rangeMap = some (builtinColl .rangeMap))
    (hsub : ∀ a b : Int, c.sortOf (rangeT a b) = some Srt.range → (Srt.range, Srt.kitem) ∈ c.subsorts)
    {ws : List GroundTerm} {v : GroundTerm} (hws : c.sortsOf ws = some [Srt.rangeMap])
    (hv : rmKeysHook ws = some v) : c.sortOf v = some Srt.set := by
  match ws, hws, hv with
  | [.map s m], hws, hv =>
    simp only [rmKeysHook, Option.some.injEq] at hv
    subst hv
    obtain ⟨-, hr, he⟩ := (rmS_sortOf_map hco).mp (rmS_sortsOf_cons.mp hws).1
    obtain ⟨ts, -, hm, -⟩ := rmOK_of_value hr
    obtain ⟨h1, h2⟩ := rmK_keys_set m
    refine sortOf_set_of h1 fun e he' => ?_
    obtain ⟨⟨k, w⟩, hp, rfl⟩ := h2 e he'
    have hk := (he _ hp).1
    have hp' := hp
    rw [hm] at hp'
    obtain ⟨t, -, ht⟩ := List.mem_map.mp hp'
    simp only [Prod.mk.injEq] at ht
    obtain ⟨rfl, -⟩ := ht
    have hs := hsub _ _ hk
    have hni : (rangeT t.1 t.2.1).isInj = false := rfl
    simp only at hk ⊢
    generalize rangeT t.1 t.2.1 = r at hk hni
    simpa [Semantics.sortOf, hk, hni] using hs
  | [], hws, hv => simp [rmKeysHook] at hv
  | [.ctor _ _], hws, hv => simp [rmKeysHook] at hv
  | [.inj _ _ _], hws, hv => simp [rmKeysHook] at hv
  | [.dv _ _], hws, hv => simp [rmKeysHook] at hv
  | [.set _ _], hws, hv => simp [rmKeysHook] at hv
  | [.list _ _], hws, hv => simp [rmKeysHook] at hv
  | _ :: _ :: _, hws, hv => simp [rmKeysHook] at hv

/-- No map pattern symbol is `keys`. -/
theorem patternHooks_ne_rmKeys : ∀ f, patternHooks.contains f = true → f ≠ rmKeys := by
  intro f hf; rintro rfl; revert hf; decide

/-- No set or list pattern symbol is `keys`. -/
theorem collPatternHooks_ne_rmKeys : ∀ f, collPatternHooks.contains f = true → f ≠ rmKeys := by
  intro f hf; rintro rfl; revert hf; decide

/-- An interpreted collection pattern symbol is no `keys`. -/
theorem isCollPat_hook_ne_rmKeys {f : Sym} (hp : c.isCollPat f = true) (hh : isHook f = true) : f ≠ rmKeys := by
  unfold Semantics.isCollPat at hp
  rw [if_pos hh] at hp
  exact collPatternHooks_ne_rmKeys f (Bool.and_eq_true_iff.mp hp).2

/-- `keys`'s signature: `RangeMap → Set`. -/
theorem lookupSig_hookSigs_rmKeys : lookupSig hookSigs rmKeys = some ⟨rmKeys, [Srt.rangeMap], Srt.set⟩ := by
  decide +kernel

/-- A symbol whose signature in `hookSigs` has other arguments than `keys`'s is no `keys`. -/
theorem ne_rmKeys_of_sig {f : Sym} {k : CtorSig} (hk : lookupSig hookSigs f = some k)
    (h : k.args ≠ [Srt.rangeMap]) : f ≠ rmKeys := by
  rintro rfl
  rw [lookupSig_hookSigs_rmKeys] at hk
  cases hk
  exact h rfl

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
theorem hook_sorted {f : Sym} {k : CtorSig} {ws : List GroundTerm} {v : GroundTerm}
    (hr : f = rmKeys → RangeBelow c)
    (hk : lookupSig hookSigs f = some k) (hws : c.sortsOf ws = some k.args)
    (hv : hook f ws = some (some v)) : c.sortOf v = some k.result := by
  rw [hook_eq] at hv
  obtain ⟨e, he, hev⟩ := Option.map_eq_some_iff.mp hv
  have hmem := List.mem_of_find?_eq_some he
  have hname : e.1 = f := by simpa using List.find?_some he
  obtain ⟨g, h⟩ := e
  simp only at hname hev
  subst hname
  unfold hookTable at hmem
  rcases List.mem_append.mp hmem with hmem | hmem
  rotate_left
  · simp only [rangeMapKeysHooks, List.mem_singleton, Prod.mk.injEq] at hmem
    obtain ⟨rfl, rfl⟩ := hmem
    rw [lookupSig_hookSigs_rmKeys] at hk
    cases hk
    exact rmK_keys_sorted collOf_rangeMap (hr rfl) hws hev
  refine (List.mem_append.mp hmem).elim (fun hmem => ?_) (fun hmem => rangeMapHook_sorted hmem hk hws hev)
  refine (List.mem_append.mp hmem).elim (fun hmem => ?_) (fun hmem => iteHook_sorted hmem hk hws hev)
  refine (List.mem_append.mp hmem).elim (fun hmem => ?_) (fun hmem => bytesHook_sorted hmem hk hws hev)
  refine (List.mem_append.mp hmem).elim (fun hmem => ?_) (fun hmem => stringHook_sorted hmem hk hws hev)
  refine (List.mem_append.mp hmem).elim (fun hmem => ?_) (fun hmem => floatHook_sorted hmem hk hev)
  refine (List.mem_append.mp hmem).elim (fun hmem => ?_) (fun hmem => listHook_sorted hmem hk hws hev)
  simp only [boolHooks, intHooks, kHooks, mapHooks, setHooks, List.cons_append,
    List.nil_append, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hmem
  rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals
    simp only [lookupSig_eq, hookSigs, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
      List.find?_cons, boolNot, boolAnd, boolAndThen, boolOr, boolOrElse, boolXor, boolImplies,
      boolEq, boolNe, intAdd, intSub, intMul, intTDiv, intTMod, intEDiv, intEMod, intMin, intMax,
      intLt, intLe, intGt, intGe, intEq, intNe, intAbs, freshInt, intShr, intShl, intLog2, kEq, kNe,
      mapUnit, mapElem,
      mapConcat, mapUpdate, mapRemove, mapLookup, mapLookupOrDefault, mapInKeys, mapSize,
      mapRemoveAll, mapKeys, setUnit, setElem, setConcat, setUnion, setIntersect, setDifference,
      setIn, setInclusion, setSize] at hk
    simp (config := { decide := true }) only [Nat.reduceBEq, Option.some.injEq] at hk
    subst hk
    dsimp only at hev
  all_goals first
    | (obtain ⟨b, rfl⟩ := bool2_some hev; exact sortOf_bool _)
    | (obtain ⟨x, y, hg⟩ := int2_some hev
       first
         | (rw [nonzero_some hg]; exact sortOf_int _)
         | (split at hg
            · cases hg
            · obtain rfl := Option.some.inj hg; exact sortOf_int _)
         | (simp only [Option.some.injEq] at hg; subst hg
            first | exact sortOf_int _ | exact sortOf_bool _))
    | skip
  all_goals
    dsimp only at hws ⊢
    split at hev
  all_goals first
    | (simp only [reduceCtorEq] at hev)
    | (split at hev
       · cases hev
       · obtain rfl := Option.some.inj hev; exact sortOf_bool _)
    | (obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.mp hev
       first | exact sortOf_bool _ | exact sortOf_int _)
    | (obtain ⟨_, _, hx⟩ := Option.bind_eq_some_iff.mp hev
       split at hx
       · obtain rfl := Option.some.inj hx; exact sortOf_int _
       · cases hx)
    | (obtain rfl := Option.some.inj hev
       first
         | exact sortOf_bool _
         | exact sortOf_int _
         | (apply sortOf_map_of rfl; intro _ h; cases h; done)
         | (simp only [sortsOf_eq_cons] at hws
            apply sortOf_map_of rfl
            intro e he
            simp only [List.mem_singleton] at he
            subst he
            exact ⟨hws.1, hws.2.1⟩)
         | (simp only [sortsOf_eq_cons] at hws
            obtain ⟨hm, hk, hv, _⟩ := hws
            obtain ⟨hs, he⟩ := entriesOK_of hm
            exact sortOf_map_of (insertE_sorted hs) (fun e h => (insertE_mem h).elim
              (fun h => h ▸ ⟨hk, hv⟩) (he e)))
         | (simp only [sortsOf_eq_cons] at hws
            obtain ⟨hm, _, _⟩ := hws
            obtain ⟨hs, he⟩ := entriesOK_of hm
            exact sortOf_map_of (eraseK_sorted hs) (fun e h => he e (eraseK_sublist h)))
         | (apply sortOf_set_of List.Pairwise.nil; intro _ h; cases h; done)
         | (simp only [sortsOf_eq_cons] at hws
            apply sortOf_set_of (List.pairwise_singleton _ _)
            intro e he
            simp only [List.mem_singleton] at he
            subst he
            exact hws.1)
         | (simp only [sortsOf_eq_cons] at hws
            obtain ⟨hm, _⟩ := hws
            obtain ⟨hs, he⟩ := entriesOK_of hm
            refine sortOf_set_of (keysOf_sorted (keysSorted_iff.mp hs)) (fun k hk => ?_)
            obtain ⟨e, he', rfl⟩ := List.mem_map.mp hk
            exact (he e he').1)
         | (simp only [sortsOf_eq_cons] at hws
            obtain ⟨hm, _, _⟩ := hws
            obtain ⟨hs, he⟩ := entriesOK_of hm
            exact sortOf_map_of (keysSorted_iff.mpr ((keysSorted_iff.mp hs).filter _))
              (fun e h => he e (List.mem_filter.mp h).1))
         | (simp only [sortsOf_eq_cons] at hws
            obtain ⟨ha, hb, _⟩ := hws
            obtain ⟨_, hae⟩ := setOK_of ha
            obtain ⟨hbs, hbe⟩ := setOK_of hb
            exact sortOf_set_of (unionS_sorted hbs) (fun e h => (unionS_mem h).elim (hae e) (hbe e)))
         | (simp only [sortsOf_eq_cons] at hws
            obtain ⟨ha, _, _⟩ := hws
            obtain ⟨has, hae⟩ := setOK_of ha
            exact sortOf_set_of (has.filter _) (fun e h => hae e (List.mem_filter.mp h).1))
         | (simp only [sortsOf_eq_cons] at hws
            obtain ⟨hm, _, hd, _⟩ := hws
            obtain ⟨_, he⟩ := entriesOK_of hm
            cases hf : findK _ _ with
            | none => simpa using hd
            | some w =>
              obtain ⟨k', hk'⟩ := findK_mem hf
              simpa using (he _ hk').2))
    | (simp only [sortsOf_eq_cons] at hws
       obtain ⟨hm, _, _⟩ := hws
       obtain ⟨_, he⟩ := entriesOK_of hm
       obtain ⟨k', hk'⟩ := findK_mem hev
       exact (he _ hk').2)
    | (obtain ⟨m, hm, rfl⟩ := Option.map_eq_some_iff.mp hev
       simp only [sortsOf_eq_cons] at hws
       obtain ⟨ha, hb, _⟩ := hws
       obtain ⟨has, hae⟩ := entriesOK_of ha
       obtain ⟨hbs, hbe⟩ := entriesOK_of hb
       exact sortOf_map_of (union_sorted hbs hm)
         (fun e h => (union_mem hm e h).elim (hae e) (hbe e)))
    | (obtain ⟨m, hm, rfl⟩ := Option.map_eq_some_iff.mp hev
       simp only [sortsOf_eq_cons] at hws
       obtain ⟨ha, hb, _⟩ := hws
       obtain ⟨_, hae⟩ := setOK_of ha
       obtain ⟨hbs, hbe⟩ := setOK_of hb
       rw [← concatS_some hm]
       exact sortOf_set_of (unionS_sorted hbs) (fun e h => (unionS_mem h).elim (hae e) (hbe e)))

/-! ## Terms -/

/-- An interpreted symbol's result (`hookRes`) has its declared result sort: `hook`'s value by
`hook_sorted`, the fallback by its filter. -/
theorem hookRes_sorted {f : Sym} {k : CtorSig} {ws : List GroundTerm} {v : GroundTerm}
    (hr : f = rmKeys → RangeBelow c)
    (hk : lookupSig hookSigs f = some k) (hws : c.sortsOf ws = some k.args)
    (hv : c.hookRes f ws = some (some v)) : c.sortOf v = some k.result := by
  rcases Semantics.hookRes_cases hv with ⟨hh, -⟩ | ⟨-, -, hf⟩
  · exact hook_sorted hr hk hws hh
  · exact Semantics.fallback_sorted hk hf.symm

section Terms
variable {x : TermCtx} {vars : List Srt}

theorem sortOfTerm_var {i : Nat} {s : Srt} :
    sortOfTerm x vars (.var i) = some s ↔ vars[i]? = some s := by
  simp [sortOfTerm]

theorem sortOfTerm_dv {t s : Srt} {lit : Lit} :
    sortOfTerm x vars (.dv t lit) = some s ↔ dvOK x.lib t lit = true ∧ s = t := by
  simp only [sortOfTerm]
  by_cases h : dvOK x.lib t lit = true <;> simp [h, eq_comm]

theorem sortOfTerm_app {f : Sym} {ts : List Term} {s : Srt} :
    sortOfTerm x vars (.app f ts) = some s ↔
      ∃ k, lookupSig x.heads f = some k ∧ sortsOfTerms x vars ts = some k.args ∧ s = k.result := by
  simp only [sortOfTerm]
  cases hk : lookupSig x.heads f with
  | none => simp
  | some k =>
    by_cases he : sortsOfTerms x vars ts = some k.args
    · simp [he, eq_comm]
    · simp [he]

theorem sortOfTerm_inj {a b : Srt} {t : Term} {s : Srt} :
    sortOfTerm x vars (.inj a b t) = some s ↔
      (a, b) ∈ x.subs ∧ sortOfTerm x vars t = some a ∧ s = b := by
  simp only [sortOfTerm]
  constructor
  · intro h
    split at h
    · rename_i hc
      simp only [Bool.and_eq_true, List.contains_iff_mem, beq_iff_eq] at hc
      exact ⟨hc.1, hc.2, (Option.some.inj h).symm⟩
    · cases h
  · rintro ⟨h1, h2, rfl⟩
    simp [h1, h2]

theorem sortsOfTerms_cons {t : Term} {ts : List Term} {ss : List Srt} :
    sortsOfTerms x vars (t :: ts) = some ss ↔
      ∃ s ss', sortOfTerm x vars t = some s ∧ sortsOfTerms x vars ts = some ss' ∧ ss = s :: ss' := by
  simp only [sortsOfTerms]
  cases h1 : sortOfTerm x vars t <;> cases h2 : sortsOfTerms x vars ts <;> simp [eq_comm]

theorem sortsOfTerms_nil {ss : List Srt} : sortsOfTerms x vars [] = some ss ↔ ss = [] := by
  simp only [sortsOfTerms, Option.some.injEq]; exact eq_comm

end Terms

/-! ## Evaluation keeps sorts -/

/-- The function signatures a right-hand side may call: signatures of functions of `c` (the
user's and the generated sort predicates). -/
def HeadsOK (c : Semantics) (L : List CtorSig) : Prop := ∀ k ∈ L, ∃ fn ∈ c.allFns, fn.sig = k

/-- A right-hand side may call the sort predicates besides the functions given (`rhsCtx`). -/
theorem headsOK_preds {L : List CtorSig} (h : HeadsOK c L) : HeadsOK c (c.sortPreds.map Fn.sig ++ L) := by
  intro k hk
  rcases List.mem_append.mp hk with hk | hk
  · obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hk
    exact ⟨g, List.mem_append_right _ hg, rfl⟩
  · exact h k hk

/-- Decided: Range is below KItem, or the Range constructor's symbol is no constructor and no
overloading symbol of result sort Range (so there is no range term of sort Range). -/
def Semantics.rangeKeysOK (c : Semantics) : Bool :=
  c.subsorts.contains (Srt.range, Srt.kitem) ||
    match lookupSig c.ctorSigs rangeCtor with
    | some k => k.result != Srt.range
    | none => match c.lookupOvl rangeCtor with
      | some o => o.sig.result != Srt.range
      | none => true

/-- The decided form gives `RangeBelow`: a range term of sort Range is the Range constructor's
symbol applied, as a constructor or an overloading symbol of that result sort (`sortOf_ctor_iff`). -/
theorem rangeBelow_of_keysOK {c : Semantics} (h : c.rangeKeysOK = true) : RangeBelow c := by
  intro a b hs
  unfold Semantics.rangeKeysOK at h
  rcases Bool.or_eq_true_iff.mp h with h | h
  · exact List.contains_iff_mem.mp h
  · exfalso
    rcases c.sortOf_ctor_iff.mp hs with ⟨k, hk, -, hres⟩ | ⟨hn, o, ho, -, -, hres⟩ | ⟨-, -, k, hk, -⟩
    · rw [hk] at h; simp [← hres] at h
    · rw [hn] at h; simp only [ho] at h; simp [← hres] at h
    · rw [c.lookupOpen_reg (show rangeCtor < nRegSyms by decide)] at hk; cases hk

open Faithful in
/-- A constructor sort Range is below KItem, under `genWf`: a constructor sort is `apartSort`, and
the only way Range is is as one of `c.sortsBelowKItem`. -/
theorem rangeKeys_cons_below {c : Semantics} (hg : genWf c = true) (hc : Srt.range ∈ consSorts c) :
    (Srt.range, Srt.kitem) ∈ c.subsorts := by
  have hgc : apartSort c Srt.range = true ∧ Srt.range ∉ c.lib.tokenSorts ∧ Srt.range ∉ c.lib.byteSorts ∧
      c.collOf Srt.range = none := by
    have hg' := hg
    simp only [genWf, Bool.and_eq_true, List.all_eq_true] at hg'
    have := hg'.1.1.2 _ hc
    simp only [Bool.and_eq_true, bne_iff_ne, Bool.not_eq_true', Option.isNone_iff_eq_none] at this
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, -⟩, -⟩, -⟩, h5⟩, h6⟩, h7⟩, -⟩, -⟩, -⟩ := this
    refine ⟨h1, fun hm => ?_, fun hm => ?_, h7⟩
    · have := List.contains_iff_mem.mpr hm; rw [h5] at this; cases this
    · have := List.contains_iff_mem.mpr hm; rw [h6] at this; cases this
  obtain ⟨hap, ht, hy, hco⟩ := hgc
  have hcar : c.lib.carriers.all (·.1 != Srt.range) = true := by
    unfold consSorts at hc
    simp only [List.mem_filter, Bool.and_eq_true] at hc
    exact hc.2.2
  unfold apartSort distinctSorts at hap
  simp only [Bool.or_eq_true, beq_iff_eq, List.contains_iff_mem, List.mem_append, List.mem_cons, List.mem_map,
    List.not_mem_nil, or_false] at hap
  unfold Semantics.subsorts
  refine List.mem_append_right _ (List.mem_map.mpr ⟨Srt.range, ?_, rfl⟩)
  rcases hap with ((h | h) | h) | h
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact h
  · rcases h with (((h | h) | h) | ⟨k, hk, hks⟩) | ⟨p, hp, hps⟩
    · rcases h with h | h | h | h | h | h <;> exact absurd h (by decide)
    · exact absurd h ht
    · exact absurd h hy
    · have : c.collOf Srt.range ≠ none := by
        unfold Semantics.collOf
        intro hn
        have := List.find?_eq_none.mp hn k hk
        simp [hks] at this
      exact absurd hco this
    · have := List.all_eq_true.mp hcar p hp
      simp [hps] at this

open Faithful in
/-- `genWf` and `overloadsOK` give the decided form: the Range constructor's result sort, as a
constructor's or an overloading symbol's, is a constructor sort (`OvlLaws.ovl_parts`). -/
theorem rangeKeysOK_of_genWf {c : Semantics} (hg : genWf c = true) (ho : c.overloadsOK = true) :
    c.rangeKeysOK = true := by
  unfold Semantics.rangeKeysOK
  by_cases hm : (Srt.range, Srt.kitem) ∈ c.subsorts
  · rw [List.contains_iff_mem.mpr hm]; rfl
  · rw [Bool.or_eq_true]; right
    cases hk : lookupSig c.ctorSigs rangeCtor with
    | some k =>
      simp only [bne_iff_ne, ne_eq]
      intro hres
      have hkc : k.result ∈ consSorts c := by
        have hg' := hg
        simp only [genWf, Bool.and_eq_true, List.all_eq_true] at hg'
        exact List.contains_iff_mem.mp (hg'.1.1.1.1 k (lookupSig_spec hk).1)
      exact hm (rangeKeys_cons_below hg (hres ▸ hkc))
    | none =>
      cases hl : c.lookupOvl rangeCtor with
      | none => rfl
      | some o =>
        simp only [bne_iff_ne, ne_eq]
        intro hres
        exact hm (rangeKeys_cons_below hg (hres ▸ (OvlLaws.ovl_parts ho hl).2.2.2.2))

/-- Three decidable conditions on the data that subject reduction reads: function labels
distinct (the user's and the sort predicates'), the subsort pairs closed under composition, and
every Range value a KItem, decided (`rangeKeysOK`; RANGEMAP's `keys` makes a Set of them). -/
def Semantics.srReady (c : Semantics) : Bool :=
  nodup (c.allFns.map (·.label)) &&
  (c.subsorts.all fun (a, b) => c.subsorts.all fun (b', d) => b != b' || c.subsorts.contains (a, d)) &&
  c.rangeKeysOK

/-- What subject reduction reads of the overloading symbols: there are none, or they are well
formed and the subsorts irreflexive (so the normal form of an overloading symbol's application is a
value of its result sort, `OvlLaws.sortOf_norm`). -/
def Semantics.OvlCase (c : Semantics) : Prop := c.ovls = [] ∨ (c.overloadsOK = true ∧ ∀ a, (a, a) ∉ c.subsorts)

/-- What the laws read of the overloading symbols' declarations (`OvlLaws.OvlFnFacts`), with
`OvlCase` and transitive subsorts. -/
theorem Semantics.OvlCase.fnFacts {c : Semantics} (h : c.OvlCase)
    (htr : ∀ a b e, (a, b) ∈ c.subsorts → (b, e) ∈ c.subsorts → (a, e) ∈ c.subsorts) : OvlLaws.OvlFnFacts c := by
  rcases h with hno | ⟨hok, hirr⟩
  · have hnil : ∀ o, o ∉ c.ovls := fun o ho => by rw [hno] at ho; cases ho
    exact ⟨fun o ho => absurd ho (hnil o), fun o ho => absurd ho (hnil o),
      fun o ho => absurd ho (hnil o), fun o ho => absurd ho (hnil o)⟩
  · exact (OvlLaws.OvlHyp.mk hok htr hirr).fnFacts

/-- **An application of an overloading symbol has a result** where its arguments have results and
each function among the symbols it overloads has a result at arguments of its sorts: the normal
form where no function overload covers the arguments' values (or an argument is undefined), the
covering function's result, lifted, where one does. -/
theorem EvalTerm.ovl_result {c : Semantics} (F : OvlLaws.OvlFnFacts c) {σ : Subst} {f : Sym} {ts : List Term}
    {rs : List (Option GroundTerm)} (hk : c.isCtor f = false) (ho : c.isOvl f = true) (hts : EvalTerms c σ ts rs)
    {o : OvlSig} (hlo : c.lookupOvl f = some o) (hws : ∀ ws, allSome rs = some ws → c.sortsOf ws = some o.sig.args)
    (hft : ∀ kg ∈ c.ovlOver o, c.ovlByFn kg = true → ∀ fn ∈ c.fns, c.lookupFn kg.name = some fn →
      kg.name = fn.label → ∀ vs, c.sortsOf vs = some fn.args → ∃ r, Eval c kg.name vs r) :
    ∃ r, EvalTerm c σ (.app f ts) r := by
  cases has : allSome rs with
  | none => exact ⟨_, .ovl hk ho hts (fun vs hv => by rw [has] at hv; cases hv)⟩
  | some ws =>
    cases hcv : c.fnCover f ws with
    | none => exact ⟨_, .ovl hk ho hts (fun vs hv => by rw [has] at hv; cases hv; exact hcv)⟩
    | some kg =>
      obtain ⟨fn, hfn, hlook, hsig, hkg, hb, -, hus⟩ := OvlLaws.fnCover_fn_ovlF F hlo (hws ws has) hcv
      obtain ⟨r, hr⟩ := hft kg hkg hb fn hfn hlook (by rw [hsig]) _ hus
      exact ⟨_, .ovlFn hk ho hts has hlo hcv hr⟩

/-- `OvlCase`, decided. -/
theorem Semantics.ovlCase_of {c : Semantics}
    (h : (c.ovls.isEmpty || (c.overloadsOK && c.subsorts.all fun p => p.1 != p.2)) = true) : c.OvlCase := by
  simp only [Bool.or_eq_true, Bool.and_eq_true, List.isEmpty_iff] at h
  refine h.imp id fun h => ⟨h.1, fun a ha => ?_⟩
  have := List.all_eq_true.mp h.2 _ ha
  simp at this

/-- `OvlCase` of a semantics whose overloading symbols are as the readings of `Γ` take them. -/
theorem OvlOK.ovlCase {c : Semantics} (h : OvlOK c) : c.OvlCase := .inr ⟨h.ok, h.irrefl⟩

/-- What evaluation needs of a well-formed definition: transitive subsorts, distinct function
labels, well-sorted right-hand sides, and overloading symbols that are none or well formed
(`OvlCase`), and every Range value a KItem (`RangeBelow`). -/
structure SortCtx (c : Semantics) : Prop where
  trans : ∀ a b d, (a, b) ∈ c.subsorts → (b, d) ∈ c.subsorts → (a, d) ∈ c.subsorts
  nodupFns : (c.allFns.map (·.label)).Nodup
  fns : ∀ fn ∈ c.allFns, ∃ L, HeadsOK c L ∧
    (∀ cl ∈ fn.clauses, sortOfTerm (c.rhsCtx L) cl.vars cl.rhs = some fn.result)
  ovl : c.OvlCase
  range : RangeBelow c

theorem nodup_of_eq_true : ∀ {l : List Srt}, nodup l = true → l.Nodup
  | [], _ => List.nodup_nil
  | a :: l, h => by
    simp only [nodup, Bool.and_eq_true, Bool.not_eq_true'] at h
    refine List.nodup_cons.mpr ⟨fun hm => ?_, nodup_of_eq_true h.2⟩
    have := List.contains_iff_mem.mpr hm
    rw [h.1] at this
    cases this

theorem lookupFn_spec {g : Sym} {fn : Fn} (h : c.lookupFn g = some fn) :
    fn ∈ c.allFns ∧ fn.label = g := by
  rw [Semantics.lookupFn_eq] at h
  exact ⟨List.mem_of_find?_eq_some h, by simpa using List.find?_some h⟩

theorem find?_label : ∀ {l : List Fn} {f : Fn}, (l.map (·.label)).Nodup → f ∈ l →
    l.find? (·.label == f.label) = some f
  | [], _, _, h => nomatch h
  | a :: l, f, hnd, h => by
    rw [List.map_cons, List.nodup_cons] at hnd
    rw [List.find?_cons]
    rcases List.mem_cons.mp h with rfl | h'
    · simp
    · have : (a.label == f.label) = false := by
        rw [beq_eq_false_iff_ne]
        intro he
        exact hnd.1 (he ▸ List.mem_map_of_mem h')
      rw [this]
      exact find?_label hnd.2 h'

theorem sortOf_injNormal (ht : ∀ a b d, (a, b) ∈ c.subsorts → (b, d) ∈ c.subsorts → (a, d) ∈ c.subsorts)
    {a b : Srt} {v : GroundTerm} (hab : (a, b) ∈ c.subsorts) (hv : c.sortOf v = some a) :
    c.sortOf (injNormal a b v) = some b := by
  cases v with
  | inj a' a'' w =>
    obtain ⟨h1, h2, h3, rfl⟩ := sortOf_inj.mp hv
    exact sortOf_inj.mpr ⟨ht _ _ _ h1 hab, h2, h3, rfl⟩
  | ctor f ts => exact sortOf_inj.mpr ⟨hab, rfl, hv, rfl⟩
  | dv s l => exact sortOf_inj.mpr ⟨hab, rfl, hv, rfl⟩
  | map s es => exact sortOf_inj.mpr ⟨hab, rfl, hv, rfl⟩
  | set s es => exact sortOf_inj.mpr ⟨hab, rfl, hv, rfl⟩
  | list s es => exact sortOf_inj.mpr ⟨hab, rfl, hv, rfl⟩

theorem sortsOf_get : ∀ {vs : List GroundTerm} {ss : List Srt}, c.sortsOf vs = some ss →
    ∀ {j : Nat} {s : Srt}, ss[j]? = some s → ∃ v, vs[j]? = some v ∧ c.sortOf v = some s
  | [], ss, h, j, s, hs => by
    rw [sortsOf_nil] at h; cases h; simp at hs
  | v :: vs, ss, h, j, s, hs => by
    obtain ⟨s₀, ss', hv, hvs, rfl⟩ := sortsOf_cons.mp h
    cases j with
    | zero => simp at hs; subst hs; exact ⟨v, rfl, hv⟩
    | succ j => simpa using sortsOf_get hvs (by simpa using hs)

theorem lookupSig_append_of_none {l l' : List CtorSig} {f : Sym} (h : lookupSig l f = none) :
    lookupSig (l ++ l') f = lookupSig l' f := by
  simp only [lookupSig_eq] at *
  rw [List.find?_append, h, Option.none_or]

theorem lookupSig_append_of_some {l l' : List CtorSig} {f : Sym} {k : CtorSig}
    (h : lookupSig l f = some k) : lookupSig (l ++ l') f = some k := by
  simp only [lookupSig_eq] at *
  rw [List.find?_append, h, Option.some_or]

theorem lookupSig_hookSigs_of_isHook {f : Sym} (h : isHook f = true) :
    ∃ k, lookupSig hookSigs f = some k := by
  have h' : ∃ g, (f, g) ∈ hookTable := by simpa [isHook, hook_eq] using h
  obtain ⟨g, hg⟩ := h'
  exact Option.isSome_iff_exists.mp (hookTable_sig (f, g) hg)

theorem lookupSig_hookSigs_of_not_isHook {f : Sym} (h : isHook f = false) :
    lookupSig hookSigs f = none := by
  cases hk : lookupSig hookSigs f with
  | none => rfl
  | some k =>
    obtain ⟨hm, hn⟩ := lookupSig_spec hk
    have := hookSigs_hooked k hm
    rw [hn, h] at this
    cases this

theorem allSome_some : ∀ {rs : List (Option GroundTerm)} {ws : List GroundTerm},
    allSome rs = some ws → ∀ (i : Nat) (r : Option GroundTerm), rs[i]? = some r → ∃ w, r = some w
  | [], _, _, i, r, hr => by simp at hr
  | r₀ :: rs, ws, h, i, r, hr => by
    simp only [allSome, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨w, hw, ws', hws', rfl⟩ := h
    cases i with
    | zero => simp at hr; subst hr; exact ⟨w, hw⟩
    | succ i => exact allSome_some hws' i r (by simpa using hr)

/-- A symbol of a well-sorted right-hand side that is not a function the right-hand side may call
is not found among them. -/
theorem lookup_preds_none (hc : SortCtx c) {L : List CtorSig} (hL : HeadsOK c L) {f : Sym}
    (hfn0 : c.lookupFn f = none) : lookupSig (c.sortPreds.map Fn.sig ++ L) f = none := by
  cases hk' : lookupSig (c.sortPreds.map Fn.sig ++ L) f with
  | none => rfl
  | some k =>
    obtain ⟨hkL, hkn⟩ := lookupSig_spec hk'
    obtain ⟨fn, hfn, rfl⟩ := headsOK_preds hL k hkL
    have hlook : c.lookupFn f = some fn := by
      rw [← hkn, Semantics.lookupFn_eq]; exact find?_label hc.nodupFns hfn
    rw [hlook] at hfn0; cases hfn0

/-- An overloading symbol heading a well-sorted right-hand side has the signature of its declaration. -/
theorem rhs_lookup_ovl (hc : SortCtx c) {L : List CtorSig} (hL : HeadsOK c L) {f : Sym} {k : CtorSig}
    (hk' : lookupSig (c.rhsCtx L).heads f = some k) (ho : c.isOvl f = true) :
    ∃ o, c.lookupOvl f = some o ∧ k = o.sig := by
  obtain ⟨hk, hhk, hp, hfn0, hso⟩ := c.isOvl_parts ho
  have hnc : lookupSig c.ctorSigs f = none :=
    Option.not_isSome_iff_eq_none.mp (by simpa [Semantics.isCtor] using hk)
  simp only [Semantics.rhsCtx, List.append_assoc] at hk'
  rw [lookupSig_append_of_none hnc, lookupSig_append_of_none (lookupSig_hookSigs_of_not_isHook hhk),
    lookupSig_append_of_none (c.lookupSig_params_of_not hp)] at hk'
  rw [show c.sortPreds.map Fn.sig ++ (L ++ c.ovlSigs) = (c.sortPreds.map Fn.sig ++ L) ++ c.ovlSigs from
    (List.append_assoc ..).symm, lookupSig_append_of_none (lookup_preds_none hc hL hfn0), lookupSig_eq,
    OvlLaws.find_ovlSigs] at hk'
  obtain ⟨o, ho', rfl⟩ := Option.map_eq_some_iff.mp hk'
  exact ⟨o, ho', rfl⟩

/-- A function that `Eval` relates is one of the semantics'. -/
theorem Eval.lookupFn_ne {f : Sym} {vs : List GroundTerm} {r : Option GroundTerm} (h : Eval c f vs r) :
    c.lookupFn f ≠ none := match h with
  | .clause hfn' .. => by rw [hfn']; simp
  | .rest hfn' _ => by rw [hfn']; simp
  | .ensFails hfn' .. => by rw [hfn']; simp
  | .clauseEx hfn' .. => by rw [hfn']; simp
  | .exNone hfn' .. => by rw [hfn']; simp

/-- A symbol of no overloading symbol's name is found among the functions a right-hand side may call
as it is found in the right-hand sides' context past the parameters. -/
theorem lookup_drop_ovls {L : List CtorSig} {f : Sym} {k : CtorSig} (hno : c.lookupOvl f = none)
    (hk' : lookupSig (c.sortPreds.map Fn.sig ++ (L ++ c.ovlSigs)) f = some k) :
    lookupSig (c.sortPreds.map Fn.sig ++ L) f = some k := by
  rw [← List.append_assoc] at hk'
  cases h0 : lookupSig (c.sortPreds.map Fn.sig ++ L) f with
  | some k0 => rw [lookupSig_append_of_some h0] at hk'; exact hk'
  | none => rw [lookupSig_append_of_none h0, lookupSig_eq, OvlLaws.find_ovlSigs, hno] at hk'; cases hk'

/-- With `OvlCase`, a symbol that is no overloading symbol has no overloading symbol's declaration. -/
theorem lookupOvl_none_of (hc : SortCtx c) {f : Sym} (h : c.isOvl f = false) : c.lookupOvl f = none := by
  cases ho : c.lookupOvl f with
  | none => rfl
  | some o =>
    rcases hc.ovl with hno | H
    · simp [Semantics.lookupOvl, hno] at ho
    · rw [(OvlLaws.ovl_facts_ovlF (OvlLaws.OvlHyp.fnFacts ⟨H.1, hc.trans, H.2⟩) ho).2.2.1] at h; cases h

/-- A function a well-sorted right-hand side calls has the signature it is found under among the
functions it may call: no overloading symbol shares its name. -/
theorem rhs_lookup_fn (hc : SortCtx c) {L : List CtorSig} {f : Sym} {k : CtorSig} {fn : Fn}
    (hfn : c.lookupFn f = some fn) (hk' : lookupSig (c.sortPreds.map Fn.sig ++ (L ++ c.ovlSigs)) f = some k) :
    lookupSig (c.sortPreds.map Fn.sig ++ L) f = some k := by
  rw [← List.append_assoc] at hk'
  cases h0 : lookupSig (c.sortPreds.map Fn.sig ++ L) f with
  | some k0 => rw [lookupSig_append_of_some h0] at hk'; exact hk'
  | none =>
    exfalso
    rw [lookupSig_append_of_none h0, lookupSig_eq, OvlLaws.find_ovlSigs] at hk'
    obtain ⟨o, ho, -⟩ := Option.map_eq_some_iff.mp hk'
    rcases hc.ovl with hno | H
    · simp [Semantics.lookupOvl, hno] at ho
    · have := (OvlLaws.ovl_facts_ovlF (OvlLaws.OvlHyp.fnFacts ⟨H.1, hc.trans, H.2⟩) ho).2.2.1
      rw [Semantics.isOvl, hfn] at this
      simp at this

mutual
  /-- A function at arguments of its argument sorts, when defined, has a value of its result sort. -/
  theorem Eval.sorted (hc : SortCtx c) {f : Sym} {vs : List GroundTerm} {r : Option GroundTerm}
      (h : Eval c f vs r) {fn : Fn} (hfn : c.lookupFn f = some fn)
      (hvs : c.sortsOf vs = some fn.args) {v : GroundTerm} (hr : r = some v) :
      c.sortOf v = some fn.result :=
    match h with
    | .clause (cl := cl) hfn' hmem hσ _ _ _ _ _ hrhs _ _ => by
      rw [hfn] at hfn'
      cases hfn'
      obtain ⟨L, hL, hcl⟩ := hc.fns fn (lookupFn_spec hfn).1
      exact EvalTerm.sorted hc hrhs hL hσ (hcl cl hmem) hr
    | .clauseEx (cl := cl) hfn' hmem hσ _ _ _ _ _ hrhs _ _ _ => by
      rw [hfn] at hfn'
      cases hfn'
      obtain ⟨L, hL, hcl⟩ := hc.fns fn (lookupFn_spec hfn).1
      exact EvalTerm.sorted hc hrhs hL hσ (hcl cl hmem) hr
    | .exNone .. => by cases hr
    | .rest (fn := fn') hfn' _ => by
      rw [hfn] at hfn'
      cases hfn'
      exact Semantics.fnRest_sorted hr
    | .ensFails .. => by cases hr
  termination_by structural h
  /-- A well-sorted term under a well-sorted σ, when defined, has a value of its sort. -/
  theorem EvalTerm.sorted (hc : SortCtx c) {σ : Subst} {t : Term} {r : Option GroundTerm}
      (h : EvalTerm c σ t r) {L : List CtorSig} {vars : List Srt} {s : Srt}
      (hL : HeadsOK c L) (hσ : c.WellSorted vars σ)
      (ht : sortOfTerm (c.rhsCtx L) vars t = some s) {v : GroundTerm} (hr : r = some v) :
      c.sortOf v = some s :=
    match h with
    | .var (i := i) => by
      obtain ⟨w, hw, hsw⟩ := hσ i s (sortOfTerm_var.mp ht)
      rw [hw] at hr
      cases hr
      exact hsw
    | .dv => by
      obtain ⟨hok, rfl⟩ := sortOfTerm_dv.mp ht
      cases hr
      exact sortOf_dv.mpr ⟨hok, rfl⟩
    | .inj (a := a) (b := b) h' => by
      obtain ⟨hab, ht', rfl⟩ := sortOfTerm_inj.mp ht
      obtain ⟨w, hw, rfl⟩ := Option.map_eq_some_iff.mp hr
      exact sortOf_injNormal hc.trans hab (EvalTerm.sorted hc h' hL hσ ht' hw)
    | .ctor (f := f) hk hts => by
      obtain ⟨k, hk', hargs, rfl⟩ := sortOfTerm_app.mp ht
      obtain ⟨ws, hws, rfl⟩ := Option.map_eq_some_iff.mp hr
      obtain ⟨k₀, hk₀⟩ := Option.isSome_iff_exists.mp hk
      simp only [Semantics.rhsCtx, List.append_assoc] at hk'
      rw [lookupSig_append_of_some hk₀] at hk'
      cases hk'
      exact sortOf_ctor_intro ⟨k, hk₀, EvalTerms.sorted hc hts hL hσ hargs hws, rfl⟩
    | .hook (f := f) (rs := rs) hk hhk hts hh hund => by
      obtain ⟨k, hk', hargs, rfl⟩ := sortOfTerm_app.mp ht
      cases hws : allSome rs with
      | none => rw [hund hws] at hr; cases hr
      | some ws =>
        have hv := hh ws hws
        rw [hr] at hv
        have hnc : lookupSig c.ctorSigs f = none :=
          Option.not_isSome_iff_eq_none.mp (by simpa [Semantics.isCtor] using hk)
        obtain ⟨k₀, hk₀⟩ := lookupSig_hookSigs_of_isHook hhk
        simp only [Semantics.rhsCtx, List.append_assoc] at hk'
        rw [lookupSig_append_of_none hnc, lookupSig_append_of_some hk₀] at hk'
        cases hk'
        exact hookRes_sorted (fun _ => hc.range) hk₀ (EvalTerms.sorted hc hts hL hσ hargs hws) hv
    | .param (f := f) (rs := rs) hk hhk hp hts hr' => by
      obtain ⟨k, hk', hargs, rfl⟩ := sortOfTerm_app.mp ht
      have hnc : lookupSig c.ctorSigs f = none :=
        Option.not_isSome_iff_eq_none.mp (by simpa [Semantics.isCtor] using hk)
      simp only [Semantics.rhsCtx, List.append_assoc] at hk'
      rw [lookupSig_append_of_none hnc, lookupSig_append_of_none (lookupSig_hookSigs_of_not_isHook hhk)] at hk'
      rw [hr'] at hr
      obtain ⟨ws, -, hv⟩ := Option.bind_eq_some_iff.mp hr
      obtain ⟨k₀, hk₀, hs⟩ := c.paramVal_sorted hv
      rw [lookupSig_append_of_some (l' := c.sortPreds.map Fn.sig ++ (L ++ c.ovlSigs)) (k := k₀.sig)
        (by rw [c.lookupSig_params, hk₀]; rfl)] at hk'
      cases hk'
      exact hs
    | .call (f := f) hk hhk hts hvs hf hp => by
      obtain ⟨k, hk', hargs, rfl⟩ := sortOfTerm_app.mp ht
      have hnc : lookupSig c.ctorSigs f = none :=
        Option.not_isSome_iff_eq_none.mp (by simpa [Semantics.isCtor] using hk)
      simp only [Semantics.rhsCtx, List.append_assoc] at hk'
      rw [lookupSig_append_of_none hnc, lookupSig_append_of_none (lookupSig_hookSigs_of_not_isHook hhk),
        lookupSig_append_of_none (c.lookupSig_params_of_not hp)]
        at hk'
      have hfn0 : ∃ fn0, c.lookupFn f = some fn0 := match hf with
        | .clause hfn' .. => ⟨_, hfn'⟩
        | .rest hfn' _ => ⟨_, hfn'⟩
        | .ensFails hfn' .. => ⟨_, hfn'⟩
        | .clauseEx hfn' .. => ⟨_, hfn'⟩
        | .exNone hfn' .. => ⟨_, hfn'⟩
      obtain ⟨hkL, hkn⟩ := lookupSig_spec (rhs_lookup_fn hc hfn0.choose_spec hk')
      obtain ⟨fn, hfn, rfl⟩ := headsOK_preds hL k hkL
      have hlook : c.lookupFn f = some fn := by
        rw [← hkn, Semantics.lookupFn_eq]; exact find?_label hc.nodupFns hfn
      exact Eval.sorted hc hf hlook (EvalTerms.sorted hc hts hL hσ hargs hvs) hr
    | .callUndef .. => by cases hr
    | .ovl (f := f) (rs := rs) hk ho hts hnf => by
      obtain ⟨k, hk', hargs, rfl⟩ := sortOfTerm_app.mp ht
      obtain ⟨o, hlo, rfl⟩ := rhs_lookup_ovl hc hL hk' ho
      obtain ⟨ws, hws, rfl⟩ := Option.map_eq_some_iff.mp hr
      have H := hc.ovl.resolve_left fun hno => by simp [Semantics.lookupOvl, hno] at hlo
      have HH : OvlLaws.OvlHyp c := ⟨H.1, hc.trans, H.2⟩
      exact OvlLaws.sortOf_norm_ovlF HH HH.fnFacts hlo (EvalTerms.sorted hc hts hL hσ hargs hws) (hnf ws hws)
    | .ovlFn (f := f) (vs := ws) (kg := kg) _ ho hts hws hlo hcov hf => by
      -- the covering function's value, of its result sort, lifted to the symbol's
      obtain ⟨k, hk', hargs, rfl⟩ := sortOfTerm_app.mp ht
      obtain ⟨o', hlo', rfl⟩ := rhs_lookup_ovl hc hL hk' ho
      rw [hlo] at hlo'
      cases hlo'
      obtain ⟨r1, hr1, rfl⟩ := Option.map_eq_some_iff.mp hr
      have H := hc.ovl.resolve_left fun hno => by simp [Semantics.lookupOvl, hno] at hlo
      have HH : OvlLaws.OvlHyp c := ⟨H.1, hc.trans, H.2⟩
      obtain ⟨o2, hlo2, hkg, hb, hcv⟩ := OvlLaws.fnCover_some_parts hcov
      rw [hlo] at hlo2
      cases hlo2
      obtain ⟨fn, -, hfn, hsig⟩ := OvlLaws.byFn_fn hkg hb
      have ha : fn.args = kg.args := by rw [hsig]
      have hres' : fn.result = kg.result := by rw [hsig]
      obtain ⟨hlen, -, hres, -⟩ := OvlLaws.over_ovlF HH.fnFacts hlo hkg
      obtain ⟨-, -, hlies⟩ := OvlLaws.covers_iff.mp hcv
      have hvs := EvalTerms.sorted hc hts hL hσ hargs hws
      have hs1 := Eval.sorted hc hf hfn (by rw [ha]; exact OvlLaws.sortsOf_stripAll hlen hvs hlies) hr1
      rw [hres'] at hs1
      exact OvlLaws.sortOf_lift HH hs1 hres
  termination_by structural h
  theorem EvalTerms.sorted (hc : SortCtx c) {σ : Subst} {ts : List Term}
      {rs : List (Option GroundTerm)} (h : EvalTerms c σ ts rs) {L : List CtorSig}
      {vars : List Srt} {ss : List Srt} (hL : HeadsOK c L) (hσ : c.WellSorted vars σ)
      (hts : sortsOfTerms (c.rhsCtx L) vars ts = some ss) {ws : List GroundTerm}
      (hws : allSome rs = some ws) : c.sortsOf ws = some ss :=
    match h with
    | .nil => by
      rw [sortsOfTerms_nil.mp hts]
      simp only [allSome, Option.some.injEq] at hws
      subst hws
      exact sortsOf_nil
    | .cons h' hs => by
      obtain ⟨s, ss', ht, hts', rfl⟩ := sortsOfTerms_cons.mp hts
      simp only [allSome, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hws
      obtain ⟨w, hw, ws', hws', rfl⟩ := hws
      exact sortsOf_cons.mpr ⟨s, ss', EvalTerm.sorted hc h' hL hσ ht hw,
        EvalTerms.sorted hc hs hL hσ hts' hws', rfl⟩
  termination_by structural h
end

/-! ## The generated sort predicates are well-formed functions -/

theorem lookupSig_ctorSigs_of_fixed {f : Sym} {k : CtorSig} (h : lookupSig fixedCtors f = some k)
    (L : List CtorSig) : lookupSig (c.ctorSigs ++ L) f = some k := by
  unfold Semantics.ctorSigs
  exact lookupSig_append_of_some (lookupSig_append_of_some (lookupSig_append_of_some h))

theorem sortsBelowKItem_sub {X : Srt} (h : X ∈ c.sortsBelowKItem) : (X, Srt.kitem) ∈ c.subsorts := by
  unfold Semantics.subsorts
  exact List.mem_append_right _ (List.mem_map_of_mem (f := (·, Srt.kitem)) h)

/-- What `fnOK` checks of a function, for the sort predicates, with no other function called. -/
theorem sortPreds_ctx {fn : Fn} (hfn : fn ∈ c.sortPreds) :
    ∀ cl ∈ fn.clauses, sortsOfTerms c.patCtx cl.vars cl.pats = some fn.args ∧
      noMapInList cl.pats = true ∧
      binds cl.vars.length (varOccsList cl.pats) = true ∧
      reqOK (c.rhsCtx []) cl.vars cl.req = true ∧
      sortOfTerm (c.rhsCtx []) cl.vars cl.rhs = some fn.result ∧
      reqOK (c.rhsCtx []) cl.vars cl.ens = true := by
  have hkseq : lookupSig c.patCtx.heads kseq = some ⟨kseq, [Srt.kitem, Srt.k], Srt.k⟩ :=
    lookupSig_ctorSigs_of_fixed (by decide) _
  have hdotk : lookupSig c.patCtx.heads dotk = some ⟨dotk, [], Srt.k⟩ :=
    lookupSig_ctorSigs_of_fixed (by decide) _
  have hdk : ∀ (vs : List Srt), sortOfTerm c.patCtx vs (.app dotk []) = some Srt.k := fun _ =>
    sortOfTerm_app.mpr ⟨_, hdotk, sortsOfTerms_nil.mpr rfl, rfl⟩
  have hbool : ∀ (vs : List Srt) (b : Bool),
      sortOfTerm (c.rhsCtx []) vs (.dv Srt.bool (.bool b)) = some Srt.bool := fun _ _ =>
    sortOfTerm_dv.mpr ⟨rfl, rfl⟩
  have hvar : sortsOfTerms c.patCtx [Srt.k] [.var 0] = some [Srt.k] :=
    sortsOfTerms_cons.mpr ⟨Srt.k, [], sortOfTerm_var.mpr rfl, sortsOfTerms_nil.mpr rfl, rfl⟩
  simp only [Semantics.sortPreds, List.cons_append, List.nil_append, List.mem_cons,
    List.mem_filterMap, Option.map_eq_some_iff] at hfn
  rcases hfn with rfl | rfl | ⟨X, hX, _, _, rfl⟩ <;> intro cl hcl <;>
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hcl
  · subst hcl
    exact ⟨hvar, rfl, rfl, rfl, hbool _ _, rfl⟩
  · rcases hcl with rfl | rfl
    · refine ⟨sortsOfTerms_cons.mpr ⟨Srt.k, [], sortOfTerm_app.mpr ⟨_, hkseq,
        sortsOfTerms_cons.mpr ⟨Srt.kitem, [Srt.k], sortOfTerm_var.mpr rfl,
          sortsOfTerms_cons.mpr ⟨Srt.k, [], hdk _, sortsOfTerms_nil.mpr rfl, rfl⟩, rfl⟩, rfl⟩,
        sortsOfTerms_nil.mpr rfl, rfl⟩, rfl, rfl, rfl, hbool _ _, rfl⟩
    · exact ⟨hvar, rfl, rfl, rfl, hbool _ _, rfl⟩
  · rcases hcl with rfl | rfl
    · refine ⟨sortsOfTerms_cons.mpr ⟨Srt.k, [], sortOfTerm_app.mpr ⟨_, hkseq,
        sortsOfTerms_cons.mpr ⟨Srt.kitem, [Srt.k],
          sortOfTerm_inj.mpr ⟨sortsBelowKItem_sub hX, sortOfTerm_var.mpr rfl, rfl⟩,
          sortsOfTerms_cons.mpr ⟨Srt.k, [], hdk _, sortsOfTerms_nil.mpr rfl, rfl⟩, rfl⟩, rfl⟩,
        sortsOfTerms_nil.mpr rfl, rfl⟩, rfl, rfl, rfl, hbool _ _, rfl⟩
    · exact ⟨hvar, rfl, rfl, rfl, hbool _ _, rfl⟩

/-- The sort predicates' clauses have no `ensures`. -/
theorem sortPreds_ens {fn : Fn} (hfn : fn ∈ c.sortPreds) : ∀ cl ∈ fn.clauses, cl.ens = none := by
  simp only [Semantics.sortPreds, List.cons_append, List.nil_append, List.mem_cons,
    List.mem_filterMap, Option.map_eq_some_iff] at hfn
  rcases hfn with rfl | rfl | ⟨X, _, _, _, rfl⟩ <;> intro cl hcl <;>
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hcl
  · subst hcl; rfl
  · rcases hcl with rfl | rfl <;> rfl
  · rcases hcl with rfl | rfl <;> rfl

/-- The sort predicates' clauses fix their variables (`clauseFixed`): each pattern is a variable,
or a constructor term over a variable and `.K`. -/
theorem sortPreds_fixed {fn : Fn} (hfn : fn ∈ c.sortPreds) : ∀ cl ∈ fn.clauses, c.clauseFixed cl = true := by
  have hks : (lookupSig c.ctorSigs kseq).isSome = true := by
    have := lookupSig_ctorSigs_of_fixed (c := c) (f := kseq) (k := ⟨kseq, [Srt.kitem, Srt.k], Srt.k⟩) (by decide) []
    rw [List.append_nil] at this; rw [this]; rfl
  have hds : (lookupSig c.ctorSigs dotk).isSome = true := by
    have := lookupSig_ctorSigs_of_fixed (c := c) (f := dotk) (k := ⟨dotk, [], Srt.k⟩) (by decide) []
    rw [List.append_nil] at this; rw [this]; rfl
  simp only [Semantics.sortPreds, List.cons_append, List.nil_append, List.mem_cons,
    List.mem_filterMap, Option.map_eq_some_iff] at hfn
  rcases hfn with rfl | rfl | ⟨X, hX, _, _, rfl⟩ <;> intro cl hcl <;>
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hcl
  · subst hcl; simp [Semantics.clauseFixed, uniqList, uniq]
  · rcases hcl with rfl | rfl <;> simp [Semantics.clauseFixed, uniqList, uniq, hks, hds]
  · rcases hcl with rfl | rfl <;> simp [Semantics.clauseFixed, uniqList, uniq, hks, hds]

/-! ## From `sortedOK` and `srReady` -/

/-- What evaluation needs, from `sortedOK` and `srReady`. Of each function it reads the right-hand
sides of its clauses (`clauseSorted`'s conjunct on them). -/
theorem sortCtx_of_all {c : Semantics} (hok : c.sortedOK = true) (hr : c.srReady = true)
    (hov : c.OvlCase) : SortCtx c := by
  simp only [Semantics.srReady, Bool.and_eq_true, List.all_eq_true] at hr
  obtain ⟨⟨hnd, htr⟩, hrk⟩ := hr
  replace hok := Semantics.sortedOK_sorted hok
  simp only [Bool.and_eq_true, List.all_eq_true] at hok
  obtain ⟨⟨_, hfns⟩, _⟩ := hok
  have htr' : ∀ a b d, (a, b) ∈ c.subsorts → (b, d) ∈ c.subsorts → (a, d) ∈ c.subsorts := fun a b d hab hbd => by
    have := htr (a, b) hab (b, d) hbd
    simp only [bne_self_eq_false, Bool.false_or, List.contains_iff_mem] at this
    exact this
  refine ⟨htr', nodup_of_eq_true hnd, fun fn hfn' => ?_, hov, rangeBelow_of_keysOK hrk⟩
  · rcases List.mem_append.mp hfn' with hfn | hfn
    rotate_left
    · exact ⟨[], fun k hk => (nomatch hk), fun cl h => (sortPreds_ctx hfn cl h).2.2.2.2.1⟩
    refine ⟨c.fns.map Fn.sig, fun k hk => ?_, fun cl hcl => ?_⟩
    · obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hk
      exact ⟨g, List.mem_append_left _ hg, rfl⟩
    · have := hfns fn hfn cl hcl
      simp only [Semantics.clauseSorted, Bool.and_eq_true, beq_iff_eq] at this
      replace this := this.1
      exact this.1.1.2

theorem sortCtx_of_okM {c : Semantics} (hok : c.okM = true) (hr : c.srReady = true) (hov : c.OvlCase) : SortCtx c :=
  sortCtx_of_all (Semantics.sortedOK_of_okAll (Semantics.okAll_of_okM hok)) hr hov

theorem sortCtx_of {c : Semantics} (hok : c.ok = true) (hr : c.srReady = true) (hov : c.OvlCase) : SortCtx c :=
  sortCtx_of_okM (Semantics.okM_of_ok hok) hr hov

/-- Subject reduction: in a core that `sortedOK` and `srReady` accept, a rule's right-hand side
evaluated under a well-sorted σ is, when defined, a configuration. Of the rule it reads the
right-hand side's sort (`ruleSorted`'s last conjunct); the left-hand side is not read. -/
theorem rhs_sorted_core {c : Semantics} (hok : c.sortedOK = true) (hsr : c.srReady = true) (hov : c.OvlCase) {r : Rule}
    (hr : r ∈ c.rules) {σ : Subst} (hσ : c.WellSorted r.vars σ) {v : GroundTerm}
    (he : EvalTerm c σ r.rhs (some v)) : c.sortOf v = some topCellSort := by
  have hrule : c.ruleSorted r = true := by
    replace hok := Semantics.sortedOK_sorted hok
    simp only [Bool.and_eq_true, List.all_eq_true] at hok
    exact hok.2 r hr
  simp only [Semantics.ruleSorted, Bool.and_eq_true, beq_iff_eq] at hrule
  exact EvalTerm.sorted (sortCtx_of_all hok hsr hov) he
    (fun k hk => by
      obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hk; exact ⟨g, List.mem_append_left _ hg, rfl⟩) hσ hrule.2 rfl

/-- `rhs_sorted_core` in a core that `okAll` accepts. -/
theorem rhs_sorted_all {c : Semantics} (hok : c.okAll = true) (hsr : c.srReady = true) (hov : c.OvlCase) {r : Rule}
    (hr : r ∈ c.rules) {σ : Subst} (hσ : c.WellSorted r.vars σ) {v : GroundTerm}
    (he : EvalTerm c σ r.rhs (some v)) : c.sortOf v = some topCellSort :=
  rhs_sorted_core (Semantics.sortedOK_of_okAll hok) hsr hov hr hσ he

/-- `rhs_sorted_all` in a core that `okM` accepts. -/
theorem rhs_sorted_okM {c : Semantics} (hok : c.okM = true) (hsr : c.srReady = true) (hov : c.OvlCase) {r : Rule}
    (hr : r ∈ c.rules) {σ : Subst} (hσ : c.WellSorted r.vars σ) {v : GroundTerm}
    (he : EvalTerm c σ r.rhs (some v)) : c.sortOf v = some topCellSort :=
  rhs_sorted_all (Semantics.okAll_of_okM hok) hsr hov hr hσ he

/-- `rhs_sorted_all` in a core that `ok` accepts. -/
theorem rhs_sorted {c : Semantics} (hok : c.ok = true) (hsr : c.srReady = true) (hov : c.OvlCase) {r : Rule}
    (hr : r ∈ c.rules) {σ : Subst} (hσ : c.WellSorted r.vars σ) {v : GroundTerm}
    (he : EvalTerm c σ r.rhs (some v)) : c.sortOf v = some topCellSort :=
  rhs_sorted_okM (Semantics.okM_of_ok hok) hsr hov hr hσ he

/-- So no rule application is lost to sorts: a match, a true `requires`, the predicate `pre`
holding, a defined right-hand side, a true `ensures`, the predicate `post` holding and no rule of a
smaller priority applying make a step. -/
theorem step_of_apply_core {c : Semantics} (hok : c.sortedOK = true) (hsr : c.srReady = true) (hov : c.OvlCase) {r : Rule}
    (hr : r ∈ c.rules) {x : Config c} {σ : Subst} (hσ : c.WellSorted r.vars σ)
    (hm : PatVal c σ r.lhs x.val) (hreq : ∀ t, r.req = some t → EvalTerm c σ t (some (bool true)))
    (hpre : Holds c r.vars.length σ r.pre true)
    {v : GroundTerm} (he : EvalTerm c σ r.rhs (some v))
    (hens : ∀ t, r.ens = some t → EvalTerm c σ t (some (bool true)))
    (hpost : Holds c r.vars.length σ r.post true)
    (hprio : ∀ r' ∈ c.rules, r'.prio < r.prio → NotApplies c r' x.val) :
    Step c x ⟨v, rhs_sorted_core hok hsr hov hr hσ he⟩ :=
  .rule r hr σ hσ hm hreq hpre he hens hpost hprio

/-- `step_of_apply_core` in a core that `okAll` accepts. -/
theorem step_of_apply_all {c : Semantics} (hok : c.okAll = true) (hsr : c.srReady = true) (hov : c.OvlCase) {r : Rule}
    (hr : r ∈ c.rules) {x : Config c} {σ : Subst} (hσ : c.WellSorted r.vars σ)
    (hm : PatVal c σ r.lhs x.val) (hreq : ∀ t, r.req = some t → EvalTerm c σ t (some (bool true)))
    (hpre : Holds c r.vars.length σ r.pre true)
    {v : GroundTerm} (he : EvalTerm c σ r.rhs (some v))
    (hens : ∀ t, r.ens = some t → EvalTerm c σ t (some (bool true)))
    (hpost : Holds c r.vars.length σ r.post true)
    (hprio : ∀ r' ∈ c.rules, r'.prio < r.prio → NotApplies c r' x.val) :
    Step c x ⟨v, rhs_sorted_all hok hsr hov hr hσ he⟩ :=
  step_of_apply_core (Semantics.sortedOK_of_okAll hok) hsr hov hr hσ hm hreq hpre he hens hpost hprio

/-- `step_of_apply_all` in a core that `ok` accepts: its rules' predicates are `\top` (`ok_rule`). -/
theorem step_of_apply {c : Semantics} (hok : c.ok = true) (hsr : c.srReady = true) (hov : c.OvlCase) {r : Rule}
    (hr : r ∈ c.rules) {x : Config c} {σ : Subst} (hσ : c.WellSorted r.vars σ)
    (hm : PatVal c σ r.lhs x.val) (hreq : ∀ t, r.req = some t → EvalTerm c σ t (some (bool true)))
    {v : GroundTerm} (he : EvalTerm c σ r.rhs (some v))
    (hens : ∀ t, r.ens = some t → EvalTerm c σ t (some (bool true)))
    (hprio : ∀ r' ∈ c.rules, r'.prio < r.prio → NotApplies c r' x.val) :
    Step c x ⟨v, rhs_sorted hok hsr hov hr hσ he⟩ :=
  step_of_apply_all (Semantics.okAll_of_ok hok) hsr hov hr hσ hm hreq ((Semantics.ok_rule hok hr).2.1 ▸ .top) he hens
    ((Semantics.ok_rule hok hr).2.2.1 ▸ .top) hprio

/-- A function of `c` at arguments of its argument sorts, when defined, has a value of its
result sort. -/
theorem Eval.sorted_of_all {c : Semantics} (hok : c.sortedOK = true) (hsr : c.srReady = true) (hov : c.OvlCase) {f : Sym}
    {vs : List GroundTerm} {v : GroundTerm} (h : Eval c f vs (some v)) {fn : Fn}
    (hfn : c.lookupFn f = some fn) (hvs : c.sortsOf vs = some fn.args) :
    c.sortOf v = some fn.result :=
  Eval.sorted (sortCtx_of_all hok hsr hov) h hfn hvs rfl

/-- `Eval.sorted_of_all` in a core that `okM` accepts. -/
theorem Eval.sorted_of_okM {c : Semantics} (hok : c.okM = true) (hsr : c.srReady = true) (hov : c.OvlCase) {f : Sym}
    {vs : List GroundTerm} {v : GroundTerm} (h : Eval c f vs (some v)) {fn : Fn}
    (hfn : c.lookupFn f = some fn) (hvs : c.sortsOf vs = some fn.args) :
    c.sortOf v = some fn.result :=
  Eval.sorted_of_all (Semantics.sortedOK_of_okAll (Semantics.okAll_of_okM hok)) hsr hov h hfn hvs

/-- `Eval.sorted_of_all` in a core that `ok` accepts. -/
theorem Eval.sorted_of {c : Semantics} (hok : c.ok = true) (hsr : c.srReady = true) (hov : c.OvlCase) {f : Sym}
    {vs : List GroundTerm} {v : GroundTerm} (h : Eval c f vs (some v)) {fn : Fn}
    (hfn : c.lookupFn f = some fn) (hvs : c.sortsOf vs = some fn.args) :
    c.sortOf v = some fn.result :=
  Eval.sorted_of_okM (Semantics.okM_of_ok hok) hsr hov h hfn hvs

end KCore
