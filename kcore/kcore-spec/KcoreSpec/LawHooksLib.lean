/-
  KCore. `lawHooks c H` is an interpretation the text admits wherever H is and gives `_RangeMap_` no
  value (`libAdmitted_lawHooks`).

  `lawHooks c H` differs from H only at the `raw` parameters. The conditions of `libAdmitted` but
  the last read the interpretation only through `fallback` at interpreted symbols (registry symbols,
  `hookSigs`) and at `rootFloat`, a registry symbol too (`sqrtFloatEq`), and the sorts only at the
  argument and result sorts of those symbols: Int, Bool, Float, String, Bytes, Endianness and
  Signedness (`lawLibSorts`). So those conditions carry over from H to `lawHooks c H` where
  - no `raw` parameter bears a registry symbol's number (`nRegSyms ≤ k.sig.name`): then
    `lawHooks c H` is H at every interpreted symbol;
  - no value of one of those sorts applies a `raw` parameter, under any interpretation
    (`Semantics.lawLibRawFree`): then such a value has the same sort under both interpretations
    (`sortOf_withHooks_rawFree`). This is the reason the statement holds: no total silent symbol of
    `totalSilentKeys` and no symbol the library's other sentences read takes an argument of a sort
    that holds a raw application.

  The last, `rangeMapAssocEq`, reads RangeMap, whose values hold KItems, and a KItem can hold a raw
  application: such a value can have its sort under `lawHooks c H` and none under H (`keepsRaw`), so
  H's condition does not reach it, and H's values of `_RangeMap_` at it are unconstrained. The
  condition is therefore not carried over; it holds under `lawHooks c H` wherever H gives
  `_RangeMap_` no value, as `lawHooks c H` then gives none either
  (`rangeMapAssocEq_of_app_none`), `HookParams.lib` among them (`lib_app_rmConcat_none`).

  `libAdmitted_lawHooks_of` states it with these two hypotheses and the third on `_RangeMap_`. `lawLibRawFree_of_shapes` gives the
  second from `shapesOK` and `floatShapeOK` (every value of those sorts is a literal, or one of
  BYTES' nullary constructors of Endianness and Signedness) and the first. `libAdmitted_lawHooks`,
  for a semantics meeting `coreOK`, takes the number outside the registry and `shapesOK` from
  `coreOK`'s `paramsPlain`, whose `raw` branch asks them (`Semantics.raw_of_core`), and
  `floatShapeOK` from `floatShapeOK_of_coreOK`.
-/
import KcoreSpec.LawHooks
import KcoreSpec.LibAdmitted

set_option autoImplicit false

namespace KCore

/-- The argument and result sorts of the interpreted symbols `libAdmitted` reads. -/
def lawLibSorts : List Srt :=
  [Srt.int, Srt.bool, Srt.float, Srt.string, Srt.bytes, Srt.endianness, Srt.signedness]

/-- **No value of a sort the library's sentences read applies a `raw` parameter**, under any
interpretation. -/
def Semantics.lawLibRawFree (c : Semantics) : Prop :=
  ∀ (H : HookParams) (v : GroundTerm) (s : Srt), s ∈ lawLibSorts →
    (c.withHooks H).sortOf v = some s → c.rawFree v = true

/-- Every interpreted symbol is a registry symbol. -/
theorem lawLib_hookSigs_reg : ∀ k ∈ hookSigs, k.name < nRegSyms := by decide +kernel

/-- The symbols of `totalSilentKeys` take arguments of, and give values of, sorts of
`lawLibSorts`. -/
theorem lawLib_totalSilentKeys_sorts :
    ∀ k ∈ hookSigs, k.name ∈ totalSilentKeys → ∀ s ∈ k.args, s ∈ lawLibSorts := by decide +kernel

theorem lawLib_totalSilentKeys_result :
    ∀ k ∈ hookSigs, k.name ∈ totalSilentKeys → lawLibSorts.contains k.result = true := by decide +kernel

section
variable {c : Semantics}

/-- Where no `raw` parameter bears a registry number, `lawHooks c H` is H at every registry symbol. -/
theorem lawLib_app_reg (hreg : ∀ k ∈ c.params, k.raw = true → nRegSyms ≤ k.sig.name) (H : HookParams)
    {f : Sym} (hf : f < nRegSyms) (vs : List GroundTerm) : (lawHooks c H).app f vs = H.app f vs := by
  apply lawHooks_app_of_find_none
  rw [List.find?_eq_none]
  intro k hk
  cases hraw : k.raw
  · simp
  · have := hreg k hk hraw
    have hne : k.sig.name ≠ f := fun he => by rw [he] at this; exact absurd hf (Nat.not_lt.mpr this)
    simp [hne]

/-- A value of a sort of `lawLibSorts` has that sort under one interpretation exactly where it has
it under another. -/
theorem lawLib_sortOf (hl : c.lawLibRawFree) (H₁ H₂ : HookParams) {v : GroundTerm} {s : Srt}
    (hs : s ∈ lawLibSorts) : (c.withHooks H₁).sortOf v = some s ↔ (c.withHooks H₂).sortOf v = some s := by
  constructor
  · intro h
    have hv := hl H₁ v s hs h
    rw [Semantics.sortOf_withHooks_rawFree c H₂ hv, ← Semantics.sortOf_withHooks_rawFree c H₁ hv]
    exact h
  · intro h
    have hv := hl H₂ v s hs h
    rw [Semantics.sortOf_withHooks_rawFree c H₁ hv, ← Semantics.sortOf_withHooks_rawFree c H₂ hv]
    exact h

theorem lawLib_sortsOf (hl : c.lawLibRawFree) (H₁ H₂ : HookParams) :
    ∀ {vs : List GroundTerm} {ss : List Srt}, (∀ s ∈ ss, s ∈ lawLibSorts) →
      (c.withHooks H₁).sortsOf vs = some ss → (c.withHooks H₂).sortsOf vs = some ss
  | [], ss, _, h => by
    rw [show (c.withHooks H₁).sortsOf [] = some [] from rfl] at h
    cases h; rfl
  | v :: vs, [], _, h => by
    simp only [Semantics.sortsOf] at h
    split at h <;> cases h
  | v :: vs, s :: ss, hss, h => by
    obtain ⟨h1, h2⟩ := OvlLaws.sortsOf_cons_iff.mp h
    exact OvlLaws.sortsOf_cons_iff.mpr ⟨(lawLib_sortOf hl H₁ H₂ (hss s (List.mem_cons_self ..))).mp h1,
      lawLib_sortsOf hl H₁ H₂ (fun s' hs' => hss s' (List.mem_cons_of_mem _ hs')) h2⟩

/-- **At an interpreted symbol whose result sort is one of `lawLibSorts`, the interpretation's
value is the same under `lawHooks c H` as under H.** -/
theorem lawLib_fallback (hreg : ∀ k ∈ c.params, k.raw = true → nRegSyms ≤ k.sig.name)
    (hl : c.lawLibRawFree) (H : HookParams) {f : Sym}
    (hr : (lookupSig hookSigs f).all (fun k => lawLibSorts.contains k.result) = true) (vs : List GroundTerm) :
    (c.withHooks (lawHooks c H)).fallback f vs = (c.withHooks H).fallback f vs := by
  unfold Semantics.fallback
  cases hk : lookupSig hookSigs f with
  | none => rfl
  | some k =>
    rw [hk] at hr
    have hres : k.result ∈ lawLibSorts := List.contains_iff_mem.mp (by simpa using hr)
    have hf : f < nRegSyms := by
      obtain ⟨hm, hn⟩ := lookupSig_spec hk
      exact hn ▸ lawLib_hookSigs_reg k hm
    have hp : ∀ w, ((c.withHooks (lawHooks c H)).sortOf w == some k.result) =
        ((c.withHooks H).sortOf w == some k.result) := fun w =>
      Bool.eq_iff_iff.mpr (by simp only [beq_iff_eq]; exact lawLib_sortOf hl _ _ hres)
    show ((lawHooks c H).app f vs).filter _ = (H.app f vs).filter _
    rw [lawLib_app_reg hreg H hf vs]
    simp only [hp]

theorem lawLib_hv (hreg : ∀ k ∈ c.params, k.raw = true → nRegSyms ≤ k.sig.name)
    (hl : c.lawLibRawFree) (H : HookParams) {f : Sym}
    (hr : (lookupSig hookSigs f).all (fun k => lawLibSorts.contains k.result) = true) (vs : List GroundTerm) :
    (c.withHooks (lawHooks c H)).hv f vs = (c.withHooks H).hv f vs := by
  unfold Semantics.hv Semantics.hookRes
  rw [lawLib_fallback hreg hl H hr vs]

/-- **`lawHooks c H` is admitted where H is and gives `_RangeMap_` no value**, where no `raw`
parameter bears a registry number and no value of a sort the library's sentences other than
`_RangeMap_`'s associativity read applies a `raw` parameter. -/
theorem libAdmitted_lawHooks_of (hreg : ∀ k ∈ c.params, k.raw = true → nRegSyms ≤ k.sig.name)
    (hl : c.lawLibRawFree) (H : HookParams) (ha : (c.withHooks H).libAdmitted)
    (hrm : ∀ vs, H.app rmConcat vs = none) :
    (c.withHooks (lawHooks c H)).libAdmitted := by
  obtain ⟨h1, h3, h4, h5, h6, h7, -⟩ := ha
  have e : ∀ f, (lookupSig hookSigs f).all (fun k => lawLibSorts.contains k.result) = true →
      ∀ vs, (c.withHooks (lawHooks c H)).hv f vs = (c.withHooks H).hv f vs :=
    fun f hr vs => lawLib_hv hreg hl H hr vs
  have eInf := e floatIsInfinite (by decide +kernel)
  have ePr := e floatPrecision (by decide +kernel)
  have eEx := e floatExponentBits (by decide +kernel)
  have eMx := e floatMaxValue (by decide +kernel)
  have eGt := e floatGt (by decide +kernel)
  have eNg := e floatNeg (by decide +kernel)
  have eLt := e floatLt (by decide +kernel)
  have eOr := e boolOr (by decide +kernel)
  have eSNe := e stringNe (by decide +kernel)
  have eRc := e stringRfindChar (by decide +kernel)
  have eSub := e stringSubstr (by decide +kernel)
  have eLen := e stringLength (by decide +kernel)
  have eRf := e stringRfind (by decide +kernel)
  have eMax := e intMax (by decide +kernel)
  have eFc := e stringFindChar (by decide +kernel)
  have eFd := e stringFind (by decide +kernel)
  have eIEq := e intEq (by decide +kernel)
  have eMin := e intMin (by decide +kernel)
  have eSq := e floatSqrt (by decide +kernel)
  have eIte : ∀ vs, (c.withHooks (lawHooks c H)).hv kIte vs = (c.withHooks H).hv kIte vs := fun vs => by
    unfold Semantics.hv
    rw [Semantics.hookRes_of_notKey silentKey_kIte, Semantics.hookRes_of_notKey silentKey_kIte]
  have eRa := e stringReplaceAll (by decide +kernel)
  have eCa := e stringCountAll (by decide +kernel)
  have eRp := e stringReplace (by decide +kernel)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_,
    rangeMapAssocEq_of_app_none fun vs => (lawLib_app_reg hreg H (by decide) vs).trans (hrm vs)⟩
  · intro k hk hkey vs hvs hh hs
    have hvs' := lawLib_sortsOf hl (lawHooks c H) H (lawLib_totalSilentKeys_sorts k hk hkey) hvs
    rw [lawLib_fallback hreg hl H (by
      rw [hookSigs_lookup k hk]; exact lawLib_totalSilentKeys_result k hk hkey) vs]
    exact h1 k hk hkey vs hvs' hh hs
  · intro F hF hh
    have hF' := (lawLib_sortOf hl (lawHooks c H) H (by decide)).mp hF
    simp only [eInf, ePr, eEx, eMx, eGt, eNg, eLt, eOr]
    exact h3 F hF' hh
  · intro s1 s2 i hs hne hh
    have hs' := lawLib_sortsOf hl (lawHooks c H) H (by decide) hs
    rw [eSNe] at hne
    simp only [eRc, eSub, eLen, eRf, eMax]
    exact h4 s1 s2 i hs' hne hh
  · intro s1 s2 i hs hne hh
    have hs' := lawLib_sortsOf hl (lawHooks c H) H (by decide) hs
    rw [eSNe] at hne
    simp only [eFc, eSub, eLen, eFd, eIEq, eMin, eIte]
    exact h5 s1 s2 i hs' hne hh
  · intro F hF
    have hF' := (lawLib_sortOf hl (lawHooks c H) H (by decide)).mp hF
    have hp : ∀ w, ((c.withHooks (lawHooks c H)).sortOf w == some Srt.float) =
        ((c.withHooks H).sortOf w == some Srt.float) := fun w =>
      Bool.eq_iff_iff.mpr (by simp only [beq_iff_eq]; exact lawLib_sortOf hl _ _ (by decide))
    have hr : (c.withHooks (lawHooks c H)).rootAt2 F = (c.withHooks H).rootAt2 F := by
      show ((lawHooks c H).app libRootFloat [F, int 2]).filter _ = (H.app libRootFloat [F, int 2]).filter _
      rw [lawLib_app_reg hreg H (by decide) [F, int 2]]
      simp only [hp]
    rw [hr, eSq]
    exact h6 F hF'
  · intro s n r hs hh
    have hs' := lawLib_sortsOf hl (lawHooks c H) H (by decide) hs
    simp only [eRa, eCa, eRp]
    exact h7 s n r hs' hh

/-- Where no parameter is raw, no value applies one. -/
theorem lawLibRawFree_of_noRaw (hr : ∀ k ∈ c.params, k.raw = false) : c.lawLibRawFree :=
  fun _ v _ _ _ => Semantics.rawFree_of_noRaw hr v

/-- A literal applies no parameter. -/
theorem lawLib_rawFree_dv (s : Srt) (l : Lit) : c.rawFree (.dv s l) = true := by
  simp [Semantics.rawFree]

/-- Int and Bool are no collection sort where no collection sort of the definition's own is one of
`shapeSorts`. -/
theorem lawLib_collOf_intBool (hs : c.shapesOK = true) {s : Srt} (hS : s = Srt.int ∨ s = Srt.bool)
    {k : CollSig} (h : c.collOf s = some k) : False := by
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

/-- **Under `shapesOK` and `floatShapeOK`, no value of a sort of `lawLibSorts` applies a `raw`
parameter**, where none bears a registry number: every value of Int, Bool, Float, String and Bytes
is a literal, and every value of Endianness and Signedness one of BYTES' nullary constructors. -/
theorem lawLibRawFree_of_shapes (hs : c.shapesOK = true) (hf : c.floatShapeOK = true)
    (hreg : ∀ k ∈ c.params, k.raw = true → nRegSyms ≤ k.sig.name) : c.lawLibRawFree := by
  intro H v s hsm hv
  have hs' : (c.withHooks H).shapesOK = true := hs
  have hf' : (c.withHooks H).floatShapeOK = true := hf
  have hctor : ∀ f : Sym, f < nRegSyms → c.rawFree (.ctor f []) = true := by
    intro f hfr
    simp only [Semantics.rawFree, Bool.and_eq_true, Bool.not_eq_true']
    refine ⟨List.any_eq_false.mpr fun k hk => ?_, rfl⟩
    cases hraw : k.raw
    · simp
    · have := hreg k hk hraw
      have hne : k.sig.name ≠ f := fun he => by rw [he] at this; exact absurd hfr (Nat.not_lt.mpr this)
      simp [hne]
  simp only [lawLibSorts, List.mem_cons, List.not_mem_nil, or_false] at hsm
  rcases hsm with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rcases shape_of_sortOf hs' (by decide) hv with ⟨l, rfl, -⟩ | ⟨_, k, -, hk, -⟩ | ⟨_, k, -, hk, -⟩ |
      ⟨_, k, -, hk, -⟩
    · exact lawLib_rawFree_dv _ _
    all_goals exact (lawLib_collOf_intBool (c := c.withHooks H) hs' (.inl rfl) hk).elim
  · rcases shape_of_sortOf hs' (by decide) hv with ⟨l, rfl, -⟩ | ⟨_, k, -, hk, -⟩ | ⟨_, k, -, hk, -⟩ |
      ⟨_, k, -, hk, -⟩
    · exact lawLib_rawFree_dv _ _
    all_goals exact (lawLib_collOf_intBool (c := c.withHooks H) hs' (.inr rfl) hk).elim
  · obtain ⟨p, e, b, rfl, -⟩ := shape_float hf' hv
    exact lawLib_rawFree_dv _ _
  · obtain ⟨t, rfl⟩ := shape_lit hs' (by decide) hv
    exact lawLib_rawFree_dv _ _
  · obtain ⟨t, rfl⟩ := shape_lit hs' (by decide) hv
    exact lawLib_rawFree_dv _ _
  · obtain ⟨f, rfl, he, -⟩ := shape_enum hs' (.inl rfl) hv
    rcases he rfl with rfl | rfl <;> exact hctor _ (by decide)
  · obtain ⟨f, rfl, -, he⟩ := shape_enum hs' (.inr rfl) hv
    rcases he rfl with rfl | rfl <;> exact hctor _ (by decide)

end

/-- **`lawHooks c H` is admitted wherever H is and gives `_RangeMap_` no value**, in a semantics
meeting `coreOK`: there the two hypotheses of `libAdmitted_lawHooks_of` on c hold. A raw parameter is numbered outside the registry
(`raw_of_core`); and no value of a sort of `lawLibSorts` applies one: where no parameter is raw by
`lawLibRawFree_of_noRaw`, and otherwise by `lawLibRawFree_of_shapes`, `paramsPlain`'s `raw` branch
asking `shapesOK` and `coreOK` giving `floatShapeOK` (`floatShapeOK_of_coreOK`). -/
theorem libAdmitted_lawHooks (c : Semantics) (h : c.coreOK = true) (H : HookParams)
    (ha : (c.withHooks H).libAdmitted) (hrm : ∀ vs, H.app rmConcat vs = none) :
    (c.withHooks (lawHooks c H)).libAdmitted := by
  have hreg : ∀ k ∈ c.params, k.raw = true → nRegSyms ≤ k.sig.name :=
    fun k hk hr => (Semantics.raw_of_core h hk hr).2.2.1
  refine libAdmitted_lawHooks_of hreg ?_ H ha hrm
  cases hany : c.params.any (·.raw)
  · exact lawLibRawFree_of_noRaw fun k hk => by simpa using List.any_eq_false.mp hany k hk
  · obtain ⟨k, hk, hr⟩ := List.any_eq_true.mp hany
    exact lawLibRawFree_of_shapes (Semantics.raw_of_core h hk hr).2.2.2.2 (floatShapeOK_of_coreOK h) hreg

end KCore
