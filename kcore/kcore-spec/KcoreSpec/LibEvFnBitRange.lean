/-
  KCore, checked layer: the equations of `bitRangeInt` and `signExtendBitRangeInt` (INT,
  domains.md 1438 and 1440 in K 7.1.337), in the function form (`LibEv.FnEqn`), entailed at values
  in every semantics meeting `coreOK` whose Int values are literals (`shapesOK`), for every
  interpretation.

  - `fnBitRange` (1438): `bitRangeInt(I, IDX, LEN) => (I >>Int IDX) modInt (1 <<Int LEN)`.
  - `fnSignExt` (1440): `signExtendBitRangeInt(I, IDX, LEN) => (bitRangeInt(I, IDX, LEN) +Int
    (1 <<Int (LEN -Int 1))) modInt (1 <<Int LEN) -Int (1 <<Int (LEN -Int 1))`.

  No symbol either side applies has a silent point (`silentKey` is false for each), so each side's
  value is `hook`'s. At an index and a length that are not negative (for 1440, a length of at
  least 1) both sides have the value `hook` gives the left side (`bitRangeVal`, `signExtVal`): the
  shifts are `x.fdiv 2^n` and `1 * 2^n`, and `modInt` by the power, which is not 0, is `emod`.
  Elsewhere both sides have no value: the left side's hook has none there, and on the right a
  shift by a negative amount (`IDX`, `LEN`, or `LEN -Int 1` at `LEN = 0`) has none, and so does
  every application above it.
-/
import KcoreSpec.LibEvCeil

set_option autoImplicit false

namespace KCore

namespace LibEv

open ML Faithful

section
variable {c : Semantics}

theorem brv_hv_bitRange {x i l : Int} (hi : 0 ≤ i) (hl : 0 ≤ l) :
    c.hv intBitRange [int x, int i, int l] = some (int (bitRangeVal x i l)) :=
  hv_of_value (by
    show hook intBitRange [int x, int i, int l] = some (some (int (bitRangeVal x i l)))
    have : hook intBitRange [int x, int i, int l] =
        some (if i < 0 ∨ l < 0 then none else some (int (bitRangeVal x i l))) := rfl
    rw [this]; simp only [show ¬ (i < 0 ∨ l < 0) by omega, ↓reduceIte])

theorem brv_hv_bitRange_none {x i l : Int} (h : i < 0 ∨ l < 0) :
    c.hv intBitRange [int x, int i, int l] = none :=
  ceil_hv_none (by decide +kernel) (by
    have : hook intBitRange [int x, int i, int l] =
        some (if i < 0 ∨ l < 0 then none else some (int (bitRangeVal x i l))) := rfl
    rw [this]; simp only [h, ↓reduceIte])

theorem brv_hv_signExt {x i l : Int} (hi : 0 ≤ i) (hl : 1 ≤ l) :
    c.hv intSignExtBitRange [int x, int i, int l] = some (int (signExtVal x i l)) :=
  hv_of_value (by
    show hook intSignExtBitRange [int x, int i, int l] = some (some (int (signExtVal x i l)))
    have : hook intSignExtBitRange [int x, int i, int l] =
        some (if i < 0 ∨ l < 1 then none else some (int (signExtVal x i l))) := rfl
    rw [this]; simp only [show ¬ (i < 0 ∨ l < 1) by omega, ↓reduceIte])

theorem brv_hv_signExt_none {x i l : Int} (h : i < 0 ∨ l < 1) :
    c.hv intSignExtBitRange [int x, int i, int l] = none :=
  ceil_hv_none (by decide +kernel) (by
    have : hook intSignExtBitRange [int x, int i, int l] =
        some (if i < 0 ∨ l < 1 then none else some (int (signExtVal x i l))) := rfl
    rw [this]; simp only [h, ↓reduceIte])

theorem brv_hv_shl_none {x n : Int} (hn : n < 0) : c.hv intShl [int x, int n] = none :=
  ceil_hv_none (by decide +kernel) (by
    have : hook intShl [int x, int n] = some (if n < 0 then none else some (int (x * 2 ^ n.toNat))) := rfl
    rw [this]; simp only [hn, ↓reduceIte])

theorem brv_hv_shr_none {x n : Int} (hn : n < 0) : c.hv intShr [int x, int n] = none :=
  ceil_hv_none (by decide +kernel) (by
    have : hook intShr [int x, int n] = some (if n < 0 then none else some (int (x.fdiv (2 ^ n.toNat)))) := rfl
    rw [this]; simp only [hn, ↓reduceIte])

theorem brv_pow_ne (n : Nat) : (2 : Int) ^ n ≠ 0 := by
  have : (0 : Int) < 2 ^ n := Int.pow_pos (by decide)
  omega

end

/-! ## 1438: `bitRangeInt(I, IDX, LEN) => (I >>Int IDX) modInt (1 <<Int LEN)` -/

def fnBitRange : FnEqn :=
  ⟨[("VarI", Srt.int), ("VarIDX", Srt.int), ("VarLEN", Srt.int)], intBitRange,
    [(Srt.int, .var 0, none), (Srt.int, .var 1, none), (Srt.int, .var 2, none)], Srt.int, none,
    .app intEMod [.app intShr [.var 0, .var 1], .app intShl [intT 1, .var 2]]⟩

theorem fnBitRange_holds {c : Semantics} (hs : c.shapesOK = true) : fnBitRange.Holds c := by
  intro σ hσ _ hm
  obtain ⟨x, hx⟩ := int_at hs hσ 0 (n := "VarI") rfl
  obtain ⟨i, hi⟩ := int_at hs hσ 1 (n := "VarIDX") rfl
  obtain ⟨l, hl⟩ := int_at hs hσ 2 (n := "VarLEN") rfl
  obtain ⟨h3, -, h4, -, h5, -, -⟩ := hm
  rw [fq_val_var] at h3 h4 h5
  have h3' : σ.lookup 3 = some (int x) := h3.symm.trans hx
  have h4' : σ.lookup 4 = some (int i) := h4.symm.trans hi
  have h5' : σ.lookup 5 = some (int l) := h5.symm.trans hl
  by_cases hi0 : i < 0
  · fq_eval [fnBitRange, h3', h4', h5', hx, hi, hl, brv_hv_bitRange_none (Or.inl hi0), brv_hv_shr_none hi0,
      Option.bind_none, Option.map_none]
  by_cases hl0 : l < 0
  · fq_eval [fnBitRange, h3', h4', h5', hx, hi, hl, brv_hv_bitRange_none (Or.inr hl0), brv_hv_shl_none hl0,
      hv_intShr (c := c) (x := x) (show 0 ≤ i by omega), Option.bind_none, Option.map_none]
  fq_eval [fnBitRange, h3', h4', h5', hx, hi, hl, brv_hv_bitRange (c := c) (x := x) (i := i) (l := l) (by omega) (by omega),
    hv_intShr (c := c) (x := x) (show 0 ≤ i by omega), hv_intShl (c := c) (x := 1) (show 0 ≤ l by omega),
    Int.one_mul, hv_intEMod (c := c) (brv_pow_ne l.toNat), bitRangeVal]

theorem fnBitRange_ev {c : Semantics} (h : c.coreOK = true) (hs : c.shapesOK = true) (ad : KoreAML.AxiomDecl)
    (hp : ad.ax.pattern = fnBitRange.patR) (hsv : ad.ax.sortVars = [KoreAML.Rv]) :
    EntailsAtValues c ad (KoreAML.trAxiom [] [] ad).pat :=
  FnEqn.entailed_reg h fnBitRange (by decide) (by rfl) (fnBitRange_holds hs) ad hp hsv

/-! ## 1440: `signExtendBitRangeInt(I, IDX, LEN) => (bitRangeInt(I, IDX, LEN) +Int (1 <<Int (LEN -Int 1)))
modInt (1 <<Int LEN) -Int (1 <<Int (LEN -Int 1))` -/

def fnSignExt : FnEqn :=
  ⟨[("VarI", Srt.int), ("VarIDX", Srt.int), ("VarLEN", Srt.int)], intSignExtBitRange,
    [(Srt.int, .var 0, none), (Srt.int, .var 1, none), (Srt.int, .var 2, none)], Srt.int, none,
    .app intSub
      [.app intEMod
        [.app intAdd [.app intBitRange [.var 0, .var 1, .var 2], .app intShl [intT 1, .app intSub [.var 2, intT 1]]],
         .app intShl [intT 1, .var 2]],
       .app intShl [intT 1, .app intSub [.var 2, intT 1]]]⟩

theorem fnSignExt_holds {c : Semantics} (hs : c.shapesOK = true) : fnSignExt.Holds c := by
  intro σ hσ _ hm
  obtain ⟨x, hx⟩ := int_at hs hσ 0 (n := "VarI") rfl
  obtain ⟨i, hi⟩ := int_at hs hσ 1 (n := "VarIDX") rfl
  obtain ⟨l, hl⟩ := int_at hs hσ 2 (n := "VarLEN") rfl
  obtain ⟨h3, -, h4, -, h5, -, -⟩ := hm
  rw [fq_val_var] at h3 h4 h5
  have h3' : σ.lookup 3 = some (int x) := h3.symm.trans hx
  have h4' : σ.lookup 4 = some (int i) := h4.symm.trans hi
  have h5' : σ.lookup 5 = some (int l) := h5.symm.trans hl
  by_cases hb : i < 0 ∨ l < 0
  · fq_eval [fnSignExt, h3', h4', h5', hx, hi, hl, brv_hv_signExt_none (c := c) (x := x) (i := i) (l := l) (Or.imp_right (by omega) hb),
      brv_hv_bitRange_none (c := c) (x := x) (i := i) (l := l) hb, Option.bind_none, Option.map_none]
  by_cases hl1 : l < 1
  · fq_eval [fnSignExt, h3', h4', h5', hx, hi, hl, brv_hv_signExt_none (c := c) (x := x) (i := i) (l := l) (Or.inr hl1),
      brv_hv_bitRange (c := c) (x := x) (i := i) (l := l) (show 0 ≤ i by omega) (show 0 ≤ l by omega), hv_intSub,
      brv_hv_shl_none (c := c) (x := 1) (show l - 1 < 0 by omega), Option.bind_none, Option.map_none]
  fq_eval [fnSignExt, h3', h4', h5', hx, hi, hl, brv_hv_signExt (c := c) (x := x) (i := i) (l := l) (by omega) (by omega),
    brv_hv_bitRange (c := c) (x := x) (i := i) (l := l) (show 0 ≤ i by omega) (show 0 ≤ l by omega), hv_intSub,
    hv_intShl (c := c) (x := 1) (show 0 ≤ l - 1 by omega), hv_intShl (c := c) (x := 1) (show 0 ≤ l by omega),
    Int.one_mul, hv_intAdd, hv_intEMod (c := c) (brv_pow_ne l.toNat), signExtVal]

theorem fnSignExt_ev {c : Semantics} (h : c.coreOK = true) (hs : c.shapesOK = true) (ad : KoreAML.AxiomDecl)
    (hp : ad.ax.pattern = fnSignExt.patR) (hsv : ad.ax.sortVars = [KoreAML.Rv]) :
    EntailsAtValues c ad (KoreAML.trAxiom [] [] ad).pat :=
  FnEqn.entailed_reg h fnSignExt (by decide) (by rfl) (fnSignExt_holds hs) ad hp hsv

end LibEv

end KCore
