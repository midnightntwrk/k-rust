/-
  The pattern a sort's projection is defined at, read in every model of `Γ`: for a sort X below
  KItem, `kseq(inj{X,KItem}(v), dotk)` is one element of K at each element v of X (`projPat_fun`)
  and different elements at different v (`projPat_inj`). For KItem the pattern is `kseq(v, dotk)`
  (`projItemPat_fun`, `projItemPat_inj`); for K it is `v` itself, which needs nothing.

  These follow from Cons-Fun and Cons-Inj of K's constructors `kseq` and `dotk` and of the
  injection `inj{X,KItem}`, a generator of KItem for every X with `(X, KItem)` among the subsorts:
  Γ holds those items where K and KItem are constructor sorts (`consSorts`). So an equation
  `project:X(kseq(inj{X,KItem}(K), dotk)) = K` of a projection Γ has no symbol for states of the
  pattern's symbols only what Γ entails: the pattern builds no element at two values of K.

  `projBelowB c X` decides, for a sort named X, that X is K, KItem or a sort of `c.sortsBelowKItem`,
  with K and KItem constructor sorts (`projBelowB_spec`), and then the pattern of X's projection
  (`projSelPat`, the shape `Parse.selectorPat` reads) is functional and injective on X in every
  model of `Γ` (`projSel_fun`, `projSel_inj`).

  The statements are over every interpretation that satisfies `Γ c`, not a particular model.
-/
import KcoreSpec.FaithfulNeg

set_option autoImplicit false

namespace KCore

open ML Faithful

namespace GenEqs

/-- K's constructor `kseq`, as `fixedCtors` declares it. -/
def projKseqSig : CtorSig := ⟨kseq, [Srt.kitem, Srt.k], Srt.k⟩

/-- K's constructor `dotk`, as `fixedCtors` declares it. -/
def projDotkSig : CtorSig := ⟨dotk, [], Srt.k⟩

/-- `kseq(φ, dotk)`, with the symbols as Γ's items name them. -/
def projItemPat (c : Semantics) (φ : KoreAML.P) : KoreAML.P :=
  KoreAML.Cons.genPat (c.sortName Srt.k) (Gen.toK c (.ctor projKseqSig))
    [φ, KoreAML.Cons.genPat (c.sortName Srt.k) (Gen.toK c (.ctor projDotkSig)) []]

/-- `kseq(inj{X,KItem}(φ), dotk)` for the sort named `X`. -/
def projInjPat (c : Semantics) (X : String) (φ : KoreAML.P) : KoreAML.P :=
  projItemPat c (KoreAML.Cons.genPat (c.sortName Srt.kitem) (.inj X) [φ])

/-- The pattern of the projection of the sort named `X` at `φ`: `φ` for K, `kseq(φ, dotk)` for
KItem, `kseq(inj{X,KItem}(φ), dotk)` otherwise. -/
def projSelPat (c : Semantics) (X : String) (φ : KoreAML.P) : KoreAML.P :=
  if X = "K" then φ else if X = "KItem" then projItemPat c φ else projInjPat c X φ

/-- The sort named `X` is K, KItem or a sort of `c.sortsBelowKItem`, and K and KItem are
constructor sorts. (`kseq` is a constructor, so it is never function-overloaded:
`projKseq_fnOvl`.) -/
def projBelowB (c : Semantics) (X : String) : Bool :=
  (consSorts c).contains Srt.k && (consSorts c).contains Srt.kitem &&
    (X == "K" || X == "KItem" || c.sortsBelowKItem.any (c.sortName · == X))

section
variable {c : Semantics}

theorem projSortName_k : c.sortName Srt.k = "K" := by
  unfold Semantics.sortName; simp only [show Srt.k < nRegSorts by decide, ↓reduceIte]; decide

theorem projSortName_kitem : c.sortName Srt.kitem = "KItem" := by
  unfold Semantics.sortName; simp only [show Srt.kitem < nRegSorts by decide, ↓reduceIte]; decide

theorem projKseq_mem : projKseqSig ∈ c.ctorSigs := by
  unfold Semantics.ctorSigs; exact List.mem_append_left _ (List.mem_append_left _ (by simp [fixedCtors, projKseqSig]))

theorem projDotk_mem : projDotkSig ∈ c.ctorSigs := by
  unfold Semantics.ctorSigs; exact List.mem_append_left _ (List.mem_append_left _ (by simp [fixedCtors, projDotkSig]))

theorem projKseq_fnOvl : c.fnOvl (.ctor projKseqSig) = false := fnOvl_ctorSigs projKseq_mem

theorem projDotk_fnOvl : c.fnOvl (.ctor projDotkSig) = false := fnOvl_ctorSigs projDotk_mem

/-- `kseq` is a generator of K and no open generator (its number is below `nRegSyms`). -/
theorem projKseq_gen : Gen.ctor projKseqSig ∈ (c.gens Srt.k).filter (!c.isOpenGen ·) := by
  refine List.mem_filter.mpr ⟨gens_ctor projKseq_mem, ?_⟩
  have h : ¬ nRegSyms ≤ kseq := by show ¬ nRegSyms ≤ 0; unfold nRegSyms; omega
  simp [Semantics.isOpenGen, Semantics.lookupOpen, projKseqSig, h]

/-- `dotk` is a generator of K and no open generator (its number is below `nRegSyms`). -/
theorem projDotk_gen : Gen.ctor projDotkSig ∈ (c.gens Srt.k).filter (!c.isOpenGen ·) := by
  refine List.mem_filter.mpr ⟨gens_ctor projDotk_mem, ?_⟩
  have h : ¬ nRegSyms ≤ dotk := by show ¬ nRegSyms ≤ 1; unfold nRegSyms; omega
  simp [Semantics.isOpenGen, Semantics.lookupOpen, projDotkSig, h]

/-- What `projBelowB` decides. -/
theorem projBelowB_spec {X : String} (h : projBelowB c X = true) :
    Srt.k ∈ consSorts c ∧ Srt.kitem ∈ consSorts c ∧
      (X = "K" ∨ X = "KItem" ∨ ∃ s, (s, Srt.kitem) ∈ c.subsorts ∧ c.sortName s = X) := by
  simp only [projBelowB, Bool.and_eq_true, Bool.or_eq_true, List.contains_iff_mem, beq_iff_eq,
    List.any_eq_true] at h
  obtain ⟨⟨hk, hki⟩, hX⟩ := h
  refine ⟨hk, hki, ?_⟩
  rcases hX with (hX | hX) | ⟨s, hs, hn⟩
  · exact Or.inl hX
  · exact Or.inr (Or.inl hX)
  · refine Or.inr (Or.inr ⟨s, ?_, hn⟩)
    unfold Semantics.subsorts
    exact List.mem_append_right _ (List.mem_map.mpr ⟨s, hs, rfl⟩)

end

section
variable {c : Semantics} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hI : I ⊧ᴵP Γ c)
include hI

omit hI in
/-- A generator applied to patterns that each denote one element denotes what the generator
builds from those elements. -/
theorem projGenPat_sing {e : Valuation M} (N : String) (g : KoreAML.Gen) {φs : List KoreAML.P} {xs : List M}
    (h : All2 (fun φ x => ∀ m, φ.interpret I e m ↔ m = x) φs xs) (m : M) :
    (KoreAML.Cons.genPat N g φs).interpret I e m ↔ GS I N g xs m := by
  rw [genPat_eq, interp_appList_sing _ _ xs h]
  unfold GS
  simp only [(genHead_closed N g).interp e KoreAML.val0]

/-- `dotk` denotes one element of K, at every valuation. -/
theorem projDotk_one (hK : Srt.k ∈ consSorts c) :
    ∃ d, InS I (c.sortName Srt.k) d ∧ ∀ (e : Valuation M) m,
      (KoreAML.Cons.genPat (c.sortName Srt.k) (Gen.toK c (.ctor projDotkSig)) []).interpret I e m ↔ m = d := by
  obtain ⟨d, hd, hdm⟩ := fun_at (defOK hI)
    (sat_cons hI (Or.inl ⟨_, funItem_mem hK projDotk_gen projDotk_fnOvl, rfl⟩)) (xs := []) rfl
    (fun i x s h1 _ => by simp at h1)
  exact ⟨d, hd, fun e m => (projGenPat_sing (I := I) _ _ .nil m).trans (hdm m)⟩

/-- `kseq(φ, dotk)`, for `φ` denoting an element `v` of KItem, as what `kseq` builds from `v` and
`dotk`'s element. -/
theorem projItem_gs (hK : Srt.k ∈ consSorts c) :
    ∃ d, InS I (c.sortName Srt.k) d ∧ ∀ (e : Valuation M) (φ : KoreAML.P) (v : M),
      (∀ m, φ.interpret I e m ↔ m = v) → ∀ m,
        (projItemPat c φ).interpret I e m ↔ GS I (c.sortName Srt.k) (Gen.toK c (.ctor projKseqSig)) [v, d] m := by
  obtain ⟨d, hd, hdm⟩ := projDotk_one hI hK
  exact ⟨d, hd, fun e φ v hφ m => projGenPat_sing _ _ (.cons hφ (.cons (hdm e) .nil)) m⟩

/-- **KItem's projection pattern is functional**: at an element `v` of KItem, `kseq(v, dotk)` is
one element of K. -/
theorem projItemPat_fun (hK : Srt.k ∈ consSorts c) {e : Valuation M} {φ : KoreAML.P} {v : M}
    (hφ : ∀ m, φ.interpret I e m ↔ m = v) (hv : InS I (c.sortName Srt.kitem) v) :
    ∃ y, InS I (c.sortName Srt.k) y ∧ ∀ m, (projItemPat c φ).interpret I e m ↔ m = y := by
  obtain ⟨d, hd, hgs⟩ := projItem_gs hI hK
  obtain ⟨y, hy, hym⟩ := fun_at (defOK hI)
    (sat_cons hI (Or.inl ⟨_, funItem_mem hK projKseq_gen projKseq_fnOvl, rfl⟩)) (xs := [v, d]) rfl
    (fun i x s h1 h2 => by
      match i with
      | 0 => simp [toK_argSorts, projKseqSig, Gen.argSorts] at h1 h2; subst h1; subst h2; exact hv
      | 1 => simp [toK_argSorts, projKseqSig, Gen.argSorts] at h1 h2; subst h1; subst h2; exact hd
      | _ + 2 => simp at h1)
  exact ⟨y, hy, fun m => (hgs e φ v hφ m).trans (hym m)⟩

/-- **KItem's projection pattern is injective**: `kseq(v, dotk)` and `kseq(v', dotk)` at elements
`v`, `v'` of KItem denote the same only where `v = v'`. -/
theorem projItemPat_inj (hK : Srt.k ∈ consSorts c) {e e' : Valuation M} {φ φ' : KoreAML.P} {v v' : M}
    (hφ : ∀ m, φ.interpret I e m ↔ m = v) (hφ' : ∀ m, φ'.interpret I e' m ↔ m = v')
    (hv : InS I (c.sortName Srt.kitem) v) (hv' : InS I (c.sortName Srt.kitem) v')
    (heq : ∀ m, (projItemPat c φ).interpret I e m ↔ (projItemPat c φ').interpret I e' m) : v = v' := by
  obtain ⟨d, hd, hgs⟩ := projItem_gs hI hK
  have hargs : ∀ w, InS I (c.sortName Srt.kitem) w → ∀ (i : Nat) x s, [w, d][i]? = some x →
      (Gen.toK c (.ctor projKseqSig)).argSorts[i]? = some s → InS I s x := fun w hw i x s h1 h2 => by
    match i with
    | 0 => simp [toK_argSorts, projKseqSig, Gen.argSorts] at h1 h2; subst h1; subst h2; exact hw
    | 1 => simp [toK_argSorts, projKseqSig, Gen.argSorts] at h1 h2; subst h1; subst h2; exact hd
    | _ + 2 => simp at h1
  have h := inj_at (defOK hI)
    (sat_cons hI (Or.inl ⟨_, injItem_mem hK projKseq_gen (by simp [projKseqSig, Gen.argSorts])
      projKseq_fnOvl, rfl⟩)) (xs := [v, d]) (ys := [v', d]) rfl rfl (hargs v hv) (hargs v' hv')
    (fun m => (hgs e φ v hφ m).symm.trans ((heq m).trans (hgs e' φ' v' hφ' m)))
  simpa using h

/-- `inj{X,KItem}(φ)`, for `φ` denoting an element `v` of a sort X below KItem, is one element of
KItem. -/
theorem projInj_one {X : Srt} (hX : (X, Srt.kitem) ∈ c.subsorts) (hKI : Srt.kitem ∈ consSorts c)
    {e : Valuation M} {φ : KoreAML.P} {v : M}
    (hφ : ∀ m, φ.interpret I e m ↔ m = v) (hv : InS I (c.sortName X) v) :
    ∃ a, InS I (c.sortName Srt.kitem) a ∧
      (∀ m, (KoreAML.Cons.genPat (c.sortName Srt.kitem) (.inj (c.sortName X)) [φ]).interpret I e m ↔ m = a) ∧
      (∀ m, GS I (c.sortName Srt.kitem) (.inj (c.sortName X)) [v] m ↔ m = a) := by
  obtain ⟨a, ha, ham⟩ := fun_at (defOK hI)
    (sat_cons hI (Or.inl ⟨_, funItem_mem hKI (gensF_inj hX) (g := .inj X) rfl, rfl⟩)) (xs := [v]) rfl
    (fun i x s h1 h2 => by
      match i with
      | 0 => simp [toK_argSorts, Gen.argSorts] at h1 h2; subst h1; subst h2; exact hv
      | _ + 1 => simp at h1)
  exact ⟨a, ha, fun m => (projGenPat_sing _ _ (.cons hφ .nil) m).trans (ham m), ham⟩

/-- **A projection's pattern is functional**: for a sort X below KItem (`(X, KItem)` among the
subsorts), with K and KItem constructor sorts, `kseq(inj{X,KItem}(v), dotk)` at an element `v` of X
is one element of K. -/
theorem projPat_fun {X : Srt} (hX : (X, Srt.kitem) ∈ c.subsorts) (hK : Srt.k ∈ consSorts c)
    (hKI : Srt.kitem ∈ consSorts c) {e : Valuation M} {φ : KoreAML.P} {v : M}
    (hφ : ∀ m, φ.interpret I e m ↔ m = v) (hv : InS I (c.sortName X) v) :
    ∃ y, InS I (c.sortName Srt.k) y ∧ ∀ m, (projInjPat c (c.sortName X) φ).interpret I e m ↔ m = y := by
  obtain ⟨a, ha, hpa, -⟩ := projInj_one hI hX hKI hφ hv
  exact projItemPat_fun hI hK hpa ha

/-- **A projection's pattern is injective**: for a sort X below KItem, with K and KItem
constructor sorts, `kseq(inj{X,KItem}(v), dotk)` and `kseq(inj{X,KItem}(v'), dotk)` at elements
`v`, `v'` of X denote the same only where `v = v'`. -/
theorem projPat_inj {X : Srt} (hX : (X, Srt.kitem) ∈ c.subsorts) (hK : Srt.k ∈ consSorts c)
    (hKI : Srt.kitem ∈ consSorts c) {e e' : Valuation M} {φ φ' : KoreAML.P} {v v' : M}
    (hφ : ∀ m, φ.interpret I e m ↔ m = v) (hφ' : ∀ m, φ'.interpret I e' m ↔ m = v')
    (hv : InS I (c.sortName X) v) (hv' : InS I (c.sortName X) v')
    (heq : ∀ m, (projInjPat c (c.sortName X) φ).interpret I e m ↔
      (projInjPat c (c.sortName X) φ').interpret I e' m) : v = v' := by
  obtain ⟨a, ha, hpa, hga⟩ := projInj_one hI hX hKI hφ hv
  obtain ⟨a', ha', hpa', hga'⟩ := projInj_one hI hX hKI hφ' hv'
  have haa : a = a' := projItemPat_inj hI hK hpa hpa' ha ha' heq
  subst haa
  have hargs : ∀ w, InS I (c.sortName X) w → ∀ (i : Nat) x s, [w][i]? = some x →
      (Gen.toK c (.inj X)).argSorts[i]? = some s → InS I s x := fun w hw i x s h1 h2 => by
    match i with
    | 0 => simp [toK_argSorts, Gen.argSorts] at h1 h2; subst h1; subst h2; exact hw
    | _ + 1 => simp at h1
  have h := inj_at (defOK hI)
    (sat_cons hI (Or.inl ⟨_, injItem_mem hKI (gensF_inj hX) (g := .inj X) (by simp [Gen.argSorts]) rfl, rfl⟩))
    (xs := [v]) (ys := [v']) rfl rfl (hargs v hv) (hargs v' hv')
    (fun m => (hga m).trans (hga' m).symm)
  simpa using h

/-- **The pattern of the projection of a sort that `projBelowB` accepts is functional** on that
sort, in every model of `Γ`. -/
theorem projSel_fun {X : String} (hB : projBelowB c X = true) {e : Valuation M} {φ : KoreAML.P} {v : M}
    (hφ : ∀ m, φ.interpret I e m ↔ m = v) (hv : InS I X v) :
    ∃ y, InS I "K" y ∧ ∀ m, (projSelPat c X φ).interpret I e m ↔ m = y := by
  obtain ⟨hK, hKI, hX⟩ := projBelowB_spec hB
  unfold projSelPat
  by_cases h1 : X = "K"
  · subst h1; exact ⟨v, hv, by simpa using hφ⟩
  by_cases h2 : X = "KItem"
  · subst h2
    simp only [h1, ↓reduceIte]
    rw [← projSortName_k (c := c)]
    exact projItemPat_fun hI hK hφ (by rw [projSortName_kitem]; exact hv)
  simp only [h1, h2, ↓reduceIte]
  rw [← projSortName_k (c := c)]
  obtain ⟨s, hs, rfl⟩ := hX.resolve_left h1 |>.resolve_left h2
  exact projPat_fun hI hs hK hKI hφ hv

/-- **The pattern of the projection of a sort that `projBelowB` accepts is injective** on that
sort, in every model of `Γ`. -/
theorem projSel_inj {X : String} (hB : projBelowB c X = true) {e e' : Valuation M} {φ φ' : KoreAML.P}
    {v v' : M} (hφ : ∀ m, φ.interpret I e m ↔ m = v) (hφ' : ∀ m, φ'.interpret I e' m ↔ m = v')
    (hv : InS I X v) (hv' : InS I X v')
    (heq : ∀ m, (projSelPat c X φ).interpret I e m ↔ (projSelPat c X φ').interpret I e' m) : v = v' := by
  obtain ⟨hK, hKI, hX⟩ := projBelowB_spec hB
  unfold projSelPat at heq
  by_cases h1 : X = "K"
  · subst h1
    simp only [↓reduceIte] at heq
    exact (hφ' v).mp ((heq v).mp ((hφ v).mpr rfl))
  by_cases h2 : X = "KItem"
  · subst h2
    simp only [h1, ↓reduceIte] at heq
    exact projItemPat_inj hI hK hφ hφ' (by rw [projSortName_kitem]; exact hv)
      (by rw [projSortName_kitem]; exact hv') heq
  simp only [h1, h2, ↓reduceIte] at heq
  obtain ⟨s, hs, rfl⟩ := hX.resolve_left h1 |>.resolve_left h2
  exact projPat_inj hI hs hK hKI hφ hφ' hv hv' heq

end

end GenEqs

end KCore

