/-
  KCore. The value model satisfies the items of the constructors' axioms.

  A generator of a constructor sort N builds, from values of its argument sorts that no function
  overload of it covers, one value of N (`genVal`, `gs_gen`): a constructor the constructor term,
  an overloading symbol the normal form (`norm`), the injection from a subsort `a` the value
  `injNormal a N v`. So each generator that is no function-overloaded symbol is a function
  (Cons-Fun); it is injective (Cons-Inj): a constructor term determines its arguments, `norm` is
  injective (`OvlLaws.norm_inj_ovlF`), and `injNormal a N` is injective on values of `a`, since an
  injection is never nested and no sort is below itself. Two generators build different values
  (Cons-Dist): two constructors of distinct names (`ctorsOnce`, `ovlsOnce`) build different terms,
  a normal form's raw application is of a symbol of its overload closure
  (`OvlLaws.norm_head_ovlF`), so generators whose closures do not meet build different values, at
  uncovered arguments an overloading symbol builds its raw application (Cons-Dist at uncovered
  arguments), a constructor term is no injection, and two injections from incomparable sorts build
  one value only from an injection of one value of a common lower bound (Cons-Dist′, and Cons-Dist
  where there is none). The values of N are exactly what its generators build (Cons-NoJunk,
  `consSort_shape`; a raw overloading application is its own normal form,
  `OvlLaws.norm_fixed_ovlF`), and injections compose (Cons-Coh). The items of a function-overloaded
  symbol, the overload equations and `SatConsGoal` are in ModelConsFn.lean.
-/
import KcoreSpec.ModelColls
import KcoreSpec.NamesApart
import KcoreSpec.OvlLawsFn

set_option autoImplicit false

namespace KCore

namespace Faithful

namespace Model

open ML
open KCore.NamesApart (lib_sorts_lt lib_ok)

variable {c : Semantics}

/-! ## What `HypModelCore` gives of the constructors and their sorts -/

theorem HypModelCore.ctorNames (h : HypModelCore c) : (c.ctorSigs.map (·.name)).Nodup := nodup_of_eq_true h.ctors

theorem HypModelCore.trans (h : HypModelCore c) :
    ∀ a b d, (a, b) ∈ c.subsorts → (b, d) ∈ c.subsorts → (a, d) ∈ c.subsorts :=
  (sortCtx_of_allClEx h.hyp.1 h.hyp.2.1 h.ovlCase).trans

theorem isCtor_of_mem {k : CtorSig} (hk : k ∈ c.ctorSigs) : c.isCtor k.name = true := by
  unfold Semantics.isCtor
  rw [lookupSig_eq]
  cases hf : c.ctorSigs.find? (·.name == k.name) with
  | none => exact absurd (List.find?_eq_none.mp hf k hk) (by simp)
  | some _ => rfl

theorem ctor_kernel {k : CtorSig} (hk : k ∈ c.ctorSigs) : k ∈ kernelSyms c :=
  List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hk)))

/-- The constructor sorts are numbered. -/
theorem consSorts_numbered (h : HypModelCore c) {N : Srt} (hN : N ∈ consSorts c) :
    N < nRegSorts + c.sortNames.length := by
  have hreg : ∀ s, s < nRegSorts → s < nRegSorts + c.sortNames.length :=
    fun s hs => Nat.lt_of_lt_of_le hs (Nat.le_add_right _ _)
  have hown : ∀ s ∈ c.userSorts, s < nRegSorts + c.sortNames.length := by
    have hids := h.ids
    unfold Semantics.idsOK at hids
    simp only [Bool.and_eq_true, beq_iff_eq] at hids
    have he : c.ownSorts = _ := hids.1.1.1
    intro s hs
    by_cases hge : nRegSorts ≤ s
    · have hs' : s ∈ c.ownSorts := List.mem_filter.mpr ⟨hs, decide_eq_true hge⟩
      rw [he] at hs'
      exact (List.mem_range'_1.mp hs').2
    · exact hreg _ (Nat.lt_of_not_le hge)
  unfold consSorts at hN
  rcases List.mem_append.mp (List.mem_filter.mp hN).1 with h1 | h1
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h1
    rcases h1 with rfl | rfl <;> exact hreg _ (by decide)
  · rw [mem_sortBy] at h1
    simp only [List.mem_append] at h1
    rcases h1 with h1 | h1
    · exact hown _ h1
    · unfold Semantics.libCtorSorts at h1
      exact hreg _ (lib_sorts_lt (lib_ok h.ids) _ (List.mem_filter.mp h1).1).1

theorem ovl_kernel {o : OvlSig} (ho : o ∈ c.ovls) : o.sig ∈ kernelSyms c :=
  List.mem_append_right _ (List.mem_map_of_mem ho)

/-- The generators: the constructors, the overloading symbols, the open generators (the `raw`
parameters) and the injections. -/
theorem mem_gens {N : Srt} {g : Gen} (hg : g ∈ c.gens N) :
    (∃ k ∈ c.ctorSigs, k.result = N ∧ g = .ctor k) ∨ (∃ o ∈ c.ovls, o.sig.result = N ∧ g = .ctor o.sig) ∨
      (∃ a, (a, N) ∈ c.subsorts ∧ g = .inj a) ∨
      (∃ k ∈ c.params, k.raw = true ∧ k.sig.result = N ∧ g = .ctor k.sig) := by
  unfold Semantics.gens at hg
  rcases List.mem_append.mp hg with hg | hg
  · rcases List.mem_append.mp hg with hg | hg
    · rcases List.mem_append.mp hg with hg | hg
      · obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hg
        obtain ⟨hk, hr⟩ := List.mem_filter.mp hk
        exact Or.inl ⟨k, hk, by simpa using hr, rfl⟩
      · obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hg
        obtain ⟨hk, hr⟩ := List.mem_filter.mp hk
        obtain ⟨o, ho, rfl⟩ := List.mem_map.mp hk
        exact Or.inr (Or.inl ⟨o, ho, by simpa using hr, rfl⟩)
    · obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hg
      obtain ⟨hk, hr⟩ := List.mem_filter.mp hk
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hk
      obtain ⟨hp, hraw⟩ := List.mem_filter.mp hp
      exact Or.inr (Or.inr (Or.inr ⟨p, hp, hraw, by simpa using hr, rfl⟩))
  · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hg
    rw [mem_sortBy] at ha
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ha
    obtain ⟨hp, hr⟩ := List.mem_filter.mp hp
    have : p.2 = N := by simpa using hr
    exact Or.inr (Or.inr (Or.inl ⟨p.1, by rw [← this]; exact hp, rfl⟩))

/-- **A raw parameter is an open generator**: `lookupOpen` answers for its name. By `paramsPlain`'s
`raw` branch it is numbered outside the registry (`raw_of_sortedOKCl`: `lookupOpen`'s guard), and
`idsOK` numbers it once, so the lookup finds it (`raw_lookup`). -/
theorem HypModelCore.raw_open (h : HypModelCore c) {k : ParamSig} (hk : k ∈ c.params) (hr : k.raw = true) :
    c.isOpenGen (.ctor k.sig) = true := by
  show (c.lookupOpen k.sig.name).isSome = true
  rw [(Semantics.raw_lookup h.ids hk hr (Semantics.raw_of_sortedOKClEx h.sound.1 hk hr).2.2.1).2]
  rfl

/-- The generators `consItemsK` writes functionality, injectivity and distinctness for (those that
are no open generator): the constructors, the overloading symbols and the injections. -/
theorem mem_gensF (h : HypModelCore c) {N : Srt} {g : Gen} (hg : g ∈ (c.gens N).filter (!c.isOpenGen ·)) :
    (∃ k ∈ c.ctorSigs, k.result = N ∧ g = .ctor k) ∨ (∃ o ∈ c.ovls, o.sig.result = N ∧ g = .ctor o.sig) ∨
      (∃ a, (a, N) ∈ c.subsorts ∧ g = .inj a) := by
  obtain ⟨hg, ho⟩ := List.mem_filter.mp hg
  rcases mem_gens hg with h1 | h2 | h3 | ⟨k, hk, hraw, -, rfl⟩
  · exact Or.inl h1
  · exact Or.inr (Or.inl h2)
  · exact Or.inr (Or.inr h3)
  · simp [h.raw_open hk hraw] at ho

/-- The generators that are no open generator, listed: the constructors, the overloading symbols
and the injections of `gens`, in its order. -/
theorem gensF_eq (h : HypModelCore c) (N : Srt) :
    (c.gens N).filter (!c.isOpenGen ·) =
      (c.ctorSigs.filter (·.result == N)).map .ctor ++ (c.ovlSigs.filter (·.result == N)).map .ctor ++
        (sortBy id ((c.subsorts.filter (·.2 == N)).map (·.1))).map .inj := by
  unfold Semantics.gens
  simp only [List.filter_append]
  have h1 : ((c.ctorSigs.filter (·.result == N)).map Gen.ctor).filter (!c.isOpenGen ·) =
      (c.ctorSigs.filter (·.result == N)).map Gen.ctor :=
    List.filter_eq_self.mpr fun g hg => by
      obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hg
      simp [isOpenGen_ctor h.genWf (List.mem_filter.mp hk).1]
  have h2 : ((c.ovlSigs.filter (·.result == N)).map Gen.ctor).filter (!c.isOpenGen ·) =
      (c.ovlSigs.filter (·.result == N)).map Gen.ctor :=
    List.filter_eq_self.mpr fun g hg => by
      obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hg
      simp [isOpenGen_ovl h.genWf (List.mem_filter.mp hk).1]
  have h3 : ((((c.params.filter (·.raw)).map (·.sig)).filter (·.result == N)).map Gen.ctor).filter
      (!c.isOpenGen ·) = [] :=
    List.filter_eq_nil_iff.mpr fun g hg => by
      obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hg
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp (List.mem_filter.mp hk).1
      obtain ⟨hp, hr⟩ := List.mem_filter.mp hp
      simp [h.raw_open hp hr]
  have h4 : ((sortBy id ((c.subsorts.filter (·.2 == N)).map (·.1))).map Gen.inj).filter (!c.isOpenGen ·) =
      (sortBy id ((c.subsorts.filter (·.2 == N)).map (·.1))).map Gen.inj :=
    List.filter_eq_self.mpr fun g hg => by
      obtain ⟨a, -, rfl⟩ := List.mem_map.mp hg
      rfl
  rw [h1, h2, h3, h4, List.append_nil]

theorem gens_ovl {o : OvlSig} (ho : o ∈ c.ovls) : Gen.ctor o.sig ∈ c.gens o.sig.result := by
  unfold Semantics.gens
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _
    (List.mem_map.mpr ⟨o.sig, List.mem_filter.mpr ⟨List.mem_map_of_mem ho, by simp⟩, rfl⟩)))

/-- A raw parameter is a generator of its result sort. -/
theorem gens_open {k : ParamSig} (hk : k ∈ c.params) (hr : k.raw = true) : Gen.ctor k.sig ∈ c.gens k.sig.result := by
  unfold Semantics.gens
  exact List.mem_append_left _ (List.mem_append_right _
    (List.mem_map.mpr ⟨k.sig, List.mem_filter.mpr ⟨List.mem_map_of_mem (List.mem_filter.mpr ⟨hk, hr⟩), by simp⟩, rfl⟩))

/-- The argument sorts of a generator of a constructor sort are numbered. -/
theorem gen_args_numbered (h : HypModelCore c) {N : Srt} {g : Gen} (hg : g ∈ c.gens N) :
    ∀ s ∈ g.argSorts, s < nRegSorts + c.sortNames.length := by
  rcases mem_gens hg with ⟨k, hk, -, rfl⟩ | ⟨o, ho, -, rfl⟩ | ⟨a, ha, rfl⟩ | ⟨k, hk, -, -, rfl⟩
  · exact fun s hs => h.symSorts (ctor_kernel hk) s (List.mem_cons_of_mem _ hs)
  · exact fun s hs => h.symSorts (ovl_kernel ho) s (List.mem_cons_of_mem _ hs)
  rotate_left
  · exact fun s hs => h.symSorts (kernel_param hk) s (List.mem_cons_of_mem _ hs)
  · intro s hs
    rw [show (Gen.inj a).argSorts = [a] from rfl, List.mem_singleton] at hs
    subst hs
    exact (h.subSorts ha).1

/-! ## The generators in the model -/

/-- What the generator `g` of the sort N builds from the values `vs`: a constructor's or an
overloading symbol's normal form (for a constructor, the constructor term), an injection's
`injNormal`. -/
def genVal (c : Semantics) (N : Srt) : Gen → List GroundTerm → GroundTerm
  | .ctor k, vs => c.norm k.name vs
  | .inj a, vs => injNormal a N (vs.headD (.ctor 0 []))

/-- A constructor's normal form is its term. -/
theorem norm_ctor (h : HypModelCore c) {k : CtorSig} (hk : k ∈ c.ctorSigs) (vs : List GroundTerm) :
    c.norm k.name vs = .ctor k.name vs :=
  OvlLaws.norm_none (OvlLaws.lookupOvl_none_of_ctor h.ovlHyp hk) vs

namespace AtT

variable {T : GroundTerm → GroundTerm → Prop}

theorem gs_ovl (hn : NamesApartK c) {o : OvlSig} (ho : o ∈ c.ovls) (hio : c.isOvl o.sig.name = true) (N : String)
    {vs : List GroundTerm} (hl : vs.length = o.sig.args.length) (hnf : c.fnCover o.sig.name vs = none) (m : Elem) :
    GS (stdI_T c T) N (Gen.toK c (.ctor o.sig)) (vs.map Elem.val) m ↔ m = .val (c.norm o.sig.name vs) := by
  rw [← result_ovl (vs := vs) hio hnf]
  exact symE_vals hn (ovl_kernel ho) hl m

end AtT

theorem gs_ovl (hn : NamesApartK c) {o : OvlSig} (ho : o ∈ c.ovls) (hio : c.isOvl o.sig.name = true) (N : String)
    {vs : List GroundTerm} (hl : vs.length = o.sig.args.length) (hnf : c.fnCover o.sig.name vs = none) (m : Elem) :
    GS (stdI c) N (Gen.toK c (.ctor o.sig)) (vs.map Elem.val) m ↔ m = .val (c.norm o.sig.name vs) :=
  AtT.gs_ovl (c := c) (T := StepM c) (hn := hn) (o := o) (ho := ho) (hio := hio) (N := N) (vs := vs) (hl := hl) (hnf := hnf) (m := m)

namespace AtT

variable {T : GroundTerm → GroundTerm → Prop}

theorem gs_ctor (hn : NamesApartK c) {k : CtorSig} (hk : k ∈ c.ctorSigs) (N : String) {vs : List GroundTerm}
    (hl : vs.length = k.args.length) (m : Elem) :
    GS (stdI_T c T) N (Gen.toK c (.ctor k)) (vs.map Elem.val) m ↔ m = .val (.ctor k.name vs) := by
  rw [← result_ctor (vs := vs) (isCtor_of_mem hk)]
  exact symE_vals hn (ctor_kernel hk) hl m

end AtT

theorem gs_ctor (hn : NamesApartK c) {k : CtorSig} (hk : k ∈ c.ctorSigs) (N : String) {vs : List GroundTerm}
    (hl : vs.length = k.args.length) (m : Elem) :
    GS (stdI c) N (Gen.toK c (.ctor k)) (vs.map Elem.val) m ↔ m = .val (.ctor k.name vs) :=
  AtT.gs_ctor (c := c) (T := StepM c) (hn := hn) (k := k) (hk := hk) (N := N) (vs := vs) (hl := hl) (m := m)

namespace AtT

variable {T : GroundTerm → GroundTerm → Prop}

theorem appE_inj2 (a N : Srt) (x m : Elem) :
    AppE (stdI_T c T) (.app .inj [.srt a, .srt N]) [x] m ↔ ∃ v, x = .val v ∧ m = .val (injNormal a N v) := by
  simp only [AppE]
  constructor
  · rintro ⟨a', ha', rfl⟩
    cases x with
    | val v => exact ⟨v, rfl, ha'⟩
    | srt _ => exact ha'.elim
    | app _ _ => exact ha'.elim
  · rintro ⟨v, rfl, rfl⟩
    exact ⟨_, rfl, rfl⟩

end AtT

theorem appE_inj2 (a N : Srt) (x m : Elem) :
    AppE (stdI c) (.app .inj [.srt a, .srt N]) [x] m ↔ ∃ v, x = .val v ∧ m = .val (injNormal a N v) :=
  AtT.appE_inj2 (c := c) (T := StepM c) (a := a) (N := N) (x := x) (m := m)

namespace AtT

variable {T : GroundTerm → GroundTerm → Prop}

theorem gs_inj (hn : NamesApartK c) {a N : Srt} (ha : a < nRegSorts + c.sortNames.length)
    (hN : N < nRegSorts + c.sortNames.length) (x m : Elem) :
    GS (stdI_T c T) (c.sortName N) (.inj (c.sortName a)) [x] m ↔ ∃ v, x = .val v ∧ m = .val (injNormal a N v) := by
  unfold GS genHead
  have hh : ∀ y, (KoreAML.appList (KoreAML.sym (.symbol "inj"))
      [KoreAML.Cons.sortP (c.sortName a), KoreAML.Cons.sortP (c.sortName N)]).interpret (stdI_T c T) KoreAML.val0 y ↔
      y = .app .inj [.srt a, .srt N] := by
    intro y
    rw [interp_appList_sing _ _ [.srt a, .srt N]
      (.cons (sort_den hn ha _) (.cons (sort_den hn hN _) .nil))]
    simp only [KoreAML.interp_sym, stdI_symb, evalSymb_inj, exists_eq_left, AppE, stdI_app, evalApp_inj0,
      evalApp_inj1]
  simp only [hh, exists_eq_left]
  exact appE_inj2 a N x m

end AtT

theorem gs_inj (hn : NamesApartK c) {a N : Srt} (ha : a < nRegSorts + c.sortNames.length)
    (hN : N < nRegSorts + c.sortNames.length) (x m : Elem) :
    GS (stdI c) (c.sortName N) (.inj (c.sortName a)) [x] m ↔ ∃ v, x = .val v ∧ m = .val (injNormal a N v) :=
  AtT.gs_inj (c := c) (T := StepM c) (hn := hn) (a := a) (N := N) (ha := ha) (hN := hN) (x := x) (m := m)

theorem sortsOf_len : ∀ {ws : List GroundTerm} {ss : List Srt}, c.sortsOf ws = some ss → ws.length = ss.length
  | [], ss, h => by rw [sortsOf_nil] at h; cases h; rfl
  | w :: ws, ss, h => by
    obtain ⟨s, ss', _, h2, rfl⟩ := sortsOf_cons.mp h
    simp [sortsOf_len h2]

theorem sortsOf_single {vs : List GroundTerm} {a : Srt} (h : c.sortsOf vs = some [a]) :
    ∃ v, vs = [v] ∧ c.sortOf v = some a := by
  cases vs with
  | nil => rw [sortsOf_nil] at h; cases h
  | cons v vs' =>
    obtain ⟨s, ss', hv, hss', he⟩ := sortsOf_cons.mp h
    simp only [List.cons.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact ⟨v, by rw [sortsOf_nil_eq hss'], hv⟩

namespace AtT

variable {T : GroundTerm → GroundTerm → Prop}

/-- **An open generator's raw value is its generator's application** at the transition `T`. -/
theorem gs_open (h : HypModelCore c) {f : Sym} {ws : List GroundTerm} {kp : ParamSig}
    (hko : c.lookupOpen f = some kp) (hws : c.sortsOf ws = some kp.sig.args) (hkr : c.keepsRaw f ws = true)
    (hv : c.sortOf (.ctor f ws) = some kp.sig.result) (N : String) :
    GS (stdI_T c T) N (Gen.toK c (.ctor kp.sig)) (ws.map Elem.val) (.val (.ctor f ws)) := by
  obtain ⟨hlp, hi⟩ := h.open_param hko
  obtain ⟨hkp, hraw, hn, -⟩ := c.lookupOpen_spec hko
  subst hn
  obtain ⟨hc, hh⟩ := h.paramKinds hkp
  have hp : c.isParam kp.sig.name = true := by
    unfold Semantics.isParam; rw [hlp]; rfl
  have hraw' : (c.hooks.app kp.sig.name ws).getD (.ctor kp.sig.name ws) = .ctor kp.sig.name ws := by
    unfold Semantics.keepsRaw at hkr
    cases ha : c.hooks.app kp.sig.name ws with
    | none => rfl
    | some w =>
      rw [ha] at hkr
      exact GroundTerm.cmp_eq _ _ (by simpa using hkr)
  have hpv : c.paramVal kp.sig.name ws = some (.ctor kp.sig.name ws) :=
    (paramVal_raw_sorted hlp hraw hi).mpr ⟨hraw'.symm, hv⟩
  exact (symE_vals (T := T) h.namesK (kernel_param hkp) (sortsOf_len hws) _).mpr
    ((result_param hc hh hp _).mpr ⟨_, rfl, hpv⟩)

/-- **A generator builds one value of its sort** from values of its argument sorts that no function
overload of it covers. -/
theorem gs_gen (h : HypModelCore c) {N : Srt} (hN : N ∈ consSorts c) {g : Gen} (hg : g ∈ (c.gens N).filter (!c.isOpenGen ·))
    {vs : List GroundTerm} (hvs : c.sortsOf vs = some g.argSorts)
    (hnc : ∀ k, g = .ctor k → c.fnCover k.name vs = none) :
    (∀ m, GS (stdI_T c T) (c.sortName N) (Gen.toK c g) (vs.map Elem.val) m ↔ m = .val (genVal c N g vs)) ∧
      c.sortOf (genVal c N g vs) = some N := by
  have hn := h.namesK
  rcases mem_gensF h hg with ⟨k, hk, rfl, rfl⟩ | ⟨o, ho, rfl, rfl⟩ | ⟨a, ha, rfl⟩
  · simp only [genVal, norm_ctor h hk]
    refine ⟨fun m => gs_ctor hn hk _ (sortsOf_len hvs) m, ?_⟩
    exact result_sorted h (ctor_kernel hk) hvs ((result_ctor (isCtor_of_mem hk) _).mpr rfl)
  · have hlo := OvlLaws.lookupOvl_of_nodup h.ovlsOnce ho
    have F := h.ovlHyp.fnFacts
    have hnf := hnc _ rfl
    exact ⟨fun m => gs_ovl hn ho (F.isOvl o ho) _ (sortsOf_len hvs) hnf m,
      OvlLaws.sortOf_norm_ovlF h.ovlHyp F hlo hvs hnf⟩
  · obtain ⟨v, rfl, hv⟩ := sortsOf_single hvs
    obtain ⟨hsa, hsN⟩ := h.subSorts ha
    refine ⟨fun m => ?_, sortOf_injNormal h.trans ha hv⟩
    show GS (stdI_T c T) (c.sortName N) (.inj (c.sortName a)) [Elem.val v] m ↔ _
    rw [gs_inj hn hsa hsN]
    constructor
    · rintro ⟨v', hv', rfl⟩; cases hv'; rfl
    · rintro rfl; exact ⟨v, rfl, rfl⟩

end AtT

/-- **An open generator's raw value is its generator's application**: the symbol applied to the
arguments' elements is the parameter's value (`result`), which is the raw application where the
interpretation leaves it raw (`paramVal_raw_sorted`). From the parameter the symbol names, with no
registry hook (`HypModelCore.open_param`). -/
theorem gs_open (h : HypModelCore c) {f : Sym} {ws : List GroundTerm} {kp : ParamSig}
    (hko : c.lookupOpen f = some kp) (hws : c.sortsOf ws = some kp.sig.args) (hkr : c.keepsRaw f ws = true)
    (hv : c.sortOf (.ctor f ws) = some kp.sig.result) (N : String) :
    GS (stdI c) N (Gen.toK c (.ctor kp.sig)) (ws.map Elem.val) (.val (.ctor f ws)) :=
  AtT.gs_open (c := c) (T := StepM c) h hko hws hkr hv N

/-- **A generator builds one value of its sort** from values of its argument sorts that no function
overload of it covers. -/
theorem gs_gen (h : HypModelCore c) {N : Srt} (hN : N ∈ consSorts c) {g : Gen} (hg : g ∈ (c.gens N).filter (!c.isOpenGen ·))
    {vs : List GroundTerm} (hvs : c.sortsOf vs = some g.argSorts)
    (hnc : ∀ k, g = .ctor k → c.fnCover k.name vs = none) :
    (∀ m, GS (stdI c) (c.sortName N) (Gen.toK c g) (vs.map Elem.val) m ↔ m = .val (genVal c N g vs)) ∧
      c.sortOf (genVal c N g vs) = some N :=
  AtT.gs_gen (c := c) (T := StepM c) (h := h) (N := N) (hN := hN) (g := g) (hg := hg) (vs := vs) (hvs := hvs)
    (hnc := hnc)

/-- No function overload covers anything at a generator that is no function-overloaded symbol. -/
theorem fnCover_none_of_fnOvl_false (h : HypModelCore c) {g : Gen} (hnf : c.fnOvl g = false) (vs : List GroundTerm) :
    ∀ k, g = .ctor k → c.fnCover k.name vs = none := by
  rintro k rfl
  cases hlo : c.lookupOvl k.name with
  | none => exact c.fnCover_of_lookupOvl_none hlo vs
  | some o =>
    obtain ⟨-, -, hio, -⟩ := OvlLaws.ovl_facts_ovlF h.ovlHyp.fnFacts hlo
    refine OvlLaws.fnCover_none_of_not_fnOvl (fun hm => ?_) vs
    simp [Semantics.fnOvl, hio, hlo, hm] at hnf

/-- A constructor is no function-overloaded symbol. -/
theorem fnOvl_ctor_false {k : CtorSig} (hio : c.isOvl k.name = false) : c.fnOvl (.ctor k) = false := by
  simp [Semantics.fnOvl, hio]

/-! ## Injections -/

theorem HypModelCore.irrefl (h : HypModelCore c) (s : Srt) : (s, s) ∉ c.subsorts :=
  fun hs => (genWf_sub h.genWf hs).2 rfl

/-- `injNormal a N` is injective on values of `a`. -/
theorem injNormal_inj' (h : HypModelCore c) {a N : Srt} {v w : GroundTerm} (hv : c.sortOf v = some a)
    (hw : c.sortOf w = some a) (he : injNormal a N v = injNormal a N w) : v = w := by
  cases v with
  | inj a₁ b₁ u₁ =>
    obtain ⟨_, _, _, rfl⟩ := sortOf_inj.mp hv
    cases w with
    | inj a₂ b₂ u₂ =>
      obtain ⟨_, _, _, rfl⟩ := sortOf_inj.mp hw
      simp only [injNormal, GroundTerm.inj.injEq] at he
      obtain ⟨rfl, -, rfl⟩ := he
      rfl
    | _ =>
      simp only [injNormal, GroundTerm.inj.injEq] at he
      obtain ⟨rfl, -, -⟩ := he
      exact absurd (sortOf_inj.mp hv).1 (h.irrefl _)
  | _ =>
    cases w with
    | inj a₂ b₂ u₂ =>
      obtain ⟨_, _, _, rfl⟩ := sortOf_inj.mp hw
      simp only [injNormal, GroundTerm.inj.injEq] at he
      obtain ⟨rfl, -, -⟩ := he
      exact absurd (sortOf_inj.mp hw).1 (h.irrefl _)
    | _ =>
      simp only [injNormal, GroundTerm.inj.injEq, true_and] at he
      exact he

theorem genVal_inj (h : HypModelCore c) {N : Srt} {g : Gen} (hg : g ∈ (c.gens N).filter (!c.isOpenGen ·)) {vs ws : List GroundTerm}
    (hvs : c.sortsOf vs = some g.argSorts) (hws : c.sortsOf ws = some g.argSorts)
    (hnv : ∀ k, g = .ctor k → c.fnCover k.name vs = none) (hnw : ∀ k, g = .ctor k → c.fnCover k.name ws = none)
    (he : genVal c N g vs = genVal c N g ws) : vs = ws := by
  rcases mem_gensF h hg with ⟨k, hk, -, rfl⟩ | ⟨o, ho, -, rfl⟩ | ⟨a, -, rfl⟩
  · simp only [genVal, norm_ctor h hk, GroundTerm.ctor.injEq] at he
    exact he.2
  · exact OvlLaws.norm_inj_ovlF h.ovlHyp h.ovlHyp.fnFacts (OvlLaws.lookupOvl_of_nodup h.ovlsOnce ho) hvs hws
      (hnv _ rfl) (hnw _ rfl) he
  · obtain ⟨v, rfl, hv⟩ := sortsOf_single hvs
    obtain ⟨w, rfl, hw⟩ := sortsOf_single hws
    simp only [genVal, List.headD_cons] at he
    rw [injNormal_inj' h hv hw he]

theorem mem_lowerBounds_of {a b x : Srt} (ha : (x, a) ∈ c.subsorts) (hb : (x, b) ∈ c.subsorts) :
    x ∈ c.lowerBounds a b := by
  unfold Semantics.lowerBounds
  rw [mem_sortBy]
  refine List.mem_filter.mpr ⟨List.mem_eraseDups.mpr (List.mem_map.mpr ⟨_, ha, rfl⟩), ?_⟩
  simp [ha, hb]

/-- Two injections from incomparable sorts build one value only from an injection of one value of
a common lower bound. -/
theorem inj_inj_eq {a b N : Srt} (hab : (c.le a b || c.le b a) = false) {v w : GroundTerm}
    (hv : c.sortOf v = some a) (hw : c.sortOf w = some b) (he : injNormal a N v = injNormal b N w) :
    ∃ x u, x ∈ c.lowerBounds a b ∧ c.sortOf u = some x ∧ u.isInj = false ∧ v = .inj x a u ∧ w = .inj x b u := by
  simp only [Bool.or_eq_false_iff, Semantics.le, beq_eq_false_iff_ne] at hab
  obtain ⟨⟨hne, hab1⟩, -, hba1⟩ := hab
  have hab1' : (a, b) ∉ c.subsorts := fun h' => by
    have := List.contains_iff_mem.mpr h'; simp_all
  have hba1' : (b, a) ∉ c.subsorts := fun h' => by
    have := List.contains_iff_mem.mpr h'; simp_all
  cases v with
  | inj a₁ b₁ u₁ =>
    obtain ⟨h1, h2, h3, rfl⟩ := sortOf_inj.mp hv
    cases w with
    | inj a₂ b₂ u₂ =>
      obtain ⟨h1', h2', h3', rfl⟩ := sortOf_inj.mp hw
      simp only [injNormal, GroundTerm.inj.injEq] at he
      obtain ⟨rfl, -, rfl⟩ := he
      exact ⟨a₁, u₁, mem_lowerBounds_of h1 h1', h3, h2, rfl, rfl⟩
    | _ =>
      simp only [injNormal, GroundTerm.inj.injEq] at he
      obtain ⟨rfl, -, -⟩ := he
      exact absurd h1 hba1'
  | _ =>
    cases w with
    | inj a₂ b₂ u₂ =>
      obtain ⟨h1', h2', h3', rfl⟩ := sortOf_inj.mp hw
      simp only [injNormal, GroundTerm.inj.injEq] at he
      obtain ⟨rfl, -, -⟩ := he
      exact absurd h1' hab1'
    | _ =>
      simp only [injNormal, GroundTerm.inj.injEq] at he
      exact absurd he.1 hne

theorem injNormal_comp (a b d : Srt) (v : GroundTerm) :
    injNormal b d (injNormal a b v) = injNormal a d v := by
  cases v <;> rfl

/-! ## Reading the items' patterns -/

namespace AtT

variable {T : GroundTerm → GroundTerm → Prop}

theorem disjList_intro {e : Valuation Elem} {m : Elem} : ∀ {ws : List KoreAML.P} {w : KoreAML.P}, w ∈ ws →
    w.interpret (stdI_T c T) e m → (KoreAML.disjList ws).interpret (stdI_T c T) e m
  | [], _, hw, _ => absurd hw List.not_mem_nil
  | [_], _, hw, h => by rw [List.mem_singleton.mp hw] at h; exact h
  | w' :: w'' :: ws, w, hw, h => by
    unfold KoreAML.disjList
    rw [interpret_disj]
    rcases List.mem_cons.mp hw with rfl | hw
    · exact Or.inl h
    · exact Or.inr (disjList_intro hw h)

end AtT

theorem disjList_intro {e : Valuation Elem} {m : Elem} : ∀ {ws : List KoreAML.P} {w : KoreAML.P}, w ∈ ws →
    w.interpret (stdI c) e m → (KoreAML.disjList ws).interpret (stdI c) e m :=
  AtT.disjList_intro (c := c) (T := StepM c) (e := e) (m := m)

theorem memGuards_cons (x : EVar) (xs : List EVar) (s : String) (ss : List String) :
    KoreAML.Cons.memGuards (x :: xs) (s :: ss) =
      (x ∈∈ KoreAML.inhOf (KoreAML.Cons.sortP s)) :: KoreAML.Cons.memGuards xs ss := rfl

namespace AtT

variable {T : GroundTerm → GroundTerm → Prop}

/-- Membership guards of numbered sorts hold of values of those sorts. -/
theorem memGuards_vals (hn : NamesApartK c) {e : Valuation Elem} {m : Elem} :
    ∀ (xs : List EVar) (ss : List Srt), (∀ s ∈ ss, s < nRegSorts + c.sortNames.length) → xs.length = ss.length →
    (∀ w ∈ KoreAML.Cons.memGuards xs (ss.map c.sortName), w.interpret (stdI_T c T) e m) →
    ∃ vs, xs.map e.evalEvar = vs.map Elem.val ∧ c.sortsOf vs = some ss
  | [], [], _, _, _ => ⟨[], rfl, sortsOf_nil⟩
  | [], _ :: _, _, hl, _ => by simp at hl
  | _ :: _, [], _, hl, _ => by simp at hl
  | x :: xs, s :: ss, hs, hl, hg => by
    rw [List.map_cons, memGuards_cons] at hg
    have h1 := hg _ (List.mem_cons_self ..)
    rw [KoreAML.interp_member defOK_std] at h1
    obtain ⟨v, hv, hvs⟩ := inSort_val ((inhOf_sort hn (hs s (List.mem_cons_self ..)) e _).mp h1)
    obtain ⟨vs, h3, h4⟩ := memGuards_vals hn xs ss (fun s' h' => hs s' (List.mem_cons_of_mem _ h'))
      (by simpa using hl) (fun w hw => hg w (List.mem_cons_of_mem _ hw))
    exact ⟨v :: vs, by simp [hv, h3], sortsOf_cons.mpr ⟨_, _, hvs, h4, rfl⟩⟩

end AtT

/-- Membership guards of numbered sorts hold of values of those sorts. -/
theorem memGuards_vals (hn : NamesApartK c) {e : Valuation Elem} {m : Elem} :
    ∀ (xs : List EVar) (ss : List Srt), (∀ s ∈ ss, s < nRegSorts + c.sortNames.length) → xs.length = ss.length →
    (∀ w ∈ KoreAML.Cons.memGuards xs (ss.map c.sortName), w.interpret (stdI c) e m) →
    ∃ vs, xs.map e.evalEvar = vs.map Elem.val ∧ c.sortsOf vs = some ss :=
  AtT.memGuards_vals (c := c) (T := StepM c) (hn := hn) (e := e) (m := m)

theorem zip_map_eq {α β : Type} (f : α → β) : ∀ (l1 l2 : List α), l1.map f = l2.map f →
    ∀ p ∈ l1.zip l2, f p.1 = f p.2
  | [], _, _, p, hp => by simp at hp
  | _ :: _, [], _, p, hp => by simp at hp
  | a :: l1, b :: l2, h, p, hp => by
    simp only [List.map_cons, List.cons.injEq] at h
    rcases List.mem_cons.mp hp with rfl | hp
    · exact h.1
    · exact zip_map_eq f l1 l2 h.2 p hp

namespace AtT

variable {T : GroundTerm → GroundTerm → Prop}

/-- `inj{s,t}(φ)` at a pattern that denotes one value. -/
theorem inj_sing (hn : NamesApartK c) {s t : Srt} (hs : s < nRegSorts + c.sortNames.length)
    (ht : t < nRegSorts + c.sortNames.length) {e : Valuation Elem} {φ : KoreAML.P} {u : GroundTerm}
    (hφ : ∀ m, φ.interpret (stdI_T c T) e m ↔ m = .val u) (m : Elem) :
    (KoreAML.appList (KoreAML.sym (.symbol "inj"))
      [KoreAML.Cons.sortP (c.sortName s), KoreAML.Cons.sortP (c.sortName t), φ]).interpret (stdI_T c T) e m ↔
      m = .val (injNormal s t u) := by
  rw [interp_injApp]
  simp only [hφ, exists_eq_left]
  rw [gs_inj hn hs ht]
  simp

end AtT

/-- `inj{s,t}(φ)` at a pattern that denotes one value. -/
theorem inj_sing (hn : NamesApartK c) {s t : Srt} (hs : s < nRegSorts + c.sortNames.length)
    (ht : t < nRegSorts + c.sortNames.length) {e : Valuation Elem} {φ : KoreAML.P} {u : GroundTerm}
    (hφ : ∀ m, φ.interpret (stdI c) e m ↔ m = .val u) (m : Elem) :
    (KoreAML.appList (KoreAML.sym (.symbol "inj"))
      [KoreAML.Cons.sortP (c.sortName s), KoreAML.Cons.sortP (c.sortName t), φ]).interpret (stdI c) e m ↔
      m = .val (injNormal s t u) :=
  AtT.inj_sing (c := c) (T := StepM c) (hn := hn) (s := s) (t := t) (hs := hs) (ht := ht) (e := e) (φ := φ) (u := u) (hφ := hφ) (m := m)

/-! ## Cons-Fun, Cons-Inj, Cons-Dist -/

section
variable (h : HypModelCore c) {N : Srt} (hN : N ∈ consSorts c)
include h hN

namespace AtT

variable {T : GroundTerm → GroundTerm → Prop}

theorem sat_funItem {g : Gen} (hg : g ∈ (c.gens N).filter (!c.isOpenGen ·)) (hnf : c.fnOvl g = false) :
    stdI_T c T ⊧ᴵ (KoreAML.Cons.funItem (c.sortName N) (Gen.toK c g)).pat := by
  have hn := h.namesK
  intro e m
  unfold KoreAML.Cons.funItem
  dsimp only
  simp only [toK_argSorts]
  refine guarded_intro fun hgd => ?_
  obtain ⟨vs, hxs, hvs⟩ := memGuards_vals (T := T) hn _ g.argSorts (gen_args_numbered h (List.mem_filter.mp hg).1) (by simp [xs_length]) hgd
  obtain ⟨hgs, hsort⟩ := gs_gen (T := T) h hN hg hvs (fnCover_none_of_fnOvl_false h hnf vs)
  rw [KoreAML.interp_sExists]
  refine ⟨.val (genVal c N g vs), ?_, ?_⟩
  · rw [KoreAML.interp_member defOK_std]
    simp only [Function.update_same]
    exact (inhOf_sort hn (consSorts_numbered h hN) _ _).mpr hsort
  · rw [KoreAML.interp_equal defOK_std]
    intro a
    rw [interp_genPat_vars, KoreAML.interp_evar]
    simp only [Function.update_same]
    rw [map_update_xs 0 _ _ _ _ (fun i hi he => by simp only [EVar.mk.injEq, List.length_map] at he hi; omega), hxs]
    exact hgs a

end AtT

theorem sat_funItem {g : Gen} (hg : g ∈ (c.gens N).filter (!c.isOpenGen ·)) (hnf : c.fnOvl g = false) :
    stdI c ⊧ᴵ (KoreAML.Cons.funItem (c.sortName N) (Gen.toK c g)).pat :=
  AtT.sat_funItem (c := c) (T := StepM c) (g := g) (hg := hg) (h := h) (hN := hN) (hnf := hnf)

namespace AtT

variable {T : GroundTerm → GroundTerm → Prop}

theorem sat_injItem {g : Gen} (hg : g ∈ (c.gens N).filter (!c.isOpenGen ·)) (hnf : c.fnOvl g = false) :
    stdI_T c T ⊧ᴵ (KoreAML.Cons.injItem (c.sortName N) (Gen.toK c g)).pat := by
  have hn := h.namesK
  intro e m
  unfold KoreAML.Cons.injItem
  dsimp only
  simp only [toK_argSorts]
  refine guarded_intro fun hgd => ?_
  have hnum := gen_args_numbered h (List.mem_filter.mp hg).1
  obtain ⟨vs, hxs, hvs⟩ := memGuards_vals (T := T) hn _ g.argSorts hnum (by simp [xs_length])
    (fun w hw => hgd w (List.mem_append_left _ hw))
  obtain ⟨ws, hys, hws⟩ := memGuards_vals (T := T) hn _ g.argSorts hnum (by simp [xs_length])
    (fun w hw => hgd w (List.mem_append_right _ hw))
  rw [interpret_impl]
  intro heq
  rw [KoreAML.interp_equal defOK_std] at heq
  have hv : genVal c N g vs = genVal c N g ws := by
    have := heq (.val (genVal c N g vs))
    rw [interp_genPat_vars, interp_genPat_vars, hxs, hys,
      (gs_gen h hN hg hvs (fnCover_none_of_fnOvl_false h hnf vs)).1,
      (gs_gen h hN hg hws (fnCover_none_of_fnOvl_false h hnf ws)).1] at this
    exact Elem.val.inj (this.mp rfl)
  have hvw : vs = ws := genVal_inj h hg hvs hws (fnCover_none_of_fnOvl_false h hnf vs)
    (fnCover_none_of_fnOvl_false h hnf ws) hv
  subst hvw
  rw [← hys] at hxs
  apply KoreAML.interp_conjList
  intro w hw
  obtain ⟨⟨a, b⟩, hab, rfl⟩ := List.mem_map.mp hw
  rw [KoreAML.interp_equal defOK_std]
  intro z
  rw [KoreAML.interp_evar, KoreAML.interp_evar, zip_map_eq e.evalEvar _ _ hxs _ hab]

end AtT

theorem sat_injItem {g : Gen} (hg : g ∈ (c.gens N).filter (!c.isOpenGen ·)) (hnf : c.fnOvl g = false) :
    stdI c ⊧ᴵ (KoreAML.Cons.injItem (c.sortName N) (Gen.toK c g)).pat :=
  AtT.sat_injItem (c := c) (T := StepM c) (g := g) (hg := hg) (h := h) (hN := hN) (hnf := hnf)

namespace AtT

variable {T : GroundTerm → GroundTerm → Prop}

theorem sat_dist_of {g g' : Gen} (hg : g ∈ (c.gens N).filter (!c.isOpenGen ·)) (hg' : g' ∈ (c.gens N).filter (!c.isOpenGen ·))
    (hnf : c.fnOvl g = false) (hnf' : c.fnOvl g' = false)
    (hne : ∀ vs ws, c.sortsOf vs = some g.argSorts → c.sortsOf ws = some g'.argSorts →
      genVal c N g vs ≠ genVal c N g' ws) :
    stdI_T c T ⊧ᴵ (KoreAML.Cons.distItem (c.sortName N) (Gen.toK c g) (Gen.toK c g')).pat := by
  have hn := h.namesK
  intro e m
  unfold KoreAML.Cons.distItem
  dsimp only
  simp only [toK_argSorts]
  refine guarded_intro fun hgd => ?_
  obtain ⟨vs, hxs, hvs⟩ := memGuards_vals (T := T) hn _ g.argSorts (gen_args_numbered h (List.mem_filter.mp hg).1) (by simp [xs_length])
    (fun w hw => hgd w (List.mem_append_left _ hw))
  obtain ⟨ws, hys, hws⟩ := memGuards_vals (T := T) hn _ g'.argSorts (gen_args_numbered h (List.mem_filter.mp hg').1) (by simp [xs_length])
    (fun w hw => hgd w (List.mem_append_right _ hw))
  rw [KoreAML.interp_notEqual defOK_std]
  intro heq
  have := heq (.val (genVal c N g vs))
  rw [interp_genPat_vars, interp_genPat_vars, hxs, hys,
    (gs_gen h hN hg hvs (fnCover_none_of_fnOvl_false h hnf vs)).1,
    (gs_gen h hN hg' hws (fnCover_none_of_fnOvl_false h hnf' ws)).1] at this
  exact hne vs ws hvs hws (Elem.val.inj (this.mp rfl))

end AtT

theorem sat_dist_of {g g' : Gen} (hg : g ∈ (c.gens N).filter (!c.isOpenGen ·)) (hg' : g' ∈ (c.gens N).filter (!c.isOpenGen ·))
    (hnf : c.fnOvl g = false) (hnf' : c.fnOvl g' = false)
    (hne : ∀ vs ws, c.sortsOf vs = some g.argSorts → c.sortsOf ws = some g'.argSorts →
      genVal c N g vs ≠ genVal c N g' ws) :
    stdI c ⊧ᴵ (KoreAML.Cons.distItem (c.sortName N) (Gen.toK c g) (Gen.toK c g')).pat :=
  AtT.sat_dist_of (c := c) (T := StepM c) (g := g) (g' := g') (hg := hg) (hg' := hg') (hne := hne) (h := h) (hN := hN)
    (hnf := hnf) (hnf' := hnf')

end

namespace AtT

variable {T : GroundTerm → GroundTerm → Prop}

theorem inj_sing' (hn : NamesApartK c) {s t : Srt} (hs : s < nRegSorts + c.sortNames.length)
    (ht : t < nRegSorts + c.sortNames.length) {e : Valuation Elem} {φ : KoreAML.P} {u : GroundTerm}
    (hφ : ∀ m, φ.interpret (stdI_T c T) e m ↔ m = .val u) (m : Elem) :
    (KoreAML.appList (KoreAML.sym (.symbol "inj"))
      [sortP (c.sortName s), sortP (c.sortName t), φ]).interpret (stdI_T c T) e m ↔
      m = .val (injNormal s t u) :=
  inj_sing hn hs ht hφ m

end AtT

theorem inj_sing' (hn : NamesApartK c) {s t : Srt} (hs : s < nRegSorts + c.sortNames.length)
    (ht : t < nRegSorts + c.sortNames.length) {e : Valuation Elem} {φ : KoreAML.P} {u : GroundTerm}
    (hφ : ∀ m, φ.interpret (stdI c) e m ↔ m = .val u) (m : Elem) :
    (KoreAML.appList (KoreAML.sym (.symbol "inj"))
      [sortP (c.sortName s), sortP (c.sortName t), φ]).interpret (stdI c) e m ↔
      m = .val (injNormal s t u) :=
  AtT.inj_sing' (c := c) (T := StepM c) (hn := hn) (s := s) (t := t) (hs := hs) (ht := ht) (e := e) (φ := φ) (u := u) (hφ := hφ) (m := m)

/-! ## The pairs of generators -/

/-- A pair of a filtered list is a pair of the list. -/
theorem pairs_filter_sub {α : Type} {p : α → Bool} {x y : α} : ∀ {l : List α},
    (x, y) ∈ pairs (l.filter p) → (x, y) ∈ pairs l
  | [], hp => by simp [pairs] at hp
  | a :: as, hp => by
    rw [List.filter_cons] at hp
    split at hp
    · simp only [pairs, List.mem_append, List.mem_map, Prod.mk.injEq] at hp ⊢
      rcases hp with ⟨y', hy', rfl, rfl⟩ | hp
      · exact Or.inl ⟨y', (List.mem_filter.mp hy').1, rfl, rfl⟩
      · exact Or.inr (pairs_filter_sub hp)
    · simp only [pairs, List.mem_append]
      exact Or.inr (pairs_filter_sub hp)

theorem pairs_mem {α : Type} {x y : α} : ∀ {l : List α}, (x, y) ∈ pairs l → x ∈ l ∧ y ∈ l
  | [], hp => by simp [pairs] at hp
  | a :: as, hp => by
    simp only [pairs, List.mem_append, List.mem_map, Prod.mk.injEq] at hp
    rcases hp with ⟨y', hy', rfl, rfl⟩ | hp
    · exact ⟨List.mem_cons_self .., List.mem_cons_of_mem _ hy'⟩
    · obtain ⟨h1, h2⟩ := pairs_mem hp
      exact ⟨List.mem_cons_of_mem _ h1, List.mem_cons_of_mem _ h2⟩

/-- Of two elements paired by `pairs` whose keys are listed without repetition, the second has
not the first's key. -/
theorem pairs_key_ne {α β : Type} (f : α → Option β) : ∀ (l : List α), (l.filterMap f).Nodup →
    ∀ x y, (x, y) ∈ pairs l → ∀ b, f x = some b → f y ≠ some b
  | [], _, x, y, hp, _, _, _ => by simp [pairs] at hp
  | a :: as, hnd, x, y, hp, b, hx, hy => by
    simp only [pairs, List.mem_append, List.mem_map, Prod.mk.injEq] at hp
    rcases hp with ⟨y', hy', rfl, rfl⟩ | hp
    · simp only [List.filterMap_cons, hx] at hnd
      exact (List.nodup_cons.mp hnd).1 (List.mem_filterMap.mpr ⟨y', hy', hy⟩)
    · exact pairs_key_ne f as ((List.Sublist.filterMap f (List.sublist_cons_self a as)).nodup hnd) x y hp b hx hy

/-- A generator's constructor name, if it is a constructor. -/
def genKey : Gen → Option Sym
  | .ctor k => some k.name
  | .inj _ => none

theorem keys_ctor : ∀ F : List CtorSig, (F.map Gen.ctor).filterMap genKey = F.map (·.name)
  | [] => rfl
  | k :: F => by simp only [List.map_cons, List.filterMap_cons, genKey, keys_ctor F]

theorem keys_inj : ∀ S : List Srt, (S.map Gen.inj).filterMap genKey = []
  | [] => rfl
  | a :: S => by simp only [List.map_cons, List.filterMap_cons, genKey, keys_inj S]

theorem pairs_ctor_names (h : HypModelCore c) {N : Srt} {k k' : CtorSig}
    (hp : (Gen.ctor k, Gen.ctor k') ∈ pairs ((c.gens N).filter (!c.isOpenGen ·))) : k.name ≠ k'.name := by
  have hnd : (((c.gens N).filter (!c.isOpenGen ·)).filterMap genKey).Nodup := by
    rw [gensF_eq h N]
    rw [List.filterMap_append, List.filterMap_append, keys_ctor, keys_ctor, keys_inj, List.append_nil]
    have ho : (c.ovlSigs.map (·.name)).Nodup := by
      simpa [Semantics.ovlSigs, Function.comp_def] using h.ovlsOnce
    refine List.nodup_append.mpr ⟨((List.filter_sublist).map _).nodup h.ctorNames,
      ((List.filter_sublist).map _).nodup ho, ?_⟩
    intro a ha b hb hab
    subst hab
    obtain ⟨k1, hk1, rfl⟩ := List.mem_map.mp ha
    obtain ⟨k2, hk2, he⟩ := List.mem_map.mp hb
    obtain ⟨o, hom, rfl⟩ := List.mem_map.mp (List.mem_filter.mp hk2).1
    have h1 := OvlLaws.lookupOvl_none_of_ctor h.ovlHyp (List.mem_filter.mp hk1).1
    rw [← he, OvlLaws.lookupOvl_of_mem h.ovlHyp hom] at h1
    cases h1
  intro he
  exact pairs_key_ne genKey _ hnd _ _ hp k.name rfl (by show some k'.name = some k.name; rw [he])

/-! ## Cons-Dist′, the pairs, Cons-NoJunk -/

section
variable (h : HypModelCore c) {N : Srt} (hN : N ∈ consSorts c)
include h hN

namespace AtT

variable {T : GroundTerm → GroundTerm → Prop}

omit hN in
theorem sat_distLb {a b : Srt} (ha : (a, N) ∈ c.subsorts) (hb : (b, N) ∈ c.subsorts)
    (hab : (c.le a b || c.le b a) = false) :
    stdI_T c T ⊧ᴵ (distLbItem (c.sortName N) (c.sortName a) (c.sortName b) ((c.lowerBounds a b).map c.sortName)).pat := by
  have hn := h.namesK
  obtain ⟨hsa, hsN⟩ := h.subSorts ha
  obtain ⟨hsb, -⟩ := h.subSorts hb
  intro e m
  unfold distLbItem
  dsimp only
  refine guarded_intro fun hgd => ?_
  obtain ⟨v, hv1, hv⟩ := guard_val (T := T) hn hsa (hgd _ (List.mem_cons_self ..))
  obtain ⟨w, hw1, hw⟩ := guard_val (T := T) hn hsb (hgd _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
  rw [interpret_impl]
  intro heq
  rw [KoreAML.interp_equal defOK_std] at heq
  have hx : ∀ m, (Pattern.evar ⟨1⟩ : KoreAML.P).interpret (stdI_T c T) e m ↔ m = .val v := fun m => by
    rw [KoreAML.interp_evar, hv1]
  have hy : ∀ m, (Pattern.evar ⟨2⟩ : KoreAML.P).interpret (stdI_T c T) e m ↔ m = .val w := fun m => by
    rw [KoreAML.interp_evar, hw1]
  have he := heq (.val (injNormal a N v))
  rw [inj_sing' hn hsa hsN hx, inj_sing' hn hsb hsN hy] at he
  obtain ⟨x, u, hxl, hu, hui, rfl, rfl⟩ := inj_inj_eq hab hv hw (Elem.val.inj (he.mp rfl))
  obtain ⟨hsx, -⟩ := h.subSorts (mem_lowerBounds hxl).1
  refine disjList_intro (List.mem_map.mpr ⟨c.sortName x, List.mem_map.mpr ⟨x, hxl, rfl⟩, rfl⟩) ?_
  rw [KoreAML.interp_sExists]
  refine ⟨.val u, ?_, ?_⟩
  · rw [KoreAML.interp_member defOK_std]
    simp only [Function.update_same]
    exact (inhOf_sort hn hsx _ _).mpr hu
  · have hz : ∀ m, (Pattern.evar ⟨3⟩ : KoreAML.P).interpret (stdI_T c T)
        ⟨Function.update e.evalEvar ⟨3⟩ (.val u), e.evalSvar⟩ m ↔ m = .val u := fun m => by
      rw [KoreAML.interp_evar]; simp only [Function.update_same]
    rw [interpret_conj, KoreAML.interp_equal defOK_std, KoreAML.interp_equal defOK_std]
    refine ⟨fun z => ?_, fun z => ?_⟩
    · rw [inj_sing' hn hsx hsa hz, KoreAML.interp_evar, injNormal_of_not hui]
      simp only [upd_ne (show 1 ≠ 3 by decide), hv1]
    · rw [inj_sing' hn hsx hsb hz, KoreAML.interp_evar, injNormal_of_not hui]
      simp only [upd_ne (show 2 ≠ 3 by decide), hw1]

end AtT

omit hN in
theorem sat_distLb {a b : Srt} (ha : (a, N) ∈ c.subsorts) (hb : (b, N) ∈ c.subsorts)
    (hab : (c.le a b || c.le b a) = false) :
    stdI c ⊧ᴵ (distLbItem (c.sortName N) (c.sortName a) (c.sortName b) ((c.lowerBounds a b).map c.sortName)).pat :=
  AtT.sat_distLb (c := c) (T := StepM c) (a := a) (b := b) (ha := ha) (hb := hb) (hab := hab) (h := h)

/-- The argument sorts of the overloads of an overloading generator (as `consItemsK` writes them). -/
def ovlArgsOf (c : Semantics) : Gen → Option (List (List String))
  | .ctor k => if c.isOvl k.name then (c.lookupOvl k.name).map fun o =>
      (c.ovlOver o).map fun kg => kg.args.map c.sortName else none
  | .inj _ => none

/-- What the uncovered guards of `distUncItem` give of a generator's arguments: an overloading
symbol's are covered by none of its overloads. -/
def UncG (c : Semantics) : Gen → List GroundTerm → Prop
  | .ctor k, vs => c.isOvl k.name = true → c.uncovered k.name vs = true
  | .inj _, _ => True

omit hN in
/-- A generator of N that is a constructor or an overloading symbol: its signature is the one its
name finds, of result sort N. -/
theorem gen_known {k : CtorSig} (hg : Gen.ctor k ∈ (c.gens N).filter (!c.isOpenGen ·)) : OvlLaws.KnownSig c k ∧ k.result = N := by
  rcases mem_gensF h hg with ⟨k', hk', hr, he⟩ | ⟨o, ho, hr, he⟩ | ⟨a, -, he⟩
  · cases he
    refine ⟨?_, hr⟩
    unfold OvlLaws.KnownSig
    rw [lookupSig_eq, List.find?_append]
    cases hf : c.ctorSigs.find? (·.name == k.name) with
    | none => exact absurd (List.find?_eq_none.mp hf k hk') (by simp)
    | some k'' =>
      have hm := List.mem_of_find?_eq_some hf
      have hn : k''.name = k.name := by simpa using List.find?_some hf
      rw [inj_of_nodup_map h.ctorNames k'' hm k hk' hn]
      rfl
  · cases he
    exact ⟨(OvlLaws.ovl_facts_ovlF h.ovlHyp.fnFacts (OvlLaws.lookupOvl_of_nodup h.ovlsOnce ho)).2.2.2.2.1, hr⟩
  · cases he

omit hN in
/-- At arguments its uncovered guards accept, a constructor or overloading generator builds its raw
application. -/
theorem genVal_unc {k : CtorSig} (hg : Gen.ctor k ∈ (c.gens N).filter (!c.isOpenGen ·)) {vs : List GroundTerm}
    (hvs : c.sortsOf vs = some k.args) (hu : UncG c (.ctor k) vs) : genVal c N (.ctor k) vs = .ctor k.name vs := by
  rcases mem_gensF h hg with ⟨k', hk', -, he⟩ | ⟨o, ho, -, he⟩ | ⟨a, -, he⟩
  · cases he; exact norm_ctor h hk' vs
  · cases he
    have hlo := OvlLaws.lookupOvl_of_nodup h.ovlsOnce ho
    have hio := h.ovlHyp.fnFacts.isOvl o ho
    exact (OvlLaws.norm_eq_raw_iff_ovlF h.ovlHyp h.ovlHyp.fnFacts hlo hvs
      (OvlLaws.fnCover_none_of_uncovered (hu hio))).mpr (hu hio)
  · cases he

omit hN in
/-- No function overload covers arguments a generator's uncovered guards accept. -/
theorem fnCover_none_of_uncG {g : Gen} {vs : List GroundTerm} (hu : UncG c g vs) :
    ∀ k, g = .ctor k → c.fnCover k.name vs = none := by
  rintro k rfl
  cases hlo : c.lookupOvl k.name with
  | none => exact c.fnCover_of_lookupOvl_none hlo vs
  | some o =>
    obtain ⟨-, -, hio, -⟩ := OvlLaws.ovl_facts_ovlF h.ovlHyp.fnFacts hlo
    exact OvlLaws.fnCover_none_of_uncovered (hu hio)

omit h hN in
/-- A symbol an overloading symbol overloads is a kernel symbol: a constructor, an overloading
symbol or a function. -/
theorem over_kernel {o : OvlSig} {kg : CtorSig} (hkg : kg ∈ c.ovlOver o) : kg ∈ kernelSyms c := by
  cases hb : c.ovlByFn kg with
  | true =>
    obtain ⟨fn, hfn, -, hsig⟩ := OvlLaws.byFn_fn hkg hb
    rw [hsig]
    exact fn_sig_mem (List.mem_append_left _ hfn)
  | false =>
    rcases OvlLaws.knownSig_mem (OvlLaws.known_of_not_byFn hkg hb) with hm | hm
    · exact ctor_kernel hm
    · exact List.mem_append_right _ hm

namespace AtT

variable {T : GroundTerm → GroundTerm → Prop}

omit hN in
/-- The uncovered guard of an overloading generator, in the model: its arguments are covered by
none of its overloads. -/
theorem unc_guard {o : OvlSig} (ho : o ∈ c.ovls) {x : List EVar} {z : EVar} (hz : z ∉ x) {e : Valuation Elem}
    {m : Elem} {vs : List GroundTerm} (hxs : x.map e.evalEvar = vs.map Elem.val)
    (hvs : c.sortsOf vs = some o.sig.args)
    (hg : (KoreAML.Cons.uncoveredP (o.sig.args.map c.sortName) ((c.ovlOver o).map fun kg => kg.args.map c.sortName)
      x z).interpret (stdI_T c T) e m) :
    c.uncovered o.sig.name vs = true := by
  have H := h.ovlHyp
  have hn := h.namesK
  have hlo := OvlLaws.lookupOvl_of_nodup h.ovlsOnce ho
  simp only [Semantics.uncovered, hlo, List.all_eq_true, Bool.not_eq_true']
  intro kg hkg
  cases hcv : c.ovlCovers o.sig kg vs with
  | false => rfl
  | true =>
  exfalso
  obtain ⟨hl, hvl, hli⟩ := OvlLaws.covers_iff.mp hcv
  have hli := OvlLaws.zip3_all_iff.mp hli
  have hxl : x.length = vs.length := by simpa using congrArg List.length hxs
  unfold KoreAML.Cons.uncoveredP at hg
  have hd := conjList_elim (T := T) hg _ (List.mem_map.mpr ⟨kg.args.map c.sortName, List.mem_map_of_mem hkg, rfl⟩)
  obtain ⟨w, hw, hwi⟩ := disjList_mem hd
  obtain ⟨⟨⟨A, B⟩, xi⟩, hmem, hF⟩ := List.mem_filterMap.mp hw
  obtain ⟨i, hi, hie⟩ := List.getElem_of_mem hmem
  simp only [List.length_zip, List.length_map] at hi
  simp only [List.getElem_zip, List.getElem_map, Prod.mk.injEq] at hie
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hie
  dsimp only at hF
  have hkern : kg ∈ kernelSyms c := over_kernel hkg
  have hA := h.symSorts hkern _ (List.mem_cons_of_mem _ (List.getElem_mem (show i < kg.args.length by omega)))
  have hB := h.symSorts (ovl_kernel ho) _ (List.mem_cons_of_mem _ (List.getElem_mem (show i < o.sig.args.length by omega)))
  have hAB : kg.args[i]'(by omega) ≠ o.sig.args[i]'(by omega) := by
    intro he
    rw [he] at hF
    simp at hF
  have hneq : (c.sortName (kg.args[i]'(by omega)) == c.sortName (o.sig.args[i]'(by omega))) = false := by
    rw [beq_eq_false_iff_ne]
    intro he
    exact hAB (hn.2.2 _ (List.mem_range.mpr hA) _ (List.mem_range.mpr hB) he)
  simp only [hneq, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hF
  subst hF
  rw [interpret_neg] at hwi
  apply hwi
  have hvi : (vs[i]'(by omega)) = vs[i]'(by omega) := rfl
  obtain ⟨-, hvi'⟩ := OvlLaws.sortsOf_iff.mp hvs
  have hv := hvi' i (by omega) (by omega)
  have hlies := hli i (by omega) (by omega) (by omega)
  have hex : e.evalEvar (x[i]'(by omega)) = .val (vs[i]'(by omega)) := by
    have := congrArg (·[i]?) hxs
    simp only [List.getElem?_map, List.getElem?_eq_getElem (show i < x.length by omega),
      List.getElem?_eq_getElem (show i < vs.length by omega), Option.map_some, Option.some.injEq] at this
    exact this
  have hu := OvlLaws.sortOf_strip hv hlies
  have hback := OvlLaws.lift_strip hv hlies
  rw [OvlLaws.lift_ne hAB] at hback
  have hxz : x[i]'(by omega) ≠ z := fun he => hz (he ▸ List.getElem_mem _)
  unfold KoreAML.Cons.liesP
  rw [KoreAML.interp_sExists]
  refine ⟨.val (strip (kg.args[i]'(by omega)) (o.sig.args[i]'(by omega)) (vs[i]'(by omega))), ?_, ?_⟩
  · rw [KoreAML.interp_member defOK_std]
    simp only [Function.update_same]
    exact (inhOf_sort hn hA _ _).mpr hu
  · rw [KoreAML.interp_equal defOK_std]
    intro b
    rw [KoreAML.interp_evar, inj_sing hn hA hB (fun m => by
      rw [KoreAML.interp_evar]; simp only [Function.update_same]; exact Iff.rfl) b, hback]
    simp only [Function.update_noteq hxz, hex]

end AtT

omit hN in
/-- The uncovered guard of an overloading generator, in the model: its arguments are covered by
none of its overloads. -/
theorem unc_guard {o : OvlSig} (ho : o ∈ c.ovls) {x : List EVar} {z : EVar} (hz : z ∉ x) {e : Valuation Elem}
    {m : Elem} {vs : List GroundTerm} (hxs : x.map e.evalEvar = vs.map Elem.val)
    (hvs : c.sortsOf vs = some o.sig.args)
    (hg : (KoreAML.Cons.uncoveredP (o.sig.args.map c.sortName) ((c.ovlOver o).map fun kg => kg.args.map c.sortName)
      x z).interpret (stdI c) e m) :
    c.uncovered o.sig.name vs = true :=
  AtT.unc_guard (c := c) (T := StepM c) (o := o) (ho := ho) (x := x) (z := z) (hz := hz) (e := e) (m := m) (vs := vs) (hxs := hxs) (hvs := hvs) (hg := hg) (h := h)

omit h hN in
theorem notMem_xs_z {off n k : Nat} (hk : off + n < k) : (⟨k⟩ : EVar) ∉ KoreAML.Cons.xs off n := by
  intro hm
  obtain ⟨i, hi⟩ := List.getElem?_of_mem hm
  obtain ⟨hin, he⟩ := xs_get hi
  simp only [EVar.mk.injEq] at he
  omega

namespace AtT

variable {T : GroundTerm → GroundTerm → Prop}

theorem sat_distUnc_of {g g' : Gen} (hg : g ∈ (c.gens N).filter (!c.isOpenGen ·)) (hg' : g' ∈ (c.gens N).filter (!c.isOpenGen ·))
    (hne : ∀ vs ws, c.sortsOf vs = some g.argSorts → c.sortsOf ws = some g'.argSorts →
      UncG c g vs → UncG c g' ws → genVal c N g vs ≠ genVal c N g' ws) :
    stdI_T c T ⊧ᴵ (KoreAML.Cons.distUncItem (c.sortName N) (Gen.toK c g) (Gen.toK c g') (ovlArgsOf c g)
      (ovlArgsOf c g')).pat := by
  have hn := h.namesK
  intro e m
  unfold KoreAML.Cons.distUncItem
  dsimp only
  simp only [toK_argSorts]
  refine guarded_intro fun hgd => ?_
  obtain ⟨vs, hxs, hvs⟩ := memGuards_vals (T := T) hn _ g.argSorts (gen_args_numbered h (List.mem_filter.mp hg).1) (by simp [xs_length])
    (fun w hw => hgd w (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hw))))
  obtain ⟨ws, hys, hws⟩ := memGuards_vals (T := T) hn _ g'.argSorts (gen_args_numbered h (List.mem_filter.mp hg').1) (by simp [xs_length])
    (fun w hw => hgd w (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hw))))
  have unc : ∀ (g0 : Gen), g0 ∈ (c.gens N).filter (!c.isOpenGen ·) → ∀ (x : List EVar) (us : List GroundTerm) (z : EVar), z ∉ x →
      x.map e.evalEvar = us.map Elem.val → c.sortsOf us = some g0.argSorts →
      (∀ w ∈ (match ovlArgsOf c g0 with
        | some covs => [KoreAML.Cons.uncoveredP (g0.argSorts.map c.sortName) covs x z]
        | none => []), w.interpret (stdI_T c T) e m) → UncG c g0 us := by
    intro g0 hg0 x us z hz hx hus hw
    cases g0 with
    | inj a => trivial
    | ctor k =>
      intro hio
      rcases mem_gensF h hg0 with ⟨k', hk', -, he⟩ | ⟨o, ho, -, he⟩ | ⟨a, -, he⟩
      · cases he; rw [isOvl_of_ctorSigs hk'] at hio; cases hio
      · cases he
        have hlo := OvlLaws.lookupOvl_of_mem h.ovlHyp ho
        have hov : ovlArgsOf c (.ctor o.sig) = some ((c.ovlOver o).map fun kg => kg.args.map c.sortName) := by
          simp [ovlArgsOf, hio, hlo]
        rw [hov] at hw
        exact unc_guard h ho hz hx hus (hw _ (List.mem_singleton_self _))
      · cases he
  have hu := unc g hg (KoreAML.Cons.xs 0 (g.argSorts.map c.sortName).length) vs
    ⟨(g.argSorts.map c.sortName).length + (g'.argSorts.map c.sortName).length + 1⟩
    (notMem_xs_z (by omega)) hxs hvs
    (fun w hw => hgd w (List.mem_append_left _ (List.mem_append_right _ hw)))
  have hu' := unc g' hg' (KoreAML.Cons.xs (g.argSorts.map c.sortName).length (g'.argSorts.map c.sortName).length) ws
    ⟨(g.argSorts.map c.sortName).length + (g'.argSorts.map c.sortName).length + 1⟩
    (notMem_xs_z (by omega)) hys hws
    (fun w hw => hgd w (List.mem_append_right _ hw))
  rw [KoreAML.interp_notEqual defOK_std]
  intro heq
  have := heq (.val (genVal c N g vs))
  rw [interp_genPat_vars, interp_genPat_vars, hxs, hys, (gs_gen h hN hg hvs (fnCover_none_of_uncG h hu)).1,
    (gs_gen h hN hg' hws (fnCover_none_of_uncG h hu')).1] at this
  exact hne vs ws hvs hws hu hu' (Elem.val.inj (this.mp rfl))

end AtT

theorem sat_distUnc_of {g g' : Gen} (hg : g ∈ (c.gens N).filter (!c.isOpenGen ·)) (hg' : g' ∈ (c.gens N).filter (!c.isOpenGen ·))
    (hne : ∀ vs ws, c.sortsOf vs = some g.argSorts → c.sortsOf ws = some g'.argSorts →
      UncG c g vs → UncG c g' ws → genVal c N g vs ≠ genVal c N g' ws) :
    stdI c ⊧ᴵ (KoreAML.Cons.distUncItem (c.sortName N) (Gen.toK c g) (Gen.toK c g') (ovlArgsOf c g)
      (ovlArgsOf c g')).pat :=
  AtT.sat_distUnc_of (c := c) (T := StepM c) (g := g) (g' := g') (hg := hg) (hg' := hg') (hne := hne) (h := h) (hN := hN)

namespace AtT

variable {T : GroundTerm → GroundTerm → Prop}

theorem sat_pairItem {g g' : Gen} (hp : (g, g') ∈ pairs ((c.gens N).filter (!c.isOpenGen ·))) {it : KoreAML.Item}
    (hit : it ∈ (match g, g' with
      | .inj a, .inj b =>
        if c.le a b || c.le b a then []
        else match c.lowerBounds a b with
          | [] => [KoreAML.Cons.distItem (c.sortName N) (Gen.toK c g) (Gen.toK c g')]
          | lbs => [distLbItem (c.sortName N) (c.sortName a) (c.sortName b) (lbs.map c.sortName)]
      | _, _ =>
        if c.distGuarded g g' then
          [KoreAML.Cons.distUncItem (c.sortName N) (Gen.toK c g) (Gen.toK c g')
            (ovlArgsOf c g) (ovlArgsOf c g')]
        else [KoreAML.Cons.distItem (c.sortName N) (Gen.toK c g) (Gen.toK c g')])) :
    stdI_T c T ⊧ᴵ it.pat := by
  obtain ⟨hg, hg'⟩ := pairs_mem hp
  have hci : ∀ (f : Sym) (b : Srt) (vs ws : List GroundTerm), GroundTerm.ctor f vs ≠ injNormal b N (ws.headD (.ctor 0 [])) :=
    fun f b vs ws he => by have := injNormal_isInj b N (ws.headD (.ctor 0 [])); rw [← he] at this; cases this
  have hctor : ∀ {k : CtorSig}, Gen.ctor k ∈ (c.gens N).filter (!c.isOpenGen ·) → c.isOvl k.name = false → k ∈ c.ctorSigs := by
    intro k hk hio
    rcases mem_gensF h hk with ⟨k', hk', -, he⟩ | ⟨o, ho, -, he⟩ | ⟨a, -, he⟩
    · cases he; exact hk'
    · cases he
      rw [h.ovlHyp.fnFacts.isOvl o ho] at hio
      cases hio
    · cases he
  cases g with
  | ctor k =>
    cases g' with
    | ctor k' =>
      have hkk := gen_known h hg
      have hkk' := gen_known h hg'
      by_cases hdg : c.distGuarded (.ctor k) (.ctor k') = true
      · simp only [hdg, ↓reduceIte, List.mem_singleton] at hit
        rw [hit]
        refine sat_distUnc_of h hN hg hg' fun vs ws hvs hws hu hu' he => ?_
        rw [genVal_unc h hg hvs hu, genVal_unc h hg' hws hu', GroundTerm.ctor.injEq] at he
        exact pairs_ctor_names h hp he.1
      · simp only [hdg, Bool.false_eq_true, ↓reduceIte, List.mem_singleton] at hit
        rw [hit]
        have hfo : c.fnOvl (.ctor k) = false ∧ c.fnOvl (.ctor k') = false := by
          simp only [Semantics.distGuarded, Bool.or_eq_true, not_or, Bool.not_eq_true] at hdg
          exact hdg.1
        refine sat_dist_of h hN hg hg' hfo.1 hfo.2 fun vs ws hvs hws he => ?_
        obtain ⟨A, f, us, hf, hfk⟩ := OvlLaws.norm_head_ovlF h.ovlHyp h.ovlHyp.fnFacts hkk.1 hvs
          (fnCover_none_of_fnOvl_false h hfo.1 vs _ rfl)
        obtain ⟨A', f', us', hf', hfk'⟩ := OvlLaws.norm_head_ovlF h.ovlHyp h.ovlHyp.fnFacts hkk'.1 hws
          (fnCover_none_of_fnOvl_false h hfo.2 ws _ rfl)
        simp only [genVal] at he
        rw [hf, hf', hkk.2, hkk'.2] at he
        obtain ⟨rfl, -⟩ := OvlLaws.lift_ctor_inj he
        simp only [Semantics.distGuarded, hfo.1, hfo.2, Bool.or_self, Bool.false_or] at hdg
        simp only [Bool.and_eq_true, Bool.or_eq_true, List.any_eq_true,
          List.contains_iff_mem, not_and] at hdg
        cases ho : c.isOvl k.name || c.isOvl k'.name with
        | true =>
          simp only [Bool.or_eq_true] at ho
          exact hdg ho ⟨f, hfk, hfk'⟩
        | false =>
          simp only [Bool.or_eq_false_iff] at ho
          have hv := norm_ctor h (hctor hg ho.1) vs
          have hw := norm_ctor h (hctor hg' ho.2) ws
          have e1 : k.name = f := (OvlLaws.lift_ctor_inj (A := k.result) (B := k.result)
            (by rw [OvlLaws.lift_self, ← hv]; exact hf)).1
          have e2 : k'.name = f := (OvlLaws.lift_ctor_inj (A := k'.result) (B := k'.result)
            (by rw [OvlLaws.lift_self, ← hw]; exact hf')).1
          exact pairs_ctor_names h hp (e1.trans e2.symm)
    | inj b =>
      have hkk := gen_known h hg
      by_cases hdg : c.isOvl k.name = true
      · have hdg' : c.distGuarded (.ctor k) (.inj b) = true := by simp [Semantics.distGuarded, hdg]
        simp only [hdg', ↓reduceIte, List.mem_singleton] at hit
        rw [hit]
        refine sat_distUnc_of h hN hg hg' fun vs ws hvs _ hu _ he => ?_
        rw [genVal_unc h hg hvs hu] at he
        exact hci k.name b vs ws he
      · have hdg' : c.distGuarded (.ctor k) (.inj b) = false := by simpa [Semantics.distGuarded] using hdg
        simp only [hdg', Bool.false_eq_true, ↓reduceIte, List.mem_singleton] at hit
        rw [hit]
        refine sat_dist_of h hN hg hg' (fnOvl_ctor_false (by simpa using hdg)) rfl fun vs ws _ _ he => ?_
        simp only [genVal] at he
        rw [norm_ctor h (hctor hg (by simpa using hdg))] at he
        exact hci k.name b vs ws he
  | inj a =>
    cases g' with
    | ctor k' =>
      by_cases hdg : c.isOvl k'.name = true
      · have hdg' : c.distGuarded (.inj a) (.ctor k') = true := by simp [Semantics.distGuarded, hdg]
        simp only [hdg', ↓reduceIte, List.mem_singleton] at hit
        rw [hit]
        refine sat_distUnc_of h hN hg hg' fun vs ws _ hws _ hu' he => ?_
        rw [genVal_unc h hg' hws hu'] at he
        exact hci k'.name a ws vs he.symm
      · have hdg' : c.distGuarded (.inj a) (.ctor k') = false := by simpa [Semantics.distGuarded] using hdg
        simp only [hdg', Bool.false_eq_true, ↓reduceIte, List.mem_singleton] at hit
        rw [hit]
        refine sat_dist_of h hN hg hg' rfl (fnOvl_ctor_false (by simpa using hdg)) fun vs ws _ _ he => ?_
        simp only [genVal] at he
        rw [norm_ctor h (hctor hg' (by simpa using hdg))] at he
        exact hci k'.name a ws vs he.symm
    | inj b =>
      have ha : (a, N) ∈ c.subsorts := by
        rcases mem_gensF h hg with ⟨_, _, _, he⟩ | ⟨_, _, _, he⟩ | ⟨a', ha', he⟩
        · cases he
        · cases he
        · cases he; exact ha'
      have hb : (b, N) ∈ c.subsorts := by
        rcases mem_gensF h hg' with ⟨_, _, _, he⟩ | ⟨_, _, _, he⟩ | ⟨b', hb', he⟩
        · cases he
        · cases he
        · cases he; exact hb'
      dsimp only at hit
      cases hle : (c.le a b || c.le b a) with
      | true => rw [hle] at hit; simp at hit
      | false =>
        rw [hle] at hit
        simp only [Bool.false_eq_true, ↓reduceIte] at hit
        cases hl : c.lowerBounds a b with
        | nil =>
          rw [hl] at hit
          rw [List.mem_singleton.mp hit]
          refine sat_dist_of h hN hg hg' rfl rfl fun vs ws hvs hws he => ?_
          obtain ⟨v, rfl, hv⟩ := sortsOf_single hvs
          obtain ⟨w, rfl, hw⟩ := sortsOf_single hws
          obtain ⟨x, -, hxl, -⟩ := inj_inj_eq hle hv hw he
          rw [hl] at hxl
          exact absurd hxl List.not_mem_nil
        | cons l ls =>
          rw [hl] at hit
          rw [List.mem_singleton.mp hit, ← hl]
          exact sat_distLb h ha hb hle

end AtT

theorem sat_pairItem {g g' : Gen} (hp : (g, g') ∈ pairs ((c.gens N).filter (!c.isOpenGen ·))) {it : KoreAML.Item}
    (hit : it ∈ (match g, g' with
      | .inj a, .inj b =>
        if c.le a b || c.le b a then []
        else match c.lowerBounds a b with
          | [] => [KoreAML.Cons.distItem (c.sortName N) (Gen.toK c g) (Gen.toK c g')]
          | lbs => [distLbItem (c.sortName N) (c.sortName a) (c.sortName b) (lbs.map c.sortName)]
      | _, _ =>
        if c.distGuarded g g' then
          [KoreAML.Cons.distUncItem (c.sortName N) (Gen.toK c g) (Gen.toK c g')
            (ovlArgsOf c g) (ovlArgsOf c g')]
        else [KoreAML.Cons.distItem (c.sortName N) (Gen.toK c g) (Gen.toK c g')])) :
    stdI c ⊧ᴵ it.pat :=
  AtT.sat_pairItem (c := c) (T := StepM c) (g := g) (g' := g') (hp := hp) (it := it) (hit := hit) (h := h) (hN := hN)

omit h hN in
/-- Cons-NoJunk's item is the translation of the text's sentence: the guards of its free variables
imply that the sentence's translation is the whole of the sort N. -/
theorem noJunk_pat (c : Semantics) (N : Srt) :
    (KoreAML.Cons.noJunkItem (c.sortName N) ((c.gens N).map (Gen.toK c))).pat =
      let X := Kore.Pattern.or (KoreAML.srt (c.sortName N))
        (KoreAML.noJunkDisjuncts (c.sortName N) [] ((c.gens N).map (Gen.toK c)))
      (KoreAML.conjList (((KoreAML.freeOf [] X).eraseDups).map (KoreAML.guardOf (KoreAML.tableOf [] X))) ⇒
        (KoreAML.tr ⟨KoreAML.tableOf [] X, []⟩ X ≡ KoreAML.inhOf (KoreAML.Cons.sortP (c.sortName N)))) := rfl

namespace AtT

variable {T : GroundTerm → GroundTerm → Prop}

omit h hN in
theorem genPat_interp (N' : String) (g : KoreAML.Gen) (args : List KoreAML.P) (e : Valuation Elem) (x : Elem) :
    (KoreAML.Cons.genPat N' g args).interpret (stdI_T c T) e x ↔
      ∃ bs, All2 (fun φ b => φ.interpret (stdI_T c T) e b) args bs ∧ GS (stdI_T c T) N' g bs x := by
  rw [genPat_eq, interp_appList]
  constructor
  · rintro ⟨a, ha, bs, hbs, hx⟩
    exact ⟨bs, hbs, a, ((genHead_closed N' g).interp e KoreAML.val0 a).mp ha, hx⟩
  · rintro ⟨bs, hbs, a, ha, hx⟩
    exact ⟨a, ((genHead_closed N' g).interp e KoreAML.val0 a).mpr ha, bs, hbs, hx⟩

end AtT

omit h hN in
theorem genPat_interp (N' : String) (g : KoreAML.Gen) (args : List KoreAML.P) (e : Valuation Elem) (x : Elem) :
    (KoreAML.Cons.genPat N' g args).interpret (stdI c) e x ↔
      ∃ bs, All2 (fun φ b => φ.interpret (stdI c) e b) args bs ∧ GS (stdI c) N' g bs x :=
  AtT.genPat_interp (c := c) (T := StepM c) (N' := N') (g := g) (args := args) (e := e) (x := x)

end

/-! ## The no-junk sentence's binders and disjuncts -/

/-- A name `noJunkName` gives from the base `b`: `b`, or `b` followed by `V` and a number. -/
def NameFrom (n b : String) : Prop := n = b ∨ ∃ j : Nat, n = b ++ "V" ++ toString j

theorem noJunkName_from (seen : List (String × List String)) (b s : String) :
    NameFrom (KoreAML.noJunkName seen b s).1 b := by
  unfold KoreAML.noJunkName
  dsimp only
  split
  · split
    · exact Or.inl rfl
    · exact Or.inr ⟨_, rfl⟩
  · split
    · exact Or.inl rfl
    · exact Or.inr ⟨_, rfl⟩

theorem noJunkVars_shape : ∀ (seen : List (String × List String)) (l : List (String × String)),
    (KoreAML.noJunkVars seen l).1.map (·.sort) = l.map (KoreAML.srt ∘ Prod.snd) ∧
      All2 (fun (x : Kore.EVar) (p : String × String) => NameFrom x.var.ident.name p.1) (KoreAML.noJunkVars seen l).1 l
  | _, [] => ⟨rfl, .nil⟩
  | seen, (b, s) :: l => by
    have ih := noJunkVars_shape (KoreAML.noJunkName seen b s).2 l
    refine ⟨?_, ?_⟩
    · show KoreAML.srt s :: (KoreAML.noJunkVars (KoreAML.noJunkName seen b s).2 l).1.map (·.sort) = _
      rw [ih.1]; rfl
    · exact .cons (noJunkName_from seen b s) ih.2

theorem digits_prefix : ∀ (l₁ l₂ r₁ r₂ : List Char), (∀ ch ∈ l₁, ch.isDigit = true) → (∀ ch ∈ l₂, ch.isDigit = true) →
    (∀ ch ∈ r₁.head?, ch.isDigit = false) → (∀ ch ∈ r₂.head?, ch.isDigit = false) → l₁ ++ r₁ = l₂ ++ r₂ → l₁ = l₂
  | [], [], _, _, _, _, _, _, _ => rfl
  | [], d :: _, r₁, _, _, h₂, hr₁, _, he => by
    simp only [List.nil_append, List.cons_append] at he
    subst he
    have := hr₁ d rfl
    rw [h₂ d (List.mem_cons_self ..)] at this
    cases this
  | d :: _, [], _, r₂, h₁, _, _, hr₂, he => by
    simp only [List.nil_append, List.cons_append] at he
    subst he
    have := hr₂ d rfl
    rw [h₁ d (List.mem_cons_self ..)] at this
    cases this
  | a :: l₁, b :: l₂, r₁, r₂, h₁, h₂, hr₁, hr₂, he => by
    simp only [List.cons_append, List.cons.injEq] at he
    obtain ⟨rfl, he⟩ := he
    rw [digits_prefix l₁ l₂ r₁ r₂ (fun ch h => h₁ ch (List.mem_cons_of_mem _ h))
      (fun ch h => h₂ ch (List.mem_cons_of_mem _ h)) hr₁ hr₂ he]

theorem toString_toList (i : Nat) : (toString i).toList = Nat.toDigits 10 i := by
  show (Nat.repr i).toList = _
  simp only [Nat.repr_eq_ofList_toDigits, String.toList_ofList]

theorem nameFrom_tail {n b : String} (h : NameFrom n b) : ∃ r : List Char, n.toList = b.toList ++ r ∧
    ∀ ch ∈ r.head?, ch.isDigit = false := by
  rcases h with rfl | ⟨j, rfl⟩
  · exact ⟨[], by simp, fun _ h => by simp at h⟩
  · refine ⟨('V' :: (toString j).toList), by simp [String.toList_append], fun ch h => ?_⟩
    simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at h
    subst h; rfl

theorem nameFrom_inj {n : String} {i j : Nat} (hi : NameFrom n ("X" ++ toString i)) (hj : NameFrom n ("X" ++ toString j)) :
    i = j := by
  obtain ⟨r, hr, hr'⟩ := nameFrom_tail hi
  obtain ⟨q, hq, hq'⟩ := nameFrom_tail hj
  rw [hr] at hq
  simp only [String.toList_append, toString_toList] at hq
  have hd : ∀ k : Nat, ∀ ch ∈ Nat.toDigits 10 k, ch.isDigit = true := fun _ _ h =>
    Nat.isDigit_of_mem_toDigits (by decide) (by decide) h
  have := digits_prefix _ _ _ _ (hd i) (hd j) hr' hq'
    (List.append_cancel_left (by simpa only [List.append_assoc] using hq))
  exact toString_inj (by rw [← String.toList_inj, toString_toList, toString_toList, this])

theorem all2_nodup {α β γ δ : Type} {R : α → β → Prop} {f : α → γ} {g : β → δ}
    (hR : ∀ x p y q, R x p → R y q → f x = f y → g p = g q) :
    ∀ {xs : List α} {l : List β}, All2 R xs l → (l.map g).Nodup → (xs.map f).Nodup
  | _, _, .nil, _ => List.nodup_nil
  | _, _, .cons (a := x) (b := p) hxp hs, hn => by
    rw [List.map_cons, List.nodup_cons] at hn ⊢
    refine ⟨fun hm => ?_, all2_nodup hR hs hn.2⟩
    obtain ⟨y, hy, hfy⟩ := List.mem_map.mp hm
    obtain ⟨q, hq, hyq⟩ := all2_mem hs hy
    exact hn.1 (List.mem_map.mpr ⟨q, hq, (hR x p y q hxp hyq hfy.symm).symm⟩)
where
  all2_mem {xs : List α} {l : List β} : All2 R xs l → ∀ {y}, y ∈ xs → ∃ q ∈ l, R y q
    | .nil, _, h => absurd h List.not_mem_nil
    | .cons h hs, _, hy => by
      rcases List.mem_cons.mp hy with rfl | hy
      · exact ⟨_, List.mem_cons_self .., h⟩
      · obtain ⟨q, hq, h'⟩ := all2_mem hs hy
        exact ⟨q, List.mem_cons_of_mem _ hq, h'⟩

/-- The binders of a constructor's disjunct have distinct keys. -/
theorem ctorBinders_nodup (seen : List (String × List String)) (args : List String) :
    ((KoreAML.noJunkVars seen ((List.range args.length).map (fun i => "X" ++ toString i) |>.zip args)).1.map
      KoreAML.evarKey).Nodup := by
  let bases := (List.range args.length).map (fun i => "X" ++ toString i)
  have hb : ∀ p ∈ bases.zip args, ∃ i : Nat, p.1 = "X" ++ toString i := fun p hp =>
    let ⟨i, _, h⟩ := List.mem_map.mp (List.of_mem_zip hp).1
    ⟨i, h.symm⟩
  have hsh := (noJunkVars_shape seen (bases.zip args)).2
  -- restrict the relation to the bases' pairs
  have hR : All2 (fun (x : Kore.EVar) (p : String × String) => NameFrom x.var.ident.name p.1 ∧ ∃ i : Nat, p.1 = "X" ++ toString i)
      (KoreAML.noJunkVars seen (bases.zip args)).1 (bases.zip args) := by
    clear_value bases
    revert hb hsh
    generalize (KoreAML.noJunkVars seen (bases.zip args)).1 = xs
    generalize bases.zip args = l
    intro hb hsh
    induction hsh with
    | nil => exact .nil
    | cons h hs ih => exact .cons ⟨h, hb _ (List.mem_cons_self ..)⟩ (ih fun p hp => hb p (List.mem_cons_of_mem _ hp))
  refine all2_nodup (g := Prod.fst) (fun x p y q hx hy hk => ?_) hR ?_
  · obtain ⟨hx, i, hi⟩ := hx
    obtain ⟨hy, j, hj⟩ := hy
    simp only [KoreAML.evarKey, KoreAML.VarKey.evar.injEq] at hk
    rw [hi] at hx; rw [hj] at hy; rw [hk.1] at hx
    rw [hi, hj, nameFrom_inj hx hy]
  · rw [List.map_fst_zip (by simp [bases])]
    exact nodup_map_range _ _ fun i j _ _ h => xName_inj h

/-- The disjunct of a generator in the no-junk sentence: binders at the generator's argument sorts,
with distinct keys, around the generator applied to them. -/
theorem noJunkDisjuncts_gen (N : String) : ∀ (seen : List (String × List String)) (gs : List KoreAML.Gen)
    (g : KoreAML.Gen), g ∈ gs →
    ∃ (bs : List Kore.EVar) (body : Kore.Pattern),
      KoreAML.existsAll (KoreAML.srt N) bs body ∈ KoreAML.noJunkDisjuncts N seen gs ∧
      bs.map (·.sort) = g.argSorts.map KoreAML.srt ∧ (bs.map KoreAML.evarKey).Nodup ∧
      ∀ t : KoreAML.VarTable, KoreAML.tr ⟨t, []⟩ body =
        KoreAML.Cons.genPat N g (bs.map fun b => .evar (t.ev (KoreAML.evarKey b)))
  | _, [], _, h => absurd h List.not_mem_nil
  | seen, g' :: gs, g, hg => by
    rcases List.mem_cons.mp hg with rfl | hg'
    · cases g with
      | ctor k =>
        refine ⟨(KoreAML.noJunkVars seen (((List.range k.args.length).map (fun i => "X" ++ toString i)).zip k.args)).1,
          KoreAML.ap k.name (KoreAML.vars (KoreAML.noJunkVars seen
            (((List.range k.args.length).map (fun i => "X" ++ toString i)).zip k.args)).1),
          List.mem_cons_self .., ?_, ctorBinders_nodup seen k.args, fun t => ?_⟩
        · rw [(noJunkVars_shape seen _).1, ← List.map_map, List.map_snd_zip (by simp)]; rfl
        · rw [KoreAML.ap, KoreAML.tr_app0, trArgs_appList]
          simp only [KoreAML.vars, List.map_map]
          rfl
      | inj a =>
        refine ⟨[KoreAML.evar (KoreAML.noJunkName seen "Val" a).1 (KoreAML.srt a)],
          KoreAML.injP a N (.var (.evar (KoreAML.evar (KoreAML.noJunkName seen "Val" a).1 (KoreAML.srt a)))),
          List.mem_cons_self .., rfl, by simp, fun t => ?_⟩
        rw [KoreAML.tr_injP]; rfl
    · cases g' with
      | ctor k =>
        obtain ⟨bs, body, hm, hr⟩ := noJunkDisjuncts_gen N _ gs g hg'
        exact ⟨bs, body, List.mem_cons_of_mem _ hm, hr⟩
      | inj a =>
        obtain ⟨bs, body, hm, hr⟩ := noJunkDisjuncts_gen N _ gs g hg'
        exact ⟨bs, body, List.mem_cons_of_mem _ hm, hr⟩

theorem noJunkDisjuncts_ne_nil (N : String) (seen : List (String × List String)) :
    ∀ gs : List KoreAML.Gen, KoreAML.noJunkDisjuncts N seen gs ≠ []
  | [] => by simp [KoreAML.noJunkDisjuncts]
  | .ctor _ :: _ => by simp [KoreAML.noJunkDisjuncts]
  | .inj _ :: _ => by simp [KoreAML.noJunkDisjuncts]

theorem varsOf_existsAll' {S : Kore.KSort} {body : Kore.Pattern} : ∀ {bs : List Kore.EVar} {b : Kore.EVar}, b ∈ bs →
    KoreAML.evarKey b ∈ KoreAML.varsOf (KoreAML.existsAll S bs body)
  | b' :: bs, b, hb => by
    show KoreAML.evarKey b ∈ KoreAML.varsOf (.exist S b' (KoreAML.existsAll S bs body))
    rw [KoreAML.varsOf]
    rcases List.mem_cons.mp hb with rfl | hb
    · exact List.mem_append_left _ (List.mem_append_right _ (List.mem_singleton_self _))
    · exact List.mem_append_right _ (varsOf_existsAll' hb)

theorem nodup_map_of_injOn {α β : Type} (f : α → β) : ∀ {l : List α}, (∀ x ∈ l, ∀ y ∈ l, f x = f y → x = y) →
    l.Nodup → (l.map f).Nodup
  | [], _, _ => List.nodup_nil
  | x :: l, hi, hn => by
    rw [List.nodup_cons] at hn
    rw [List.map_cons, List.nodup_cons]
    refine ⟨fun hm => ?_, nodup_map_of_injOn f (fun a ha b hb => hi a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb)) hn.2⟩
    obtain ⟨y, hy, he⟩ := List.mem_map.mp hm
    exact hn.1 (hi y (List.mem_cons_of_mem _ hy) x (List.mem_cons_self ..) he ▸ hy)

/-- A valuation updated at `xs`, in order, with `as`. -/
def updAll (e : Valuation Elem) : List EVar → List Elem → Valuation Elem
  | x :: xs, a :: as => updAll ⟨Function.update e.evalEvar x a, e.evalSvar⟩ xs as
  | _, _ => e

theorem updAll_off : ∀ (xs : List EVar) (as : List Elem) (e : Valuation Elem) (x : EVar), x ∉ xs →
    (updAll e xs as).evalEvar x = e.evalEvar x
  | [], _, _, _, _ => rfl
  | _ :: _, [], _, _, _ => rfl
  | y :: xs, a :: as, e, x, hx => by
    rw [updAll, updAll_off xs as _ x (fun h => hx (List.mem_cons_of_mem _ h))]
    exact Function.update_noteq (fun h => hx (by subst h; exact List.mem_cons_self ..)) _ _

namespace AtT

variable {T : GroundTerm → GroundTerm → Prop}

theorem updAll_at : ∀ (xs : List EVar) (as : List Elem) (e : Valuation Elem), xs.Nodup → xs.length = as.length →
    All2 (fun x a => (Pattern.evar x : KoreAML.P).interpret (stdI_T c T) (updAll e xs as) a) xs as
  | [], [], _, _, _ => .nil
  | [], _ :: _, _, _, h => by simp at h
  | _ :: _, [], _, _, h => by simp at h
  | x :: xs, a :: as, e, hn, hl => by
    rw [List.nodup_cons] at hn
    refine .cons ?_ (updAll_at xs as _ hn.2 (by simpa using hl))
    show a = (updAll _ xs as).evalEvar x
    rw [updAll_off xs as _ x hn.1]; simp

end AtT

theorem updAll_at : ∀ (xs : List EVar) (as : List Elem) (e : Valuation Elem), xs.Nodup → xs.length = as.length →
    All2 (fun x a => (Pattern.evar x : KoreAML.P).interpret (stdI c) (updAll e xs as) a) xs as :=
  AtT.updAll_at (c := c) (T := StepM c)

theorem all2_map_left {α β γ : Type} {R : α → β → Prop} {f : γ → α} : ∀ {l : List γ} {bs : List β},
    All2 (fun x b => R (f x) b) l bs → All2 R (l.map f) bs
  | _, _, .nil => .nil
  | _, _, .cons h hs => .cons h (all2_map_left hs)

namespace AtT

variable {T : GroundTerm → GroundTerm → Prop}

/-- `∃b̄. body` holds where body holds at the valuation updated at the binders with elements of their sorts. -/
theorem existsAll_upd (hn : NamesApartK c) (t : KoreAML.VarTable) (S : Kore.KSort) (body : Kore.Pattern) :
    ∀ {bs : List Kore.EVar} {as : List Elem} (e : Valuation Elem) (m : Elem),
    All2 (fun (b : Kore.EVar) a => ∃ s, s < nRegSorts + c.sortNames.length ∧ b.sort = KoreAML.srt (c.sortName s) ∧ InSort c s a) bs as →
    (KoreAML.tr ⟨t, []⟩ body).interpret (stdI_T c T) (updAll e (bs.map fun b => t.ev (KoreAML.evarKey b)) as) m →
    (KoreAML.tr ⟨t, []⟩ (KoreAML.existsAll S bs body)).interpret (stdI_T c T) e m
  | _, _, _, _, .nil, hb => hb
  | b :: bs, a :: as, e, m, .cons ⟨s, hs, hbs, ha⟩ hrest, hb => by
    show (KoreAML.tr ⟨t, []⟩ (.exist S b (KoreAML.existsAll S bs body))).interpret (stdI_T c T) e m
    rw [KoreAML.tr, KoreAML.interp_sExists]
    refine ⟨a, ?_, existsAll_upd hn t S body _ m hrest hb⟩
    rw [KoreAML.interp_member defOK_std]
    simp only [Function.update_same]
    rw [hbs, trSort_srt]
    exact (inhOf_sort hn hs _ _).mpr ha

end AtT

/-- `∃b̄. body` holds where body holds at the valuation updated at the binders with elements of their sorts. -/
theorem existsAll_upd (hn : NamesApartK c) (t : KoreAML.VarTable) (S : Kore.KSort) (body : Kore.Pattern) :
    ∀ {bs : List Kore.EVar} {as : List Elem} (e : Valuation Elem) (m : Elem),
    All2 (fun (b : Kore.EVar) a => ∃ s, s < nRegSorts + c.sortNames.length ∧ b.sort = KoreAML.srt (c.sortName s) ∧ InSort c s a) bs as →
    (KoreAML.tr ⟨t, []⟩ body).interpret (stdI c) (updAll e (bs.map fun b => t.ev (KoreAML.evarKey b)) as) m →
    (KoreAML.tr ⟨t, []⟩ (KoreAML.existsAll S bs body)).interpret (stdI c) e m :=
  AtT.existsAll_upd (c := c) (T := StepM c) (hn := hn) (t := t) (S := S) (body := body)

theorem guards_of (hn : NamesApartK c) : ∀ {bs : List Kore.EVar} {ss : List Srt} {vs : List GroundTerm},
    bs.map (·.sort) = (ss.map c.sortName).map KoreAML.srt → c.sortsOf vs = some ss →
    (∀ s ∈ ss, s < nRegSorts + c.sortNames.length) →
    All2 (fun (b : Kore.EVar) a => ∃ s, s < nRegSorts + c.sortNames.length ∧ b.sort = KoreAML.srt (c.sortName s) ∧ InSort c s a)
      bs (vs.map Elem.val)
  | [], [], vs, _, hvs, _ => by rw [sortsOf_nil_eq hvs]; exact .nil
  | [], _ :: _, _, h, _, _ => by simp at h
  | _ :: _, [], _, h, _, _ => by simp at h
  | b :: bs, s :: ss, [], _, hvs, _ => by rw [sortsOf_nil] at hvs; cases hvs
  | b :: bs, s :: ss, v :: vs, hb, hvs, hs => by
    obtain ⟨s', ss', hv, hvs', he⟩ := sortsOf_cons.mp hvs
    simp only [List.cons.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    simp only [List.map_cons, List.cons.injEq] at hb
    exact .cons ⟨s, hs s (List.mem_cons_self ..), hb.1, hv⟩
      (guards_of hn hb.2 hvs' (fun s' h' => hs s' (List.mem_cons_of_mem _ h')))

namespace AtT

variable {T : GroundTerm → GroundTerm → Prop}

theorem trOrList_intro {ctx : KoreAML.Ctx} {s : KoreAML.P} {e : Valuation Elem} {m : Elem}
    (hs : (KoreAML.inhOf s).interpret (stdI_T c T) e m) :
    ∀ {ps : List Kore.Pattern} {p : Kore.Pattern}, p ∈ ps → (KoreAML.tr ctx p).interpret (stdI_T c T) e m →
      (KoreAML.trOrList ctx s ps).interpret (stdI_T c T) e m
  | [_], _, hp, h => by rw [List.mem_singleton.mp hp] at h; rw [KoreAML.trOrList]; exact h
  | q :: q' :: ps, p, hp, h => by
    rw [KoreAML.trOrList, KoreAML.interp_sOr]
    refine ⟨hs, ?_⟩
    rcases List.mem_cons.mp hp with rfl | hp
    · exact Or.inl h
    · exact Or.inr (trOrList_intro hs hp h)

end AtT

theorem trOrList_intro {ctx : KoreAML.Ctx} {s : KoreAML.P} {e : Valuation Elem} {m : Elem}
    (hs : (KoreAML.inhOf s).interpret (stdI c) e m) :
    ∀ {ps : List Kore.Pattern} {p : Kore.Pattern}, p ∈ ps → (KoreAML.tr ctx p).interpret (stdI c) e m →
      (KoreAML.trOrList ctx s ps).interpret (stdI c) e m :=
  AtT.trOrList_intro (c := c) (T := StepM c) (ctx := ctx) (s := s) (e := e) (m := m) (hs := hs)

namespace AtT

variable {T : GroundTerm → GroundTerm → Prop}

theorem trOr_noJunk_inh {ctx : KoreAML.Ctx} {N : String} {seen : List (String × List String)}
    {gs : List KoreAML.Gen} {e : Valuation Elem} {m : Elem}
    (h : (KoreAML.trOrList ctx (KoreAML.trSort ctx.vars (KoreAML.srt N)) (KoreAML.noJunkDisjuncts N seen gs)).interpret (stdI_T c T) e m) :
    (KoreAML.inhOf (KoreAML.trSort ctx.vars (KoreAML.srt N))).interpret (stdI_T c T) e m := by
  cases gs with
  | nil =>
    simp only [KoreAML.noJunkDisjuncts, KoreAML.trOrList, KoreAML.tr] at h
    unfold KoreAML.sBot at h
    exact (KoreAML.interp_sNot.mp h).2
  | cons g gs =>
    have hne := noJunkDisjuncts_ne_nil N seen (g :: gs)
    obtain ⟨d, rest, hdr⟩ : ∃ d rest, KoreAML.noJunkDisjuncts N seen (g :: gs) = d :: rest :=
      match KoreAML.noJunkDisjuncts N seen (g :: gs), hne with
      | d :: rest, _ => ⟨d, rest, rfl⟩
    have hrest : rest ≠ [] := by
      cases g with
      | ctor k =>
        simp only [KoreAML.noJunkDisjuncts, List.cons.injEq] at hdr
        rw [← hdr.2]; exact noJunkDisjuncts_ne_nil _ _ _
      | inj a =>
        simp only [KoreAML.noJunkDisjuncts, List.cons.injEq] at hdr
        rw [← hdr.2]; exact noJunkDisjuncts_ne_nil _ _ _
    obtain ⟨d', rest', rfl⟩ : ∃ d' rest', rest = d' :: rest' :=
      match rest, hrest with
      | d' :: rest', _ => ⟨d', rest', rfl⟩
    rw [hdr, KoreAML.trOrList] at h
    exact (KoreAML.interp_sOr.mp h).1

end AtT

theorem trOr_noJunk_inh {ctx : KoreAML.Ctx} {N : String} {seen : List (String × List String)}
    {gs : List KoreAML.Gen} {e : Valuation Elem} {m : Elem}
    (h : (KoreAML.trOrList ctx (KoreAML.trSort ctx.vars (KoreAML.srt N)) (KoreAML.noJunkDisjuncts N seen gs)).interpret (stdI c) e m) :
    (KoreAML.inhOf (KoreAML.trSort ctx.vars (KoreAML.srt N))).interpret (stdI c) e m :=
  AtT.trOr_noJunk_inh (c := c) (T := StepM c) (ctx := ctx) (N := N) (seen := seen) (gs := gs) (e := e) (m := m) (h := h)

section
variable (h : HypModelCore c) {N : Srt} (hN : N ∈ consSorts c)
include h hN

namespace AtT

variable {T : GroundTerm → GroundTerm → Prop}

/-- The text's no-junk sentence of N, read in the value model, holds of N's values and nothing else. -/
theorem noJunk_sentence (e : Valuation Elem) (a : Elem) :
    (KoreAML.tr ⟨KoreAML.tableOf [] (KoreAML.Cons.noJunkAx (c.sortName N) ((c.gens N).map (Gen.toK c))).pattern, []⟩
        (KoreAML.Cons.noJunkAx (c.sortName N) ((c.gens N).map (Gen.toK c))).pattern).interpret (stdI_T c T) e a ↔
      InSort c N a := by
  have hn := h.namesK
  have hNn := consSorts_numbered h hN
  let X := (KoreAML.Cons.noJunkAx (c.sortName N) ((c.gens N).map (Gen.toK c))).pattern
  let t := KoreAML.tableOf [] X
  have hinh : ∀ e' a', (KoreAML.inhOf (KoreAML.trSort t (KoreAML.srt (c.sortName N)))).interpret (stdI_T c T) e' a' ↔ InSort c N a' :=
    fun e' a' => by rw [trSort_srt]; exact inhOf_sort hn hNn e' a'
  show (KoreAML.tr ⟨t, []⟩ (.or (KoreAML.srt (c.sortName N)) _)).interpret (stdI_T c T) e a ↔ _
  rw [KoreAML.tr]
  constructor
  · intro ha
    exact (hinh e a).mp (trOr_noJunk_inh (ctx := ⟨t, []⟩) ha)
  · intro ha
    obtain ⟨w, rfl, hw⟩ := inSort_val ha
    have hgen : ∃ g ∈ c.gens N, ∃ vs, c.sortsOf vs = some g.argSorts ∧
        GS (stdI_T c T) (c.sortName N) (Gen.toK c g) (vs.map Elem.val) (.val w) := by
      have hF : ∀ g ∈ (c.gens N).filter (!c.isOpenGen ·), ∀ vs, c.sortsOf vs = some g.argSorts →
          (∀ k, g = .ctor k → c.fnCover k.name vs = none) →
          genVal c N g vs = w → ∃ g ∈ c.gens N, ∃ vs, c.sortsOf vs = some g.argSorts ∧
            GS (stdI_T c T) (c.sortName N) (Gen.toK c g) (vs.map Elem.val) (.val w) :=
        fun g hg vs hvs hnc he => ⟨g, (List.mem_filter.mp hg).1, vs, hvs,
          ((gs_gen (T := T) h hN hg hvs hnc).1 _).mpr (by rw [he])⟩
      rcases consSort_shape h.genWf hN hw with ⟨f, ws, rfl⟩ | ⟨a, b, w0, rfl⟩
      · rcases c.sortOf_ctor_iff.mp hw with ⟨k, hk, hws, rfl⟩ | ⟨-, o, hlo, hws, hu, rfl⟩ | ⟨-, -, kp, hko, hws, hkr, rfl⟩
        rotate_right
        · obtain ⟨hkp, hraw, -, -⟩ := c.lookupOpen_spec hko
          exact ⟨.ctor kp.sig, gens_open hkp hraw, ws, hws, gs_open h hko hws hkr hw _⟩
        · obtain ⟨hkm, rfl⟩ := lookupSig_spec hk
          exact hF _ (gensF_ctor h.genWf hkm) ws hws
            (fnCover_none_of_fnOvl_false h (fnOvl_ctor_false (isOvl_of_ctorSigs hkm)) ws) (norm_ctor h hkm ws)
        · have hom : o ∈ c.ovls := List.mem_of_find?_eq_some hlo
          obtain ⟨-, hon, -⟩ := OvlLaws.ovl_facts_ovlF h.ovlHyp.fnFacts hlo
          refine hF _ (gensF_of_ovl h.genWf hom) ws hws
            (fun k hk => by cases hk; rw [hon]; exact OvlLaws.fnCover_none_of_uncovered hu) ?_
          show c.norm o.sig.name ws = _
          rw [hon]
          exact OvlLaws.norm_fixed_ovlF h.ovlHyp h.ovlHyp.fnFacts hlo hw
      · obtain ⟨hab, hni, hw0, rfl⟩ := sortOf_inj.mp hw
        exact hF _ (gensF_inj hab) [w0] (sortsOf_cons.mpr ⟨a, [], hw0, sortsOf_nil, rfl⟩) (fun k hk => by cases hk)
          (by simp [genVal, injNormal_of_not hni])
    obtain ⟨g, hg, vs, hvs, hgs⟩ := hgen
    obtain ⟨bs, body, hm, hsorts, hnd, htr⟩ := noJunkDisjuncts_gen (c.sortName N) [] ((c.gens N).map (Gen.toK c))
      (Gen.toK c g) (List.mem_map.mpr ⟨g, hg, rfl⟩)
    refine trOrList_intro ((hinh e _).mpr ha) hm ?_
    rw [toK_argSorts] at hsorts
    have hgd := guards_of hn hsorts hvs (gen_args_numbered h hg)
    refine existsAll_upd hn t _ body e _ hgd ?_
    rw [htr, genPat_interp]
    refine ⟨vs.map Elem.val, ?_, hgs⟩
    -- the binders' indices are distinct: their keys are, and all lie in the table
    have hkt : ∀ b ∈ bs, KoreAML.evarKey b ∈ t := fun b hb =>
      List.mem_eraseDups.mpr (List.mem_append_right _ (by
        show KoreAML.evarKey b ∈ KoreAML.varsOf (.or _ _)
        rw [KoreAML.varsOf]
        exact List.mem_append_right _ (mem_varsOfList hm (varsOf_existsAll' hb))))
    have hidx : (bs.map fun b => t.ev (KoreAML.evarKey b)).Nodup := by
      rw [show (bs.map fun b => t.ev (KoreAML.evarKey b)) = (bs.map KoreAML.evarKey).map t.ev by rw [List.map_map]; rfl]
      refine nodup_map_of_injOn t.ev (fun k hk k' hk' he => ?_) hnd
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hk
      obtain ⟨b', hb', rfl⟩ := List.mem_map.mp hk'
      exact ev_inj (hkt b hb) (hkt b' hb') he
    have := updAll_at (T := T) (c := c) _ (vs.map Elem.val) e hidx (by rw [List.length_map, hgd.length])
    have h2 := all2_map_left_inv (R := fun x a => (Pattern.evar x : KoreAML.P).interpret (stdI_T c T) _ a)
      (f := fun b => t.ev (KoreAML.evarKey b)) this
    refine all2_map_left ?_
    exact h2
where
  all2_map_left_inv {α β γ : Type} {R : α → β → Prop} {f : γ → α} : ∀ {l : List γ} {bs : List β},
      All2 R (l.map f) bs → All2 (fun x b => R (f x) b) l bs
    | [], [], _ => .nil
    | [], _ :: _, hb => by cases hb
    | _ :: _, [], hb => by cases hb
    | _ :: _, _ :: _, .cons h hs => .cons h (all2_map_left_inv hs)

end AtT

/-- The text's no-junk sentence of N, read in the value model, holds of N's values and nothing else. -/
theorem noJunk_sentence (e : Valuation Elem) (a : Elem) :
    (KoreAML.tr ⟨KoreAML.tableOf [] (KoreAML.Cons.noJunkAx (c.sortName N) ((c.gens N).map (Gen.toK c))).pattern, []⟩
        (KoreAML.Cons.noJunkAx (c.sortName N) ((c.gens N).map (Gen.toK c))).pattern).interpret (stdI c) e a ↔
      InSort c N a :=
  AtT.noJunk_sentence (c := c) (T := StepM c) (e := e) (a := a) (h := h) (hN := hN)
where
  all2_map_left_inv {α β γ : Type} {R : α → β → Prop} {f : γ → α} : ∀ {l : List γ} {bs : List β},
      All2 R (l.map f) bs → All2 (fun x b => R (f x) b) l bs
    | [], [], _ => .nil
    | [], _ :: _, hb => by cases hb
    | _ :: _, [], hb => by cases hb
    | _ :: _, _ :: _, .cons h hs => .cons h (all2_map_left_inv hs)

namespace AtT

variable {T : GroundTerm → GroundTerm → Prop}

theorem sat_noJunk : stdI_T c T ⊧ᴵ (KoreAML.Cons.noJunkItem (c.sortName N) ((c.gens N).map (Gen.toK c))).pat := by
  have hn := h.namesK
  have hNn := consSorts_numbered h hN
  intro e m
  rw [noJunk_pat]
  dsimp only
  rw [interpret_impl]
  intro _
  rw [KoreAML.interp_equal defOK_std]
  intro a
  refine (noJunk_sentence h hN e a).trans ?_
  unfold KoreAML.Cons.sortP
  exact (inhOf_sort hn hNn e a).symm

end AtT

theorem sat_noJunk : stdI c ⊧ᴵ (KoreAML.Cons.noJunkItem (c.sortName N) ((c.gens N).map (Gen.toK c))).pat :=
  AtT.sat_noJunk (c := c) (T := StepM c) (h := h) (hN := hN)

end

/-! ## Cons-Coh -/

namespace AtT

variable {T : GroundTerm → GroundTerm → Prop}

theorem sat_coh (h : HypModelCore c) {a b d : Srt} (hab : (a, b) ∈ c.subsorts) (hbd : (b, d) ∈ c.subsorts) :
    stdI_T c T ⊧ᴵ (KoreAML.Cons.cohItem (c.sortName a) (c.sortName b) (c.sortName d)).pat := by
  have hn := h.namesK
  obtain ⟨hsa, hsb⟩ := h.subSorts hab
  obtain ⟨-, hsd⟩ := h.subSorts hbd
  intro e m
  unfold KoreAML.Cons.cohItem
  dsimp only
  refine guarded_intro fun hgd => ?_
  obtain ⟨v, hv1, -⟩ := guard_val (T := T) hn hsa (hgd _ (List.mem_cons_self ..))
  have hx : ∀ m, (Pattern.evar ⟨1⟩ : KoreAML.P).interpret (stdI_T c T) e m ↔ m = .val v := fun m => by
    rw [KoreAML.interp_evar, hv1]
  rw [KoreAML.interp_equal defOK_std]
  intro z
  rw [inj_sing hn hsb hsd (inj_sing hn hsa hsb hx), inj_sing hn hsa hsd hx, injNormal_comp]

end AtT

theorem sat_coh (h : HypModelCore c) {a b d : Srt} (hab : (a, b) ∈ c.subsorts) (hbd : (b, d) ∈ c.subsorts) :
    stdI c ⊧ᴵ (KoreAML.Cons.cohItem (c.sortName a) (c.sortName b) (c.sortName d)).pat :=
  AtT.sat_coh (c := c) (T := StepM c) (h := h) (a := a) (b := b) (d := d) (hab := hab) (hbd := hbd)

/-! ## The overload equations -/

theorem known_kernel {k : CtorSig} (hk : OvlLaws.KnownSig c k) : k ∈ kernelSyms c := by
  rcases OvlLaws.knownSig_mem hk with hm | hm
  · exact ctor_kernel hm
  · exact List.mem_append_right _ hm

namespace AtT

variable {T : GroundTerm → GroundTerm → Prop}

theorem evars_den {e : Valuation Elem} :
    ∀ (xs : List EVar) (us : List GroundTerm), xs.map e.evalEvar = us.map Elem.val →
      All2 (fun φ x => ∀ m, φ.interpret (stdI_T c T) e m ↔ m = x) (xs.map Pattern.evar) (us.map Elem.val)
  | [], [], _ => .nil
  | [], _ :: _, he => by simp at he
  | _ :: _, [], he => by simp at he
  | x :: xs, u :: us, he => by
    simp only [List.map_cons, List.cons.injEq] at he
    exact .cons (fun m => by rw [KoreAML.interp_evar, he.1]) (evars_den xs us he.2)

end AtT

theorem evars_den {e : Valuation Elem} :
    ∀ (xs : List EVar) (us : List GroundTerm), xs.map e.evalEvar = us.map Elem.val →
      All2 (fun φ x => ∀ m, φ.interpret (stdI c) e m ↔ m = x) (xs.map Pattern.evar) (us.map Elem.val) :=
  AtT.evars_den (c := c) (T := StepM c) (e := e)

namespace AtT

variable {T : GroundTerm → GroundTerm → Prop}

/-- The overload equation's argument patterns: each variable, injected where the two sorts differ,
denotes its value lifted. -/
theorem liftArgs_den (hn : NamesApartK c) {e : Valuation Elem} (F : (String × String) × EVar → KoreAML.P)
    (hF : ∀ A B xi, F ((A, B), xi) = if A == B then Pattern.evar xi else
      KoreAML.appList (KoreAML.sym (.symbol "inj")) [KoreAML.Cons.sortP A, KoreAML.Cons.sortP B, .evar xi]) :
    ∀ (as bs : List Srt) (xs : List EVar) (us : List GroundTerm),
      (∀ s ∈ as, s < nRegSorts + c.sortNames.length) → (∀ s ∈ bs, s < nRegSorts + c.sortNames.length) →
      xs.map e.evalEvar = us.map Elem.val → as.length = bs.length → us.length = as.length →
      All2 (fun φ x => ∀ m, φ.interpret (stdI_T c T) e m ↔ m = x)
        ((((as.map c.sortName).zip (bs.map c.sortName)).zip xs).map F) ((liftAll as bs us).map Elem.val)
  | [], _, _, _, _, _, _, _, _ => by simp [liftAll]; exact .nil
  | _ :: _, [], _, _, _, _, _, hl, _ => by simp at hl
  | _ :: _, _ :: _, [], _, _, _, he, _, hu => by
    simp at he; subst he; simp at hu
  | _ :: _, _ :: _, _ :: _, [], _, _, he, _, hu => by simp at hu
  | a :: as, b :: bs, x :: xs, u :: us, ha, hb, he, hl, hu => by
    simp only [List.map_cons, List.cons.injEq] at he
    have hla : liftAll (a :: as) (b :: bs) (u :: us) = lift a b u :: liftAll as bs us := rfl
    rw [hla, List.map_cons, List.map_cons, List.zip_cons_cons, List.zip_cons_cons, List.map_cons]
    have han := ha a (List.mem_cons_self ..)
    have hbn := hb b (List.mem_cons_self ..)
    refine .cons (fun m => ?_) (liftArgs_den hn F hF as bs xs us (fun s hs => ha s (List.mem_cons_of_mem _ hs))
      (fun s hs => hb s (List.mem_cons_of_mem _ hs)) he.2 (by simpa using hl) (by simpa using hu))
    rw [hF]
    by_cases hab : a = b
    · subst hab
      simp only [beq_self_eq_true, ↓reduceIte, KoreAML.interp_evar, he.1, OvlLaws.lift_self]
    · have hne : (c.sortName a == c.sortName b) = false := by
        rw [beq_eq_false_iff_ne]
        intro hs
        exact hab (hn.2.2 _ (List.mem_range.mpr han) _ (List.mem_range.mpr hbn) hs)
      simp only [hne, Bool.false_eq_true, ↓reduceIte]
      rw [inj_sing hn han hbn (fun m => by rw [KoreAML.interp_evar, he.1]) m, OvlLaws.lift_ne hab]

end AtT

/-- The overload equation's argument patterns: each variable, injected where the two sorts differ,
denotes its value lifted. -/
theorem liftArgs_den (hn : NamesApartK c) {e : Valuation Elem} (F : (String × String) × EVar → KoreAML.P)
    (hF : ∀ A B xi, F ((A, B), xi) = if A == B then Pattern.evar xi else
      KoreAML.appList (KoreAML.sym (.symbol "inj")) [KoreAML.Cons.sortP A, KoreAML.Cons.sortP B, .evar xi]) :
    ∀ (as bs : List Srt) (xs : List EVar) (us : List GroundTerm),
      (∀ s ∈ as, s < nRegSorts + c.sortNames.length) → (∀ s ∈ bs, s < nRegSorts + c.sortNames.length) →
      xs.map e.evalEvar = us.map Elem.val → as.length = bs.length → us.length = as.length →
      All2 (fun φ x => ∀ m, φ.interpret (stdI c) e m ↔ m = x)
        ((((as.map c.sortName).zip (bs.map c.sortName)).zip xs).map F) ((liftAll as bs us).map Elem.val) :=
  AtT.liftArgs_den (c := c) (T := StepM c) (hn := hn) (e := e) (F := F) (hF := hF)

/-! ## The law sentences of the open generators

Where the interpretation satisfies a law at values (`OpenAssoc`, `OpenIdem`, `OpenLaws`' conjuncts),
the value model satisfies the sentence `consItemsK` writes for it (`lawItemsK`): both sides denote
the values `paramVal` gives, a symbol's application at values being its `result`. -/

/-- `f(φa, f(φb, φd))` at singletons: an element of `f(a, y)` for an element `y` of `f(b, d)`. -/
theorem interp_symR {M : Type} {I : Interpretation KoreAML.Sym M} {e : Valuation M} (n : String)
    {φa φb φd : KoreAML.P} {a b d : M}
    (ha : ∀ m, φa.interpret I e m ↔ m = a) (hb : ∀ m, φb.interpret I e m ↔ m = b)
    (hd : ∀ m, φd.interpret I e m ↔ m = d) (m : M) :
    (KoreAML.appList (KoreAML.sym (.symbol n)) [φa, KoreAML.appList (KoreAML.sym (.symbol n)) [φb, φd]]).interpret I e m ↔
      ∃ y, SymE I n [b, d] y ∧ SymE I n [a, y] m := by
  rw [interp_appList]
  constructor
  · rintro ⟨h, hh, bs, hbs, happ⟩
    cases hbs with
    | cons hb1 hbs =>
      cases hbs with
      | cons hb2 hbs =>
        cases hbs
        rename_i x y
        have hx := (ha x).mp hb1
        subst hx
        exact ⟨y, (interp_symList n _ [b, d] (.cons hb (.cons hd .nil)) y).mp hb2, h, hh, happ⟩
  · rintro ⟨y, hy, h, hh, happ⟩
    exact ⟨h, hh, [a, y], .cons ((ha a).mpr rfl)
      (.cons ((interp_symList n _ [b, d] (.cons hb (.cons hd .nil)) y).mpr hy) .nil), happ⟩

/-- `f(f(φa, φb), φd)` at singletons (`interp_concatElem` at one symbol). -/
theorem interp_symL {M : Type} {I : Interpretation KoreAML.Sym M} {e : Valuation M} (n : String)
    {φa φb φd : KoreAML.P} {a b d : M}
    (ha : ∀ m, φa.interpret I e m ↔ m = a) (hb : ∀ m, φb.interpret I e m ↔ m = b)
    (hd : ∀ m, φd.interpret I e m ↔ m = d) (m : M) :
    (KoreAML.appList (KoreAML.sym (.symbol n)) [KoreAML.appList (KoreAML.sym (.symbol n)) [φa, φb], φd]).interpret I e m ↔
      ∃ y, SymE I n [a, b] y ∧ SymE I n [y, d] m :=
  interp_concatElem n n ha hb hd m

/-- `tr` of an application (as `tr_ap_tbl`, ModelRead.lean, which this module does not import). -/
private theorem tr_apL (tbl : KoreAML.VarTable) (f : String) (ps : List Kore.Pattern) :
    KoreAML.tr ⟨tbl, []⟩ (KoreAML.ap f ps) =
      KoreAML.appList (KoreAML.sym (.symbol f)) (ps.map (KoreAML.tr ⟨tbl, []⟩)) := by
  unfold KoreAML.ap
  rw [KoreAML.tr_app0, trArgs_appList]

/-- **A raw parameter with a law has two arguments of its result sort**: `paramsPlain`'s `raw`
branch (`raw_of_sortedOKCl`: `k.sig.args == [k.sig.result, k.sig.result]` where `assoc` or
`idem`). -/
theorem HypModelCore.law_binary (h : HypModelCore c) {k : ParamSig} (hk : k ∈ c.params) (hr : k.raw = true)
    (hl : k.assoc = true ∨ k.idem = true) : k.sig.args = [k.sig.result, k.sig.result] :=
  (Semantics.raw_of_sortedOKClEx h.sound.1 hk hr).2.1 (by rcases hl with hl | hl <;> simp [hl])

namespace AtT

variable {T : GroundTerm → GroundTerm → Prop}

/-- A parameter's symbol at two values: the parameter's value there (`paramVal`), for a parameter
of two arguments. -/
theorem symE_param2 (h : HypModelCore c) {k : ParamSig} (hk : k ∈ c.params) (hl : k.sig.args.length = 2)
    (a b : GroundTerm) (m : Elem) :
    SymE (stdI_T c T) (c.symName k.sig.name) [Elem.val a, Elem.val b] m ↔
      ∃ v, m = .val v ∧ c.paramVal k.sig.name [a, b] = some v := by
  have hks : k.sig ∈ kernelSyms c :=
    List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (List.mem_map_of_mem hk)))
  have hkinds : c.isCtor k.sig.name = false ∧ isHook k.sig.name = false := by
    have := h.kinds
    simp only [kindsApart, Bool.and_eq_true, List.all_eq_true] at this
    simpa using this.2 k hk
  have hp : c.isParam k.sig.name = true := by
    unfold Semantics.isParam
    rw [Semantics.lookupParam_eq]
    exact List.find?_isSome.mpr ⟨k, hk, by simp⟩
  have := symE_vals (T := T) h.namesK hks (vs := [a, b]) (by simp [hl]) m
  rw [show [Elem.val a, Elem.val b] = [a, b].map Elem.val from rfl, this,
    result_param hkinds.1 hkinds.2 hp]

/-- The guards of a law sentence: the sort variable `R` is a sort, and a variable `n` of the
law's sort holds a value of it. -/
theorem law_guards (h : HypModelCore c) {k : ParamSig} (hk : k ∈ c.params) {P : Kore.Pattern}
    {tbl : KoreAML.VarTable} {e : Valuation Elem} {m : Elem}
    (hgs : (KoreAML.conjList ((([KoreAML.Rv].map KoreAML.sortVarKey) ++ KoreAML.freeOf [] P).eraseDups.map
      (KoreAML.guardOf tbl))).interpret (stdI_T c T) e m) :
    KoreAML.IsSort (stdI_T c T) (e.evalEvar (tbl.ev (.sortVar "R"))) ∧
    ∀ n, KoreAML.VarKey.evar n (KoreAML.srt (c.sortName k.sig.result)) ∈ KoreAML.freeOf [] P →
      ∃ v, e.evalEvar (tbl.ev (.evar n (KoreAML.srt (c.sortName k.sig.result)))) = .val v ∧
        c.sortOf v = some k.sig.result := by
  have hks : k.sig ∈ kernelSyms c :=
    List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (List.mem_map_of_mem hk)))
  have hres := h.symSorts hks _ (List.mem_cons_self ..)
  have hguard : ∀ k' ∈ (([KoreAML.Rv].map KoreAML.sortVarKey) ++ KoreAML.freeOf [] P).eraseDups,
      (KoreAML.guardOf tbl k').interpret (stdI_T c T) e m := fun k' hk' =>
    conjList_elim hgs _ (List.mem_map.mpr ⟨k', hk', rfl⟩)
  refine ⟨?_, fun n hn => ?_⟩
  · have := hguard (.sortVar "R") (List.mem_eraseDups.mpr (List.mem_append_left _
      (List.mem_map.mpr ⟨KoreAML.Rv, List.mem_singleton_self _, rfl⟩)))
    obtain ⟨s, hs, he⟩ := sortGuard_iff.mp this
    rw [he]; exact (isSort_iff _).mpr ⟨s, hs, rfl⟩
  · have hg := hguard _ (List.mem_eraseDups.mpr (List.mem_append_right _ hn))
    rw [KoreAML.interp_guard_evar defOK_std, trSort_srt] at hg
    exact inSort_val ((inhOf_sort h.namesK hres e _).mp hg)

/-- A variable read at its value. -/
theorem ev_read {tbl : KoreAML.VarTable} {e : Valuation Elem} {n : String} {s : Kore.KSort} {v : GroundTerm}
    (hv : e.evalEvar (tbl.ev (.evar n s)) = .val v) (m : Elem) :
    (KoreAML.tr ⟨tbl, []⟩ (KoreAML.ev n s)).interpret (stdI_T c T) e m ↔ m = .val v := by
  unfold KoreAML.ev
  rw [KoreAML.tr, KoreAML.interp_evar]
  exact Iff.of_eq (congrArg (m = ·) hv)

/-- The two sides of the associativity sentence at values: `f(f(a, b), d)` is the value
`paramVal` gives `f(a, b)` and then that with d. -/
theorem symE_param2_bind (h : HypModelCore c) {k : ParamSig} (hk : k ∈ c.params) (hl : k.sig.args.length = 2)
    (a b d : GroundTerm) (m : Elem) :
    (∃ y, SymE (stdI_T c T) (c.symName k.sig.name) [Elem.val a, Elem.val b] y ∧
      SymE (stdI_T c T) (c.symName k.sig.name) [y, Elem.val d] m) ↔
      ∃ w, m = .val w ∧ (c.paramVal k.sig.name [a, b]).bind (fun ab => c.paramVal k.sig.name [ab, d]) = some w := by
  constructor
  · rintro ⟨y, hy, hy2⟩
    obtain ⟨v, rfl, hv⟩ := (symE_param2 h hk hl a b y).mp hy
    obtain ⟨w, rfl, hw⟩ := (symE_param2 h hk hl v d m).mp hy2
    exact ⟨w, rfl, by simp [hv, hw]⟩
  · rintro ⟨w, rfl, hw⟩
    cases hv : c.paramVal k.sig.name [a, b] with
    | none => simp [hv] at hw
    | some v =>
      simp only [hv, Option.bind_some] at hw
      exact ⟨.val v, (symE_param2 h hk hl a b _).mpr ⟨v, rfl, hv⟩, (symE_param2 h hk hl v d _).mpr ⟨w, rfl, hw⟩⟩

/-- `sat_assocItem` at the transition `T`. -/
theorem sat_assocItem (h : HypModelCore c) {k : ParamSig} (hk : k ∈ c.params)
    (hb : k.sig.args = [k.sig.result, k.sig.result]) (ha : OpenAssoc c k.sig.name k.sig.result) :
    stdI_T c T ⊧ᴵ (KoreAML.trAxiom [] [] ⟨0, "kernel", assocAxK c k⟩).pat := by
  have hn := h.namesK
  have hks : k.sig ∈ kernelSyms c :=
    List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (List.mem_map_of_mem hk)))
  have hres := h.symSorts hks _ (List.mem_cons_self ..)
  have hl : k.sig.args.length = 2 := by rw [hb]; rfl
  intro e m
  unfold KoreAML.trAxiom
  dsimp only
  generalize hP : (assocAxK c k).pattern = P
  have hsortP : KoreAML.sortOf [] P = some KoreAML.R := by rw [← hP]; rfl
  simp only [hsortP]
  rw [interpret_impl]
  intro hgs
  have hsv : (assocAxK c k).sortVars = [KoreAML.Rv] := rfl
  rw [hsv] at hgs ⊢
  generalize htb : KoreAML.tableOf [KoreAML.Rv] P = tbl at hgs ⊢
  let S := KoreAML.srt (c.sortName k.sig.result)
  let f := c.symName k.sig.name
  have hPeq : P = .equals S KoreAML.R
      (KoreAML.ap f [KoreAML.ap f [KoreAML.ev "K1" S, KoreAML.ev "K2" S], KoreAML.ev "K3" S])
      (KoreAML.ap f [KoreAML.ev "K1" S, KoreAML.ap f [KoreAML.ev "K2" S, KoreAML.ev "K3" S]]) := by
    rw [← hP]; rfl
  have hfree : KoreAML.freeOf [] P = [.evar "K1" S, .evar "K2" S, .evar "K3" S,
      .evar "K1" S, .evar "K2" S, .evar "K3" S] := by rw [hPeq]; rfl
  obtain ⟨hRs, hval⟩ := law_guards h hk hgs
  obtain ⟨a, hea, hsa⟩ := hval "K1" (by rw [hfree]; simp [S])
  obtain ⟨b, heb, hsb⟩ := hval "K2" (by rw [hfree]; simp [S])
  obtain ⟨d, hed, hsd⟩ := hval "K3" (by rw [hfree]; simp [S])
  have hSres : ∀ x, (KoreAML.trSort tbl S).interpret (stdI_T c T) e x ↔ x = .srt k.sig.result := fun x => by
    rw [trSort_srt]; exact sort_den hn hres e x
  have hRr : ∀ x, (KoreAML.trSort tbl KoreAML.R).interpret (stdI_T c T) e x ↔ x = e.evalEvar (tbl.ev (.sortVar "R")) :=
    fun x => by rw [trSort_R, KoreAML.interp_evar]
  have hresS : KoreAML.IsSort (stdI_T c T) (.srt k.sig.result) := (isSort_iff _).mpr ⟨_, List.mem_range.mpr hres, rfl⟩
  have hsorts : c.sortsOf [a, b, d] = some [k.sig.result, k.sig.result, k.sig.result] :=
    sortsOf_cons.mpr ⟨_, _, hsa, sortsOf_cons.mpr ⟨_, _, hsb, sortsOf_cons.mpr ⟨_, _, hsd, sortsOf_nil, rfl⟩, rfl⟩, rfl⟩
  rw [KoreAML.interp_equal defOK_std]
  intro x
  rw [hPeq, KoreAML.tr, KoreAML.interp_sEquals defOK_std sat_ceilDef hSres hRr hresS hRs,
    KoreAML.interp_inhOf_of hRr]
  refine ⟨fun hx => hx.1, fun hx => ⟨hx, fun y _ => ?_⟩⟩
  simp only [tr_apL, List.map_cons, List.map_nil]
  rw [interp_symL _ (ev_read hea) (ev_read heb) (ev_read hed), interp_symR _ (ev_read hea) (ev_read heb) (ev_read hed),
    symE_param2_bind h hk hl, ha a b d hsorts]
  constructor
  · rintro ⟨w, rfl, hw⟩
    cases hv : c.paramVal k.sig.name [b, d] with
    | none => simp [hv] at hw
    | some v =>
      simp only [hv, Option.bind_some] at hw
      exact ⟨.val v, (symE_param2 h hk hl b d _).mpr ⟨v, rfl, hv⟩, (symE_param2 h hk hl a v _).mpr ⟨w, rfl, hw⟩⟩
  · rintro ⟨z, hz, hz2⟩
    obtain ⟨v, rfl, hv⟩ := (symE_param2 h hk hl b d z).mp hz
    obtain ⟨w, rfl, hw⟩ := (symE_param2 h hk hl a v y).mp hz2
    exact ⟨w, rfl, by simp [hv, hw]⟩

/-- `sat_idemItem` at the transition `T`. -/
theorem sat_idemItem (h : HypModelCore c) {k : ParamSig} (hk : k ∈ c.params)
    (hb : k.sig.args = [k.sig.result, k.sig.result]) (hi : OpenIdem c k.sig.name k.sig.result) :
    stdI_T c T ⊧ᴵ (KoreAML.trAxiom [] [] ⟨0, "kernel", idemAxK c k⟩).pat := by
  have hn := h.namesK
  have hks : k.sig ∈ kernelSyms c :=
    List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (List.mem_map_of_mem hk)))
  have hres := h.symSorts hks _ (List.mem_cons_self ..)
  have hl : k.sig.args.length = 2 := by rw [hb]; rfl
  intro e m
  unfold KoreAML.trAxiom
  dsimp only
  generalize hP : (idemAxK c k).pattern = P
  have hsortP : KoreAML.sortOf [] P = some KoreAML.R := by rw [← hP]; rfl
  simp only [hsortP]
  rw [interpret_impl]
  intro hgs
  have hsv : (idemAxK c k).sortVars = [KoreAML.Rv] := rfl
  rw [hsv] at hgs ⊢
  generalize htb : KoreAML.tableOf [KoreAML.Rv] P = tbl at hgs ⊢
  let S := KoreAML.srt (c.sortName k.sig.result)
  have hPeq : P = .equals S KoreAML.R
      (KoreAML.ap (c.symName k.sig.name) [KoreAML.ev "K" S, KoreAML.ev "K" S]) (KoreAML.ev "K" S) := by
    rw [← hP]; rfl
  have hfree : KoreAML.freeOf [] P = [.evar "K" S, .evar "K" S, .evar "K" S] := by rw [hPeq]; rfl
  obtain ⟨hRs, hval⟩ := law_guards h hk hgs
  obtain ⟨a, hea, hsa⟩ := hval "K" (by rw [hfree]; simp [S])
  have hSres : ∀ x, (KoreAML.trSort tbl S).interpret (stdI_T c T) e x ↔ x = .srt k.sig.result := fun x => by
    rw [trSort_srt]; exact sort_den hn hres e x
  have hRr : ∀ x, (KoreAML.trSort tbl KoreAML.R).interpret (stdI_T c T) e x ↔ x = e.evalEvar (tbl.ev (.sortVar "R")) :=
    fun x => by rw [trSort_R, KoreAML.interp_evar]
  have hresS : KoreAML.IsSort (stdI_T c T) (.srt k.sig.result) := (isSort_iff _).mpr ⟨_, List.mem_range.mpr hres, rfl⟩
  rw [KoreAML.interp_equal defOK_std]
  intro x
  rw [hPeq, KoreAML.tr, KoreAML.interp_sEquals defOK_std sat_ceilDef hSres hRr hresS hRs,
    KoreAML.interp_inhOf_of hRr]
  refine ⟨fun hx => hx.1, fun hx => ⟨hx, fun y _ => ?_⟩⟩
  simp only [tr_apL, List.map_cons, List.map_nil]
  rw [interp_symList _ _ [Elem.val a, Elem.val a] (.cons (ev_read hea) (.cons (ev_read hea) .nil)) y,
    symE_param2 h hk hl, hi a hsa, ev_read hea]
  constructor
  · rintro ⟨w, rfl, hw⟩; cases hw; rfl
  · rintro rfl; exact ⟨a, rfl, rfl⟩

end AtT

/-- **The associativity sentence of an open generator holds in the value model** where the
interpretation satisfies it at values (`OpenAssoc`), for a parameter of two arguments of its result
sort: both sides of `f(f(K1, K2), K3) = f(K1, f(K2, K3))` denote the values `paramVal` gives. -/
theorem sat_assocItem (h : HypModelCore c) {k : ParamSig} (hk : k ∈ c.params)
    (hb : k.sig.args = [k.sig.result, k.sig.result]) (ha : OpenAssoc c k.sig.name k.sig.result) :
    stdI c ⊧ᴵ (KoreAML.trAxiom [] [] ⟨0, "kernel", assocAxK c k⟩).pat :=
  AtT.sat_assocItem (c := c) (T := StepM c) h hk hb ha

/-- **The idempotence sentence of an open generator holds in the value model** where the
interpretation satisfies it at values (`OpenIdem`), for a parameter of two arguments: `f(K, K)`
denotes what `K` does. -/
theorem sat_idemItem (h : HypModelCore c) {k : ParamSig} (hk : k ∈ c.params)
    (hb : k.sig.args = [k.sig.result, k.sig.result]) (hi : OpenIdem c k.sig.name k.sig.result) :
    stdI c ⊧ᴵ (KoreAML.trAxiom [] [] ⟨0, "kernel", idemAxK c k⟩).pat :=
  AtT.sat_idemItem (c := c) (T := StepM c) h hk hb hi

end Model

end Faithful

end KCore
