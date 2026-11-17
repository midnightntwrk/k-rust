/-
  The extension of a model (`extModel`, ConsExtModel.lean) satisfies the registry family
  (`RegistryItem`, RegistryOwn.lean).

  The sort constant of a detached sort holds directly (`sat_registry_sortConst`). The other kinds
  are read from what the extension does with values (`ValElems`): each value has its element
  (`ElemOf`), its pattern denotes exactly that element, values of one sort with one element are
  equal, and the element is in the value's sort. From that, a detached hooked symbol applied to
  values denotes the element of its result (`ext_hookApp_rs`), which gives its arity, its graph and
  its fallback values; and a value is one element of its sort, distinct values distinct ones.
  `sat_registry_of` collects the kinds, given the no-junk items of the detached library collections.

  `ValElems` holds at the decided form of `Detached` (`valElems_of_decided`) for a definition
  without an open generator: a value of a sort outside `D` by its pattern, which names no detached
  name, and a literal of a detached sort because at one sort a literal's text determines it and two
  numbered sorts have distinct names (`ext_den_dvDet`). The values of a detached sort other than
  its literals are a hypothesis there (`hrest`), as is the no-junk item (`hnj`).
-/
import KcoreSpec.ConsTransfer
import KcoreSpec.ConsOwnValues

set_option autoImplicit false

namespace KCore.Cons

open ML Faithful
open Faithful (All2 AppE)

variable {c : Semantics} {D : KoreAML.Sym → Prop} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}

/-- **The sort constant of a detached sort holds in the extension**: the sort's name denotes one
element, the added one, and it is a sort. -/
theorem sat_registry_sortConst {s : Srt} (hs : D (.sort ("Sort" ++ c.sortName s))) :
    extModel c D I ⊧ᴵ (KoreAML.sortConstantItem (sortDeclOf c s)).pat := by
  intro e' pt
  show (KoreAML.sExists ⟨1⟩ (KoreAML.sym .sortSort)
    (KoreAML.sym (.sort ("Sort" ++ c.sortName s)) ≡ .evar ⟨1⟩)).interpret (extModel c D I) e' pt
  rw [interp_sExists' (ext_defOK c D I)]
  refine ⟨.inr (.srt ("Sort" ++ c.sortName s)), ⟨.inr .inh, .inr .sorts, rfl, rfl, _, hs, rfl⟩, ?_⟩
  rw [KoreAML.interp_equal (ext_defOK c D I)]
  intro a
  rw [KoreAML.interp_evar]
  show (extModel c D I).evalSymb (.sort ("Sort" ++ c.sortName s)) a ↔
    a = Function.update e'.evalEvar ⟨1⟩ (.inr (.srt ("Sort" ++ c.sortName s))) ⟨1⟩
  rw [Function.update_same]
  exact ext_sortName c D I hs a


/-! ## A detached hooked symbol in the extension -/

section
open Faithful.Model (NamesApartK)

/-- What a partial or full application of a detached hooked symbol denotes is its added element,
an old element, or the added element of a value. -/
theorem partOf_shape_rs {k : CtorSig} {vs : List GroundTerm} {x : Ext M} (h : PartOf c D I k vs x) :
    x = .inr (.hk k.name vs) ∨ (∃ m, x = .inl m) ∨ (∃ v, x = .inr (.val v)) := by
  unfold PartOf at h
  split at h
  · exact .inl h
  · obtain ⟨v, -, h⟩ := h
    rcases h with ⟨_, _, _, rfl⟩ | ⟨_, m, _, _, rfl, _⟩
    · exact .inr (.inr ⟨v, rfl⟩)
    · exact .inr (.inl ⟨m, rfl⟩)

theorem partOf_lt_rs {k : CtorSig} {vs : List GroundTerm} {x : Ext M} (h : vs.length < k.args.length) :
    PartOf c D I k vs x ↔ x = .inr (.hk k.name vs) := by
  unfold PartOf
  split
  · exact Iff.rfl
  · exact absurd h ‹_›

theorem partOf_full_rs {k : CtorSig} {vs : List GroundTerm} {x : Ext M} (h : vs.length = k.args.length) :
    PartOf c D I k vs x ↔ ResOf c D I k vs x := by
  unfold PartOf
  split
  · omega
  · exact Iff.rfl

/-- Two detached hooked symbols with one name are one. -/
theorem dhook_unique_rs (hn : NamesApartK c) {k k' : CtorSig} (hk : DHook c D k) (hk' : DHook c D k')
    (h : c.symName k.name = c.symName k'.name) : k = k' :=
  hn.1 k (List.mem_append_left _ (List.mem_append_right _ hk.1))
    k' (List.mem_append_left _ (List.mem_append_right _ hk'.1)) h

/-- **A detached hooked symbol denotes, in the extension, its application to no argument.** -/
theorem ext_hookSym_rs (hn : NamesApartK c) {k : CtorSig} (hk : DHook c D k) (x : Ext M) :
    (extModel c D I).evalSymb (.symbol (c.symName k.name)) x ↔ PartOf c D I k [] x := by
  have uniq : ∀ k', DHook c D k' → KoreAML.Sym.symbol (c.symName k.name) = .symbol (c.symName k'.name) →
      k' = k := fun k' hk' he => (dhook_unique_rs hn hk hk' (KoreAML.Sym.symbol.inj he)).symm
  constructor
  · intro h
    match x, h with
    | .inl _, .inl h => exact absurd hk.2 h.1
    | .inl _, .inr ⟨k', hk', he, hp⟩ => obtain rfl := uniq k' hk' he; exact hp
    | .inr (.srt _), h => cases h.2
    | .inr (.lit _), h => cases h
    | .inr (.val _), ⟨k', hk', he, hp⟩ => obtain rfl := uniq k' hk' he; exact hp
    | .inr (.hk _ _), ⟨k', hk', he, hp⟩ => obtain rfl := uniq k' hk' he; exact hp
    | .inr .dfn, h => cases h
    | .inr .inh, h => cases h
    | .inr .sorts, h => cases h
    | .inr .ceil, h => cases h
    | .inr (.ceil1 _), h => exact h.elim
    | .inr (.ceil2 _ _), h => exact h.elim
  · intro h
    rcases partOf_shape_rs h with rfl | ⟨m, rfl⟩ | ⟨v, rfl⟩
    · exact ⟨k, hk, rfl, h⟩
    · exact .inr ⟨k, hk, rfl, h⟩
    · exact ⟨k, hk, rfl, h⟩

/-- The argument sorts after the first `n`, one by one. -/
theorem drop_cons_rs {l : List Srt} {n : Nat} {s : Srt} (h : l[n]? = some s) :
    l.drop n = s :: l.drop (n + 1) := by
  obtain ⟨hn, rfl⟩ := List.getElem?_eq_some_iff.mp h
  exact List.drop_eq_getElem_cons hn

/-- **Applying a partial application to elements, forward**: what comes out is the application to
values those elements are elements of, of the next argument sorts. -/
theorem appE_hk_fwd_rs (hn : NamesApartK c) {k : CtorSig} (hk : DHook c D k) :
    ∀ (bs : List (Ext M)) (ws : List GroundTerm) (a x : Ext M), ws.length + bs.length = k.args.length →
      PartOf c D I k ws a → AppE (extModel c D I) a bs x →
      ∃ ws', All2 (ElemOf c D I) ws' bs ∧ c.sortsOf ws' = some (k.args.drop ws.length) ∧
        PartOf c D I k (ws ++ ws') x
  | [], ws, a, x, hl, hp, hx => by
    simp only [AppE] at hx
    subst hx
    refine ⟨[], .nil, ?_, by simpa using hp⟩
    rw [List.drop_eq_nil_of_le (by simp at hl; omega)]
    exact sortsOf_nil
  | b :: bs, ws, a, x, hl, hp, hx => by
    simp only [List.length_cons] at hl
    rw [partOf_lt_rs (by omega)] at hp
    subst hp
    obtain ⟨a', ha, hx⟩ := hx
    obtain ⟨k', w, s, hk', hkn, hs, hw, he, hp'⟩ := ha
    obtain rfl := dhook_unique_rs hn hk hk' (by rw [hkn])
    obtain ⟨ws', h1, h2, h3⟩ := appE_hk_fwd_rs hn hk bs (ws ++ [w]) a' x (by simp; omega) hp' hx
    refine ⟨w :: ws', .cons he h1, ?_, by simpa using h3⟩
    rw [drop_cons_rs hs]
    simp only [List.length_append, List.length_singleton] at h2
    exact sortsOf_cons.mpr ⟨s, _, hw, h2, rfl⟩

/-- **Applying a partial application to elements, backward**: the application to values of the
next argument sorts comes out of their elements. -/
theorem appE_hk_bwd_rs {k : CtorSig} (hk : DHook c D k) :
    ∀ (vs : List GroundTerm) (bs : List (Ext M)) (ws : List GroundTerm) (x : Ext M),
      ws.length + vs.length = k.args.length → c.sortsOf vs = some (k.args.drop ws.length) →
      All2 (ElemOf c D I) vs bs → PartOf c D I k (ws ++ vs) x →
      ∃ a, PartOf c D I k ws a ∧ AppE (extModel c D I) a bs x
  | [], _, ws, x, _, _, hb, hp => by
    cases hb
    exact ⟨x, by simpa using hp, rfl⟩
  | v :: vs, _, ws, x, hl, hs, .cons (b := b) (bs := bs) hb hbs, hp => by
    simp only [List.length_cons] at hl
    have hlt : ws.length < k.args.length := by omega
    have hd := List.drop_eq_getElem_cons hlt
    rw [hd] at hs
    obtain ⟨hv, hvs⟩ := OvlLaws.sortsOf_cons_iff.mp hs
    obtain ⟨a', ha', hx⟩ := appE_hk_bwd_rs hk vs bs (ws ++ [v]) x (by simp; omega)
      (by simpa using hvs) hbs (by simpa using hp)
    refine ⟨.inr (.hk k.name ws), (partOf_lt_rs hlt).mpr rfl, a',
      ⟨k, v, _, hk, rfl, List.getElem?_eq_getElem hlt, hv, hb, ha'⟩, hx⟩

end

/-! ## The registry family from what the values denote -/

variable (c D I) in
/-- What the extension does with values: each value has an element (`ElemOf`), its pattern
denotes exactly that element, two values of one sort with one element are equal, and the element
is in the value's sort. -/
structure ValElems : Prop where
  total : ∀ {v : GroundTerm} {s : Srt}, c.sortOf v = some s → ∃ x, ElemOf c D I v x
  den : ∀ {v : GroundTerm} {s : Srt}, c.sortOf v = some s → ∀ (e : Valuation (Ext M)) (x : Ext M),
    (den c v).interpret (extModel c D I) e x ↔ ElemOf c D I v x
  inj : ∀ {v w : GroundTerm} {s : Srt} {x : Ext M}, c.sortOf v = some s → c.sortOf w = some s →
    ElemOf c D I v x → ElemOf c D I w x → v = w
  inh : ∀ {v : GroundTerm} {s : Srt} {x : Ext M}, c.sortOf v = some s → ElemOf c D I v x →
    ∀ e : Valuation (Ext M), (KoreAML.inhOf (sortP (c.sortName s))).interpret (extModel c D I) e x

/-- A value has one element. -/
theorem elemOf_fun_rs {v : GroundTerm} {x y : Ext M} (hx : ElemOf c D I v x) (hy : ElemOf c D I v y) :
    x = y := by
  rcases hx with ⟨s, hs, hd, rfl⟩ | ⟨s, m, hs, hd, rfl, hm⟩ <;>
    rcases hy with ⟨s', hs', hd', rfl⟩ | ⟨s', m', hs', hd', rfl, hm'⟩
  · rfl
  · rw [hs] at hs'; cases hs'; exact absurd hd hd'
  · rw [hs] at hs'; cases hs'; exact absurd hd' hd
  · rw [(hm' m).mp ((hm m).mpr rfl)]

open Faithful.Model (NamesApartK) in
/-- The pattern of a detached hooked symbol applied to values. -/
theorem den_hookApp_rs {k : CtorSig} (hk : k ∈ hookSigs) (vs : List GroundTerm) :
    KoreAML.den (symApp c k.name (GroundTerm.koreList c vs)) =
      KoreAML.appList (KoreAML.sym (.symbol (c.symName k.name))) (vs.map (den c)) := by
  unfold symApp
  rw [Faithful.Model.hook_plain hk]
  unfold KoreAML.den
  rw [KoreAML.tr_app0, Faithful.trArgs_appList, DetachedB.koreList_map, List.map_map]
  rfl

theorem elems_rs (hV : ValElems c D I) : ∀ {vs : List GroundTerm} {ss : List Srt}, c.sortsOf vs = some ss →
    ∃ xs, All2 (ElemOf c D I) vs xs
  | [], _, _ => ⟨[], .nil⟩
  | v :: vs, _, h => by
    obtain ⟨s, ss', hv, hvs, -⟩ := sortsOf_cons.mp h
    obtain ⟨x, hx⟩ := hV.total hv
    obtain ⟨xs, hxs⟩ := elems_rs hV hvs
    exact ⟨x :: xs, .cons hx hxs⟩

theorem elems_den_rs (hV : ValElems c D I) (e : Valuation (Ext M)) :
    ∀ {vs : List GroundTerm} {ss : List Srt} {xs : List (Ext M)}, c.sortsOf vs = some ss →
      All2 (ElemOf c D I) vs xs →
      All2 (fun φ x => ∀ m, φ.interpret (extModel c D I) e m ↔ m = x) (vs.map (den c)) xs
  | [], _, _, _, .nil => .nil
  | v :: vs, _, _ :: _, h, .cons hx hxs => by
    obtain ⟨s, ss', hv, hvs, -⟩ := sortsOf_cons.mp h
    exact .cons (fun m => (hV.den hv e m).trans ⟨fun h => elemOf_fun_rs h hx, fun h => h ▸ hx⟩)
      (elems_den_rs hV e hvs hxs)

theorem elems_inj_rs (hV : ValElems c D I) :
    ∀ {vs ws : List GroundTerm} {ss : List Srt} {xs : List (Ext M)}, c.sortsOf vs = some ss →
      c.sortsOf ws = some ss → All2 (ElemOf c D I) vs xs → All2 (ElemOf c D I) ws xs → vs = ws
  | [], [], _, _, _, _, _, _ => rfl
  | v :: vs, w :: ws, _, _ :: _, h1, h2, .cons hv hvs, .cons hw hws => by
    obtain ⟨s, ss', hv1, hvs1, rfl⟩ := sortsOf_cons.mp h1
    obtain ⟨_, _, hw1, hws1, he⟩ := sortsOf_cons.mp h2
    cases he
    rw [hV.inj hv1 hw1 hv hw, elems_inj_rs hV hvs1 hws1 hvs hws]
  | [], _ :: _, _, _, _, _, .nil, h => by cases h
  | _ :: _, [], _, _, _, _, h, .nil => by cases h

open Faithful.Model (NamesApartK) in
/-- **A detached hooked symbol applied to values of its argument sorts denotes, in the extension,
the element of its result** (`ResOf`). -/
theorem ext_hookApp_rs (hn : NamesApartK c) (hV : ValElems c D I) {k : CtorSig} (hk : DHook c D k)
    {vs : List GroundTerm} (hvs : c.sortsOf vs = some k.args) (e : Valuation (Ext M)) (x : Ext M) :
    (KoreAML.den (symApp c k.name (GroundTerm.koreList c vs))).interpret (extModel c D I) e x ↔
      ResOf c D I k vs x := by
  obtain ⟨xs, hxs⟩ := elems_rs hV hvs
  rw [den_hookApp_rs hk.1, Faithful.interp_appList_sing _ _ _ (elems_den_rs hV e hvs hxs)]
  have hl : vs.length = k.args.length := sortsOf_length hvs
  constructor
  · rintro ⟨a, ha, hx⟩
    rw [KoreAML.interp_sym, ext_hookSym_rs hn hk] at ha
    obtain ⟨ws, h1, h2, h3⟩ := appE_hk_fwd_rs hn hk xs [] a x
      (by rw [← Faithful.All2.length hxs]; simpa using hl) ha hx
    obtain rfl := elems_inj_rs hV (by simpa using h2) hvs h1 hxs
    exact (partOf_full_rs hl).mp (by simpa using h3)
  · intro h
    obtain ⟨a, ha, hx⟩ := appE_hk_bwd_rs hk vs xs [] x (by simpa using hl) (by simpa using hvs) hxs
      (by simpa using (partOf_full_rs hl).mpr h)
    exact ⟨a, (ext_hookSym_rs hn hk a).mpr ha, hx⟩

open Faithful.Model (NamesApartK) in
/-- **The arity of a detached hooked symbol holds in the extension** (kind 2): applied to
elements of its argument sorts it gives an element of its result sort. -/
theorem sat_registry_arity (hn : NamesApartK c) (hV : ValElems c D I) (hrb : RangeBelow c)
    {k : CtorSig} (hk : DHook c D k) : extModel c D I ⊧ᴵ (symArityItem c k).pat := by
  intro e pt
  unfold symArityItem
  rw [Faithful.Model.hook_plain hk.1]
  dsimp only
  show (KoreAML.appList (KoreAML.sym (.symbol (c.symName k.name)))
      ((k.args.map (srtOf c)).map fun s => KoreAML.inhOf (KoreAML.trSort [] s)) ⊆⊆
    KoreAML.inhOf (KoreAML.trSort [] (srtOf c k.result))).interpret (extModel c D I) e pt
  rw [KoreAML.interp_included (ext_defOK c D I)]
  intro a ha
  rw [Faithful.interp_appList] at ha
  obtain ⟨h0, hh0, bs, hbs, hap⟩ := ha
  have hh0' : PartOf c D I k [] h0 := (ext_hookSym_rs hn hk h0).mp hh0
  have hl := Faithful.All2.length hbs
  simp only [List.length_map] at hl
  obtain ⟨ws, -, h2, h3⟩ := appE_hk_fwd_rs hn hk bs [] h0 a (by simpa using hl.symm) hh0' hap
  simp only [List.length_nil, List.drop_zero, List.nil_append] at h2 h3
  rw [partOf_full_rs (sortsOf_length h2)] at h3
  obtain ⟨v, hv, hx⟩ := h3
  have hvs : c.sortOf v = some k.result := hv.elim
    (hook_sorted (fun _ => hrb) (hookSigs_lookup k hk.1) h2)
    (fun h => Semantics.fallback_sorted (hookSigs_lookup k hk.1) h.2.2)
  rw [trSort_srtOf_twoT]
  exact hV.inh hvs hx e

open Faithful.Model (NamesApartK) in
/-- **The graph of a detached hooked symbol at values holds in the extension** (kind 3). -/
theorem sat_registry_graph (hn : NamesApartK c) (hV : ValElems c D I) (hrb : RangeBelow c)
    {k : CtorSig} (hk : DHook c D k) {vs : List GroundTerm} (hvs : c.sortsOf vs = some k.args)
    {r : Option GroundTerm} (hr : hook k.name vs = some r) (hs : r = none → silent k.name vs = false) :
    extModel c D I ⊧ᴵ (KoreAML.den (symApp c k.name (GroundTerm.koreList c vs)) ≡ (match (generalizing := false) r with
        | some v => den c v
        | none => ⊥)) := by
  intro e _
  rw [KoreAML.interp_equal (ext_defOK c D I)]
  intro x
  rw [ext_hookApp_rs hn hV hk hvs]
  cases r with
  | some v =>
    have hv : c.sortOf v = some k.result := hook_sorted (fun _ => hrb) (hookSigs_lookup k hk.1) hvs hr
    show ResOf c D I k vs x ↔ (den c v).interpret _ e x
    rw [hV.den hv]
    constructor
    · rintro ⟨v', h | ⟨h, -⟩, hx⟩
      · rw [hr] at h; cases h; exact hx
      · rw [hr] at h; cases h
    · intro hx; exact ⟨v, .inl hr, hx⟩
  | none =>
    show ResOf c D I k vs x ↔ False
    simp only [iff_false]
    rintro ⟨v', h | ⟨-, h, -⟩, -⟩
    · rw [hr] at h; cases h
    · rw [hs rfl] at h; cases h

open Faithful.Model (NamesApartK) in
/-- **The value of a detached hooked symbol at a silent point holds in the extension** (kind 4). -/
theorem sat_registry_fallback (hn : NamesApartK c) (hV : ValElems c D I)
    {k : CtorSig} (hk : DHook c D k) {vs : List GroundTerm} (hvs : c.sortsOf vs = some k.args)
    (hr : hook k.name vs = some none) (hs : silent k.name vs = true) :
    extModel c D I ⊧ᴵ (KoreAML.den (symApp c k.name (GroundTerm.koreList c vs)) ≡
      (match (generalizing := false) c.fallback k.name vs with
        | some v => den c v
        | none => ⊥)) := by
  intro e _
  rw [KoreAML.interp_equal (ext_defOK c D I)]
  intro x
  rw [ext_hookApp_rs hn hV hk hvs]
  cases hf : c.fallback k.name vs with
  | some v =>
    have hv : c.sortOf v = some k.result := Semantics.fallback_sorted (hookSigs_lookup k hk.1) hf
    show ResOf c D I k vs x ↔ (den c v).interpret _ e x
    rw [hV.den hv]
    constructor
    · rintro ⟨v', h | ⟨-, -, h⟩, hx⟩
      · rw [hr] at h; cases h
      · rw [hf] at h; cases h; exact hx
    · intro hx; exact ⟨v, .inr ⟨hr, hs, hf⟩, hx⟩
  | none =>
    show ResOf c D I k vs x ↔ False
    simp only [iff_false]
    rintro ⟨v', h | ⟨-, -, h⟩, -⟩
    · rw [hr] at h; cases h
    · rw [hf] at h; cases h

/-- **A value is one element of its sort in the extension** (kind 5). -/
theorem sat_registry_value (hV : ValElems c D I) {v : GroundTerm} {s : Srt} (hv : c.sortOf v = some s) :
    extModel c D I ⊧ᴵ KoreAML.sExists ⟨1⟩ (sortP (c.sortName s)) (den c v ≡ .evar ⟨1⟩) := by
  intro e _
  obtain ⟨x, hx⟩ := hV.total hv
  rw [interp_sExists' (ext_defOK c D I)]
  refine ⟨x, hV.inh hv hx _, ?_⟩
  rw [KoreAML.interp_equal (ext_defOK c D I)]
  intro a
  rw [hV.den hv, KoreAML.interp_evar]
  show _ ↔ a = Function.update e.evalEvar ⟨1⟩ x ⟨1⟩
  rw [Function.update_same]
  exact ⟨fun h => elemOf_fun_rs h hx, fun h => h ▸ hx⟩

/-- **Distinct values of one sort are distinct elements in the extension** (kind 6). -/
theorem sat_registry_distinct (hV : ValElems c D I) {v w : GroundTerm} {s : Srt} (hv : c.sortOf v = some s)
    (hw : c.sortOf w = some s) (hne : GroundTerm.cmp v w ≠ .eq) :
    extModel c D I ⊧ᴵ ∼(den c v ⋀ den c w) := by
  intro e x
  rw [ML.interpret_neg, ML.interpret_conj, hV.den hv, hV.den hw]
  rintro ⟨h1, h2⟩
  obtain rfl := hV.inj hv hw h1 h2
  exact hne (GroundTerm.cmp_refl v)

/-! ## The values of a detached sort -/

/-- The element of a value of a detached sort is its added element. -/
theorem elemOf_det_rs {v : GroundTerm} {s : Srt} (hv : c.sortOf v = some s) (hs : DSort c D s) {x : Ext M} :
    ElemOf c D I v x ↔ x = .inr (.val v) :=
  ⟨fun h => h.elim (fun ⟨_, _, _, h⟩ => h)
    (fun ⟨s', _, hv', hs', _, _⟩ => by rw [hv] at hv'; cases hv'; exact absurd hs hs'),
   fun h => .inl ⟨s, hv, hs, h⟩⟩

/-- The added element of a value of a detached sort is in the sort. -/
theorem inh_det_rs {v : GroundTerm} {s : Srt} (hv : c.sortOf v = some s) (hs : DSort c D s)
    (e : Valuation (Ext M)) :
    (KoreAML.inhOf (sortP (c.sortName s))).interpret (extModel c D I) e (.inr (.val v)) :=
  ⟨.inr .inh, .inr (.srt _), rfl, (ext_sortName c D I hs _).mpr rfl, ⟨s, v, rfl, hs, hv, rfl⟩⟩

open Faithful.Model (HypModelCore) in
/-- **A literal of a detached sort denotes, in the extension, exactly its added element**: the
literal's `dv` symbol has, besides its old elements (whose application to an added element is
empty), one added element, whose application to the sort's name gives the values of a sort with
that name with a literal of that text. Distinct numbered sorts have distinct names and, at one sort,
distinct literals distinct texts (`LitsApart`), so that is the one value. -/
theorem ext_den_dvDet (hm : HypModelCore c) {s : Srt} {lit : Lit} (hv : c.sortOf (.dv s lit) = some s)
    (hs : DSort c D s) (e : Valuation (Ext M)) (x : Ext M) :
    (den c (.dv s lit)).interpret (extModel c D I) e x ↔ x = .inr (.val (.dv s lit)) := by
  have hdv : ∀ {s' : Srt} {l : Lit}, c.sortOf (.dv s' l) = some s' → dvOK c.lib s' l = true := by
    intro s' l h
    simp only [Semantics.sortOf] at h
    split at h
    · assumption
    · cases h
  have hden : den c (.dv s lit) =
      KoreAML.sym (.dv lit.text) ⬝ KoreAML.sym (.sort ("Sort" ++ c.sortName s)) := by
    unfold den KoreAML.den; rw [GroundTerm.kore, KoreAML.tr_dv]; rfl
  rw [hden, KoreAML.interp_app]
  constructor
  · rintro ⟨a, b, ha, hb, hx⟩
    obtain rfl := (ext_sortName c D I hs b).mp hb
    match a, ha, hx with
    | .inl _, _, hx => exact (app_inl_inr hx).elim
    | .inr (.lit l), ha, hx =>
      cases ha
      obtain ⟨s', lit', hn, ht, -, hv', rfl⟩ := hx
      have hname := (String.append_right_inj "Sort").mp hn
      have hs1 := hm.dvSort (hdv hv)
      have hs2 := hm.dvSort (hdv hv')
      obtain rfl := hm.namesK.2.2 s (List.mem_range.mpr hs1) s' (List.mem_range.mpr hs2) hname
      obtain rfl := Faithful.Model.lit_unique hm.lits (hdv hv') (hdv hv) ht
      rfl
    | .inr (.srt _), ha, _ => cases ha.2
    | .inr (.val _), ⟨_, _, ha, _⟩, _ => cases ha
    | .inr (.hk _ _), ⟨_, _, ha, _⟩, _ => cases ha
    | .inr .dfn, ha, _ => cases ha
    | .inr .inh, ha, _ => cases ha
    | .inr .sorts, ha, _ => cases ha
    | .inr .ceil, ha, _ => cases ha
    | .inr (.ceil1 _), ha, _ => exact ha.elim
    | .inr (.ceil2 _ _), ha, _ => exact ha.elim
  · rintro rfl
    exact ⟨.inr (.lit lit.text), .inr (.srt _), ext_lit c D I lit.text, (ext_sortName c D I hs _).mpr rfl,
      ext_dv_app c D I hs hv⟩

/-! ## The values of a sort outside `D` -/

section
open KoreAML (KGround)

theorem psyms_trSortApp_rs {t : KoreAML.VarTable} : ∀ (ss : List Kore.KSort) (acc : KoreAML.P)
    {σ : KoreAML.Sym}, σ ∈ psyms acc → σ ∈ psyms (KoreAML.trSortApp t acc ss)
  | [], _, _, h => by rw [KoreAML.trSortApp]; exact h
  | _ :: ss, _, _, h => by
    rw [KoreAML.trSortApp]
    exact psyms_trSortApp_rs ss _ (by simp only [psyms]; exact List.mem_append_left _ h)

theorem psyms_appList_head_rs : ∀ (as : List KoreAML.P) (h : KoreAML.P) {σ : KoreAML.Sym},
    σ ∈ psyms h → σ ∈ psyms (KoreAML.appList h as)
  | [], _, _, hσ => hσ
  | _ :: as, _, _, hσ => psyms_appList_head_rs as _ (by simp only [psyms]; exact List.mem_append_left _ hσ)

theorem psyms_appList_arg_rs : ∀ (as : List KoreAML.P) (h : KoreAML.P) {a : KoreAML.P} {σ : KoreAML.Sym},
    a ∈ as → σ ∈ psyms a → σ ∈ psyms (KoreAML.appList h as)
  | [], _, _, _, ha, _ => absurd ha List.not_mem_nil
  | b :: as, h, a, σ, ha, hσ => by
    rcases List.mem_cons.mp ha with rfl | ha
    · exact psyms_appList_head_rs as _ (by simp only [psyms]; exact List.mem_append_right _ hσ)
    · exact psyms_appList_arg_rs as _ ha hσ

theorem ownEx_trSortApp_rs {V : List EVar} {W : List SVar} {t : KoreAML.VarTable} :
    ∀ (ss : List Kore.KSort) (acc : KoreAML.P), (∀ s ∈ ss, ∃ C, s = .ctor C []) →
      OwnSorted D V W .ex acc → (∀ σ ∈ psyms (KoreAML.trSortApp t acc ss), ¬ D σ) →
      OwnSorted D V W .ex (KoreAML.trSortApp t acc ss)
  | [], _, _, ha, _ => by rw [KoreAML.trSortApp]; exact ha
  | s :: ss, acc, hs, ha, hD => by
    obtain ⟨C, rfl⟩ := hs s (List.mem_cons_self ..)
    rw [KoreAML.trSortApp] at hD ⊢
    rw [KoreAML.trSort_const] at hD ⊢
    refine ownEx_trSortApp_rs ss _ (fun s' h => hs s' (List.mem_cons_of_mem _ h))
      (.appE ha (OwnSorted.toOld (.sym trivial ?_))) hD
    exact hD _ (psyms_trSortApp_rs ss _ (by simp [psyms, KoreAML.sym]))

/-- **The pattern of a ground KORE term whose symbols are outside `D` is of the class** (kind
`ex`): it denotes in the extension the old elements it denotes in the model, and no added one. -/
theorem ownEx_kground_rs {V : List EVar} {W : List SVar} {t : KoreAML.VarTable} {p : Kore.Pattern}
    (hp : KGround p) : (∀ σ ∈ psyms (KoreAML.tr ⟨t, []⟩ p), ¬ D σ) →
      OwnSorted D V W .ex (KoreAML.tr ⟨t, []⟩ p) := by
  induction hp with
  | @app h ss ps hs _ ih =>
    intro hD
    have htr : KoreAML.tr ⟨t, []⟩ (.app h ss ps) =
        KoreAML.appList (KoreAML.trSortApp t (KoreAML.sym (.symbol h.ident.name)) ss)
          (ps.map (KoreAML.tr ⟨t, []⟩)) := by
      rw [KoreAML.tr]
      simp only [List.contains_nil, Bool.false_eq_true, ↓reduceIte]
      exact Faithful.trArgs_appList _ _ _
    rw [htr] at hD ⊢
    refine OwnSorted.appList (ownEx_trSortApp_rs ss _ hs (.sym trivial ?_) ?_) ?_
    · exact hD _ (psyms_appList_head_rs _ _ (psyms_trSortApp_rs ss _ (by simp [psyms, KoreAML.sym])))
    · exact fun σ hσ => hD σ (psyms_appList_head_rs _ _ hσ)
    · intro a ha
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ha
      exact OwnSorted.toOld (ih p hp fun σ hσ => hD σ (psyms_appList_arg_rs _ _ ha hσ))
  | dv =>
    intro hD
    rw [KoreAML.tr, KoreAML.trSort_const] at hD ⊢
    exact .appH (.dv _) (.sym trivial (hD _ (by simp [psyms, KoreAML.sym])))

end

section
open DetachedB
variable {ss : List Srt} {ks : List Sym} (hd : detachedB c ss ks = true)
  (hI : I ⊧ᴵP Γown c (DetachedB.names c ss ks))
include hd hI

omit hd hI in
theorem names_plain_rs : ∀ σ, DetachedB.names c ss ks σ → plainSym σ := by
  rintro σ (⟨_, _, rfl⟩ | ⟨_, _, rfl⟩) <;> trivial

/-- **A value of a sort without a detached name denotes, in the extension, exactly its element**:
its pattern names no detached name, so it denotes the old elements it denotes in the model, which
are one. -/
theorem den_own_rs {v : GroundTerm} {s : Srt} (hv : c.sortOf v = some s)
    (hs : ¬ DSort c (DetachedB.names c ss ks) s) (e : Valuation (Ext M)) (x : Ext M) :
    (den c v).interpret (extModel c (DetachedB.names c ss ks) I) e x ↔
      ElemOf c (DetachedB.names c ss ks) I v x := by
  have hV : valuesB c ss ks = true := by
    simp only [detachedB, Bool.and_eq_true] at hd
    exact hd.1.2
  have hcl := clean_spec (clean_val hV v s hv (sOK_of_not_DSort hs))
  have hT := transfer_rel (c := c) (I := I) names_plain_rs (ownVals_of_decided hd hI).defOK
    (ownEx_kground_rs (V := []) (W := []) (Faithful.kore_ground c v)
      (fun σ hσ hn => hcl ⟨σ, hσ, hn⟩)) KoreAML.val0 e (rel_nil _ _)
  obtain ⟨a, ha, -⟩ := own_single hd hI hv (sOK_of_not_DSort hs) KoreAML.val0
  constructor
  · intro h
    cases x with
    | inl m =>
      have hma : m = a := (ha m).mp ((hT.1 m).mp h)
      exact .inr ⟨s, m, hv, hs, rfl, fun m' => by rw [ha m', hma]⟩
    | inr n => exact absurd h (hT.2 n)
  · intro h
    rcases h with ⟨s', hv', hs', rfl⟩ | ⟨s', m, hv', hs', rfl, hm⟩
    · rw [hv] at hv'; cases hv'; exact absurd hs' hs
    · exact (hT.1 m).mpr ((hm m).mpr rfl)

/-- The element of a value of a sort without a detached name is in the sort, in the extension. -/
theorem inh_own_rs {v : GroundTerm} {s : Srt} {m : M} (hv : c.sortOf v = some s)
    (hs : ¬ DSort c (DetachedB.names c ss ks) s)
    (hm : ∀ m', (den c v).interpret I KoreAML.val0 m' ↔ m' = m) (e : Valuation (Ext M)) :
    (KoreAML.inhOf (sortP (c.sortName s))).interpret (extModel c (DetachedB.names c ss ks) I) e (.inl m) := by
  obtain ⟨a, ha, hinh⟩ := own_single hd hI hv (sOK_of_not_DSort hs) KoreAML.val0
  obtain rfl : m = a := (ha m).mp ((hm m).mpr rfl)
  have hT := transfer_rel (c := c) (I := I) names_plain_rs (ownVals_of_decided hd hI).defOK
    (OwnSorted.inhOf (V := []) (W := []) (OwnSorted.sortC hs)) KoreAML.val0 e (rel_nil _ _)
  exact (hT.1 m).mpr hinh

open Faithful.Model (HypModelCore) in
/-- **`ValElems` at the decided form of `Detached`**, for a definition without an open generator,
given what the values of a detached sort other than its literals denote. -/
theorem valElems_of_decided (hm : HypModelCore c) (hg : Faithful.genWf c = true) [OvlOK c]
    (htr : ∀ a b d, (a, b) ∈ c.subsorts → (b, d) ∈ c.subsorts → (a, d) ∈ c.subsorts)
    (hraw : ∀ p ∈ c.params, p.raw = false)
    (hrest : ∀ {v : GroundTerm} {s : Srt}, c.sortOf v = some s → DSort c (DetachedB.names c ss ks) s →
      (∀ lit, v ≠ .dv s lit) → ∀ (e : Valuation (Ext M)) (x : Ext M),
        (den c v).interpret (extModel c (DetachedB.names c ss ks) I) e x ↔ x = .inr (.val v)) :
    ValElems c (DetachedB.names c ss ks) I where
  total := elemOf_total hd hI
  den := fun {v s} hv e x => by
    by_cases hs : DSort c (DetachedB.names c ss ks) s
    · rw [elemOf_det_rs hv hs]
      by_cases hl : ∃ lit, v = .dv s lit
      · obtain ⟨lit, rfl⟩ := hl
        exact ext_den_dvDet hm hv hs e x
      · exact hrest hv hs (fun lit h => hl ⟨lit, h⟩) e x
    · exact den_own_rs hd hI hv hs e x
  inj := fun hv hw h1 h2 => elemOf_inj hd hI hg htr hraw hv hw h1 h2
  inh := fun {v s x} hv hx e => by
    rcases hx with ⟨s', hv', hs', rfl⟩ | ⟨s', m, hv', hs', rfl, hm⟩ <;> rw [hv] at hv' <;> cases hv'
    · exact inh_det_rs hv hs' e
    · exact inh_own_rs hd hI hv hs' hm e

end

/-! ## The family -/

open Faithful.Model (HypModelCore) in
/-- **The extension satisfies the registry family**, where every value has its element
(`ValElems`) and the extension satisfies the no-junk item of each library collection whose sort is
detached, a detached collection sort having no axioms. -/
theorem sat_registry_of (hm : HypModelCore c) (hV : ValElems c D I)
    (hax : ∀ k ∈ builtinColls, D (.sort ("Sort" ++ c.sortName k.sort)) → collAxioms c k = [])
    (hnj : ∀ k ∈ builtinColls, k.sort < nRegSorts → D (.sort ("Sort" ++ c.sortName k.sort)) →
      extModel c D I ⊧ᴵ collNoJunk c k)
    {φ : KoreAML.P} (h : RegistryItem c D φ) : extModel c D I ⊧ᴵ φ := by
  have hn := hm.namesK
  have hrb := rangeBelow_of_model hm
  unfold RegistryItem at h
  dsimp only at h
  rcases h with ⟨s, ⟨-, hs⟩, rfl⟩ | ⟨k, hk, rfl⟩ | ⟨k, vs, r, hk, hvs, hr, hsil, rfl⟩ |
    ⟨k, vs, hk, hvs, hr, hsil, rfl⟩ | ⟨v, s, -, hv, rfl⟩ | ⟨v, w, s, -, -, hv, hw, hne, rfl⟩ |
    ⟨k, hk, ⟨hlt, hs⟩, h | h⟩
  · exact sat_registry_sortConst hs
  · exact sat_registry_arity hn hV hrb hk
  · exact sat_registry_graph hn hV hrb hk hvs hr hsil
  · exact sat_registry_fallback hn hV hk hvs hr hsil
  · exact sat_registry_value hV hv
  · exact sat_registry_distinct hV hv hw hne
  · subst h; exact hnj k hk hlt hs
  · rw [hax k hk hs] at h; exact absurd h List.not_mem_nil

section
open DetachedB
variable {ss : List Srt} {ks : List Sym}

open Faithful.Model (HypModelCore) in
/-- **The extension satisfies the registry family at the decided form of `Detached`**, for a
definition without an open generator, given what the values of a detached sort other than its
literals denote and the no-junk items of the library collections whose sort is detached. -/
theorem sat_registry_decided (hd : detachedB c ss ks = true) (hI : I ⊧ᴵP Γown c (DetachedB.names c ss ks))
    (hm : HypModelCore c) (hg : Faithful.genWf c = true) [OvlOK c]
    (htr : ∀ a b d, (a, b) ∈ c.subsorts → (b, d) ∈ c.subsorts → (a, d) ∈ c.subsorts)
    (hraw : ∀ p ∈ c.params, p.raw = false)
    (hrest : ∀ {v : GroundTerm} {s : Srt}, c.sortOf v = some s → DSort c (DetachedB.names c ss ks) s →
      (∀ lit, v ≠ .dv s lit) → ∀ (e : Valuation (Ext M)) (x : Ext M),
        (den c v).interpret (extModel c (DetachedB.names c ss ks) I) e x ↔ x = .inr (.val v))
    (hnj : ∀ k ∈ builtinColls, k.sort < nRegSorts → DetachedB.names c ss ks (.sort ("Sort" ++ c.sortName k.sort)) →
      extModel c (DetachedB.names c ss ks) I ⊧ᴵ collNoJunk c k)
    {φ : KoreAML.P} (h : RegistryItem c (DetachedB.names c ss ks) φ) :
    extModel c (DetachedB.names c ss ks) I ⊧ᴵ φ := by
  have hB : builtinColls.all (fun k => sOK c ss ks k.sort || (collAxioms c k).isEmpty) = true := by
    simp only [detachedB, Bool.and_eq_true] at hd
    exact hd.1.1.1.2
  refine sat_registry_of hm (valElems_of_decided hd hI hm hg htr hraw hrest) (fun k hk hs => ?_) hnj h
  rcases Bool.or_eq_true _ _ ▸ List.all_eq_true.mp hB k hk with h1 | h2
  · simp only [sOK, isName_iff.mpr hs, Bool.not_true, Bool.false_eq_true] at h1
  · exact List.isEmpty_iff.mp h2

end

end KCore.Cons
