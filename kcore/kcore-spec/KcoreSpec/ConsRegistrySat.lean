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
  without an open generator or where `_==K_` is none of the names: a value of a sort outside `D` by its pattern, which names no detached
  name, and a literal of a detached sort because at one sort a literal's text determines it and two
  numbered sorts have distinct names (`ext_den_dvDet`), given what the values of a detached sort
  other than its literals denote (`hrest`).

  Those are range maps (`detVal_shape_rs`): a constructor or overloading symbol of a detached
  result sort would have an arity item that is neither clean nor the registry's own
  (`ctor_not_det_rs`), an injection's sorts are outside `D`, and a collection sort with a detached
  name is the library's RangeMap (`coll_det_rs`). A range map denotes exactly its added element
  (`den_rm_rs`), as `_RangeMap_` of its first entry and the rest at a map of maximal intervals gives
  the map, so every value does (`den_val_rs`, `valElems_decided`). RangeMap's no-junk item holds
  where it is detached, entry by entry (`noJunk_rm_rs`); with these `sat_registry` holds at the
  decided form of `Detached` with no hypothesis on values.
-/
import KcoreSpec.ConsTransfer
import KcoreSpec.ConsTransferR
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
/-- **`ValElems` at the decided form of `Detached`**, for a definition without an open generator or where
`_==K_` is none of the names,
given what the values of a detached sort other than its literals denote. -/
theorem valElems_of_decided (hm : HypModelCore c) (hg : Faithful.genWf c = true) [OvlOK c]
    (htr : ∀ a b d, (a, b) ∈ c.subsorts → (b, d) ∈ c.subsorts → (a, d) ∈ c.subsorts)
    (hra : (∀ p ∈ c.params, p.raw = false) ∨ DetachedB.kOK c ss ks kEq = true)
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
  inj := fun hv hw h1 h2 => elemOf_inj hd hI hg htr hra hv hw h1 h2
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
definition without an open generator or where `_==K_` is none of the names, given what the values of a detached sort other than its
literals denote and the no-junk items of the library collections whose sort is detached. -/
theorem sat_registry_decided (hd : detachedB c ss ks = true) (hI : I ⊧ᴵP Γown c (DetachedB.names c ss ks))
    (hm : HypModelCore c) (hg : Faithful.genWf c = true) [OvlOK c]
    (htr : ∀ a b d, (a, b) ∈ c.subsorts → (b, d) ∈ c.subsorts → (a, d) ∈ c.subsorts)
    (hra : (∀ p ∈ c.params, p.raw = false) ∨ DetachedB.kOK c ss ks kEq = true)
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
  refine sat_registry_of hm (valElems_of_decided hd hI hm hg htr hra hrest) (fun k hk hs => ?_) hnj h
  rcases Bool.or_eq_true _ _ ▸ List.all_eq_true.mp hB k hk with h1 | h2
  · simp only [sOK, isName_iff.mpr hs, Bool.not_true, Bool.false_eq_true] at h1
  · exact List.isEmpty_iff.mp h2

end

/-! ## The values of a detached sort -/

/-- The head of a left-nested application. -/
def headRs : KoreAML.P → KoreAML.P
  | .application a _ => headRs a
  | p => p

/-- The arguments of a left-nested application. -/
def argsRs : KoreAML.P → List KoreAML.P
  | .application a b => argsRs a ++ [b]
  | _ => []

theorem headRs_appList : ∀ (as : List KoreAML.P) (h : KoreAML.P),
    headRs (KoreAML.appList h as) = headRs h
  | [], _ => rfl
  | _ :: as, h => by rw [KoreAML.appList, headRs_appList as]; rfl

theorem argsRs_appList : ∀ (as : List KoreAML.P) (h : KoreAML.P),
    argsRs (KoreAML.appList h as) = argsRs h ++ as
  | [], _ => by simp [KoreAML.appList]
  | _ :: as, h => by rw [KoreAML.appList, argsRs_appList as]; simp [argsRs]

section
variable {c : Semantics}

/-- The arity item of a symbol, as an inclusion of its left side in its result sort. -/
theorem symArity_pat_rs (k : CtorSig) :
    (symArityItem c k).pat =
      (KoreAML.appList (match iteSort? (c.symName k.name) with
          | none => KoreAML.sym (.symbol (c.symName k.name))
          | some X => KoreAML.sym (.symbol "Lblite") ⬝ sortP X)
        (k.args.map fun s => KoreAML.inhOf (sortP (c.sortName s))) ⊆⊆
        KoreAML.inhOf (sortP (c.sortName k.result))) := by
  unfold symArityItem
  cases iteSort? (c.symName k.name) with
  | none =>
    simp only [KoreAML.arityItem, KoreAML.guarded, List.map_nil, KoreAML.appList, List.map_map]
    simp [srtOf, KoreAML.srt, KoreAML.trSort_const, sortP, Function.comp_def]
  | some X => rfl


/-- The arity item of a symbol names its result sort. -/
theorem sort_mem_arity_rs (k : CtorSig) :
    KoreAML.Sym.sort ("Sort" ++ c.sortName k.result) ∈ psyms (symArityItem c k).pat := by
  rw [symArity_pat_rs]
  simp [psyms, ML.included, ML.total, Pattern.negation, KoreAML.inhOf, KoreAML.sym, sortP]

end

section
open DetachedB
variable {c : Semantics} {ss : List Srt} {ks : List Sym}

/-- **No constructor and no overloading symbol has a detached result sort**, under the decided form
of `Detached`: its arity item names the sort, so it is the sort constant of a sort of `ss` or the
arity of a hook of `ks`; it is neither, as its head is its own name, which no hook of `ks` has, or
`Lblite` applied to a sort, which no hook's arity item applies. -/
theorem ctor_not_det_rs (hd : detachedB c ss ks = true) {k : CtorSig} (hk : k ∈ c.ctorSigs ++ c.ovlSigs)
    (hs : DSort c (DetachedB.names c ss ks) k.result) : False := by
  have hd' := hd
  simp only [detachedB, Bool.and_eq_true] at hd'
  obtain ⟨⟨⟨⟨⟨-, -⟩, -⟩, hL⟩, hV⟩, -⟩ := hd'
  have hko : kOK c ss ks k.name = true := (valuesB_sig hV (List.mem_append_left _ hk)).1
  simp only [listsB, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true] at hL
  have hmem : symArityItem c k ∈ sigItems c := by
    unfold sigItems
    simp only [List.mem_append, List.mem_map]
    refine .inl (.inr ⟨k, ?_, rfl⟩)
    unfold kernelSyms
    rcases List.mem_append.mp hk with h | h
    · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ h)))
    · exact List.mem_append_right _ h
  rcases hL.1.1.1 _ hmem with h | h
  · exact clean_spec h ⟨_, sort_mem_arity_rs k, hs⟩
  · simp only [regSig, Bool.or_eq_true, List.any_eq_true, beq_iff_eq, Bool.and_eq_true] at h
    rcases h with ⟨s, -, he⟩ | ⟨g, hg, hgk, he⟩
    · rw [symArity_pat_rs] at he
      simp [KoreAML.sortConstantItem, sortDeclOf, KoreAML.guarded, ML.included, ML.total, KoreAML.sExists,
        Pattern.negation] at he
    · rw [symArity_pat_rs, symArity_pat_rs, Faithful.Model.hook_plain hg] at he
      simp only [ML.included, ML.total, Pattern.negation, Pattern.implication.injEq,
        Pattern.application.injEq, true_and, and_true] at he
      cases hX : iteSort? (c.symName k.name) with
      | none =>
        simp only [hX] at he
        have := congrArg headRs he.1
        rw [headRs_appList, headRs_appList] at this
        have hn : c.symName k.name = c.symName g.name := KoreAML.Sym.symbol.inj (Pattern.symbol.inj this)
        simp only [kOK, isName, hn, Bool.not_eq_true', List.any_eq_false, beq_iff_eq] at hko
        exact hko g.name (List.contains_iff_mem.mp hgk) rfl
      | some X =>
        simp only [hX] at he
        have := congrArg argsRs he.1
        rw [argsRs_appList, argsRs_appList] at this
        cases hga : g.args with
        | nil => simp [hga, argsRs, KoreAML.sym, sortP] at this
        | cons a as => simp [hga, argsRs, KoreAML.sym, sortP, KoreAML.inhOf] at this

/-- **A collection sort with a detached name is the library's RangeMap**: a collection of the
definition at a detached sort would have its no-junk item name the sort, and the library's Map, Set
and List have axioms. -/
theorem coll_det_rs (hd : detachedB c ss ks = true) {s : Srt} {k : CollSig} (hco : c.collOf s = some k)
    (hs : DSort c (DetachedB.names c ss ks) s) : k = builtinColl .rangeMap := by
  obtain ⟨hk, rfl⟩ := Faithful.Model.collOf_spec hco
  have hd' := hd
  simp only [detachedB, Bool.and_eq_true] at hd'
  obtain ⟨⟨⟨⟨⟨-, -⟩, -⟩, hL⟩, -⟩, -⟩ := hd'
  simp only [listsB, Bool.and_eq_true, List.all_eq_true] at hL
  have h := hL.1.2 k hk
  by_cases hb : builtinColls.contains k = true ∧ ss.contains k.sort = true
  · have hkb : k ∈ builtinColls := List.contains_iff_mem.mp hb.1
    simp only [hb, and_self, ↓reduceIte, List.isEmpty_iff] at h
    simp only [builtinColls, List.mem_cons, List.not_mem_nil, or_false] at hkb
    rcases hkb with rfl | rfl | rfl | rfl
    · simp [collAxioms, mapCollAxioms] at h
    · simp [collAxioms, setCollAxioms] at h
    · simp [collAxioms, listCollAxioms] at h
    · rfl
  · simp only [hb, ↓reduceIte, Bool.and_eq_true] at h
    exfalso
    refine clean_spec h.1 ⟨.sort ("Sort" ++ c.sortName k.sort), ?_, hs⟩
    simp [collNoJunk, psyms, ML.included, ML.total, Pattern.negation, KoreAML.inhOf, KoreAML.sym, sortP]

/-- **A value of a detached sort is a literal or a range map**: under the decided form of
`Detached`. No constructor, overloading symbol, injection or open generator has a detached sort
for its result, and a collection of a detached sort is a range map. -/
theorem detVal_shape_rs (hd : detachedB c ss ks = true)
    {v : GroundTerm} {s : Srt} (hv : c.sortOf v = some s) (hs : DSort c (DetachedB.names c ss ks) s) :
    (∃ lit, v = .dv s lit) ∨
      (s = Srt.rangeMap ∧ c.collOf s = some (builtinColl .rangeMap) ∧ ∃ es, v = .map s es ∧
        rangesOK es = true ∧ ∀ e ∈ es, c.sortOf e.1 = some Srt.range ∧ c.sortOf e.2 = some Srt.kitem) := by
  have hV : valuesB c ss ks = true := by
    simp only [detachedB, Bool.and_eq_true] at hd
    exact hd.1.2
  have hsn : sOK c ss ks s = false := by
    simp [sOK, isName_iff.mpr hs]
  cases v with
  | ctor f ts =>
    exfalso
    rcases c.sortOf_ctor_iff.mp hv with ⟨k, hk, -, rfl⟩ | ⟨-, o, ho, -, -, rfl⟩ | ⟨-, -, k, hko, -, -, rfl⟩
    · exact ctor_not_det_rs hd (List.mem_append_left _ (lookupSig_spec hk).1) hs
    · have ho' : c.ovls.find? (·.sig.name == f) = some o := ho
      exact ctor_not_det_rs hd (List.mem_append_right _
        (List.mem_map_of_mem (List.mem_of_find?_eq_some ho'))) hs
    · have hG : graphsB c ss ks = true := by
        simp only [detachedB, Bool.and_eq_true] at hd
        exact hd.2
      simp only [graphsB, Bool.and_eq_true, List.all_eq_true] at hG
      have := (hG.1.2 k (c.lookupOpen_spec hko).1).2 k.sig.result (List.mem_cons_self ..)
      rw [hsn] at this; cases this
  | inj a b t =>
    exfalso
    obtain ⟨hab, -, -, rfl⟩ := sortOf_inj.mp hv
    rw [(valuesB_sub hV hab).2] at hsn; cases hsn
  | dv s0 lit =>
    obtain ⟨-, rfl⟩ := sortOf_dv.mp hv
    exact .inl ⟨lit, rfl⟩
  | map s0 es =>
    obtain ⟨k, vs, hco, hval, hkind, hes, rfl⟩ := c.sortOf_map_inv hv
    obtain rfl := coll_det_rs hd hco hs
    obtain ⟨-, hks⟩ := Faithful.Model.collOf_spec hco
    cases hval
    refine .inr ⟨hks.symm, hco, es, rfl, hkind, ?_⟩
    exact rmS_entriesOK_iff.mp hes
  | set s0 es =>
    exfalso
    obtain ⟨k, hco, hkind, -, -, rfl⟩ := sortOf_setS.mp hv
    obtain rfl := coll_det_rs hd hco hs
    cases hkind
  | list s0 es =>
    exfalso
    obtain ⟨k, hco, hkind, -, rfl⟩ := sortOf_listS.mp hv
    obtain rfl := coll_det_rs hd hco hs
    cases hkind

end

/-! ## A detached hooked symbol applied to patterns of values -/

section
variable {c : Semantics} {D : KoreAML.Sym → Prop} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}

theorem elems_injW_rs (hinj : ∀ {v w : GroundTerm} {s : Srt} {x : Ext M}, c.sortOf v = some s →
      c.sortOf w = some s → ElemOf c D I v x → ElemOf c D I w x → v = w) :
    ∀ {vs ws : List GroundTerm} {ss : List Srt} {xs : List (Ext M)}, c.sortsOf vs = some ss →
      c.sortsOf ws = some ss → All2 (ElemOf c D I) vs xs → All2 (ElemOf c D I) ws xs → vs = ws
  | [], [], _, _, _, _, _, _ => rfl
  | v :: vs, w :: ws, _, _ :: _, h1, h2, .cons hv hvs, .cons hw hws => by
    obtain ⟨s, ss', hv1, hvs1, rfl⟩ := sortsOf_cons.mp h1
    obtain ⟨_, _, hw1, hws1, he⟩ := sortsOf_cons.mp h2
    cases he
    rw [hinj hv1 hw1 hv hw, elems_injW_rs hinj hvs1 hws1 hvs hws]
  | [], _ :: _, _, _, _, _, .nil, h => by cases h
  | _ :: _, [], _, _, _, _, h, .nil => by cases h

open Faithful.Model (NamesApartK) in
/-- **A detached hooked symbol applied to patterns that denote exactly the elements of values of
its argument sorts denotes, in the extension, the element of its result** (`ResOf`), where values
of one sort with one element are equal. -/
theorem ext_hookAppP_rs (hn : NamesApartK c)
    (hinj : ∀ {v w : GroundTerm} {s : Srt} {x : Ext M}, c.sortOf v = some s → c.sortOf w = some s →
      ElemOf c D I v x → ElemOf c D I w x → v = w)
    {k : CtorSig} (hk : DHook c D k) {vs : List GroundTerm} (hvs : c.sortsOf vs = some k.args)
    {xs : List (Ext M)} (hxs : All2 (ElemOf c D I) vs xs) {ps : List KoreAML.P} (e : Valuation (Ext M))
    (hps : All2 (fun φ x => ∀ m, φ.interpret (extModel c D I) e m ↔ m = x) ps xs) (x : Ext M) :
    (KoreAML.appList (KoreAML.sym (.symbol (c.symName k.name))) ps).interpret (extModel c D I) e x ↔
      ResOf c D I k vs x := by
  rw [Faithful.interp_appList_sing _ _ _ hps]
  have hl : vs.length = k.args.length := sortsOf_length hvs
  constructor
  · rintro ⟨a, ha, hx⟩
    rw [KoreAML.interp_sym, ext_hookSym_rs hn hk] at ha
    obtain ⟨ws, h1, h2, h3⟩ := appE_hk_fwd_rs hn hk xs [] a x
      (by rw [← Faithful.All2.length hxs]; simpa using hl) ha hx
    obtain rfl := elems_injW_rs hinj (by simpa using h2) hvs h1 hxs
    exact (partOf_full_rs hl).mp (by simpa using h3)
  · intro h
    obtain ⟨a, ha, hx⟩ := appE_hk_bwd_rs hk vs xs [] x (by simpa using hl) (by simpa using hvs) hxs
      (by simpa using (partOf_full_rs hl).mpr h)
    exact ⟨a, (ext_hookSym_rs hn hk a).mpr ha, hx⟩

/-- Where `hook` gives a value, the element of the result is that value's. -/
theorem resOf_val_rs {k : CtorSig} {vs : List GroundTerm} {w : GroundTerm}
    (h : hook k.name vs = some (some w)) (x : Ext M) :
    ResOf c D I k vs x ↔ ElemOf c D I w x := by
  constructor
  · rintro ⟨v, hv | ⟨hv, -⟩, hx⟩
    · rw [h] at hv; cases hv; exact hx
    · rw [h] at hv; cases hv
  · intro hx; exact ⟨w, .inl h, hx⟩

end

/-! ## Range maps at a detached RangeMap -/

section
open DetachedB
variable {c : Semantics} {ss : List Srt} {ks : List Sym}

/-- RANGEMAP's unit, element and concatenation are interpreted hooks. -/
theorem rmSigs_mem_rs : (⟨rmUnit, [], Srt.rangeMap⟩ : CtorSig) ∈ hookSigs ∧
    (⟨rmElem, [Srt.range, Srt.kitem], Srt.rangeMap⟩ : CtorSig) ∈ hookSigs ∧
    (⟨rmConcat, [Srt.rangeMap, Srt.rangeMap], Srt.rangeMap⟩ : CtorSig) ∈ hookSigs :=
  ⟨(lookupSig_spec ((rangeMapSigs_hookSigs rmUnit (by decide)).trans rfl)).1,
   (lookupSig_spec ((rangeMapSigs_hookSigs rmElem (by decide)).trans rfl)).1,
   (lookupSig_spec ((rangeMapSigs_hookSigs rmConcat (by decide)).trans rfl)).1⟩

/-- A hook whose result sort is detached is a detached hook, under the decided form of `Detached`. -/
theorem dhook_of_result_rs (hd : detachedB c ss ks = true) {k : CtorSig} (hk : k ∈ hookSigs)
    (hs : DSort c (DetachedB.names c ss ks) k.result) : DHook c (DetachedB.names c ss ks) k := by
  refine ⟨hk, ?_⟩
  simp only [detachedB, Bool.and_eq_true] at hd
  have hG := hd.2
  simp only [graphsB, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hG
  rcases hG.1.1 k hk with h | h
  · exact isName_iff.mp (by simpa [kOK] using h)
  · exfalso
    have := h.2 k.result (List.mem_cons_self ..)
    simp [sOK, isName_iff.mpr hs] at this

theorem den_map_rs (hco : c.collOf Srt.rangeMap = some (builtinColl .rangeMap)) (es : Entries) :
    den c (.map Srt.rangeMap es) = KoreAML.den (GroundTerm.koreEntries c (builtinColl .rangeMap) es) := by
  unfold den
  rw [GroundTerm.kore, Semantics.collSig, hco]
  rfl

end

/-! ## What the values of a detached sort denote -/

section
open DetachedB
open Faithful.Model (HypModelCore)
variable {c : Semantics} {ss : List Srt} {ks : List Sym} {M : Type} [Inhabited M]
  {I : Interpretation KoreAML.Sym M}
  (hd : detachedB c ss ks = true) (hI : I ⊧ᴵP Γown c (DetachedB.names c ss ks)) (hm : HypModelCore c)
  (hg : Faithful.genWf c = true) [OvlOK c]
  (htr : ∀ a b d, (a, b) ∈ c.subsorts → (b, d) ∈ c.subsorts → (a, d) ∈ c.subsorts)
  (hra : (∀ p ∈ c.params, p.raw = false) ∨ DetachedB.kOK c ss ks kEq = true)
include hd hI hm hg htr hra

/-- A range map of one entry whose key and value denote exactly their elements denotes, in the
extension, exactly its added element: `r|->`'s value at them is that map. -/
theorem den_rm1_rs (hco : c.collOf Srt.rangeMap = some (builtinColl .rangeMap))
    (hs : DSort c (DetachedB.names c ss ks) Srt.rangeMap) {a b : GroundTerm}
    (hr : (asRange a).isSome = true) (ha : c.sortOf a = some Srt.range) (hb : c.sortOf b = some Srt.kitem)
    (hda : ∀ (e : Valuation (Ext M)) (x : Ext M), (den c a).interpret (extModel c (DetachedB.names c ss ks) I) e x ↔
      ElemOf c (DetachedB.names c ss ks) I a x)
    (hdb : ∀ (e : Valuation (Ext M)) (x : Ext M), (den c b).interpret (extModel c (DetachedB.names c ss ks) I) e x ↔
      ElemOf c (DetachedB.names c ss ks) I b x)
    (e : Valuation (Ext M)) (x : Ext M) :
    (den c (.map Srt.rangeMap [(a, b)])).interpret (extModel c (DetachedB.names c ss ks) I) e x ↔
      x = .inr (.val (.map Srt.rangeMap [(a, b)])) := by
  obtain ⟨xa, hxa⟩ := elemOf_total hd hI ha
  obtain ⟨xb, hxb⟩ := elemOf_total hd hI hb
  have hk := dhook_of_result_rs hd rmSigs_mem_rs.2.1 hs
  have hsing : c.sortOf (.map Srt.rangeMap [(a, b)]) = some Srt.rangeMap :=
    (rmS_sortOf_map hco).mpr ⟨rfl, by simpa [rangesOK] using hr, by simp [ha, hb]⟩
  rw [den_map_rs hco]
  show (KoreAML.den (KoreAML.ap (c.symName rmElem) [a.kore c, b.kore c])).interpret _ e x ↔ _
  unfold KoreAML.den
  rw [Faithful.Model.tr_ap]
  refine (ext_hookAppP_rs (k := ⟨rmElem, [Srt.range, Srt.kitem], Srt.rangeMap⟩) hm.namesK
    (fun hv hw h1 h2 => elemOf_inj hd hI hg htr hra hv hw h1 h2) hk (vs := [a, b])
    (rmS_sortsOf_cons.mpr ⟨ha, rmS_sortsOf_cons.mpr ⟨hb, sortsOf_nil⟩⟩) (.cons hxa (.cons hxb .nil)) e
    (.cons (fun m => (hda e m).trans ⟨fun h => elemOf_fun_rs h hxa, fun h => h ▸ hxa⟩)
      (.cons (fun m => (hdb e m).trans ⟨fun h => elemOf_fun_rs h hxb, fun h => h ▸ hxb⟩) .nil)) x).trans ?_
  exact (resOf_val_rs (rmM_elem hr) x).trans (elemOf_det_rs hsing hs)

/-- **A range map whose keys and values denote exactly their elements denotes, in the extension,
exactly its added element**: it is its first entry concatenated with the rest, and `_RangeMap_`'s
value there is the map. -/
theorem den_rm_rs (hco : c.collOf Srt.rangeMap = some (builtinColl .rangeMap))
    (hs : DSort c (DetachedB.names c ss ks) Srt.rangeMap) : ∀ (es : Entries), rangesOK es = true →
    (∀ p ∈ es, c.sortOf p.1 = some Srt.range ∧ c.sortOf p.2 = some Srt.kitem ∧
      (∀ (e : Valuation (Ext M)) (x : Ext M), (den c p.1).interpret (extModel c (DetachedB.names c ss ks) I) e x ↔
        ElemOf c (DetachedB.names c ss ks) I p.1 x) ∧
      (∀ (e : Valuation (Ext M)) (x : Ext M), (den c p.2).interpret (extModel c (DetachedB.names c ss ks) I) e x ↔
        ElemOf c (DetachedB.names c ss ks) I p.2 x)) →
    ∀ (e : Valuation (Ext M)) (x : Ext M),
      (den c (.map Srt.rangeMap es)).interpret (extModel c (DetachedB.names c ss ks) I) e x ↔
        x = .inr (.val (.map Srt.rangeMap es))
  | [], _, _, e, x => by
    have hk := dhook_of_result_rs hd rmSigs_mem_rs.1 hs
    have hsing : c.sortOf (.map Srt.rangeMap []) = some Srt.rangeMap :=
      (rmS_sortOf_map hco).mpr ⟨rfl, rfl, by simp⟩
    rw [den_map_rs hco]
    show (KoreAML.den (KoreAML.ap (c.symName rmUnit) [])).interpret _ e x ↔ _
    unfold KoreAML.den
    rw [Faithful.Model.tr_ap]
    refine (ext_hookAppP_rs (k := ⟨rmUnit, [], Srt.rangeMap⟩) hm.namesK
      (fun hv hw h1 h2 => elemOf_inj hd hI hg htr hra hv hw h1 h2) hk (vs := []) sortsOf_nil .nil e .nil x).trans ?_
    exact (resOf_val_rs rmM_unit x).trans (elemOf_det_rs hsing hs)
  | [(a, b)], hr, hes, e, x => by
    obtain ⟨ha, hb, hda, hdb⟩ := hes (a, b) (List.mem_singleton.mpr rfl)
    exact den_rm1_rs hd hI hm hg htr hra hco hs (rangesOK_head hr) ha hb hda hdb e x
  | (a, b) :: p2 :: es, hr, hes, e, x => by
    obtain ⟨ha, hb, hda, hdb⟩ := hes (a, b) (List.mem_cons_self ..)
    have hr' := rmM_tail hr
    have h1 := den_rm1_rs hd hI hm hg htr hra hco hs (rangesOK_head hr) ha hb hda hdb e
    have h2 := den_rm_rs hco hs (p2 :: es) hr' (fun p hp => hes p (List.mem_cons_of_mem _ hp)) e
    rw [den_map_rs hco] at h1 h2
    have hk := dhook_of_result_rs hd rmSigs_mem_rs.2.2 hs
    have hsort : ∀ {fs : Entries}, rangesOK fs = true → (∀ p ∈ fs, p ∈ (a, b) :: p2 :: es) →
        c.sortOf (.map Srt.rangeMap fs) = some Srt.rangeMap := fun hfs hsub =>
      (rmS_sortOf_map hco).mpr ⟨rfl, hfs, fun p hp => ⟨(hes p (hsub p hp)).1, (hes p (hsub p hp)).2.1⟩⟩
    have hs1 := hsort (fs := [(a, b)]) (by simpa [rangesOK] using rangesOK_head hr)
      (fun p hp => by rw [List.mem_singleton.mp hp]; exact List.mem_cons_self ..)
    have hs2 := hsort (fs := p2 :: es) hr' (fun p hp => List.mem_cons_of_mem _ hp)
    have hs3 := hsort (fs := (a, b) :: p2 :: es) hr (fun p hp => hp)
    rw [den_map_rs hco]
    show (KoreAML.den (KoreAML.ap (c.symName rmConcat)
      [GroundTerm.koreEntry c (builtinColl .rangeMap) (a, b),
        GroundTerm.koreEntries c (builtinColl .rangeMap) (p2 :: es)])).interpret _ e x ↔ _
    unfold KoreAML.den
    rw [Faithful.Model.tr_ap]
    refine (ext_hookAppP_rs (k := ⟨rmConcat, [Srt.rangeMap, Srt.rangeMap], Srt.rangeMap⟩) hm.namesK
      (fun hv hw h1 h2 => elemOf_inj hd hI hg htr hra hv hw h1 h2) hk
      (vs := [.map Srt.rangeMap [(a, b)], .map Srt.rangeMap (p2 :: es)])
      (rmS_sortsOf_cons.mpr ⟨hs1, rmS_sortsOf_cons.mpr ⟨hs2, sortsOf_nil⟩⟩)
      (.cons ((elemOf_det_rs hs1 hs).mpr rfl) (.cons ((elemOf_det_rs hs2 hs).mpr rfl) .nil)) e
      (.cons h1 (.cons h2 .nil)) x).trans ?_
    exact (resOf_val_rs (rmM_concat hr) x).trans (elemOf_det_rs hs3 hs)

/-- **Every value denotes, in the extension, exactly its element**, at the decided form of
`Detached`, for a definition without an open generator or where `_==K_` is none of the names: a value of a sort without a detached name
by its pattern, a literal of a detached sort by its text, and a value of a detached sort that is
no literal is a range map (`detVal_shape_rs`), whose entries denote their elements. -/
theorem den_val_rs : ∀ (v : GroundTerm) {s : Srt}, c.sortOf v = some s → ∀ (e : Valuation (Ext M)) (x : Ext M),
    (den c v).interpret (extModel c (DetachedB.names c ss ks) I) e x ↔ ElemOf c (DetachedB.names c ss ks) I v x
  | v, s, hv, e, x => by
    by_cases hs : DSort c (DetachedB.names c ss ks) s
    · rw [elemOf_det_rs hv hs]
      rcases detVal_shape_rs hd hv hs with ⟨lit, rfl⟩ | ⟨rfl, hco, es, hvm, hr, hes⟩
      · exact ext_den_dvDet hm hv hs e x
      · have _hsz : sizeOf es < sizeOf v := by rw [hvm]; simp only [GroundTerm.map.sizeOf_spec]; omega
        subst hvm
        refine den_rm_rs hd hI hm hg htr hra hco hs es hr (fun ⟨a, b⟩ hp => ⟨(hes _ hp).1, (hes _ hp).2, ?_, ?_⟩) e x
        · have _hlt := List.sizeOf_lt_of_mem hp
          have _hab : sizeOf (a, b) = 1 + sizeOf a + sizeOf b := rfl
          exact fun e' x' => den_val_rs a (hes _ hp).1 e' x'
        · have _hlt := List.sizeOf_lt_of_mem hp
          have _hab : sizeOf (a, b) = 1 + sizeOf a + sizeOf b := rfl
          exact fun e' x' => den_val_rs b (hes _ hp).2 e' x'
    · exact den_own_rs hd hI hv hs e x
  termination_by v => v
  decreasing_by all_goals (simp_wf; omega)

/-- **`ValElems` at the decided form of `Detached`**, for a definition without an open generator
or where `_==K_` is none of the names. -/
theorem valElems_decided : ValElems c (DetachedB.names c ss ks) I :=
  valElems_of_decided hd hI hm hg htr hra fun {v _} hv hs _ e x =>
    (den_val_rs hd hI hm hg htr hra v hv e x).trans (elemOf_det_rs hv hs)

/-- **RangeMap's no-junk item holds in the extension** where RangeMap is detached: an inhabitant
of the sort is the added element of a range map value, which is built from `.RangeMap` by
`_RangeMap_` of a one-entry map `r|-> v`, entry by entry. -/
theorem noJunk_rm_rs (hs : DSort c (DetachedB.names c ss ks) Srt.rangeMap) :
    extModel c (DetachedB.names c ss ks) I ⊧ᴵ collNoJunk c (builtinColl .rangeMap) := by
  have hV := valElems_decided hd hI hm hg htr hra
  have hn := hm.namesK
  have hco : c.collOf Srt.rangeMap = some (builtinColl .rangeMap) := hm.collOf_self rmM_mem
  have hkU := dhook_of_result_rs hd rmSigs_mem_rs.1 hs
  have hkE := dhook_of_result_rs hd rmSigs_mem_rs.2.1 hs
  have hkC := dhook_of_result_rs hd rmSigs_mem_rs.2.2 hs
  intro e m
  unfold collNoJunk
  dsimp only
  rw [KoreAML.interp_included (ext_defOK c _ I)]
  intro a ha
  unfold KoreAML.inhOf at ha
  rw [KoreAML.interp_app] at ha
  obtain ⟨i, b, hi, hb, hx⟩ := ha
  obtain rfl := (ext_sortName c _ I hs b).mp hb
  obtain ⟨s', v, hname, hs', hv, rfl⟩ := inh_new.mp ⟨i, hi, hx⟩
  have hs1 : s' < nRegSorts + c.sortNames.length := Faithful.Model.sortOf_numbered hm hv
  obtain rfl : Srt.rangeMap = s' := hn.2.2 _ (List.mem_range.mpr (Nat.lt_of_lt_of_le (by decide) (Nat.le_add_right _ _))) _ (List.mem_range.mpr hs1)
    ((String.append_right_inj "Sort").mp hname)
  rcases hm.coll_shape' hco (collSortsOK_mem hm.collSortsOK rmM_mem) hv with
    ⟨-, es, rfl⟩ | ⟨hk, -⟩ | ⟨hk, -⟩
  rotate_left
  · cases hk
  · cases hk
  obtain ⟨-, hr, hent⟩ := (rmS_sortOf_map hco).mp hv
  intro B hB
  let e' : Valuation (Ext M) := ⟨e.evalEvar, Function.update e.evalSvar ⟨1⟩ B⟩
  have hX : ∀ x, (Pattern.svar ⟨1⟩ : KoreAML.P).interpret (extModel c (DetachedB.names c ss ks) I) e' x ↔ B x :=
    fun x => by
      show Function.update e.evalSvar ⟨1⟩ B ⟨1⟩ x ↔ B x
      rw [Function.update_same]
  clear hv hb hi hx
  induction es with
  | nil =>
    have hsing : c.sortOf (.map Srt.rangeMap []) = some Srt.rangeMap := (rmS_sortOf_map hco).mpr ⟨rfl, rfl, by simp⟩
    refine hB _ (interpret_disj.mpr (.inl ?_))
    show (extModel c _ I).evalSymb (.symbol (c.symName rmUnit)) _
    rw [ext_hookSym_rs (k := ⟨rmUnit, [], Srt.rangeMap⟩) hn hkU, partOf_full_rs rfl]
    exact (resOf_val_rs rmM_unit _).mpr ((elemOf_det_rs hsing hs).mpr rfl)
  | cons p es ih =>
    obtain ⟨xa, xb⟩ := p
    have hr' := rmM_tail hr
    have hB' := ih hr' (fun p hp => hent p (List.mem_cons_of_mem _ hp))
    obtain ⟨ha', hb'⟩ := hent (xa, xb) (List.mem_cons_self ..)
    have hxr := rangesOK_head hr
    have hs1 : c.sortOf (.map Srt.rangeMap [(xa, xb)]) = some Srt.rangeMap :=
      (rmS_sortOf_map hco).mpr ⟨rfl, by simpa [rangesOK] using hxr, by simp [ha', hb']⟩
    have hs2 : c.sortOf (.map Srt.rangeMap es) = some Srt.rangeMap :=
      (rmS_sortOf_map hco).mpr ⟨rfl, hr', fun p hp => hent p (List.mem_cons_of_mem _ hp)⟩
    have hs3 : c.sortOf (.map Srt.rangeMap ((xa, xb) :: es)) = some Srt.rangeMap :=
      (rmS_sortOf_map hco).mpr ⟨rfl, hr, hent⟩
    obtain ⟨ya, hya⟩ := hV.total ha'
    obtain ⟨yb, hyb⟩ := hV.total hb'
    -- the one-entry map is an element of `r|->` applied to the sorts' inhabitants
    obtain ⟨a1, ha1, hap1⟩ := appE_hk_bwd_rs (k := ⟨rmElem, [Srt.range, Srt.kitem], Srt.rangeMap⟩) hkE
      [xa, xb] [ya, yb] [] (.inr (.val (.map Srt.rangeMap [(xa, xb)]))) rfl
      (rmS_sortsOf_cons.mpr ⟨ha', rmS_sortsOf_cons.mpr ⟨hb', sortsOf_nil⟩⟩) (.cons hya (.cons hyb .nil))
      ((partOf_full_rs rfl).mpr ((resOf_val_rs (rmM_elem hxr) _).mpr ((elemOf_det_rs hs1 hs).mpr rfl)))
    have hEl : (KoreAML.appList (symP (c.symName rmElem))
        [KoreAML.inhOf (sortP (c.sortName Srt.range)), KoreAML.inhOf (sortP (c.sortName Srt.kitem))]).interpret
        (extModel c (DetachedB.names c ss ks) I) e' (.inr (.val (.map Srt.rangeMap [(xa, xb)]))) := by
      rw [Faithful.interp_appList]
      exact ⟨a1, (ext_hookSym_rs hn hkE a1).mpr ha1, [ya, yb],
        .cons (hV.inh ha' hya e') (.cons (hV.inh hb' hyb e') .nil), hap1⟩
    -- the map is `_RangeMap_` of the one-entry map and the rest
    obtain ⟨a2, ha2, hap2⟩ := appE_hk_bwd_rs (I := I) (k := ⟨rmConcat, [Srt.rangeMap, Srt.rangeMap], Srt.rangeMap⟩) hkC
      [.map Srt.rangeMap [(xa, xb)], .map Srt.rangeMap es]
      [.inr (.val (.map Srt.rangeMap [(xa, xb)])), .inr (.val (.map Srt.rangeMap es))] []
      (.inr (.val (.map Srt.rangeMap ((xa, xb) :: es)))) rfl
      (rmS_sortsOf_cons.mpr ⟨hs1, rmS_sortsOf_cons.mpr ⟨hs2, sortsOf_nil⟩⟩)
      (.cons ((elemOf_det_rs hs1 hs).mpr rfl) (.cons ((elemOf_det_rs hs2 hs).mpr rfl) .nil))
      ((partOf_full_rs rfl).mpr ((resOf_val_rs (rmM_concat hr) _).mpr ((elemOf_det_rs hs3 hs).mpr rfl)))
    refine hB _ (interpret_disj.mpr (.inr ?_))
    rw [Faithful.interp_appList]
    exact ⟨a2, (ext_hookSym_rs hn hkC a2).mpr ha2, _, .cons hEl (.cons ((hX _).mpr hB') .nil), hap2⟩

/-- **The no-junk item of each library collection whose sort is detached holds in the extension**:
such a collection is RangeMap, the others having axioms. -/
theorem noJunk_decided_rs : ∀ k ∈ builtinColls, k.sort < nRegSorts →
    DetachedB.names c ss ks (.sort ("Sort" ++ c.sortName k.sort)) →
    extModel c (DetachedB.names c ss ks) I ⊧ᴵ collNoJunk c k := by
  intro k hk _ hs
  have hB : builtinColls.all (fun k => sOK c ss ks k.sort || (collAxioms c k).isEmpty) = true := by
    simp only [detachedB, Bool.and_eq_true] at hd
    exact hd.1.1.1.2
  have hax := List.all_eq_true.mp hB k hk
  have hsn : sOK c ss ks k.sort = false := by simp [sOK, isName_iff.mpr hs]
  rw [hsn, Bool.false_or] at hax
  simp only [builtinColls, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · simp [collAxioms, mapCollAxioms] at hax
  · simp [collAxioms, setCollAxioms] at hax
  · simp [collAxioms, listCollAxioms] at hax
  · exact noJunk_rm_rs hd hI hm hg htr hra hs

/-- **The extension satisfies the registry family** at the decided form of `Detached`, for a
definition without an open generator or where `_==K_` is none of the names: every value denotes exactly its element (`den_val_rs`) and
RangeMap's no-junk item holds where it is detached (`noJunk_decided_rs`). -/
theorem sat_registry {φ : KoreAML.P} (h : RegistryItem c (DetachedB.names c ss ks) φ) :
    extModel c (DetachedB.names c ss ks) I ⊧ᴵ φ :=
  sat_registry_decided hd hI hm hg htr hra
    (fun {v _} hv hs _ e x => (den_val_rs hd hI hm hg htr hra v hv e x).trans (elemOf_det_rs hv hs))
    (noJunk_decided_rs hd hI hm hg htr hra) h

end

end KCore.Cons
