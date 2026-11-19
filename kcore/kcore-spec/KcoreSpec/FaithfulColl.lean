/-
  KCore. Map patterns read downwards, through the map axioms of `ΓColls`.

  A negated premise (a competitor's exclusion `∃ȳ. ⌈req = true⌉ ∧ X̄ ∈ p̄`, a rule's `applies`)
  binds its variables existentially over every element of their sorts. For a constructor pattern
  that is harmless: from `ctor(e) = ⟦ctor v⟧` injectivity gives `e = ⟦v⟧`. A map pattern
  `K |-> V M` is read at `⟦w⟧ ∈ concat(elem(a, b), m)` with `a`, `b`, `m` any elements of KItem,
  KItem and Map, and the graphs of `ΓDomains` speak of `elem` and `concat` on the elements of
  values only. Without `ΓColls` nothing makes `a`, `b`, `m` elements of values: the sorts below
  KItem without generators (Int, Bool, the token sorts) may hold elements that are no value's, and
  `elem` may map them anywhere in Map. For instance: add to the intended model one element `ω` of
  Int, close the constructor sorts freely over it (so KItem holds `inj{Int,KItem}(ω)`), let every
  hook and parameter be empty on arguments that are not values' elements, and let `elem(a, b)` be
  the empty map's element when `a` or `b` is not a value's. Every axiom of `Γ` but `ΓColls` still
  holds (the graphs speak of values only, Map's carrier is unchanged, so `collNoJunk` holds), and
  the empty map's element lies in `concat(elem(inj(ω), b), ⟦.Map⟧)`: the pattern `K |-> V M` holds
  of `.Map`, which it does not match. In that model a rule `<k> a => b </k> <m> K |-> V M </m>` of
  a smaller priority than `<k> a => c </k>` keeps the second from firing at `.Map`, where `Step`
  fires it; `mapElemNotUnitAx` is false there.

  With the map axioms of `ΓColls` (`mapUnitSplitAx`, `mapElemNotUnitAx`, `mapElemAtomAx`,
  `mapDecompAx`), a value's element lies in a map pattern's translation only where its parts are
  elements of values (`map_split`, `map_elem`), so the pattern denotes the value under the
  valuation's substitution (`patVal_back4`), and every step of a semantics in `Stage4` is a
  consequence of `Γ c` (`step_sound_stage4`).
-/
import KcoreSpec.FaithfulStage4

set_option autoImplicit false

namespace KCore

namespace Faithful

open ML
open KoreAML (DefOK Inh IsSort Closed KGround VarKey VarTable)

/-! ## The library's map, read in a model of `Γ` -/

/-- The library's map collection. -/
def mapColl : CollSig := ⟨Srt.map, .map, Srt.kitem, some Srt.kitem, mapUnit, mapElem, mapConcat⟩

theorem mapColl_mem (c : Semantics) : mapColl ∈ c.allColls := List.mem_append_left _ (List.mem_cons_self ..)

theorem collSig_map (c : Semantics) : c.collSig .map Srt.map = mapColl := by
  simp [Semantics.collSig, Semantics.collOf, Semantics.allColls, List.find?_append, builtinColls, mapColl]

theorem collOf_map (c : Semantics) : c.collOf Srt.map = some mapColl := by
  simp [Semantics.collOf, Semantics.allColls, List.find?_append, builtinColls, mapColl]

theorem noInst_reg_irs {c : Semantics} {f : Sym} (hf : f < nRegSyms) (h : instDecode? (regSymNames.getD f "") = none) :
    instDecode? (c.symName f) = none := by
  unfold Semantics.symName; rw [if_pos hf]; exact h

/-- The interpreted hooks have registry names, none of which the decoder reads as an instance. -/
theorem hookSigs_noInst_irs : ∀ k ∈ hookSigs, k.name < nRegSyms ∧ instDecode? (regSymNames.getD k.name "") = none := by
  decide +kernel

theorem hook_noInst_irs {c : Semantics} {k : CtorSig} (hk : k ∈ hookSigs) : instDecode? (c.symName k.name) = none :=
  noInst_reg_irs (hookSigs_noInst_irs k hk).1 (hookSigs_noInst_irs k hk).2

theorem noInst_mapUnit_irs (c : Semantics) : instDecode? (c.symName mapUnit) = none :=
  noInst_reg_irs (by decide) (by decide)
theorem noInst_mapElem_irs (c : Semantics) : instDecode? (c.symName mapElem) = none :=
  noInst_reg_irs (by decide) (by decide)
theorem noInst_mapConcat_irs (c : Semantics) : instDecode? (c.symName mapConcat) = none :=
  noInst_reg_irs (by decide) (by decide)

/-- A map of the library's sort: its keys sorted, its entries of KItem. -/
theorem sortOf_libMap {c : Semantics} {es : List (GroundTerm × GroundTerm)} :
    c.sortOf (.map Srt.map es) = some Srt.map ↔ keysSorted es = true ∧ c.entriesOK Srt.kitem Srt.kitem es = true := by
  simp only [Semantics.sortOf, collOf_map]
  simp [mapColl]

theorem entriesOK_cons {c : Semantics} {k v : GroundTerm} {es : List (GroundTerm × GroundTerm)} :
    c.entriesOK Srt.kitem Srt.kitem ((k, v) :: es) = true ↔
      c.sortOf k = some Srt.kitem ∧ c.sortOf v = some Srt.kitem ∧ c.entriesOK Srt.kitem Srt.kitem es = true := by
  simp [Semantics.entriesOK, Semantics.entryOK, and_assoc]

theorem keysSorted_tail {e : GroundTerm × GroundTerm} {es : List (GroundTerm × GroundTerm)}
    (h : keysSorted (e :: es) = true) : keysSorted es = true := by
  match es, h with
  | [], _ => rfl
  | _ :: _, h =>
    obtain ⟨k, v⟩ := e
    simp only [keysSorted, Bool.and_eq_true] at h
    exact h.2

section
variable {M : Type} {I : Interpretation KoreAML.Sym M}

/-- The elements the symbol named `n` gives on the elements `xs`. -/
def SymE (I : Interpretation KoreAML.Sym M) (n : String) (xs : List M) (m : M) : Prop :=
  ∃ a, I.evalSymb (.symbol n) a ∧ AppE I a xs m

theorem interp_symList {e : Valuation M} (n : String) (φs : List KoreAML.P) (xs : List M)
    (hx : All2 (fun φ x => ∀ m, φ.interpret I e m ↔ m = x) φs xs) (m : M) :
    (KoreAML.appList (KoreAML.sym (.symbol n)) φs).interpret I e m ↔ SymE I n xs m :=
  interp_appList_sing (KoreAML.sym (.symbol n)) φs xs hx m

/-- `concat(elem(φa, φb), ψ)` at singletons: an element of `concat(y, r)` for an element `y` of
`elem(a, b)`. -/
theorem interp_concatElem {e : Valuation M} (cn en : String) {φa φb ψ : KoreAML.P} {a b r : M}
    (ha : ∀ m, φa.interpret I e m ↔ m = a) (hb : ∀ m, φb.interpret I e m ↔ m = b)
    (hr : ∀ m, ψ.interpret I e m ↔ m = r) (m : M) :
    (KoreAML.appList (symP cn) [KoreAML.appList (symP en) [φa, φb], ψ]).interpret I e m ↔
      ∃ y, SymE I en [a, b] y ∧ SymE I cn [y, r] m := by
  rw [interp_appList]
  constructor
  · rintro ⟨h, hh, bs, hbs, happ⟩
    cases hbs with
    | cons hb1 hbs =>
      cases hbs with
      | cons hb2 hbs =>
        cases hbs
        rename_i y z
        have hz := (hr z).mp hb2
        subst hz
        exact ⟨y, (interp_symList en _ [a, b] (.cons ha (.cons hb .nil)) y).mp hb1, h, hh, happ⟩
  · rintro ⟨y, hy, h, hh, happ⟩
    exact ⟨h, hh, [y, r], .cons ((interp_symList en _ [a, b] (.cons ha (.cons hb .nil)) y).mpr hy)
      (.cons ((hr r).mpr rfl) .nil), happ⟩

end

section
variable {c : Semantics} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hI : I ⊧ᴵP Γ c) [OvlOK c]
include hI

theorem den_sing {v : GroundTerm} {s : Srt} (hv : c.sortOf v = some s) (e : Valuation M) :
    ∀ m, (den c v).interpret I e m ↔ m = elemOf c I v := (elemOf_spec hI hv e).1

/-- The empty map's element is the unit's. -/
theorem den_mapNil (e : Valuation M) (m : M) :
    (den c (.map Srt.map [])).interpret I e m ↔ I.evalSymb (.symbol (c.symName mapUnit)) m := by
  unfold den KoreAML.den
  rw [GroundTerm.kore, collSig_map, GroundTerm.koreEntries]
  unfold KoreAML.ap
  rw [KoreAML.tr_app0, KoreAML.trArgs_nil]
  exact Iff.rfl

omit hI in
theorem den_mapOne_eq (k v : GroundTerm) :
    den c (.map Srt.map [(k, v)]) = KoreAML.appList (symP (c.symName mapElem)) [den c k, den c v] := by
  unfold den KoreAML.den
  rw [GroundTerm.kore, collSig_map, GroundTerm.koreEntries, GroundTerm.koreEntry]
  unfold KoreAML.ap
  rw [KoreAML.tr_app0, trArgs_appList]
  rfl

omit hI in
theorem den_mapCons_eq (k v : GroundTerm) (e' : GroundTerm × GroundTerm) (es : List (GroundTerm × GroundTerm)) :
    den c (.map Srt.map ((k, v) :: e' :: es)) = KoreAML.appList (symP (c.symName mapConcat))
      [KoreAML.appList (symP (c.symName mapElem)) [den c k, den c v], den c (.map Srt.map (e' :: es))] := by
  have h2 : den c (.map Srt.map (e' :: es)) = KoreAML.tr ⟨[], []⟩ (GroundTerm.koreEntries c mapColl (e' :: es)) := by
    unfold den KoreAML.den; rw [GroundTerm.kore, collSig_map]
  rw [h2]
  unfold den KoreAML.den
  rw [GroundTerm.kore, collSig_map, GroundTerm.koreEntries.eq_3 c mapColl (k, v) (e' :: es) (List.cons_ne_nil _ _),
    GroundTerm.koreEntry]
  unfold KoreAML.ap
  rw [KoreAML.tr_app0, trArgs_appList]
  simp only [List.map_cons, List.map_nil]
  rw [KoreAML.tr_app0, trArgs_appList]
  rfl

/-- **An entry, at values**: `elem(⟦k⟧, ⟦v⟧)` is the one-entry map's element. The KORE of a
one-entry map is that application, so this is values-are-elements alone. -/
theorem elem_val {k v : GroundTerm} (hk : c.sortOf k = some Srt.kitem) (hv : c.sortOf v = some Srt.kitem) (m : M) :
    SymE I (c.symName mapElem) [elemOf c I k, elemOf c I v] m ↔ m = elemOf c I (.map Srt.map [(k, v)]) := by
  have hs : c.sortOf (.map Srt.map [(k, v)]) = some Srt.map :=
    sortOf_libMap.mpr ⟨rfl, entriesOK_cons.mpr ⟨hk, hv, rfl⟩⟩
  rw [← den_sing hI hs KoreAML.val0 m, den_mapOne_eq]
  exact (interp_symList _ _ _ (.cons (den_sing hI hk _) (.cons (den_sing hI hv _) .nil)) m).symm

/-- **Concatenation, at values**: `concat(⟦w₁⟧, ⟦w₂⟧)` is the element of their union where the
hook defines it and empty where it does not (the hook's graph in `ΓDomains`). -/
theorem concat_val {w₁ w₂ : GroundTerm} (h1 : c.sortOf w₁ = some Srt.map) (h2 : c.sortOf w₂ = some Srt.map) (m : M) :
    SymE I (c.symName mapConcat) [elemOf c I w₁, elemOf c I w₂] m ↔
      ∃ u, hook mapConcat [w₁, w₂] = some (some u) ∧ m = elemOf c I u := by
  have hD := defOK hI
  have hk : (⟨mapConcat, [Srt.map, Srt.map], Srt.map⟩ : CtorSig) ∈ hookSigs := by decide
  have hks : lookupSig hookSigs mapConcat = some ⟨mapConcat, [Srt.map, Srt.map], Srt.map⟩ := by decide
  have hws : c.sortsOf [w₁, w₂] = some [Srt.map, Srt.map] :=
    sortsOf_cons.mpr ⟨_, _, h1, sortsOf_cons.mpr ⟨_, _, h2, sortsOf_nil, rfl⟩, rfl⟩
  obtain ⟨r, hr⟩ : ∃ r, hook mapConcat [w₁, w₂] = some r := ⟨_, Exec.hook_concat_eq _⟩
  have hax := sat_dom hI (Or.inl ⟨⟨mapConcat, [Srt.map, Srt.map], Srt.map⟩, [w₁, w₂], r, hk, hws, hr,
    fun _ => silent_of_not_silentKey (silentKey_of_patternHook rfl) _, rfl⟩)
  have hgr := (KoreAML.interp_equal hD).mp (hax KoreAML.val0 default) m
  unfold KoreAML.den at hgr
  rw [tr_symApp, symHead_noInst (noInst_mapConcat_irs c)] at hgr
  rw [trArgs_appList] at hgr
  have hl : (GroundTerm.koreList c [w₁, w₂]).map (KoreAML.tr ⟨[], []⟩) = [den c w₁, den c w₂] := rfl
  rw [hl, interp_symList _ _ _ (.cons (den_sing hI h1 _) (.cons (den_sing hI h2 _) .nil)) m] at hgr
  rw [hgr]
  cases r with
  | none =>
    simp only [Pattern.interpret]
    constructor
    · intro h; exact h.elim
    · rintro ⟨u, hu, -⟩; rw [hr] at hu; cases hu
  | some u =>
    have hsu := hook_sorted (fun he => absurd he (by decide)) hks hws hr
    dsimp only
    rw [den_sing hI hsu]
    constructor
    · intro h; exact ⟨u, hr, h⟩
    · rintro ⟨u', hu', h⟩; rw [hr] at hu'; cases hu'; exact h
end


/-! ## The map axioms, read in a model -/

section
variable {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}

theorem ev_list (L : List M) (n : Nat) (m : M) :
    (Pattern.evar ⟨n⟩ : KoreAML.P).interpret I (listVal L) m ↔ m = L.getD (n - 1) default := Iff.rfl

/-- The valuation `listVal L` with the variable 6 given `a`. -/
def listVal6 (L : List M) (a : M) : Valuation M := ⟨Function.update (listVal L).evalEvar ⟨6⟩ a, (listVal L).evalSvar⟩

theorem ev_list6 (L : List M) (a : M) {n : Nat} (hn : n ≠ 6) (m : M) :
    (Pattern.evar ⟨n⟩ : KoreAML.P).interpret I (listVal6 L a) m ↔ m = L.getD (n - 1) default := by
  rw [KoreAML.interp_evar]
  unfold listVal6
  dsimp only
  rw [Function.update_noteq (by intro h; cases h; exact hn rfl)]
  exact Iff.rfl

theorem ev_list6_self (L : List M) (a : M) (m : M) :
    (Pattern.evar ⟨6⟩ : KoreAML.P).interpret I (listVal6 L a) m ↔ m = a := by
  rw [KoreAML.interp_evar]
  unfold listVal6
  dsimp only
  rw [Function.update_same]

end

section
variable {c : Semantics} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
  (hD : DefOK I) (hC : I ⊧ᴵP ΓColls c)

include hD in
theorem guard_at {e : Valuation M} {x : EVar} {s : Srt} (h : InS I (c.sortName s) (e.evalEvar x)) (m : M) :
    (x ∈∈ inSort c s : KoreAML.P).interpret I e m := by
  rw [KoreAML.interp_member hD]; exact (inS_iff e).mpr h

include hD hC

/-- `mapUnitSplitAx`, read: the parts of the unit's element under `concat` are the unit's. -/
theorem ax_unitSplit {m₁ m₂ x : M} (h1 : InS I (c.sortName Srt.map) m₁) (h2 : InS I (c.sortName Srt.map) m₂)
    (hu : I.evalSymb (.symbol (c.symName mapUnit)) x) (hx : SymE I (c.symName mapConcat) [m₁, m₂] x) :
    I.evalSymb (.symbol (c.symName mapUnit)) m₁ ∧ I.evalSymb (.symbol (c.symName mapUnit)) m₂ := by
  have hax := hC _ ⟨mapColl, mapColl_mem c, List.mem_cons_self ..⟩ (listVal [m₁, m₂]) default
  unfold mapUnitSplitAx at hax
  dsimp only at hax
  have hb := KoreAML.interp_guarded hax (fun w hw => by
    rcases mem_two hw with rfl | rfl
    · exact guard_at hD (s := Srt.map) h1 _
    · exact guard_at hD (s := Srt.map) h2 _)
  have hc := hb ((KoreAML.interp_defined hD).mpr ⟨x, by
    rw [interpret_conj]
    exact ⟨hu, (interp_symList _ _ [m₁, m₂] (.cons (ev_list [m₁, m₂] 1) (.cons (ev_list [m₁, m₂] 2) .nil)) x).mpr hx⟩⟩)
  rw [interpret_conj, KoreAML.interp_equal hD, KoreAML.interp_equal hD] at hc
  exact ⟨(hc.1 m₁).mp rfl, (hc.2 m₂).mp rfl⟩

/-- `mapElemNotUnitAx`, read: an entry's element is not the unit's. -/
theorem ax_elemNotUnit {a b x : M} (ha : InS I (c.sortName Srt.kitem) a) (hb : InS I (c.sortName Srt.kitem) b)
    (hu : I.evalSymb (.symbol (c.symName mapUnit)) x) (hx : SymE I (c.symName mapElem) [a, b] x) : False := by
  have hax := hC _ ⟨mapColl, mapColl_mem c, List.mem_cons_of_mem _ (List.mem_cons_self ..)⟩ (listVal [a, b]) default
  unfold mapElemNotUnitAx at hax
  dsimp only at hax
  have hb' := KoreAML.interp_guarded hax (fun w hw => by
    rcases mem_two hw with rfl | rfl
    · exact guard_at hD (s := Srt.kitem) ha _
    · exact guard_at hD (s := Srt.kitem) hb _)
  rw [interpret_neg] at hb'
  exact hb' ((KoreAML.interp_defined hD).mpr ⟨x, by
    rw [interpret_conj]
    exact ⟨hu, (interp_symList _ _ [a, b] (.cons (ev_list [a, b] 1) (.cons (ev_list [a, b] 2) .nil)) x).mpr hx⟩⟩)

/-- `mapElemAtomAx`, read: an entry's element is `concat(elem(a, b), r)` only for its own key and
value and the unit's `r`. -/
theorem ax_elemAtom {a b a' b' r x : M} (ha : InS I (c.sortName Srt.kitem) a) (hb : InS I (c.sortName Srt.kitem) b)
    (ha' : InS I (c.sortName Srt.kitem) a') (hb' : InS I (c.sortName Srt.kitem) b') (hr : InS I (c.sortName Srt.map) r)
    (hx1 : SymE I (c.symName mapElem) [a', b'] x)
    (hx2 : ∃ y, SymE I (c.symName mapElem) [a, b] y ∧ SymE I (c.symName mapConcat) [y, r] x) :
    a = a' ∧ b = b' ∧ I.evalSymb (.symbol (c.symName mapUnit)) r := by
  let L := [a, b, a', b', r]
  have hax := hC _ ⟨mapColl, mapColl_mem c,
    List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))⟩ (listVal L) default
  unfold mapElemAtomAx at hax
  dsimp only at hax
  have hg := KoreAML.interp_guarded hax (fun w hw => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl
    · exact guard_at hD (s := Srt.kitem) ha _
    · exact guard_at hD (s := Srt.kitem) hb _
    · exact guard_at hD (s := Srt.kitem) ha' _
    · exact guard_at hD (s := Srt.kitem) hb' _
    · exact guard_at hD (s := Srt.map) hr _)
  have hc := hg ((KoreAML.interp_defined hD).mpr ⟨x, by
    rw [interpret_conj]
    refine ⟨(interp_symList _ _ [a', b'] (.cons (ev_list L 3) (.cons (ev_list L 4) .nil)) x).mpr hx1, ?_⟩
    exact (interp_concatElem _ _ (ev_list L 1) (ev_list L 2) (ev_list L 5) x).mpr hx2⟩)
  rw [interpret_conj, interpret_conj, KoreAML.interp_equal hD, KoreAML.interp_equal hD, KoreAML.interp_equal hD] at hc
  exact ⟨((hc.1.1 a).mp rfl), ((hc.1.2 b).mp rfl), (hc.2 r).mp rfl⟩

/-- `mapDecompAx`, read: an entry of a concatenation of `m₁` and `m₂` is an entry of one of them,
and the rest is the rest of that one's concatenation with the other. -/
theorem ax_decomp {a b r m₁ m₂ x : M} (ha : InS I (c.sortName Srt.kitem) a) (hb : InS I (c.sortName Srt.kitem) b)
    (hr : InS I (c.sortName Srt.map) r) (h1 : InS I (c.sortName Srt.map) m₁) (h2 : InS I (c.sortName Srt.map) m₂)
    (hx1 : ∃ y, SymE I (c.symName mapElem) [a, b] y ∧ SymE I (c.symName mapConcat) [y, r] x)
    (hx2 : SymE I (c.symName mapConcat) [m₁, m₂] x) :
    (∃ y, InS I (c.sortName Srt.map) y ∧
      (∀ z, z = m₁ ↔ ∃ y', SymE I (c.symName mapElem) [a, b] y' ∧ SymE I (c.symName mapConcat) [y', y] z) ∧
      ∀ z, z = r ↔ SymE I (c.symName mapConcat) [y, m₂] z) ∨
    (∃ y, InS I (c.sortName Srt.map) y ∧
      (∀ z, z = m₂ ↔ ∃ y', SymE I (c.symName mapElem) [a, b] y' ∧ SymE I (c.symName mapConcat) [y', y] z) ∧
      ∀ z, z = r ↔ SymE I (c.symName mapConcat) [m₁, y] z) := by
  let L := [a, b, r, m₁, m₂]
  have hax := hC _ ⟨mapColl, mapColl_mem c,
    List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))⟩ (listVal L) default
  unfold mapDecompAx at hax
  dsimp only at hax
  have hg := KoreAML.interp_guarded hax (fun w hw => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl
    · exact guard_at hD (s := Srt.kitem) ha _
    · exact guard_at hD (s := Srt.kitem) hb _
    · exact guard_at hD (s := Srt.map) hr _
    · exact guard_at hD (s := Srt.map) h1 _
    · exact guard_at hD (s := Srt.map) h2 _)
  have hc := hg ((KoreAML.interp_defined hD).mpr ⟨x, by
    rw [interpret_conj]
    refine ⟨(interp_concatElem _ _ (ev_list L 1) (ev_list L 2) (ev_list L 3) x).mpr hx1, ?_⟩
    exact (interp_symList _ _ [m₁, m₂] (.cons (ev_list L 4) (.cons (ev_list L 5) .nil)) x).mpr hx2⟩)
  rw [interpret_disj, KoreAML.interp_sExists, KoreAML.interp_sExists] at hc
  have hy : ∀ y : M, ((⟨6⟩ : EVar) ∈∈ KoreAML.inhOf (sortP (c.sortName Srt.map)) : KoreAML.P).interpret I (listVal6 L y)
      default → InS I (c.sortName Srt.map) y := fun y h => by
    rw [KoreAML.interp_member hD] at h
    have h' := (inS_iff _).mp h
    unfold listVal6 at h'
    simpa using h'
  rcases hc with ⟨y, hym, hyb⟩ | ⟨y, hym, hyb⟩
  · left
    have hyb' : (_ : KoreAML.P).interpret I (listVal6 L y) default := hyb
    rw [interpret_conj, KoreAML.interp_equal hD, KoreAML.interp_equal hD] at hyb'
    refine ⟨y, hy y hym, fun z => ?_, fun z => ?_⟩
    · exact (ev_list6 L y (n := 4) (by decide) z).symm.trans ((hyb'.1 z).trans
        (interp_concatElem _ _ (ev_list6 L y (n := 1) (by decide)) (ev_list6 L y (n := 2) (by decide))
          (ev_list6_self L y) z))
    · exact (ev_list6 L y (n := 3) (by decide) z).symm.trans ((hyb'.2 z).trans
        (interp_symList _ _ [y, m₂] (.cons (ev_list6_self L y) (.cons (ev_list6 L y (n := 5) (by decide)) .nil)) z))
  · right
    have hyb' : (_ : KoreAML.P).interpret I (listVal6 L y) default := hyb
    rw [interpret_conj, KoreAML.interp_equal hD, KoreAML.interp_equal hD] at hyb'
    refine ⟨y, hy y hym, fun z => ?_, fun z => ?_⟩
    · exact (ev_list6 L y (n := 5) (by decide) z).symm.trans ((hyb'.1 z).trans
        (interp_concatElem _ _ (ev_list6 L y (n := 1) (by decide)) (ev_list6 L y (n := 2) (by decide))
          (ev_list6_self L y) z))
    · exact (ev_list6 L y (n := 3) (by decide) z).symm.trans ((hyb'.2 z).trans
        (interp_symList _ _ [m₁, y] (.cons (ev_list6 L y (n := 4) (by decide)) (.cons (ev_list6_self L y) .nil)) z))

end


/-! ## A value's element under a map pattern symbol -/

/-- The library's `Map` is not a token or byte sort of the library, so a value of it is a map.
Decidable on the data; `Hyp` does not give it. -/
def mapSortOK (c : Semantics) : Bool := !c.lib.tokenSorts.contains Srt.map && !c.lib.byteSorts.contains Srt.map

theorem map_shape {c : Semantics} (hg : genWf c = true) [OvlOK c] (hmo : mapSortOK c = true) {w : GroundTerm}
    (hw : c.sortOf w = some Srt.map) : ∃ es, w = .map Srt.map es := by
  have hnc : Srt.map ∉ consSorts c := fun h => by
    have := (genWf_cons hg h).2.2.2.2.2.2
    rw [collOf_map] at this; cases this
  cases w with
  | ctor f ts =>
    exact absurd (ctor_sort_cons hg hw) hnc
  | inj a b t =>
    obtain ⟨hab, -, -, rfl⟩ := sortOf_inj.mp hw
    exact absurd (genWf_sub hg hab).1 hnc
  | dv s lit =>
    obtain ⟨hok, rfl⟩ := sortOf_dv.mp hw
    rw [dvOK_self (Lib.carrier_of_lt _ (by decide))] at hok
    unfold mapSortOK at hmo
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hmo
    exfalso
    cases lit with
    | int i => simp only [dvOK, beq_iff_eq] at hok; exact absurd hok (by decide)
    | bool b => simp only [dvOK, beq_iff_eq] at hok; exact absurd hok (by decide)
    | tok t =>
      simp only [dvOK, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hok
      rcases hok with ((h | h) | h) | ⟨h | h, -⟩
      · exact absurd h (by decide)
      · exact absurd h (by decide)
      · rw [hmo.1] at h; cases h
      · exact absurd h (by decide)
      · rw [hmo.2] at h; cases h
    | float _ _ _ => simp only [dvOK, Bool.and_eq_true, beq_iff_eq] at hok; exact absurd hok.1 (by decide)
  | map s es =>
    obtain ⟨k, -, -, -, -, -, -, rfl⟩ := sortOf_mapS_fwd hw
    exact ⟨es, rfl⟩
  | set s es =>
    obtain ⟨k, hk, hkind, -, -, rfl⟩ := sortOf_setS.mp hw
    rw [collOf_map] at hk; cases hk
    exact absurd hkind (by decide)
  | list s es =>
    obtain ⟨k, hk, hkind, -, rfl⟩ := sortOf_listS.mp hw
    rw [collOf_map] at hk; cases hk
    exact absurd hkind (by decide)

section
variable {c : Semantics} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hI : I ⊧ᴵP Γ c) [OvlOK c]

include hI in
/-- A map's element, its first entry split off: `concat(elem(⟦k⟧, ⟦v⟧), ⟦rest⟧)` holds it. -/
theorem map_first {k v : GroundTerm} {es : List (GroundTerm × GroundTerm)}
    (hs : c.sortOf (.map Srt.map ((k, v) :: es)) = some Srt.map) :
    ∃ y, SymE I (c.symName mapElem) [elemOf c I k, elemOf c I v] y ∧
      SymE I (c.symName mapConcat) [y, elemOf c I (.map Srt.map es)] (elemOf c I (.map Srt.map ((k, v) :: es))) := by
  obtain ⟨hks, hok⟩ := sortOf_libMap.mp hs
  obtain ⟨hk, hv, hrest⟩ := entriesOK_cons.mp hok
  have hsr : c.sortOf (.map Srt.map es) = some Srt.map := sortOf_libMap.mpr ⟨keysSorted_tail hks, hrest⟩
  cases es with
  | nil =>
    have h1 : c.sortOf (.map Srt.map [(k, v)]) = some Srt.map := hs
    refine ⟨_, (elem_val hI hk hv _).mpr rfl, (concat_val hI h1 hsr _).mpr ⟨_, ?_, rfl⟩⟩
    rw [Exec.hook_concat_eq]
    simp [union, addNew, hasKey, insertE]
  | cons e' es =>
    have hx := (den_sing hI hs KoreAML.val0 _).mpr rfl
    rw [den_mapCons_eq] at hx
    exact (interp_concatElem _ _ (den_sing hI hk _) (den_sing hI hv _) (den_sing hI hsr _) _).mp hx

include hI in
/-- The unit holds no value's element but the empty map's. -/
theorem map_unit (hg : genWf c = true) [OvlOK c] (htr : ∀ a b d, (a, b) ∈ c.subsorts → (b, d) ∈ c.subsorts → (a, d) ∈ c.subsorts)
    {w : GroundTerm} (hw : c.sortOf w = some Srt.map) (hu : I.evalSymb (.symbol (c.symName mapUnit)) (elemOf c I w)) :
    w = .map Srt.map [] := by
  have h0 : c.sortOf (.map Srt.map []) = some Srt.map := sortOf_libMap.mpr ⟨rfl, rfl⟩
  have he := (den_sing hI h0 KoreAML.val0 _).mp ((den_mapNil hI KoreAML.val0 _).mpr hu)
  exact values_apart hI hg htr (apartSort_of_sorted hg hw) hw h0 he

variable (hC : I ⊧ᴵP ΓColls c) (hg : genWf c = true) [OvlOK c]
  (htr : ∀ a b d, (a, b) ∈ c.subsorts → (b, d) ∈ c.subsorts → (a, d) ∈ c.subsorts)
include hI hC hg htr

/-- **Splitting a value's element.** If a map's element is in `concat(m₁, m₂)`, for elements `m₁`,
`m₂` of Map, they are maps' elements. By induction on the map's entries: the empty map's parts are
units (`mapUnitSplitAx`); a map's first entry is in one of the parts (`mapDecompAx`), the rest
splits by induction, and that part is its rest with the entry added (the graph of `_Map_`). -/
theorem map_split : ∀ (es : List (GroundTerm × GroundTerm)), c.sortOf (.map Srt.map es) = some Srt.map →
    ∀ {m₁ m₂ : M}, InS I (c.sortName Srt.map) m₁ → InS I (c.sortName Srt.map) m₂ →
    SymE I (c.symName mapConcat) [m₁, m₂] (elemOf c I (.map Srt.map es)) →
    ∃ w₁ w₂, c.sortOf w₁ = some Srt.map ∧ c.sortOf w₂ = some Srt.map ∧ m₁ = elemOf c I w₁ ∧ m₂ = elemOf c I w₂
  | [], hs, m₁, m₂, h1, h2, hx => by
    have hD := defOK hI
    have hu := (den_mapNil hI KoreAML.val0 _).mp ((den_sing hI hs KoreAML.val0 _).mpr rfl)
    obtain ⟨u1, u2⟩ := ax_unitSplit hD hC h1 h2 hu hx
    exact ⟨_, _, hs, hs, (den_sing hI hs KoreAML.val0 _).mp ((den_mapNil hI KoreAML.val0 _).mpr u1),
      (den_sing hI hs KoreAML.val0 _).mp ((den_mapNil hI KoreAML.val0 _).mpr u2)⟩
  | (k, v) :: es, hs, m₁, m₂, h1, h2, hx => by
    have hD := defOK hI
    obtain ⟨hks, hok⟩ := sortOf_libMap.mp hs
    obtain ⟨hk, hv, hrest⟩ := entriesOK_cons.mp hok
    have hsr : c.sortOf (.map Srt.map es) = some Srt.map := sortOf_libMap.mpr ⟨keysSorted_tail hks, hrest⟩
    have h1s : c.sortOf (.map Srt.map [(k, v)]) = some Srt.map := sortOf_libMap.mpr ⟨rfl, entriesOK_cons.mpr ⟨hk, hv, rfl⟩⟩
    have hkS : InS I (c.sortName Srt.kitem) (elemOf c I k) := (elemOf_spec hI hk KoreAML.val0).2
    have hvS : InS I (c.sortName Srt.kitem) (elemOf c I v) := (elemOf_spec hI hv KoreAML.val0).2
    have hrS : InS I (c.sortName Srt.map) (elemOf c I (.map Srt.map es)) := (elemOf_spec hI hsr KoreAML.val0).2
    have hks' : lookupSig hookSigs mapConcat = some ⟨mapConcat, [Srt.map, Srt.map], Srt.map⟩ := by decide
    have hsorts : ∀ {u₁ u₂ : GroundTerm}, c.sortOf u₁ = some Srt.map → c.sortOf u₂ = some Srt.map →
        c.sortsOf [u₁, u₂] = some [Srt.map, Srt.map] := fun h1 h2 =>
      sortsOf_cons.mpr ⟨_, _, h1, sortsOf_cons.mpr ⟨_, _, h2, sortsOf_nil, rfl⟩, rfl⟩
    rcases ax_decomp hD hC hkS hvS hrS h1 h2 (map_first hI hs) hx with ⟨y, hy, hm, hr⟩ | ⟨y, hy, hm, hr⟩
    · obtain ⟨u₁, u₂, hu₁, hu₂, rfl, rfl⟩ := map_split es hsr hy h2 ((hr _).mp rfl)
      obtain ⟨y', hy', hc⟩ := (hm m₁).mp rfl
      rw [(elem_val hI hk hv y').mp hy'] at hc
      obtain ⟨u, hu, rfl⟩ := (concat_val hI h1s hu₁ m₁).mp hc
      exact ⟨u, u₂, hook_sorted (fun he => absurd he (by decide)) hks' (hsorts h1s hu₁) hu, hu₂, rfl, rfl⟩
    · obtain ⟨u₁, u₂, hu₁, hu₂, rfl, rfl⟩ := map_split es hsr h1 hy ((hr _).mp rfl)
      obtain ⟨y', hy', hc⟩ := (hm m₂).mp rfl
      rw [(elem_val hI hk hv y').mp hy'] at hc
      obtain ⟨u, hu, rfl⟩ := (concat_val hI h1s hu₂ m₂).mp hc
      exact ⟨u₁, u, hu₁, hook_sorted (fun he => absurd he (by decide)) hks' (hsorts h1s hu₂) hu, rfl, rfl⟩

/-- **An entry holding a value's element.** If a map's element is in `elem(a, b)`, for elements
`a`, `b` of KItem, the map has one entry, whose key's and value's elements `a` and `b` are
(`mapElemNotUnitAx`, `mapElemAtomAx`). -/
theorem map_elem : ∀ (es : List (GroundTerm × GroundTerm)), c.sortOf (.map Srt.map es) = some Srt.map →
    ∀ {a b : M}, InS I (c.sortName Srt.kitem) a → InS I (c.sortName Srt.kitem) b →
    SymE I (c.symName mapElem) [a, b] (elemOf c I (.map Srt.map es)) →
    ∃ k v, es = [(k, v)] ∧ c.sortOf k = some Srt.kitem ∧ c.sortOf v = some Srt.kitem ∧
      a = elemOf c I k ∧ b = elemOf c I v
  | [], hs, a, b, ha, hb, hx => by
    have hD := defOK hI
    have hu := (den_mapNil hI KoreAML.val0 _).mp ((den_sing hI hs KoreAML.val0 _).mpr rfl)
    exact (ax_elemNotUnit hD hC ha hb hu hx).elim
  | (k, v) :: es, hs, a, b, ha, hb, hx => by
    have hD := defOK hI
    obtain ⟨hks, hok⟩ := sortOf_libMap.mp hs
    obtain ⟨hk, hv, hrest⟩ := entriesOK_cons.mp hok
    have hsr : c.sortOf (.map Srt.map es) = some Srt.map := sortOf_libMap.mpr ⟨keysSorted_tail hks, hrest⟩
    have hkS : InS I (c.sortName Srt.kitem) (elemOf c I k) := (elemOf_spec hI hk KoreAML.val0).2
    have hvS : InS I (c.sortName Srt.kitem) (elemOf c I v) := (elemOf_spec hI hv KoreAML.val0).2
    have hrS : InS I (c.sortName Srt.map) (elemOf c I (.map Srt.map es)) := (elemOf_spec hI hsr KoreAML.val0).2
    obtain ⟨h1, h2, h3⟩ := ax_elemAtom hD hC hkS hvS ha hb hrS hx (map_first hI hs)
    have hnil := map_unit hI hg htr hsr h3
    cases hnil
    exact ⟨k, v, rfl, hk, hv, h1.symm, h2.symm⟩

variable (hmo : mapSortOK c = true)
include hmo

/-- **A map pattern symbol holding a value's element.** If a value's element is what a map pattern
symbol gives on elements of its argument sorts, the elements are values', on which the symbol's
hook gives the value. -/
theorem hook_back {f : Sym} {k : CtorSig} (hp : patternHooks.contains f = true) (hks : lookupSig hookSigs f = some k)
    {w : GroundTerm} (hw : c.sortOf w = some k.result) {bs : List M} (hbl : bs.length = (k.args.map c.sortName).length)
    (hbs : ∀ (i : Nat) x s, bs[i]? = some x → (k.args.map c.sortName)[i]? = some s → InS I s x)
    (hm : SymE I (c.symName f) bs (elemOf c I w)) :
    ∃ ws, c.sortsOf ws = some k.args ∧ bs = ws.map (elemOf c I) ∧ hook f ws = some (some w) := by
  rcases Exec.patternHooks_cases hp with rfl | rfl | rfl
  · rw [show lookupSig hookSigs mapUnit = some ⟨mapUnit, [], Srt.map⟩ by decide] at hks; cases hks
    match bs, hbl with
    | [], _ =>
      obtain ⟨a, ha, rfl⟩ := hm
      have := map_unit hI hg htr hw ha
      subst this
      exact ⟨[], sortsOf_nil, rfl, rfl⟩
  · rw [show lookupSig hookSigs mapElem = some ⟨mapElem, [Srt.kitem, Srt.kitem], Srt.map⟩ by decide] at hks; cases hks
    match bs, hbl with
    | [b₁, b₂], _ =>
      obtain ⟨es, rfl⟩ := map_shape hg hmo hw
      obtain ⟨kk, vv, rfl, hkk, hvv, rfl, rfl⟩ := map_elem hI hC hg htr es hw (hbs 0 b₁ _ rfl rfl) (hbs 1 b₂ _ rfl rfl) hm
      exact ⟨[kk, vv], sortsOf_cons.mpr ⟨_, _, hkk, sortsOf_cons.mpr ⟨_, _, hvv, sortsOf_nil, rfl⟩, rfl⟩, rfl, rfl⟩
  · rw [show lookupSig hookSigs mapConcat = some ⟨mapConcat, [Srt.map, Srt.map], Srt.map⟩ by decide] at hks; cases hks
    match bs, hbl with
    | [b₁, b₂], _ =>
      obtain ⟨es, rfl⟩ := map_shape hg hmo hw
      obtain ⟨w₁, w₂, hw₁, hw₂, rfl, rfl⟩ := map_split hI hC hg htr es hw (hbs 0 b₁ _ rfl rfl) (hbs 1 b₂ _ rfl rfl) hm
      obtain ⟨u, hu, he⟩ := (concat_val hI hw₁ hw₂ _).mp hm
      have hws : c.sortsOf [w₁, w₂] = some [Srt.map, Srt.map] :=
        sortsOf_cons.mpr ⟨_, _, hw₁, sortsOf_cons.mpr ⟨_, _, hw₂, sortsOf_nil, rfl⟩, rfl⟩
      have hsu := hook_sorted (fun he => absurd he (by decide)) (show lookupSig hookSigs mapConcat = some ⟨mapConcat, [Srt.map, Srt.map], Srt.map⟩ by decide) hws hu
      have := values_apart hI hg htr (apartSort_of_sorted hg hw) hw hsu he
      subst this
      exact ⟨[w₁, w₂], hws, rfl, hu⟩

end


/-! ## Map patterns read downwards -/

mutual
  /-- A pattern of constructors, injections, aliases, variables, domain values and the map pattern
  symbols (`.Map`, `|->`, `_Map_`). -/
  def mapPat (c : Semantics) : Term → Bool
    | .var _ => true
    | .dv _ _ => true
    | .app f ts => (c.isCtor f || patternHooks.contains f) && mapPats c ts
    | .inj _ _ t => mapPat c t
    | .as t _ => mapPat c t
    termination_by structural t => t
  def mapPats (c : Semantics) : List Term → Bool
    | [] => true
    | t :: ts => mapPat c t && mapPats c ts
    termination_by structural ts => ts
end

mutual
  theorem mapPat_of_plain {c : Semantics} : ∀ {t : Term}, plainPat c t = true → mapPat c t = true
    | .var _, _ => rfl
    | .dv _ _, _ => rfl
    | .app f ts, h => by
      rw [plainPat] at h; rw [mapPat]
      simp only [Bool.and_eq_true] at h ⊢
      exact ⟨by simp [h.1.1], mapPats_of_plain h.2⟩
    | .inj _ _ t, h => by rw [plainPat] at h; rw [mapPat]; exact mapPat_of_plain h
    | .as t _, h => by rw [plainPat] at h; rw [mapPat]; exact mapPat_of_plain h
  theorem mapPats_of_plain {c : Semantics} : ∀ {ts : List Term}, plainPats c ts = true → mapPats c ts = true
    | [], _ => rfl
    | t :: ts, h => by
      rw [plainPats] at h; rw [mapPats]
      simp only [Bool.and_eq_true] at h ⊢
      exact ⟨mapPat_of_plain h.1, mapPats_of_plain h.2⟩
end

theorem noInst_patHook_irs {c : Semantics} {f : Sym} (hp : patternHooks.contains f = true) :
    instDecode? (c.symName f) = none := by
  rcases Exec.patternHooks_cases hp with rfl | rfl | rfl
  · exact noInst_mapUnit_irs c
  · exact noInst_mapElem_irs c
  · exact noInst_mapConcat_irs c

theorem symHead_patHook {c : Semantics} {f : Sym} (hp : patternHooks.contains f = true) :
    symHead c f = KoreAML.sym (.symbol (c.symName f)) :=
  symHead_noInst (noInst_patHook_irs hp)

section
variable {c : Semantics} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}

/-- G-arity of an interpreted hooked symbol, at elements of its argument sorts. -/
theorem hook_arity (hI : I ⊧ᴵP Γ c) [OvlOK c] {f : Sym} {k : CtorSig} (hk : lookupSig hookSigs f = some k)
    (hit0 : instDecode? (c.symName f) = none) {bs : List M} (hbl : bs.length = (k.args.map c.sortName).length)
    (hbs : ∀ (i : Nat) x s, bs[i]? = some x → (k.args.map c.sortName)[i]? = some s → InS I s x) {m : M}
    (hm : SymE I (c.symName f) bs m) : InS I (c.sortName k.result) m := by
  have hD := defOK hI
  obtain ⟨hkm, hkn⟩ := lookupSig_spec hk
  have hit := sat_sigItem hI (sig_arity (c := c) (k := k) (List.mem_append_left _ (List.mem_append_right _ hkm)))
  rw [symArityItem_plain_irs (fun _ => symApp_noInst (by rw [hkn]; exact hit0))] at hit
  have hinc := (KoreAML.interp_included hD).mp (hit KoreAML.val0 default) m
  apply hinc
  obtain ⟨a, ha, hm⟩ := hm
  rw [interp_appList]
  refine ⟨a, by rw [hkn]; exact ha, bs, ?_, hm⟩
  clear ha hm hinc hit
  have : ∀ (ss : List Srt) (bs : List M), bs.length = (ss.map c.sortName).length →
      (∀ (i : Nat) x s, bs[i]? = some x → (ss.map c.sortName)[i]? = some s → InS I s x) →
      All2 (fun φ b => φ.interpret I KoreAML.val0 b)
        (ss.map fun s => KoreAML.inhOf (sortP (c.sortName s))) bs := by
    intro ss
    induction ss with
    | nil => intro bs hl _; cases bs with
      | nil => exact .nil
      | cons _ _ => simp at hl
    | cons s ss ih =>
      intro bs hl hb
      cases bs with
      | nil => simp at hl
      | cons b bs =>
        refine .cons ?_ (ih bs (by simpa using hl) (fun i x s' h1 h2 => hb (i + 1) x s' (by simpa using h1) (by simpa using h2)))
        exact hb 0 b (c.sortName s) rfl rfl
  exact this k.args bs hbl hbs

end

section
variable {c : Semantics} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hI : I ⊧ᴵP Γ c) [OvlOK c]
  (hph : patHooksApart c = true) (hmo : mapSortOK c = true) (hg : genWf c = true)
  (htr : ∀ a b d, (a, b) ∈ c.subsorts → (b, d) ∈ c.subsorts → (a, d) ∈ c.subsorts)
  (hnm : NamesPlain c) {vars : List Srt} {vs : List KoreAML.Var} {tbl : VarTable} {e : Valuation M}
  (hvs : vs.length = vars.length)
  (hin : ∀ i < vars.length, InS I (c.sortName (vars.getD i 0)) (e.evalEvar (tbl.ev (keyAt vs i))))
include hI hph hmo hg htr hnm hvs hin

mutual
  /-- The elements of a pattern's translation, map pattern symbols included, at a valuation of its
  variables in their sorts, lie in the pattern's sort (the G-arity of the symbols). -/
  theorem patSort4 : ∀ {p : Term} {s : Srt}, mapPat c p = true → sortOfTerm c.patCtxAll vars p = some s →
      ∀ m, (KoreAML.tr ⟨tbl, []⟩ (Term.kore c vs p)).interpret I e m → InS I (c.sortName s) m
    | .var i, s, _, ht, m, hm => by
      have hi := sortOfTerm_var.mp ht
      have hlt : i < vars.length := (List.getElem?_eq_some_iff.mp hi).1
      rw [tr_var] at hm
      rw [hm]
      have := hin i hlt
      rwa [List.getD_eq_getElem?_getD, hi, Option.getD_some] at this
    | .dv s' lit, s, _, ht, m, hm => by
      obtain ⟨hok, rfl⟩ := sortOfTerm_dv.mp ht
      rw [tr_kore_dv hI hg htr hnm hvs hin] at hm
      have hs := elemOf_spec hI (sortOf_dv.mpr ⟨hok, rfl⟩) e
      rw [(hs.1 m).mp hm]
      exact (inS_iff _).mp hs.2
    | .app f ps, s, hp, ht, m, hm => by
      obtain ⟨k, hk', hargs, rfl⟩ := sortOfTerm_app.mp ht
      rw [mapPat] at hp
      simp only [Bool.and_eq_true, Bool.or_eq_true] at hp
      obtain ⟨hc | hph', hps⟩ := hp
      · obtain ⟨k0, hk0⟩ := Option.isSome_iff_exists.mp hc
        have hkk := lookup_patCtxAll hk0 hk'
        subst hkk
        rw [kore_app_plain hnm hk0, trArgs_appList, interp_appList] at hm
        obtain ⟨a, ha, bs, hbs, hm⟩ := hm
        have hsorts := patSorts4 hps hargs hbs
        exact ctor_arity hI hnm hk0 hsorts.1 hsorts.2 ⟨a, by
          show (KoreAML.sym (.symbol (c.symName k.name))).interpret I KoreAML.val0 a
          rw [(lookupSig_spec hk0).2]; exact ha, hm⟩
      · have hks := patAll_lookup_hook hph hph' hk'
        rw [kore_app, tr_symApp, symHead_patHook hph', trArgs_appList, interp_appList] at hm
        obtain ⟨a, ha, bs, hbs, hm⟩ := hm
        have hsorts := patSorts4 hps hargs hbs
        exact hook_arity hI hks (noInst_patHook_irs hph') hsorts.1 hsorts.2 ⟨a, ha, hm⟩
    | .inj a b p, s, hp, ht, m, hm => by
      obtain ⟨hab, ht', rfl⟩ := sortOfTerm_inj.mp ht
      rw [mapPat] at hp
      rw [Term.kore, KoreAML.tr_injP, interp_injApp] at hm
      obtain ⟨x, hx, hm⟩ := hm
      have hxs := patSort4 hp ht' x hx
      obtain ⟨y, hy, hys⟩ := gen_fun hI (genWf_sub hg hab).1 (gensF_inj hab) rfl (xs := [x]) rfl (single_sorts hxs)
      rw [(hys m).mp hm]; exact hy
    | .as p i, s, hp, ht, m, hm => by
      obtain ⟨-, ht'⟩ := Exec.sortOfTerm_as ht
      rw [mapPat] at hp
      rw [tr_kore_as hI hg htr hnm hvs hin] at hm
      exact patSort4 hp ht' m hm.1
  theorem patSorts4 : ∀ {ps : List Term} {ss : List Srt} {bs : List M}, mapPats c ps = true →
      sortsOfTerms c.patCtxAll vars ps = some ss →
      All2 (fun φ b => φ.interpret I e b) ((Term.koreList c vs ps).map (KoreAML.tr ⟨tbl, []⟩)) bs →
      bs.length = (ss.map c.sortName).length ∧
        ∀ (i : Nat) x s, bs[i]? = some x → (ss.map c.sortName)[i]? = some s → InS I s x
    | [], ss, bs, _, ht, hbs => by
      rw [sortsOfTerms_nil.mp ht]
      rw [Term.koreList] at hbs
      cases hbs
      exact ⟨rfl, fun i x s h _ => by simp at h⟩
    | p :: ps, ss, bs, hp, ht, hbs => by
      obtain ⟨s, ss', h1, h2, rfl⟩ := sortsOfTerms_cons.mp ht
      rw [mapPats] at hp
      simp only [Bool.and_eq_true] at hp
      rw [Term.koreList, List.map_cons] at hbs
      cases hbs with
      | cons hb hbs =>
        have ih := patSorts4 hp.2 h2 hbs
        refine ⟨by simp [ih.1], fun i x s' hx hs' => ?_⟩
        cases i with
        | zero =>
          simp at hx hs'; subst hx; subst hs'
          exact patSort4 hp.1 h1 _ hb
        | succ i => exact ih.2 i x s' (by simpa using hx) (by simpa using hs')
end

end

section
variable {c : Semantics} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hI : I ⊧ᴵP Γ c) [OvlOK c]
  (hC : I ⊧ᴵP ΓColls c) (hph : patHooksApart c = true) (hmo : mapSortOK c = true) (hg : genWf c = true)
  (htr : ∀ a b d, (a, b) ∈ c.subsorts → (b, d) ∈ c.subsorts → (a, d) ∈ c.subsorts)
  (hnm : NamesPlain c) {vars : List Srt} {vs : List KoreAML.Var} {tbl : VarTable} {e : Valuation M}
  (hvs : vs.length = vars.length)
  (hin : ∀ i < vars.length, InS I (c.sortName (vars.getD i 0)) (e.evalEvar (tbl.ev (keyAt vs i))))
include hI hC hph hmo hg htr hnm hvs hin

mutual
  /-- **Map patterns, downwards, in a model of `Γ`.** If the element of a value of a
  pattern's sort lies in the pattern's translation, map pattern symbols included, at a valuation of
  its variables in their sorts, the pattern denotes the value under the valuation's substitution,
  and the valuation gives each of the pattern's variables the element of a value of its sort. A
  map pattern symbol is read through `hook_back`: the parts of a value's element under it are
  values' elements, on which the symbol's hook gives the value. -/
  theorem patVal_back4 : ∀ {p : Term} {s : Srt} {w : GroundTerm}, mapPat c p = true →
      sortOfTerm c.patCtxAll vars p = some s → c.sortOf w = some s →
      (KoreAML.tr ⟨tbl, []⟩ (Term.kore c vs p)).interpret I e (elemOf c I w) →
      PatVal c (substOf c I tbl vs vars e) p w ∧ ∀ i ∈ varOccs p, Witnessed c I tbl vs vars e i
    | .var i, s, w, _, ht, hw, hm => by
      rw [tr_var] at hm
      refine ⟨.var (substOf_var hI hg htr hnm hvs hin (sortOfTerm_var.mp ht) hw hm), fun j hj => ?_⟩
      rw [varOccs] at hj
      rw [mem_one hj]
      exact witnessed_of (sortOfTerm_var.mp ht) hw hm
    | .dv s' lit, s, w, _, ht, hw, hm => by
      obtain ⟨hok, hs⟩ := sortOfTerm_dv.mp ht
      subst hs
      rw [tr_kore_dv hI hg htr hnm hvs hin] at hm
      have hdv : c.sortOf (.dv s lit) = some s := sortOf_dv.mpr ⟨hok, rfl⟩
      have h1 := ((elemOf_spec hI hdv e).1 _).mp hm
      rw [values_apart hI hg htr (apartSort_of_sorted hg hw) hw hdv h1]
      exact ⟨.dv, fun j hj => by rw [varOccs] at hj; cases hj⟩
    | .app f ps, s, w, hp, ht, hw, hm => by
      obtain ⟨k, hk', hargs, rfl⟩ := sortOfTerm_app.mp ht
      rw [mapPat] at hp
      simp only [Bool.and_eq_true, Bool.or_eq_true] at hp
      obtain ⟨hc | hph', hps⟩ := hp
      · obtain ⟨k0, hk0⟩ := Option.isSome_iff_exists.mp hc
        have hkk := lookup_patCtxAll hk0 hk'
        subst hkk
        rw [kore_app_plain hnm hk0, trArgs_appList, interp_appList] at hm
        obtain ⟨a, ha, bs, hbs, hm⟩ := hm
        have hsorts := patSorts4 hI hph hmo hg htr hnm hvs hin hps hargs hbs
        obtain ⟨ws, rfl, hws, rfl⟩ := ctor_back hI hg htr hk0 hw hsorts.1 hsorts.2 ⟨a, by
          show (KoreAML.sym (.symbol (c.symName k.name))).interpret I KoreAML.val0 a
          rw [(lookupSig_spec hk0).2]; exact ha, hm⟩
        have ih := patVals_back4 hps hargs hws hbs
        exact ⟨.ctor hc ih.1, fun j hj => ih.2 j (by rw [varOccs] at hj; exact hj)⟩
      · have hks := patAll_lookup_hook hph hph' hk'
        rw [kore_app, tr_symApp, symHead_patHook hph', trArgs_appList, interp_appList] at hm
        obtain ⟨a, ha, bs, hbs, hm⟩ := hm
        have hsorts := patSorts4 hI hph hmo hg htr hnm hvs hin hps hargs hbs
        obtain ⟨ws, hws, rfl, hv⟩ := hook_back hI hC hg htr hmo hph' hks hw hsorts.1 hsorts.2 ⟨a, ha, hm⟩
        have ih := patVals_back4 hps hargs hws hbs
        exact ⟨.hook hph' ih.1 hv, fun j hj => ih.2 j (by rw [varOccs] at hj; exact hj)⟩
    | .inj a b p, s, w, hp, ht, hw, hm => by
      obtain ⟨hab, ht', rfl⟩ := sortOfTerm_inj.mp ht
      rw [mapPat] at hp
      rw [Term.kore, KoreAML.tr_injP, interp_injApp] at hm
      obtain ⟨x, hx, hm⟩ := hm
      have hxs := patSort4 hI hph hmo hg htr hnm hvs hin hp ht' x hx
      obtain ⟨w', hw', rfl, rfl⟩ := inj_back hI hg htr w hab hw hxs hm
      have ih := patVal_back4 hp ht' hw' hx
      exact ⟨.inj ih.1, fun j hj => ih.2 j (by rw [varOccs] at hj; exact hj)⟩
    | .as p i, s, w, hp, ht, hw, hm => by
      obtain ⟨hvi, ht'⟩ := Exec.sortOfTerm_as ht
      rw [mapPat] at hp
      rw [tr_kore_as hI hg htr hnm hvs hin] at hm
      have ih := patVal_back4 hp ht' hw hm.1
      refine ⟨.as ih.1 (substOf_var hI hg htr hnm hvs hin hvi hw hm.2), fun j hj => ?_⟩
      rw [varOccs] at hj
      rcases List.mem_append.mp hj with hj | hj
      · exact ih.2 j hj
      · rw [mem_one hj]; exact witnessed_of hvi hw hm.2
  theorem patVals_back4 : ∀ {ps : List Term} {ss : List Srt} {ws : List GroundTerm}, mapPats c ps = true →
      sortsOfTerms c.patCtxAll vars ps = some ss → c.sortsOf ws = some ss →
      All2 (fun φ b => φ.interpret I e b) ((Term.koreList c vs ps).map (KoreAML.tr ⟨tbl, []⟩)) (ws.map (elemOf c I)) →
      PatVals c (substOf c I tbl vs vars e) ps ws ∧ ∀ i ∈ varOccsList ps, Witnessed c I tbl vs vars e i
    | [], ss, ws, _, ht, hws, _ => by
      rw [sortsOfTerms_nil.mp ht] at hws
      rw [sortsOf_nil_eq hws]
      exact ⟨.nil, fun j hj => by rw [varOccsList] at hj; cases hj⟩
    | p :: ps, ss, ws, hp, ht, hws, hbs => by
      obtain ⟨s, ss', h1, h2, rfl⟩ := sortsOfTerms_cons.mp ht
      rw [mapPats] at hp
      simp only [Bool.and_eq_true] at hp
      cases ws with
      | nil => rw [sortsOf_nil] at hws; cases hws
      | cons w ws =>
        obtain ⟨s0, ss0, hw, hws', he⟩ := sortsOf_cons.mp hws
        cases he
        rw [Term.koreList, List.map_cons, List.map_cons] at hbs
        cases hbs with
        | cons hb hbs =>
          have ih1 := patVal_back4 hp.1 h1 hw hb
          have ih2 := patVals_back4 hp.2 h2 hws' hbs
          refine ⟨.cons ih1.1 ih2.1, fun j hj => ?_⟩
          rw [varOccsList] at hj
          rcases List.mem_append.mp hj with hj | hj
          · exact ih1.2 j hj
          · exact ih2.2 j hj
end

end

/-! ## Negated premises over map patterns -/

section
variable {c : Semantics} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hI : I ⊧ᴵP Γ c) [OvlOK c]
  (hC : I ⊧ᴵP ΓColls c) (hph : patHooksApart c = true) (hmo : mapSortOK c = true) (hg : genWf c = true)
  (htr : ∀ a b d, (a, b) ∈ c.subsorts → (b, d) ∈ c.subsorts → (a, d) ∈ c.subsorts)
  (hnm : NamesPlain c)
include hI hC hph hmo hg htr

include hnm in
/-- **The core lemma for clauses, map patterns included**, in a model of `Γ`. At
arguments where a clause fails in the model, its exclusion
`∃ȳ. ⌈req = true⌉ ∧ X̄ ∈ p̄` is empty, at a valuation that gives each formal argument `Xⱼ` the
element of the argument and the sort variable `R` a sort. -/
theorem exclusion_empty4 {fn : Fn} {cl : Clause} (hpre : cl.pre = .top)
    (hpats : sortsOfTerms c.patCtxAll cl.vars cl.pats = some fn.args)
    (hbinds : ∀ i < cl.vars.length, i ∈ varOccsList cl.pats) (hplain : mapPats c cl.pats = true)
    {ws : List GroundTerm} (hws : c.sortsOf ws = some fn.args)
    {tbl : VarTable} (hkeys : ∀ i < cl.vars.length, canonKey c cl.vars i ∈ tbl)
    (hXkeys : ∀ (j : Nat) s, fn.args[j]? = some s → VarKey.evar ("X" ++ toString j) (KoreAML.srt (c.sortName s)) ∈ tbl)
    (hRkey : VarKey.sortVar "R" ∈ tbl)
    {e : Valuation M}
    (hX : ∀ (j : Nat) w s, ws[j]? = some w → fn.args[j]? = some s →
      e.evalEvar (tbl.ev (.evar ("X" ++ toString j) (KoreAML.srt (c.sortName s)))) = elemOf c I w)
    {σR : M} (hR : e.evalEvar (tbl.ev (.sortVar "R")) = σR) (hσR : IsSort I σR)
    (hfail : ModelFails c I cl ws) (m : M) :
    ¬ (KoreAML.tr ⟨tbl, []⟩ (exclusion c fn cl (canonClausePres cl))).interpret I e m := by
  intro hm
  rw [exclusion_top _ hpre (List.all_eq_true.mpr fun i hi => by simpa using hbinds i (List.mem_range.mp hi))] at hm
  have hD := defOK hI
  let vs := canonVars c cl.vars
  obtain ⟨hnd, hsrt⟩ := canon_binders hkeys
  have hm' : (KoreAML.tr ⟨tbl, []⟩ (KoreAML.existsAll KoreAML.R (vs.map KoreAML.Var.kore)
      (premise (fn.args.map c.sortName) (cl.req.map (Term.kore c vs)) (Term.koreList c vs cl.pats)))).interpret I e m := hm
  obtain ⟨e', hag, hguard, hbody⟩ := existsAll_elim hD _ e m hnd hsrt hm'
  have hnotb : ∀ k, k ∈ tbl → (∀ i < cl.vars.length, k ≠ canonKey c cl.vars i) →
      ∀ b ∈ vs.map KoreAML.Var.kore, tbl.ev k ≠ tbl.ev (KoreAML.evarKey b) := by
    intro k hk hne b hb heq
    obtain ⟨i, hi, rfl⟩ := canonVars_kore_mem hb
    exact hne i hi (ev_inj hk (hkeys i hi) heq)
  have he'X : ∀ (j : Nat) s, fn.args[j]? = some s →
      e'.evalEvar (tbl.ev (.evar ("X" ++ toString j) (KoreAML.srt (c.sortName s)))) =
        e.evalEvar (tbl.ev (.evar ("X" ++ toString j) (KoreAML.srt (c.sortName s)))) :=
    fun j s hj => hag _ (hnotb _ (hXkeys j s hj) (fun i hi => canonKey_ne_X hI hg htr hi _ _))
  have he'R : e'.evalEvar (tbl.ev (.sortVar "R")) = e.evalEvar (tbl.ev (.sortVar "R")) :=
    hag _ (hnotb _ hRkey (fun i hi h => by rw [canonKey_eq c hi] at h; cases h))
  unfold premise at hbody
  rw [tr_and2, KoreAML.interp_sAnd] at hbody
  obtain ⟨hreq, hargs⟩ := hbody
  have hcon := argsConj_back 0 _ hargs
  have hin : ∀ i < cl.vars.length, InS I (c.sortName (cl.vars.getD i 0)) (e'.evalEvar (tbl.ev (keyAt vs i))) := by
    intro i hi
    have hlt : i < vs.length := by rw [canonVars_length]; exact hi
    have hb : (vs.getD i default).kore ∈ vs.map KoreAML.Var.kore := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]
      exact List.mem_map_of_mem (List.getElem_mem hlt)
    exact hguard _ hb _ (by show (vs.getD i default).kore.sort = _; rw [canonVars_getD c hi]; rfl)
  have hlenp : (Term.koreList c vs cl.pats).length = fn.args.length := by
    rw [koreList_length]; exact sortsOfTerms_length hpats
  have hall : All2 (fun φ b => φ.interpret I e' b) ((Term.koreList c vs cl.pats).map (KoreAML.tr ⟨tbl, []⟩))
      (ws.map (elemOf c I)) := by
    refine All2.of_get (by simp [hlenp, sortsOf_length hws]) (fun j φ b hφ hb => ?_)
    rw [List.getElem?_map] at hφ hb
    obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.mp hφ
    obtain ⟨w, hw, rfl⟩ := Option.map_eq_some_iff.mp hb
    have hjl : j < fn.args.length := by
      rw [← sortsOf_length hws]; exact (List.getElem?_eq_some_iff.mp hw).1
    have hs : fn.args[j]? = some fn.args[j] := List.getElem?_eq_getElem hjl
    have hl : ((fn.args.map c.sortName).zip (Term.koreList c vs cl.pats))[j]? = some (c.sortName fn.args[j], p) := by
      rw [List.getElem?_zip_eq_some]
      exact ⟨by rw [List.getElem?_map, hs]; rfl, hp⟩
    have := hcon j _ p hl
    rw [Nat.zero_add, he'X j _ hs, hX j w _ hw hs] at this
    exact this
  obtain ⟨hpv, hwit⟩ := patVals_back4 hI hC hph hmo hg htr hnm (canonVars_length c cl.vars) hin hplain hpats hws hall
  obtain ⟨hws', hagr⟩ := substOf_ok hI hg htr (canonVars_length c cl.vars) (fun i hi => hwit i (hbinds i hi))
  obtain ⟨t, r, ht, hr, hrs, hden⟩ := hfail _ hws' hpv tbl e' hagr
  rw [ht] at hreq
  exact reqFalse_empty hI (S' := KoreAML.R) (fun a => by rw [trSort_R, KoreAML.interp_evar, he'R, hR]) hσR hr hrs hden m hreq

include hnm in
/-- **The core lemma for rules, map patterns included**, in a model of `Γ`. If a rule
does not apply to a configuration in the model, the
configuration's element is not in the rule's `applies` pattern `∃x̄. (lhs ∧ ⌈req = true⌉)`. -/
theorem applies_empty4 {r : Rule} (hlhs : sortOfTerm c.patCtxAll r.vars r.lhs = some topCellSort)
    (hbinds : ∀ i < r.vars.length, i ∈ varOccs r.lhs) (hplain : mapPat c r.lhs = true)
    (hpre : r.pre = .top) {x : GroundTerm} (hx : c.sortOf x = some topCellSort)
    {tbl : VarTable} (hkeys : ∀ i < r.vars.length, canonKey c r.vars i ∈ tbl) (e : Valuation M)
    (hfail : ModelNotApplies c I r x) :
    ¬ (KoreAML.tr ⟨tbl, []⟩ (applies c r (canonRulePres r))).interpret I e (elemOf c I x) := by
  intro hm
  rw [applies_top _ hpre (List.all_eq_true.mpr fun i hi => by simpa using hbinds i (List.mem_range.mp hi))] at hm
  have hD := defOK hI
  let vs := canonVars c r.vars
  obtain ⟨hnd, hsrt⟩ := canon_binders hkeys
  have hm' : (KoreAML.tr ⟨tbl, []⟩ (KoreAML.existsAll (srtOf c topCellSort) (vs.map KoreAML.Var.kore)
      (.and (srtOf c topCellSort) [Term.kore c vs r.lhs, reqPat (srtOf c topCellSort) (r.req.map (Term.kore c vs))]))).interpret
        I e (elemOf c I x) := hm
  obtain ⟨e', -, hguard, hbody⟩ := existsAll_elim hD _ e _ hnd hsrt hm'
  rw [tr_and2, KoreAML.interp_sAnd] at hbody
  obtain ⟨hl, hreq⟩ := hbody
  have hin : ∀ i < r.vars.length, InS I (c.sortName (r.vars.getD i 0)) (e'.evalEvar (tbl.ev (keyAt vs i))) := by
    intro i hi
    have hlt : i < vs.length := by rw [canonVars_length]; exact hi
    have hb : (vs.getD i default).kore ∈ vs.map KoreAML.Var.kore := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]
      exact List.mem_map_of_mem (List.getElem_mem hlt)
    exact hguard _ hb _ (by show (vs.getD i default).kore.sort = _; rw [canonVars_getD c hi]; rfl)
  obtain ⟨hpv, hwit⟩ := patVal_back4 hI hC hph hmo hg htr hnm (canonVars_length c r.vars) hin hplain hlhs hx hl
  obtain ⟨hws', hagr⟩ := substOf_ok hI hg htr (canonVars_length c r.vars) (fun i hi => hwit i (hbinds i hi))
  obtain ⟨t, v, ht, hv, hvs, hden⟩ := hfail _ hws' hpv tbl e' hagr
  rw [ht] at hreq
  obtain ⟨σC, hσC1, hσC2⟩ := sortSing hI (top_numbered (c := c))
  exact reqFalse_empty hI (S' := srtOf c topCellSort) (fun a => by unfold srtOf; rw [trSort_srt]; exact hσC1 a) hσC2
    hv hvs hden _ hreq


end

/-! ## The fourth stage, its negated premises over map patterns -/

/-- **The fourth stage's scope.** `Stage4a` with map patterns allowed in the negated premises too:
every rule and clause read negatively (`RuleNeg`, `ClauseNeg`) is a pattern of constructors,
injections, aliases, variables, domain values and the library's map pattern symbols (`mapPat`);
collection patterns over a list's or a cell map's symbols stay where they are read positively only.
And `Map` is not a token or byte sort (`mapSortOK`). Decidable on the data. -/
def Stage4 (c : Semantics) : Prop :=
  genWf c = true ∧ patHooksApart c = true ∧ mapSortOK c = true ∧
  (∀ r ∈ c.rules, RuleNeg c r → mapPat c r.lhs = true) ∧
  (∀ fn ∈ c.allFns, ∀ cl ∈ fn.clauses, ClauseNeg c fn cl → mapPats c cl.pats = true)

/-- `Stage4a`, with `Map` neither a token nor a byte sort, is inside `Stage4`. -/
theorem stage4_of_stage4a {c : Semantics} (h : Stage4a c) (hmo : mapSortOK c = true) : Stage4 c :=
  ⟨h.1, h.2.1, hmo, fun r hr hn => mapPat_of_plain (h.2.2.1 r hr hn),
    fun fn hfn cl hcl hn => mapPats_of_plain (h.2.2.2 fn hfn cl hcl hn)⟩

/-- **L4, fourth stage.** Every step of `Step` is a consequence of `Γ c`, for a semantics in
`Stage4`: in every model, the configuration `x` has the configuration `y` as a successor. A
negated premise over a map pattern, a competitor's exclusion or `applies`, is empty where the
kernel says the competitor does not apply (`exclusion_empty4`, `applies_empty4`): a value's element
lies in a map pattern's translation only where the pattern matches the value (`patVal_back4`),
which the map axioms of `ΓColls` give. -/
theorem step_sound_stage4 (c : Semantics) [OvlOK c] (hy : Hyp c) (hb : ∀ r ∈ c.rules, binds r.vars.length (varOccs r.lhs) = true) (htop : ∀ r ∈ c.rules, r.pre = .top ∧ r.post = .top)
    (hbc : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, binds cl.vars.length (varOccsList cl.pats) = true) (hs : Stage4 c) :
    ∀ x y : Config c, Step c x y → Γ c ⊧ (den c x.val ⇒ KoreAML.sNext (den c y.val)) := by
  have hpreTop := Semantics.preTop_of_okAll hy.1
  have hy : HypCore c := hy.core (Semantics.overloadsOK_pats OvlOK.ok)
  have hnn : NamesNumbered c := hy.2.2.2.2.2.2
  have hsc := sortCtx_of_all hy.1 hy.2.1 (OvlOK.ovlCase inferInstance)
  intro x y hstep M _ I hI e m hm
  have hC : I ⊧ᴵP ΓColls c := sat_colls hI
  obtain ⟨hg, hph, hmo, hr4, hc4⟩ := hs
  refine step_at4 (hpreTop := hpreTop) hI hnn hsc hy.1 hbc hph (fun fn hfn cl hcl hn => ?_) hb htop (fun r hr hn => ?_) hstep e m hm
  · obtain ⟨hp', hb', -⟩ := clause_ctx hy.1 hbc hfn hcl
    exact fun hws _ hkeys hXkeys hRkey _ hX _ hR hσR hfail m =>
      exclusion_empty4 hI hC hph hmo hg hsc.trans hnn.1 (clause_preTop (hpreTop := hpreTop) hy.1 hfn hcl) hp' hb' (hc4 fn hfn cl hcl hn) hws hkeys hXkeys hRkey hX hR hσR
        hfail m
  · obtain ⟨hlhs, -⟩ := rule_ctx hy.1 hr
    exact fun hx _ hkeys e hfail =>
      applies_empty4 hI hC hph hmo hg hsc.trans hnn.1 hlhs (Exec.binds_all (hb _ hr)) (hr4 r hr hn) (htop _ hr).1 hx hkeys e hfail


end Faithful

end KCore
