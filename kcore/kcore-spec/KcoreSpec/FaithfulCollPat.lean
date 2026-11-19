/-
  KCore. Collection patterns read downwards, for every collection pattern symbol a left-hand side
  may apply: the library's map pattern symbols (`PatVal.hook`), the library's set and list
  symbols, and the parameters implemented by a map, set or list pattern symbol, a cell map's, a
  cell set's or a cell list's (`PatVal.coll`).

  A map, list or set collection `k` is read through its axioms in `ΓColls` and its symbols' graphs
  on values in `ΓDomains`: the library's symbols are interpreted hooks, a definition's
  collection's are parameters implemented by them (`collSymsOK`). `MapReading c I k`,
  `ListReading c I k` and `SetReading c I k` collect what the downward reading takes of `k` in a
  model `I`; `mapReading_lib`, `mapReading_cell`, `listReading_lib`, `listReading_cell`,
  `setReading_lib` and `setReading_cell` give them. From them, a value's element lies in what a
  symbol of `k` gives on elements of its argument sorts only where those are values' elements and
  the symbol's value on them is the value (`mapK_back`, `listK_back`, `setK_back`; a set is read
  as a map whose entries carry no value). A pattern of constructors, injections, aliases, variables, domain
  values and these symbols then denotes a value whose element lies in its translation
  (`patVal_backC`), and the negated premises of `Γ` read the kernel's failures
  (`exclusion_emptyC`, `applies_emptyC`).
-/
import KcoreSpec.FaithfulColl
import KcoreSpec.PatCtxNF

set_option autoImplicit false

namespace KCore

namespace Faithful

open ML
open KoreAML (DefOK Inh IsSort Closed KGround VarKey VarTable)

/-! ## The well-formedness of the collection sorts -/

section
variable {c : Semantics}

theorem collSortsOK_mem (h : collSortsOK c = true) {k : CollSig} (hk : k ∈ c.allColls) : collSortOK c k.sort = true :=
  List.all_eq_true.mp h k hk

theorem collSymsOK_spec {k : CollSig} (h : collSymsOK c k = true) :
    c.collOf k.sort = some k ∧ (∀ f ∈ [k.unit, k.elem, k.concat], isHook f = false ∧ iteSort? (c.symName f) = none) ∧
    c.lookupParam k.unit = some { sig := ⟨k.unit, [], k.sort⟩, impl := some (builtinColl k.kind).unit } ∧
    c.lookupParam k.elem = some { sig := ⟨k.elem, elemArgs k, k.sort⟩, impl := some (builtinColl k.kind).elem } ∧
    c.lookupParam k.concat = some { sig := ⟨k.concat, [k.sort, k.sort], k.sort⟩, impl := some (builtinColl k.kind).concat } := by
  unfold collSymsOK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, -⟩ := h
  refine ⟨h1, fun f hf => ?_, h3, h4, h5⟩
  have := List.all_eq_true.mp h2 f hf
  simp only [Bool.and_eq_true, Bool.not_eq_true', Option.isNone_iff_eq_none] at this
  exact ⟨this.1, iteSort?_none_of_instDecode this.2⟩

/-- A map collection with `collSymsOK` has its value sort, `valSort`. -/
theorem collSymsOK_val {k : CollSig} (h : collSymsOK c k = true) (hkind : k.kind = .map) :
    k.val = some (valSort k) := by
  unfold collSymsOK at h
  simp only [Bool.and_eq_true] at h
  have hv := h.2
  rw [hkind] at hv
  simp only [bne_self_eq_false, Bool.false_or, Option.isSome_iff_exists] at hv
  obtain ⟨v, hv⟩ := hv
  simp [valSort, hv]

theorem collsOK_colls (h : collsOK c = true) {k : CollSig} (hk : k ∈ c.colls) : collSymsOK c k = true := by
  unfold collsOK at h
  simp only [Bool.and_eq_true] at h
  exact List.all_eq_true.mp h.1 k hk

/-- Every map collection of a semantics with `collsOK` has its value sort: the library's map has
KItem, the definition's have theirs by `collSymsOK`. -/
theorem collsOK_val (h : collsOK c = true) {k : CollSig} (hk : k ∈ c.allColls) (hkind : k.kind = .map) :
    k.val = some (valSort k) := by
  rcases List.mem_append.mp hk with hb | hu
  · simp only [builtinColls, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · rfl
    · cases hkind
    · cases hkind
    · cases hkind
  · exact collSymsOK_val (collsOK_colls h hu) hkind

theorem collsOK_params (h : collsOK c = true) {kp : ParamSig} (hkp : kp ∈ c.params) (hi : collImpl kp = true) :
    ∃ k ∈ c.colls, kp.sig.name = k.unit ∨ kp.sig.name = k.elem ∨ kp.sig.name = k.concat := by
  unfold collsOK at h
  simp only [Bool.and_eq_true] at h
  have := List.all_eq_true.mp h.2 kp hkp
  rw [hi] at this
  simp only [Bool.not_true, Bool.false_or, List.any_eq_true, Bool.or_eq_true, beq_iff_eq] at this
  obtain ⟨k, hk, h⟩ := this
  exact ⟨k, hk, by rcases h with (h | h) | h <;> simp [h]⟩

theorem lookupParam_mem {f : Sym} {kp : ParamSig} (h : c.lookupParam f = some kp) : kp ∈ c.params := by
  rw [Semantics.lookupParam_eq] at h
  exact List.mem_of_find?_eq_some h

/-- The library's collections are built by interpreted hooks. -/
theorem builtinColls_hooks :
    builtinColls.all (fun k => [k.unit, k.elem, k.concat].all fun f => hookSigs.any (·.name == f)) = true := by
  decide +kernel

/-- **No collection symbol is a constructor** where no interpreted hook and no parameter is one
(`kindsApart`) and the definition's collections are built by parameters (`collsOK`): the library's
collection symbols are interpreted hooks, the definition's are parameters. -/
theorem collsNotCtors_of (hk : Model.kindsApart c = true) (hc : collsOK c = true) :
    Model.collsNotCtors c = true := by
  simp only [Model.kindsApart, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true'] at hk
  unfold Model.collsNotCtors
  refine List.all_eq_true.mpr fun k hk' => List.all_eq_true.mpr fun f hf => ?_
  rw [Bool.not_eq_true']
  rcases List.mem_append.mp hk' with hb | hu
  · obtain ⟨h, hh, he⟩ := List.any_eq_true.mp
      (List.all_eq_true.mp (List.all_eq_true.mp builtinColls_hooks k hb) f hf)
    rw [← beq_iff_eq.mp he]
    exact hk.1 h hh
  · obtain ⟨-, -, h1, h2, h3⟩ := collSymsOK_spec (collsOK_colls hc hu)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl
    · exact (hk.2 _ (lookupParam_mem h1)).1
    · exact (hk.2 _ (lookupParam_mem h2)).1
    · exact (hk.2 _ (lookupParam_mem h3)).1

end

/-! ## Small facts -/

theorem join_some {α : Type} {o : Option (Option α)} {a : α} : o.join = some a ↔ o = some (some a) := by
  cases o with
  | none => simp
  | some x => simp

theorem collVal_hook {c : Semantics} {f : Sym} (h : isHook f = true) (ws : List GroundTerm) :
    c.collVal f ws = (hook f ws).join := by
  unfold Semantics.collVal; rw [if_pos h]

theorem collVal_param {c : Semantics} {f : Sym} (h : isHook f = false) (ws : List GroundTerm) :
    c.collVal f ws = c.paramVal f ws := by
  unfold Semantics.collVal; rw [if_neg (by simp [h])]

theorem paramVal_impl {c : Semantics} {f : Sym} {kp : ParamSig} {g : Sym} (hp : c.lookupParam f = some kp)
    (hi : kp.impl = some g) (ws : List GroundTerm) (hg : silentKey g = false)
    (hc : Semantics.rawArgHooks.contains g = true) (hr : c.lib.carrier kp.sig.result = kp.sig.result) :
    c.paramVal f ws = ((hook g ws).join.map (GroundTerm.withSort kp.sig.result)).filter
      (fun v => c.sortOf v == some kp.sig.result) := by
  unfold Semantics.paramVal; rw [hp]; dsimp only; rw [hi]; dsimp only
  rw [Semantics.libArgs_coll c hc, Semantics.hookRes_of_notKey hg,
    show GroundTerm.asSort c.lib kp.sig.result = GroundTerm.withSort kp.sig.result from
      funext (GroundTerm.asSort_of_self hr)]

theorem filter_sorted {c : Semantics} {v : GroundTerm} {s : Srt} (h : c.sortOf v = some s) :
    (some v).filter (fun v => c.sortOf v == some s) = some v := by
  simp [Option.filter, h]

theorem collAxioms_map {c : Semantics} {k : CollSig} (h : k.kind = .map) : collAxioms c k = mapCollAxioms c k := by
  unfold collAxioms; rw [h]

theorem collSig_eq {c : Semantics} {k : CollSig} (K : CollKind) (h : c.collOf k.sort = some k) :
    c.collSig K k.sort = k := by
  unfold Semantics.collSig; rw [h]; rfl

theorem kernel_hook {c : Semantics} {k : CtorSig} (h : k ∈ hookSigs) : k ∈ kernelSyms c :=
  List.mem_append_left _ (List.mem_append_right _ h)

theorem kernel_param {c : Semantics} {kp : ParamSig} (h : kp ∈ c.params) : kp.sig ∈ kernelSyms c :=
  List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (List.mem_map_of_mem h)))

theorem sortsOf_two {c : Semantics} {w₁ w₂ : GroundTerm} {s₁ s₂ : Srt} (h1 : c.sortOf w₁ = some s₁)
    (h2 : c.sortOf w₂ = some s₂) : c.sortsOf [w₁, w₂] = some [s₁, s₂] :=
  sortsOf_cons.mpr ⟨_, _, h1, sortsOf_cons.mpr ⟨_, _, h2, sortsOf_nil, rfl⟩, rfl⟩

theorem symHead_none {c : Semantics} {f : Sym} (h : iteSort? (c.symName f) = none) :
    symHead c f = KoreAML.sym (.symbol (c.symName f)) := by
  unfold symHead; rw [h]

theorem isHook_patHook {f : Sym} (hp : patternHooks.contains f = true) : isHook f = true := by
  rcases Exec.patternHooks_cases hp with rfl | rfl | rfl <;> rfl

theorem entriesOK_consK {c : Semantics} {ks vs : Srt} {a b : GroundTerm} {es : List (GroundTerm × GroundTerm)} :
    c.entriesOK ks vs ((a, b) :: es) = true ↔
      c.sortOf a = some ks ∧ c.sortOf b = some vs ∧ c.entriesOK ks vs es = true := by
  simp [Semantics.entriesOK, Semantics.entryOK, and_assoc]

/-! ## A collection's values -/

section
variable {c : Semantics} {k : CollSig} (hco : c.collOf k.sort = some k)
include hco

theorem sortOf_mapK (hkind : k.kind = .map) (hval : k.val = some (valSort k))
    {es : List (GroundTerm × GroundTerm)} :
    c.sortOf (.map k.sort es) = some k.sort ↔ keysSorted es = true ∧ c.entriesOK k.key (valSort k) es = true := by
  rw [sortOf_mapS_map hco hkind]
  constructor
  · rintro ⟨vs, hv, h1, h2, -⟩
    rw [hval] at hv; cases hv; exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨valSort k, hval, h1, h2, rfl⟩

theorem den_mapNilK {M : Type} {I : Interpretation KoreAML.Sym M} (e : Valuation M) (m : M) :
    (den c (.map k.sort [])).interpret I e m ↔ I.evalSymb (.symbol (c.symName k.unit)) m := by
  unfold den KoreAML.den
  rw [GroundTerm.kore, collSig_eq .map hco, GroundTerm.koreEntries]
  unfold KoreAML.ap
  rw [KoreAML.tr_app0, KoreAML.trArgs_nil]
  exact Iff.rfl

theorem den_mapOneK_eq (a b : GroundTerm) :
    den c (.map k.sort [(a, b)]) = KoreAML.appList (symP (c.symName k.elem)) [den c a, den c b] := by
  unfold den KoreAML.den
  rw [GroundTerm.kore, collSig_eq .map hco, GroundTerm.koreEntries, GroundTerm.koreEntry]
  unfold KoreAML.ap
  rw [KoreAML.tr_app0, trArgs_appList]
  rfl

theorem den_mapConsK_eq (a b : GroundTerm) (e' : GroundTerm × GroundTerm) (es : List (GroundTerm × GroundTerm)) :
    den c (.map k.sort ((a, b) :: e' :: es)) = KoreAML.appList (symP (c.symName k.concat))
      [KoreAML.appList (symP (c.symName k.elem)) [den c a, den c b], den c (.map k.sort (e' :: es))] := by
  have h2 : den c (.map k.sort (e' :: es)) = KoreAML.tr ⟨[], []⟩ (GroundTerm.koreEntries c k (e' :: es)) := by
    unfold den KoreAML.den; rw [GroundTerm.kore, collSig_eq .map hco]
  rw [h2]
  unfold den KoreAML.den
  rw [GroundTerm.kore, collSig_eq .map hco, GroundTerm.koreEntries.eq_3 c k (a, b) (e' :: es) (List.cons_ne_nil _ _),
    GroundTerm.koreEntry]
  unfold KoreAML.ap
  rw [KoreAML.tr_app0, trArgs_appList]
  simp only [List.map_cons, List.map_nil]
  rw [KoreAML.tr_app0, trArgs_appList]
  rfl

/-- A value of a collection sort is a collection of that sort, of the collection's kind. -/
theorem coll_shape (hg : genWf c = true) [OvlOK c] (hso : collSortOK c k.sort = true) {w : GroundTerm}
    (hw : c.sortOf w = some k.sort) :
    ((k.kind = .map ∨ k.kind = .rangeMap) ∧ ∃ es, w = .map k.sort es) ∨ (k.kind = .set ∧ ∃ es, w = .set k.sort es) ∨
      (k.kind = .list ∧ ∃ es, w = .list k.sort es) := by
  have hnc : k.sort ∉ consSorts c := fun h => by
    have := (genWf_cons hg h).2.2.2.2.2.2
    rw [hco] at this; cases this
  have hcar : c.lib.carriers.all (·.1 != k.sort) = true := by
    unfold collSortOK at hso; simp only [Bool.and_eq_true] at hso; exact hso.2
  unfold collSortOK at hso
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_true'] at hso
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hi, hb⟩, hkv⟩, ht⟩, hy⟩, hfl⟩, hstr⟩, hbys⟩, -⟩ := hso
  cases w with
  | ctor f ts =>
    exact absurd (ctor_sort_cons hg hw) hnc
  | inj a b t =>
    obtain ⟨hab, -, -, hr⟩ := sortOf_inj.mp hw
    exact absurd (hr ▸ (genWf_sub hg hab).1) hnc
  | dv s lit =>
    obtain ⟨hok, hs⟩ := sortOf_dv.mp hw
    rw [← hs] at hok
    exfalso
    rw [dvOK_self (Lib.carrier_of_not _ hcar)] at hok
    cases lit with
    | int i => exact hi (beq_iff_eq.mp hok)
    | bool b => exact hb (beq_iff_eq.mp hok)
    | tok t =>
      simp only [dvOK, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hok
      rcases hok with ((h | h) | h) | ⟨h | h, -⟩
      · exact hkv h
      · exact hstr h
      · rw [ht] at h; cases h
      · exact hbys h
      · rw [hy] at h; cases h
    | float _ _ _ =>
      simp only [dvOK, Bool.and_eq_true, beq_iff_eq] at hok; exact hfl hok.1
  | map s es =>
    obtain ⟨k', -, hk', hkind, -, -, -, rfl⟩ := sortOf_mapS_fwd hw
    rw [hco] at hk'; cases hk'
    exact Or.inl ⟨hkind, es, rfl⟩
  | set s es =>
    obtain ⟨k', hk', hkind, -, -, rfl⟩ := sortOf_setS.mp hw
    rw [hco] at hk'; cases hk'
    exact Or.inr (Or.inl ⟨hkind, es, rfl⟩)
  | list s es =>
    obtain ⟨k', hk', hkind, -, rfl⟩ := sortOf_listS.mp hw
    rw [hco] at hk'; cases hk'
    exact Or.inr (Or.inr ⟨hkind, es, rfl⟩)

end

/-! ## The graphs of a binary symbol on values -/

section
variable {c : Semantics} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hI : I ⊧ᴵP Γ c) [OvlOK c]
include hI

omit [Inhabited M] hI in
theorem hook_some {f : Sym} (h : isHook f = true) (ws : List GroundTerm) : ∃ o, hook f ws = some o := by
  unfold isHook hook at h
  unfold hook
  cases hf : hookTrie.find f with
  | none => rw [hf] at h; simp at h
  | some g => exact ⟨g ws, rfl⟩

/-- **A binary interpreted symbol without silent points, at values**: its graph in `ΓDomains`. -/
theorem hook2_val {f : Sym} {s₁ s₂ r : Srt} (hks : lookupSig hookSigs f = some ⟨f, [s₁, s₂], r⟩)
    (hit : iteSort? (c.symName f) = none) (hns : silentKey f = false) {w₁ w₂ : GroundTerm} (h1 : c.sortOf w₁ = some s₁)
    (h2 : c.sortOf w₂ = some s₂) (m : M) :
    SymE I (c.symName f) [elemOf c I w₁, elemOf c I w₂] m ↔
      ∃ u, hook f [w₁, w₂] = some (some u) ∧ m = elemOf c I u := by
  have hD := defOK hI
  have hk := (lookupSig_spec hks).1
  have hws : c.sortsOf [w₁, w₂] = some [s₁, s₂] := sortsOf_two h1 h2
  have hhk : isHook f = true := by
    cases h : isHook f
    · rw [lookupSig_hookSigs_of_not_isHook h] at hks; cases hks
    · rfl
  obtain ⟨o, hr⟩ := hook_some hhk [w₁, w₂]
  have hax := sat_dom hI (Or.inl ⟨⟨f, [s₁, s₂], r⟩, [w₁, w₂], o, hk, hws, hr,
    fun _ => silent_of_not_silentKey hns _, rfl⟩)
  have hgr := (KoreAML.interp_equal hD).mp (hax KoreAML.val0 default) m
  unfold KoreAML.den at hgr
  rw [tr_symApp] at hgr
  unfold symHead at hgr
  dsimp only at hgr
  rw [hit] at hgr
  dsimp only at hgr
  rw [trArgs_appList] at hgr
  have hl : (GroundTerm.koreList c [w₁, w₂]).map (KoreAML.tr ⟨[], []⟩) = [den c w₁, den c w₂] := rfl
  rw [hl, interp_symList _ _ _ (.cons (den_sing hI h1 _) (.cons (den_sing hI h2 _) .nil)) m] at hgr
  rw [hgr]
  cases o with
  | none =>
    simp only [Pattern.interpret]
    constructor
    · intro h; exact h.elim
    · rintro ⟨u, hu, -⟩; rw [hr] at hu; cases hu
  | some u =>
    have hsu := hook_sorted (fun he => (ne_rmKeys_of_sig hks (by simp) he).elim) hks hws hr
    dsimp only
    rw [den_sing hI hsu]
    constructor
    · intro h; exact ⟨u, hr, h⟩
    · rintro ⟨u', hu', h⟩; rw [hr] at hu'; cases hu'; exact h

/-- **A binary parameter symbol, at values**: its graph in `ΓDomains`, under `c.hooks`. -/
theorem param2_val {f : Sym} {kp : ParamSig} {s₁ s₂ r : Srt} (hkp : c.lookupParam f = some kp)
    (hsig : kp.sig = ⟨f, [s₁, s₂], r⟩) (hit : iteSort? (c.symName f) = none) {w₁ w₂ : GroundTerm}
    (h1 : c.sortOf w₁ = some s₁) (h2 : c.sortOf w₂ = some s₂) (m : M) :
    SymE I (c.symName f) [elemOf c I w₁, elemOf c I w₂] m ↔
      ∃ u, c.paramVal f [w₁, w₂] = some u ∧ m = elemOf c I u := by
  have hD := defOK hI
  have hkpm : kp ∈ c.params := lookupParam_mem hkp
  have hws : c.sortsOf [w₁, w₂] = some kp.sig.args := by rw [hsig]; exact sortsOf_two h1 h2
  have hax := sat_dom hI (Or.inr (Or.inl ⟨kp, [w₁, w₂], hkpm, hws, rfl⟩))
  have hgr := (KoreAML.interp_equal hD).mp (hax KoreAML.val0 default) m
  rw [hsig] at hgr
  unfold KoreAML.den at hgr
  rw [tr_symApp] at hgr
  unfold symHead at hgr
  dsimp only at hgr
  rw [hit] at hgr
  dsimp only at hgr
  rw [trArgs_appList] at hgr
  have hl : (GroundTerm.koreList c [w₁, w₂]).map (KoreAML.tr ⟨[], []⟩) = [den c w₁, den c w₂] := rfl
  rw [hl, interp_symList _ _ _ (.cons (den_sing hI h1 _) (.cons (den_sing hI h2 _) .nil)) m] at hgr
  rw [hgr]
  cases hp : c.paramVal f [w₁, w₂] with
  | none =>
    simp only [Pattern.interpret]
    constructor
    · intro h; exact h.elim
    · rintro ⟨u, hu, -⟩; cases hu
  | some u =>
    obtain ⟨k', -, hsu⟩ := c.paramVal_sorted hp
    dsimp only
    rw [den_sing hI hsu]
    constructor
    · intro h; exact ⟨u, rfl, h⟩
    · rintro ⟨u', hu', h⟩; cases hu'; exact h

end

/-! ## A map collection, read in a model -/

/-- **What the downward reading takes of a map collection `k` in a model `I`**: `k` is a map
collection of the semantics, the collection of its sort, whose sort holds no domain value; its
symbols are not named like `ite` at a sort and have signatures of `Γ`; their values on values are
the empty map, the one-entry map and, where the graph of `concat` defines it, the union; and the
element `concat` gives on two values' elements is the element of their union, which is a value of
`k`'s sort. -/
structure MapReading (c : Semantics) {M : Type} [Inhabited M] (I : Interpretation KoreAML.Sym M) (k : CollSig) :
    Prop where
  mem : k ∈ c.allColls
  kind : k.kind = .map
  val : k.val = some (valSort k)
  coll : c.collOf k.sort = some k
  sortOK : collSortOK c k.sort = true
  ite : ∀ f ∈ [k.unit, k.elem, k.concat], iteSort? (c.symName f) = none
  sigs : (⟨k.unit, [], k.sort⟩ : CtorSig) ∈ kernelSyms c ∧ (⟨k.elem, [k.key, valSort k], k.sort⟩ : CtorSig) ∈ kernelSyms c ∧
    (⟨k.concat, [k.sort, k.sort], k.sort⟩ : CtorSig) ∈ kernelSyms c
  unitV : c.collVal k.unit [] = some (.map k.sort [])
  elemV : ∀ {a b : GroundTerm}, c.sortOf a = some k.key → c.sortOf b = some (valSort k) →
    c.collVal k.elem [a, b] = some (.map k.sort [(a, b)])
  catV : ∀ {w₁ w₂ : GroundTerm}, c.sortOf w₁ = some k.sort → c.sortOf w₂ = some k.sort → ∀ m,
    SymE I (c.symName k.concat) [elemOf c I w₁, elemOf c I w₂] m ↔
      ∃ u, c.collVal k.concat [w₁, w₂] = some u ∧ c.sortOf u = some k.sort ∧ m = elemOf c I u
  catOne : ∀ {a b : GroundTerm}, c.sortOf a = some k.key → c.sortOf b = some (valSort k) →
    c.collVal k.concat [.map k.sort [(a, b)], .map k.sort []] = some (.map k.sort [(a, b)])

section
variable {c : Semantics} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
  (hD : DefOK I) (hC : I ⊧ᴵP ΓColls c) {k : CollSig} (hk : k ∈ c.allColls) (hkind : k.kind = .map)
include hD hC hk hkind

/-- `mapUnitSplitAx`, read: the parts of the unit's element under `concat` are the unit's. -/
theorem axK_unitSplit {m₁ m₂ x : M} (h1 : InS I (c.sortName k.sort) m₁) (h2 : InS I (c.sortName k.sort) m₂)
    (hu : I.evalSymb (.symbol (c.symName k.unit)) x) (hx : SymE I (c.symName k.concat) [m₁, m₂] x) :
    I.evalSymb (.symbol (c.symName k.unit)) m₁ ∧ I.evalSymb (.symbol (c.symName k.unit)) m₂ := by
  have hax := hC (mapUnitSplitAx c k) ⟨k, hk, by rw [collAxioms_map hkind]; exact List.mem_cons_self ..⟩
    (listVal [m₁, m₂]) default
  unfold mapUnitSplitAx at hax
  dsimp only at hax
  have hb := KoreAML.interp_guarded hax (fun w hw => by
    rcases mem_two hw with rfl | rfl
    · exact guard_at hD (s := k.sort) h1 _
    · exact guard_at hD (s := k.sort) h2 _)
  have hc := hb ((KoreAML.interp_defined hD).mpr ⟨x, by
    rw [interpret_conj]
    exact ⟨hu, (interp_symList _ _ [m₁, m₂] (.cons (ev_list [m₁, m₂] 1) (.cons (ev_list [m₁, m₂] 2) .nil)) x).mpr hx⟩⟩)
  rw [interpret_conj, KoreAML.interp_equal hD, KoreAML.interp_equal hD] at hc
  exact ⟨(hc.1 m₁).mp rfl, (hc.2 m₂).mp rfl⟩

/-- `mapElemNotUnitAx`, read: an entry's element is not the unit's. -/
theorem axK_elemNotUnit {a b x : M} (ha : InS I (c.sortName k.key) a) (hb : InS I (c.sortName (valSort k)) b)
    (hu : I.evalSymb (.symbol (c.symName k.unit)) x) (hx : SymE I (c.symName k.elem) [a, b] x) : False := by
  have hax := hC (mapElemNotUnitAx c k)
    ⟨k, hk, by rw [collAxioms_map hkind]; exact List.mem_cons_of_mem _ (List.mem_cons_self ..)⟩ (listVal [a, b]) default
  unfold mapElemNotUnitAx at hax
  dsimp only at hax
  have hb' := KoreAML.interp_guarded hax (fun w hw => by
    rcases mem_two hw with rfl | rfl
    · exact guard_at hD (s := k.key) ha _
    · exact guard_at hD (s := valSort k) hb _)
  rw [interpret_neg] at hb'
  exact hb' ((KoreAML.interp_defined hD).mpr ⟨x, by
    rw [interpret_conj]
    exact ⟨hu, (interp_symList _ _ [a, b] (.cons (ev_list [a, b] 1) (.cons (ev_list [a, b] 2) .nil)) x).mpr hx⟩⟩)

/-- `mapElemAtomAx`, read. -/
theorem axK_elemAtom {a b a' b' r x : M} (ha : InS I (c.sortName k.key) a) (hb : InS I (c.sortName (valSort k)) b)
    (ha' : InS I (c.sortName k.key) a') (hb' : InS I (c.sortName (valSort k)) b') (hr : InS I (c.sortName k.sort) r)
    (hx1 : SymE I (c.symName k.elem) [a', b'] x)
    (hx2 : ∃ y, SymE I (c.symName k.elem) [a, b] y ∧ SymE I (c.symName k.concat) [y, r] x) :
    a = a' ∧ b = b' ∧ I.evalSymb (.symbol (c.symName k.unit)) r := by
  let L := [a, b, a', b', r]
  have hax := hC (mapElemAtomAx c k) ⟨k, hk, by
    rw [collAxioms_map hkind]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))⟩
    (listVal L) default
  unfold mapElemAtomAx at hax
  dsimp only at hax
  have hg := KoreAML.interp_guarded hax (fun w hw => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl
    · exact guard_at hD (s := k.key) ha _
    · exact guard_at hD (s := valSort k) hb _
    · exact guard_at hD (s := k.key) ha' _
    · exact guard_at hD (s := valSort k) hb' _
    · exact guard_at hD (s := k.sort) hr _)
  have hc := hg ((KoreAML.interp_defined hD).mpr ⟨x, by
    rw [interpret_conj]
    refine ⟨(interp_symList _ _ [a', b'] (.cons (ev_list L 3) (.cons (ev_list L 4) .nil)) x).mpr hx1, ?_⟩
    exact (interp_concatElem _ _ (ev_list L 1) (ev_list L 2) (ev_list L 5) x).mpr hx2⟩)
  rw [interpret_conj, interpret_conj, KoreAML.interp_equal hD, KoreAML.interp_equal hD, KoreAML.interp_equal hD] at hc
  exact ⟨((hc.1.1 a).mp rfl), ((hc.1.2 b).mp rfl), (hc.2 r).mp rfl⟩

/-- `mapDecompAx`, read. -/
theorem axK_decomp {a b r m₁ m₂ x : M} (ha : InS I (c.sortName k.key) a) (hb : InS I (c.sortName (valSort k)) b)
    (hr : InS I (c.sortName k.sort) r) (h1 : InS I (c.sortName k.sort) m₁) (h2 : InS I (c.sortName k.sort) m₂)
    (hx1 : ∃ y, SymE I (c.symName k.elem) [a, b] y ∧ SymE I (c.symName k.concat) [y, r] x)
    (hx2 : SymE I (c.symName k.concat) [m₁, m₂] x) :
    (∃ y, InS I (c.sortName k.sort) y ∧
      (∀ z, z = m₁ ↔ ∃ y', SymE I (c.symName k.elem) [a, b] y' ∧ SymE I (c.symName k.concat) [y', y] z) ∧
      ∀ z, z = r ↔ SymE I (c.symName k.concat) [y, m₂] z) ∨
    (∃ y, InS I (c.sortName k.sort) y ∧
      (∀ z, z = m₂ ↔ ∃ y', SymE I (c.symName k.elem) [a, b] y' ∧ SymE I (c.symName k.concat) [y', y] z) ∧
      ∀ z, z = r ↔ SymE I (c.symName k.concat) [m₁, y] z) := by
  let L := [a, b, r, m₁, m₂]
  have hax := hC (mapDecompAx c k) ⟨k, hk, by
    rw [collAxioms_map hkind]
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))⟩
    (listVal L) default
  unfold mapDecompAx at hax
  dsimp only at hax
  have hg := KoreAML.interp_guarded hax (fun w hw => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl
    · exact guard_at hD (s := k.key) ha _
    · exact guard_at hD (s := valSort k) hb _
    · exact guard_at hD (s := k.sort) hr _
    · exact guard_at hD (s := k.sort) h1 _
    · exact guard_at hD (s := k.sort) h2 _)
  have hc := hg ((KoreAML.interp_defined hD).mpr ⟨x, by
    rw [interpret_conj]
    refine ⟨(interp_concatElem _ _ (ev_list L 1) (ev_list L 2) (ev_list L 3) x).mpr hx1, ?_⟩
    exact (interp_symList _ _ [m₁, m₂] (.cons (ev_list L 4) (.cons (ev_list L 5) .nil)) x).mpr hx2⟩)
  rw [interpret_disj, KoreAML.interp_sExists, KoreAML.interp_sExists] at hc
  have hy : ∀ y : M, ((⟨6⟩ : EVar) ∈∈ KoreAML.inhOf (sortP (c.sortName k.sort)) : KoreAML.P).interpret I (listVal6 L y)
      default → InS I (c.sortName k.sort) y := fun y h => by
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

section
variable {c : Semantics} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hI : I ⊧ᴵP Γ c) [OvlOK c]
  {k : CollSig} (R : MapReading c I k)
include hI R

/-- An entry, at values: `elem(⟦a⟧, ⟦b⟧)` is the one-entry map's element. -/
theorem elem_valK {a b : GroundTerm} (ha : c.sortOf a = some k.key) (hb : c.sortOf b = some (valSort k)) (m : M) :
    SymE I (c.symName k.elem) [elemOf c I a, elemOf c I b] m ↔ m = elemOf c I (.map k.sort [(a, b)]) := by
  have hs : c.sortOf (.map k.sort [(a, b)]) = some k.sort :=
    (sortOf_mapK R.coll R.kind R.val).mpr ⟨rfl, entriesOK_consK.mpr ⟨ha, hb, rfl⟩⟩
  rw [← den_sing hI hs KoreAML.val0 m, den_mapOneK_eq R.coll]
  exact (interp_symList _ _ _ (.cons (den_sing hI ha _) (.cons (den_sing hI hb _) .nil)) m).symm

/-- A map's element, its first entry split off: `concat(elem(⟦a⟧, ⟦b⟧), ⟦rest⟧)` holds it. -/
theorem map_firstK {a b : GroundTerm} {es : List (GroundTerm × GroundTerm)}
    (hs : c.sortOf (.map k.sort ((a, b) :: es)) = some k.sort) :
    ∃ y, SymE I (c.symName k.elem) [elemOf c I a, elemOf c I b] y ∧
      SymE I (c.symName k.concat) [y, elemOf c I (.map k.sort es)] (elemOf c I (.map k.sort ((a, b) :: es))) := by
  obtain ⟨hks, hok⟩ := (sortOf_mapK R.coll R.kind R.val).mp hs
  obtain ⟨ha, hb, hrest⟩ := entriesOK_consK.mp hok
  have hsr : c.sortOf (.map k.sort es) = some k.sort := (sortOf_mapK R.coll R.kind R.val).mpr ⟨keysSorted_tail hks, hrest⟩
  cases es with
  | nil =>
    exact ⟨_, (elem_valK hI R ha hb _).mpr rfl, (R.catV hs hsr _).mpr ⟨_, R.catOne ha hb, hs, rfl⟩⟩
  | cons e' es =>
    have hx := (den_sing hI hs KoreAML.val0 _).mpr rfl
    rw [den_mapConsK_eq R.coll] at hx
    exact (interp_concatElem _ _ (den_sing hI ha _) (den_sing hI hb _) (den_sing hI hsr _) _).mp hx

variable (hg : genWf c = true) [OvlOK c] (htr : ∀ a b d, (a, b) ∈ c.subsorts → (b, d) ∈ c.subsorts → (a, d) ∈ c.subsorts)
include hg htr

/-- The unit holds no value's element but the empty map's. -/
theorem map_unitK {w : GroundTerm} (hw : c.sortOf w = some k.sort)
    (hu : I.evalSymb (.symbol (c.symName k.unit)) (elemOf c I w)) : w = .map k.sort [] := by
  have h0 : c.sortOf (.map k.sort []) = some k.sort := (sortOf_mapK R.coll R.kind R.val).mpr ⟨rfl, rfl⟩
  have he := (den_sing hI h0 KoreAML.val0 _).mp ((den_mapNilK R.coll KoreAML.val0 _).mpr hu)
  exact values_apart hI hg htr (apartSort_of_sorted hg hw) hw h0 he

omit hg htr in
/-- **Splitting a value's element.** If a map's element is in `concat(m₁, m₂)`, for elements `m₁`,
`m₂` of its sort, they are maps' elements: by induction on the map's entries, through
`mapUnitSplitAx` at the empty map and `mapDecompAx` at its first entry. -/
theorem map_splitK : ∀ (es : List (GroundTerm × GroundTerm)), c.sortOf (.map k.sort es) = some k.sort →
    ∀ {m₁ m₂ : M}, InS I (c.sortName k.sort) m₁ → InS I (c.sortName k.sort) m₂ →
    SymE I (c.symName k.concat) [m₁, m₂] (elemOf c I (.map k.sort es)) →
    ∃ w₁ w₂, c.sortOf w₁ = some k.sort ∧ c.sortOf w₂ = some k.sort ∧ m₁ = elemOf c I w₁ ∧ m₂ = elemOf c I w₂
  | [], hs, m₁, m₂, h1, h2, hx => by
    have hD := defOK hI
    have hu := (den_mapNilK R.coll KoreAML.val0 _).mp ((den_sing hI hs KoreAML.val0 _).mpr rfl)
    obtain ⟨u1, u2⟩ := axK_unitSplit hD (sat_colls hI) R.mem R.kind h1 h2 hu hx
    exact ⟨_, _, hs, hs, (den_sing hI hs KoreAML.val0 _).mp ((den_mapNilK R.coll KoreAML.val0 _).mpr u1),
      (den_sing hI hs KoreAML.val0 _).mp ((den_mapNilK R.coll KoreAML.val0 _).mpr u2)⟩
  | (a, b) :: es, hs, m₁, m₂, h1, h2, hx => by
    have hD := defOK hI
    obtain ⟨hks, hok⟩ := (sortOf_mapK R.coll R.kind R.val).mp hs
    obtain ⟨ha, hb, hrest⟩ := entriesOK_consK.mp hok
    have hsr : c.sortOf (.map k.sort es) = some k.sort := (sortOf_mapK R.coll R.kind R.val).mpr ⟨keysSorted_tail hks, hrest⟩
    have h1s : c.sortOf (.map k.sort [(a, b)]) = some k.sort :=
      (sortOf_mapK R.coll R.kind R.val).mpr ⟨rfl, entriesOK_consK.mpr ⟨ha, hb, rfl⟩⟩
    have haS : InS I (c.sortName k.key) (elemOf c I a) := (elemOf_spec hI ha KoreAML.val0).2
    have hbS : InS I (c.sortName (valSort k)) (elemOf c I b) := (elemOf_spec hI hb KoreAML.val0).2
    have hrS : InS I (c.sortName k.sort) (elemOf c I (.map k.sort es)) := (elemOf_spec hI hsr KoreAML.val0).2
    rcases axK_decomp hD (sat_colls hI) R.mem R.kind haS hbS hrS h1 h2 (map_firstK hI R hs) hx with
      ⟨y, hy, hm, hr⟩ | ⟨y, hy, hm, hr⟩
    · obtain ⟨u₁, u₂, hu₁, hu₂, rfl, rfl⟩ := map_splitK es hsr hy h2 ((hr _).mp rfl)
      obtain ⟨y', hy', hc⟩ := (hm m₁).mp rfl
      rw [(elem_valK hI R ha hb y').mp hy'] at hc
      obtain ⟨u, -, hus, rfl⟩ := (R.catV h1s hu₁ m₁).mp hc
      exact ⟨u, u₂, hus, hu₂, rfl, rfl⟩
    · obtain ⟨u₁, u₂, hu₁, hu₂, rfl, rfl⟩ := map_splitK es hsr h1 hy ((hr _).mp rfl)
      obtain ⟨y', hy', hc⟩ := (hm m₂).mp rfl
      rw [(elem_valK hI R ha hb y').mp hy'] at hc
      obtain ⟨u, -, hus, rfl⟩ := (R.catV h1s hu₂ m₂).mp hc
      exact ⟨u₁, u, hu₁, hus, rfl, rfl⟩

/-- **An entry holding a value's element**: the map has one entry, whose key's and value's
elements the entry's arguments are (`mapElemNotUnitAx`, `mapElemAtomAx`). -/
theorem map_elemK : ∀ (es : List (GroundTerm × GroundTerm)), c.sortOf (.map k.sort es) = some k.sort →
    ∀ {a b : M}, InS I (c.sortName k.key) a → InS I (c.sortName (valSort k)) b →
    SymE I (c.symName k.elem) [a, b] (elemOf c I (.map k.sort es)) →
    ∃ ka kb, es = [(ka, kb)] ∧ c.sortOf ka = some k.key ∧ c.sortOf kb = some (valSort k) ∧
      a = elemOf c I ka ∧ b = elemOf c I kb
  | [], hs, a, b, ha, hb, hx => by
    have hD := defOK hI
    have hu := (den_mapNilK R.coll KoreAML.val0 _).mp ((den_sing hI hs KoreAML.val0 _).mpr rfl)
    exact (axK_elemNotUnit hD (sat_colls hI) R.mem R.kind ha hb hu hx).elim
  | (ka, kb) :: es, hs, a, b, ha, hb, hx => by
    have hD := defOK hI
    obtain ⟨hks, hok⟩ := (sortOf_mapK R.coll R.kind R.val).mp hs
    obtain ⟨hka, hkb, hrest⟩ := entriesOK_consK.mp hok
    have hsr : c.sortOf (.map k.sort es) = some k.sort := (sortOf_mapK R.coll R.kind R.val).mpr ⟨keysSorted_tail hks, hrest⟩
    have haS : InS I (c.sortName k.key) (elemOf c I ka) := (elemOf_spec hI hka KoreAML.val0).2
    have hbS : InS I (c.sortName (valSort k)) (elemOf c I kb) := (elemOf_spec hI hkb KoreAML.val0).2
    have hrS : InS I (c.sortName k.sort) (elemOf c I (.map k.sort es)) := (elemOf_spec hI hsr KoreAML.val0).2
    obtain ⟨h1, h2, h3⟩ := axK_elemAtom hD (sat_colls hI) R.mem R.kind haS hbS ha hb hrS hx (map_firstK hI R hs)
    have hnil := map_unitK hI R hg htr hsr h3
    cases hnil
    exact ⟨ka, kb, rfl, hka, hkb, h1.symm, h2.symm⟩

end

/-- The symbol `f` with the signature `k0` is the unit, the element or the concatenation of the
map collection `k`, with its signature. -/
def MapRole (k : CollSig) (f : Sym) (k0 : CtorSig) : Prop :=
  (f = k.unit ∧ k0 = ⟨k.unit, [], k.sort⟩) ∨ (f = k.elem ∧ k0 = ⟨k.elem, [k.key, valSort k], k.sort⟩) ∨
    (f = k.concat ∧ k0 = ⟨k.concat, [k.sort, k.sort], k.sort⟩)

section
variable {c : Semantics} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} {k : CollSig}

theorem MapRole.ite (R : MapReading c I k) {f : Sym} {k0 : CtorSig} (h : MapRole k f k0) :
    iteSort? (c.symName f) = none := by
  rcases h with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩
  · exact R.ite _ (List.mem_cons_self ..)
  · exact R.ite _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  · exact R.ite _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))

theorem MapRole.sig (R : MapReading c I k) {f : Sym} {k0 : CtorSig} (h : MapRole k f k0) :
    k0 ∈ kernelSyms c ∧ k0.name = f := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨R.sigs.1, rfl⟩
  · exact ⟨R.sigs.2.1, rfl⟩
  · exact ⟨R.sigs.2.2, rfl⟩

variable (hI : I ⊧ᴵP Γ c) (R : MapReading c I k) (hg : genWf c = true) [OvlOK c]
  (htr : ∀ a b d, (a, b) ∈ c.subsorts → (b, d) ∈ c.subsorts → (a, d) ∈ c.subsorts)
include hI R hg htr

/-- **A map collection's symbol holding a value's element.** If a value's element is what a
symbol of `k` gives on elements of its argument sorts, the elements are values', on which the
symbol's value (`collVal`) is the value. -/
theorem mapK_back {f : Sym} {k0 : CtorSig} (hr : MapRole k f k0) {w : GroundTerm} (hw : c.sortOf w = some k0.result)
    {bs : List M} (hbl : bs.length = (k0.args.map c.sortName).length)
    (hbs : ∀ (i : Nat) x s, bs[i]? = some x → (k0.args.map c.sortName)[i]? = some s → InS I s x)
    (hm : SymE I (c.symName f) bs (elemOf c I w)) :
    ∃ ws, c.sortsOf ws = some k0.args ∧ bs = ws.map (elemOf c I) ∧ c.collVal f ws = some w := by
  have hshape : ∀ {w : GroundTerm}, c.sortOf w = some k.sort → ∃ es, w = .map k.sort es := fun hw => by
    rcases coll_shape R.coll hg R.sortOK hw with ⟨-, h⟩ | ⟨h, -⟩ | ⟨h, -⟩
    · exact h
    · rw [R.kind] at h; cases h
    · rw [R.kind] at h; cases h
  rcases hr with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · match bs, hbl with
    | [], _ =>
      obtain ⟨a, ha, rfl⟩ := hm
      have := map_unitK hI R hg htr hw ha
      subst this
      exact ⟨[], sortsOf_nil, rfl, R.unitV⟩
  · match bs, hbl with
    | [b₁, b₂], _ =>
      obtain ⟨es, rfl⟩ := hshape hw
      obtain ⟨ka, kb, rfl, hka, hkb, rfl, rfl⟩ :=
        map_elemK hI R hg htr es hw (hbs 0 b₁ _ rfl rfl) (hbs 1 b₂ _ rfl rfl) hm
      exact ⟨[ka, kb], sortsOf_two hka hkb, rfl, R.elemV hka hkb⟩
  · match bs, hbl with
    | [b₁, b₂], _ =>
      obtain ⟨es, rfl⟩ := hshape hw
      obtain ⟨w₁, w₂, hw₁, hw₂, rfl, rfl⟩ :=
        map_splitK hI R es hw (hbs 0 b₁ _ rfl rfl) (hbs 1 b₂ _ rfl rfl) hm
      obtain ⟨u, hu, hsu, he⟩ := (R.catV hw₁ hw₂ _).mp hm
      have := values_apart hI hg htr (apartSort_of_sorted hg hw) hw hsu he
      subst this
      exact ⟨[w₁, w₂], sortsOf_two hw₁ hw₂, rfl, hu⟩

end

/-! ## The map collections of a semantics -/

section
variable {c : Semantics} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hI : I ⊧ᴵP Γ c) [OvlOK c]
include hI

/-- The library's `Map` is read downwards. -/
theorem mapReading_lib (hso : collSortOK c Srt.map = true) : MapReading c I mapColl where
  mem := mapColl_mem c
  kind := rfl
  val := rfl
  coll := collOf_map c
  sortOK := hso
  ite := by
    intro f hf
    simp only [mapColl, List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl
    · exact iteSort_mapUnit c
    · exact iteSort_mapElem c
    · exact iteSort_mapConcat c
  sigs := ⟨kernel_hook (by decide), kernel_hook (by decide), kernel_hook (by decide)⟩
  unitV := by
    show c.collVal mapUnit [] = some (.map Srt.map [])
    rw [collVal_hook rfl]; rfl
  elemV := fun {a b} _ _ => by
    show c.collVal mapElem [a, b] = some (.map Srt.map [(a, b)])
    rw [collVal_hook rfl]; rfl
  catV := fun {w₁ w₂} h1 h2 m => by
    show SymE I (c.symName mapConcat) _ m ↔ ∃ u, c.collVal mapConcat [w₁, w₂] = some u ∧ c.sortOf u = some Srt.map ∧ _
    rw [concat_val hI h1 h2 m, collVal_hook rfl]
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨u, join_some.mpr hu,
        hook_sorted (fun he => absurd he (by decide)) (show lookupSig hookSigs mapConcat = some ⟨mapConcat, [Srt.map, Srt.map], Srt.map⟩ by decide)
          (sortsOf_two h1 h2) hu, rfl⟩
    · rintro ⟨u, hu, -, rfl⟩
      exact ⟨u, join_some.mp hu, rfl⟩
  catOne := fun {a b} _ _ => by
    show c.collVal mapConcat [.map Srt.map [(a, b)], .map Srt.map []] = some (.map Srt.map [(a, b)])
    rw [collVal_hook rfl, Exec.hook_concat_eq]
    simp [union, addNew, hasKey, insertE]

/-- A map collection of the definition (a cell map) is read downwards. -/
theorem mapReading_cell {k : CollSig} (hkc : k ∈ c.colls) (hok : collSymsOK c k = true)
    (hso : collSortOK c k.sort = true) (hkind : k.kind = .map) : MapReading c I k := by
  obtain ⟨hco, hsyms, hpu, hpe, hpc⟩ := collSymsOK_spec hok
  rw [hkind, show (builtinColl CollKind.map).unit = mapUnit from rfl] at hpu
  rw [hkind, show (builtinColl CollKind.map).elem = mapElem from rfl] at hpe
  rw [hkind, show (builtinColl CollKind.map).concat = mapConcat from rfl] at hpc
  have hea : elemArgs k = [k.key, valSort k] := by unfold elemArgs; rw [hkind]
  rw [hea] at hpe
  have hval := collSymsOK_val hok hkind
  have hnh : ∀ f ∈ [k.unit, k.elem, k.concat], isHook f = false := fun f hf => (hsyms f hf).1
  have hsorted : ∀ {es : List (GroundTerm × GroundTerm)}, keysSorted es = true → c.entriesOK k.key (valSort k) es = true →
      c.sortOf (.map k.sort es) = some k.sort := fun h1 h2 => (sortOf_mapK hco hkind hval).mpr ⟨h1, h2⟩
  have hU := hnh _ (List.mem_cons_self ..)
  have hE := hnh _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  have hC := hnh _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
  have hitC := (hsyms _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))).2
  exact {
    mem := List.mem_append_right _ hkc
    kind := hkind
    val := hval
    coll := hco
    sortOK := hso
    ite := fun f hf => (hsyms f hf).2
    sigs := ⟨kernel_param (lookupParam_mem hpu), kernel_param (lookupParam_mem hpe), kernel_param (lookupParam_mem hpc)⟩
    unitV := by
      rw [collVal_param hU, paramVal_impl hpu rfl _ (silentKey_of_mem rfl) (by decide) (carrier_of_collSortOK hso)]
      exact filter_sorted (hsorted rfl rfl)
    elemV := fun {a b} ha hb => by
      rw [collVal_param hE, paramVal_impl hpe rfl _ (silentKey_of_mem rfl) (by decide) (carrier_of_collSortOK hso)]
      exact filter_sorted (hsorted rfl (entriesOK_consK.mpr ⟨ha, hb, rfl⟩))
    catV := fun {w₁ w₂} h1 h2 m => by
      rw [param2_val hI hpc rfl hitC h1 h2 m, collVal_param hC]
      constructor
      · rintro ⟨u, hu, rfl⟩
        obtain ⟨k', hk', hsu⟩ := c.paramVal_sorted hu
        rw [hpc] at hk'; cases hk'
        exact ⟨u, hu, hsu, rfl⟩
      · rintro ⟨u, hu, -, rfl⟩
        exact ⟨u, hu, rfl⟩
    catOne := fun {a b} ha hb => by
      rw [collVal_param hC, paramVal_impl hpc rfl _ (silentKey_of_mem rfl) (by decide) (carrier_of_collSortOK hso)]
      dsimp only
      have hun : union [(a, b)] [] = some [(a, b)] := by simp [union, addNew, hasKey, insertE]
      have : ((hook mapConcat [.map k.sort [(a, b)], .map k.sort []]).join.map (GroundTerm.withSort k.sort)) =
          some (.map k.sort [(a, b)]) := by
        rw [Exec.hook_concat_eq]; simp [hun, GroundTerm.withSort]
      rw [this]
      exact filter_sorted (hsorted rfl (entriesOK_consK.mpr ⟨ha, hb, rfl⟩)) }

end

/-! ## A list collection, read in a model -/

section
variable {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}

omit [Inhabited M] in
/-- `concat(elem(φa), ψ)` at singletons: an element of `concat(y, r)` for an element `y` of
`elem(a)`. -/
theorem interp_concatItem {e : Valuation M} (cn en : String) {φa ψ : KoreAML.P} {a r : M}
    (ha : ∀ m, φa.interpret I e m ↔ m = a) (hr : ∀ m, ψ.interpret I e m ↔ m = r) (m : M) :
    (KoreAML.appList (symP cn) [KoreAML.appList (symP en) [φa], ψ]).interpret I e m ↔
      ∃ y, SymE I en [a] y ∧ SymE I cn [y, r] m := by
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
        exact ⟨y, (interp_symList en _ [a] (.cons ha .nil) y).mp hb1, h, hh, happ⟩
  · rintro ⟨y, hy, h, hh, happ⟩
    exact ⟨h, hh, [y, r], .cons ((interp_symList en _ [a] (.cons ha .nil) y).mpr hy)
      (.cons ((hr r).mpr rfl) .nil), happ⟩

/-- The valuation `listVal L` with the variable `n` given `a`. -/
def listValAt (L : List M) (n : Nat) (a : M) : Valuation M :=
  ⟨Function.update (listVal L).evalEvar ⟨n⟩ a, (listVal L).evalSvar⟩

theorem ev_listAt (L : List M) (n : Nat) (a : M) {j : Nat} (hj : j ≠ n) (m : M) :
    (Pattern.evar ⟨j⟩ : KoreAML.P).interpret I (listValAt L n a) m ↔ m = L.getD (j - 1) default := by
  rw [KoreAML.interp_evar]
  unfold listValAt
  dsimp only
  rw [Function.update_noteq (by intro h; cases h; exact hj rfl)]
  exact Iff.rfl

theorem ev_listAt_self (L : List M) (n : Nat) (a : M) (m : M) :
    (Pattern.evar ⟨n⟩ : KoreAML.P).interpret I (listValAt L n a) m ↔ m = a := by
  rw [KoreAML.interp_evar]
  unfold listValAt
  dsimp only
  rw [Function.update_same]

end

theorem collAxioms_list {c : Semantics} {k : CollSig} (h : k.kind = .list) : collAxioms c k = listCollAxioms c k := by
  unfold collAxioms; rw [h]

section
variable {c : Semantics} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
  (hD : DefOK I) (hC : I ⊧ᴵP ΓColls c) {k : CollSig} (hk : k ∈ c.allColls) (hkind : k.kind = .list)
include hD hC hk hkind

/-- `listUnitSplitAx`, read. -/
theorem axL_unitSplit {l₁ l₂ x : M} (h1 : InS I (c.sortName k.sort) l₁) (h2 : InS I (c.sortName k.sort) l₂)
    (hu : I.evalSymb (.symbol (c.symName k.unit)) x) (hx : SymE I (c.symName k.concat) [l₁, l₂] x) :
    I.evalSymb (.symbol (c.symName k.unit)) l₁ ∧ I.evalSymb (.symbol (c.symName k.unit)) l₂ := by
  have hax := hC (listUnitSplitAx c k) ⟨k, hk, by rw [collAxioms_list hkind]; exact List.mem_cons_self ..⟩
    (listVal [l₁, l₂]) default
  unfold listUnitSplitAx at hax
  dsimp only at hax
  have hb := KoreAML.interp_guarded hax (fun w hw => by
    rcases mem_two hw with rfl | rfl
    · exact guard_at hD (s := k.sort) h1 _
    · exact guard_at hD (s := k.sort) h2 _)
  have hc := hb ((KoreAML.interp_defined hD).mpr ⟨x, by
    rw [interpret_conj]
    exact ⟨hu, (interp_symList _ _ [l₁, l₂] (.cons (ev_list [l₁, l₂] 1) (.cons (ev_list [l₁, l₂] 2) .nil)) x).mpr hx⟩⟩)
  rw [interpret_conj, KoreAML.interp_equal hD, KoreAML.interp_equal hD] at hc
  exact ⟨(hc.1 l₁).mp rfl, (hc.2 l₂).mp rfl⟩

/-- `listElemNotUnitAx`, read. -/
theorem axL_elemNotUnit {a x : M} (ha : InS I (c.sortName k.key) a)
    (hu : I.evalSymb (.symbol (c.symName k.unit)) x) (hx : SymE I (c.symName k.elem) [a] x) : False := by
  have hax := hC (listElemNotUnitAx c k)
    ⟨k, hk, by rw [collAxioms_list hkind]; exact List.mem_cons_of_mem _ (List.mem_cons_self ..)⟩ (listVal [a]) default
  unfold listElemNotUnitAx at hax
  dsimp only at hax
  have hb' := KoreAML.interp_guarded hax (fun w hw => by
    rw [mem_one hw]
    exact guard_at hD (s := k.key) ha _)
  rw [interpret_neg] at hb'
  exact hb' ((KoreAML.interp_defined hD).mpr ⟨x, by
    rw [interpret_conj]
    exact ⟨hu, (interp_symList _ _ [a] (.cons (ev_list [a] 1) .nil) x).mpr hx⟩⟩)

/-- `listElemAtomAx`, read. -/
theorem axL_elemAtom {a a' r x : M} (ha : InS I (c.sortName k.key) a) (ha' : InS I (c.sortName k.key) a')
    (hr : InS I (c.sortName k.sort) r) (hx1 : SymE I (c.symName k.elem) [a'] x)
    (hx2 : ∃ y, SymE I (c.symName k.elem) [a] y ∧ SymE I (c.symName k.concat) [y, r] x) :
    a = a' ∧ I.evalSymb (.symbol (c.symName k.unit)) r := by
  let L := [a, a', r]
  have hax := hC (listElemAtomAx c k) ⟨k, hk, by
    rw [collAxioms_list hkind]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))⟩
    (listVal L) default
  unfold listElemAtomAx at hax
  dsimp only at hax
  have hg := KoreAML.interp_guarded hax (fun w hw => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl
    · exact guard_at hD (s := k.key) ha _
    · exact guard_at hD (s := k.key) ha' _
    · exact guard_at hD (s := k.sort) hr _)
  have hc := hg ((KoreAML.interp_defined hD).mpr ⟨x, by
    rw [interpret_conj]
    refine ⟨(interp_symList _ _ [a'] (.cons (ev_list L 2) .nil) x).mpr hx1, ?_⟩
    exact (interp_concatItem _ _ (ev_list L 1) (ev_list L 3) x).mpr hx2⟩)
  rw [interpret_conj, KoreAML.interp_equal hD, KoreAML.interp_equal hD] at hc
  exact ⟨(hc.1 a).mp rfl, (hc.2 r).mp rfl⟩

/-- `listDecompAx`, read. -/
theorem axL_decomp {a r l₁ l₂ x : M} (ha : InS I (c.sortName k.key) a) (hr : InS I (c.sortName k.sort) r)
    (h1 : InS I (c.sortName k.sort) l₁) (h2 : InS I (c.sortName k.sort) l₂)
    (hx1 : ∃ y, SymE I (c.symName k.elem) [a] y ∧ SymE I (c.symName k.concat) [y, r] x)
    (hx2 : SymE I (c.symName k.concat) [l₁, l₂] x) :
    (I.evalSymb (.symbol (c.symName k.unit)) l₁ ∧
      ∀ z, z = l₂ ↔ ∃ y', SymE I (c.symName k.elem) [a] y' ∧ SymE I (c.symName k.concat) [y', r] z) ∨
    (∃ y, InS I (c.sortName k.sort) y ∧
      (∀ z, z = l₁ ↔ ∃ y', SymE I (c.symName k.elem) [a] y' ∧ SymE I (c.symName k.concat) [y', y] z) ∧
      ∀ z, z = r ↔ SymE I (c.symName k.concat) [y, l₂] z) := by
  let L := [a, r, l₁, l₂]
  have hax := hC (listDecompAx c k) ⟨k, hk, by
    rw [collAxioms_list hkind]
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_self ..))))⟩
    (listVal L) default
  unfold listDecompAx at hax
  dsimp only at hax
  have hg := KoreAML.interp_guarded hax (fun w hw => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl
    · exact guard_at hD (s := k.key) ha _
    · exact guard_at hD (s := k.sort) hr _
    · exact guard_at hD (s := k.sort) h1 _
    · exact guard_at hD (s := k.sort) h2 _)
  have hc := hg ((KoreAML.interp_defined hD).mpr ⟨x, by
    rw [interpret_conj]
    refine ⟨(interp_concatItem _ _ (ev_list L 1) (ev_list L 2) x).mpr hx1, ?_⟩
    exact (interp_symList _ _ [l₁, l₂] (.cons (ev_list L 3) (.cons (ev_list L 4) .nil)) x).mpr hx2⟩)
  rw [interpret_disj, KoreAML.interp_sExists] at hc
  have hy : ∀ y : M, ((⟨5⟩ : EVar) ∈∈ KoreAML.inhOf (sortP (c.sortName k.sort)) : KoreAML.P).interpret I
      (listValAt L 5 y) default → InS I (c.sortName k.sort) y := fun y h => by
    rw [KoreAML.interp_member hD] at h
    have h' := (inS_iff _).mp h
    unfold listValAt at h'
    simpa using h'
  rcases hc with hc | ⟨y, hym, hyb⟩
  · left
    rw [interpret_conj, KoreAML.interp_equal hD, KoreAML.interp_equal hD] at hc
    exact ⟨(hc.1 l₁).mp rfl, fun z => (ev_list L 4 z).symm.trans ((hc.2 z).trans
      (interp_concatItem _ _ (ev_list L 1) (ev_list L 2) z))⟩
  · right
    have hyb' : (_ : KoreAML.P).interpret I (listValAt L 5 y) default := hyb
    rw [interpret_conj, KoreAML.interp_equal hD, KoreAML.interp_equal hD] at hyb'
    refine ⟨y, hy y hym, fun z => ?_, fun z => ?_⟩
    · exact (ev_listAt L 5 y (j := 3) (by decide) z).symm.trans ((hyb'.1 z).trans
        (interp_concatItem _ _ (ev_listAt L 5 y (j := 1) (by decide)) (ev_listAt_self L 5 y) z))
    · exact (ev_listAt L 5 y (j := 2) (by decide) z).symm.trans ((hyb'.2 z).trans
        (interp_symList _ _ [y, l₂] (.cons (ev_listAt_self L 5 y) (.cons (ev_listAt L 5 y (j := 4) (by decide)) .nil)) z))

end

section
variable {c : Semantics} {k : CollSig} (hco : c.collOf k.sort = some k)
include hco

theorem sortOf_listK (hkind : k.kind = .list) {es : List GroundTerm} :
    c.sortOf (.list k.sort es) = some k.sort ↔ ∀ e ∈ es, c.sortOf e = some k.key := by
  rw [sortOf_listS]
  constructor
  · rintro ⟨k', hk', -, h, -⟩
    rw [hco] at hk'; cases hk'; exact h
  · intro h
    exact ⟨k, hco, hkind, h, rfl⟩

theorem den_listNilK {M : Type} {I : Interpretation KoreAML.Sym M} (e : Valuation M) (m : M) :
    (den c (.list k.sort [])).interpret I e m ↔ I.evalSymb (.symbol (c.symName k.unit)) m := by
  unfold den KoreAML.den
  rw [GroundTerm.kore, collSig_eq .list hco, GroundTerm.koreElems]
  unfold KoreAML.ap
  rw [KoreAML.tr_app0, KoreAML.trArgs_nil]
  exact Iff.rfl

theorem den_listOneK_eq (a : GroundTerm) :
    den c (.list k.sort [a]) = KoreAML.appList (symP (c.symName k.elem)) [den c a] := by
  unfold den KoreAML.den
  rw [GroundTerm.kore, collSig_eq .list hco, GroundTerm.koreElems]
  unfold KoreAML.ap
  rw [KoreAML.tr_app0, trArgs_appList]
  rfl

theorem den_listConsK_eq (a e' : GroundTerm) (es : List GroundTerm) :
    den c (.list k.sort (a :: e' :: es)) = KoreAML.appList (symP (c.symName k.concat))
      [KoreAML.appList (symP (c.symName k.elem)) [den c a], den c (.list k.sort (e' :: es))] := by
  have h2 : den c (.list k.sort (e' :: es)) = KoreAML.tr ⟨[], []⟩ (GroundTerm.koreElems c k (e' :: es)) := by
    unfold den KoreAML.den; rw [GroundTerm.kore, collSig_eq .list hco]
  rw [h2]
  unfold den KoreAML.den
  rw [GroundTerm.kore, collSig_eq .list hco, GroundTerm.koreElems.eq_3 c k a (e' :: es) (List.cons_ne_nil _ _)]
  unfold KoreAML.ap
  rw [KoreAML.tr_app0, trArgs_appList]
  simp only [List.map_cons, List.map_nil]
  rw [KoreAML.tr_app0, trArgs_appList]
  rfl

end

/-- **What the downward reading takes of a list collection `k` in a model `I`**: as `MapReading`,
with the empty list, the one-item list and concatenation. -/
structure ListReading (c : Semantics) {M : Type} [Inhabited M] (I : Interpretation KoreAML.Sym M) (k : CollSig) :
    Prop where
  mem : k ∈ c.allColls
  kind : k.kind = .list
  coll : c.collOf k.sort = some k
  sortOK : collSortOK c k.sort = true
  ite : ∀ f ∈ [k.unit, k.elem, k.concat], iteSort? (c.symName f) = none
  sigs : (⟨k.unit, [], k.sort⟩ : CtorSig) ∈ kernelSyms c ∧ (⟨k.elem, [k.key], k.sort⟩ : CtorSig) ∈ kernelSyms c ∧
    (⟨k.concat, [k.sort, k.sort], k.sort⟩ : CtorSig) ∈ kernelSyms c
  unitV : c.collVal k.unit [] = some (.list k.sort [])
  elemV : ∀ {a : GroundTerm}, c.sortOf a = some k.key → c.collVal k.elem [a] = some (.list k.sort [a])
  catV : ∀ {w₁ w₂ : GroundTerm}, c.sortOf w₁ = some k.sort → c.sortOf w₂ = some k.sort → ∀ m,
    SymE I (c.symName k.concat) [elemOf c I w₁, elemOf c I w₂] m ↔
      ∃ u, c.collVal k.concat [w₁, w₂] = some u ∧ c.sortOf u = some k.sort ∧ m = elemOf c I u
  catOne : ∀ {a : GroundTerm}, c.sortOf a = some k.key →
    c.collVal k.concat [.list k.sort [a], .list k.sort []] = some (.list k.sort [a])

section
variable {c : Semantics} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hI : I ⊧ᴵP Γ c) [OvlOK c]
  {k : CollSig} (R : ListReading c I k)
include hI R

omit hI in
theorem list_tail {e : GroundTerm} {es : List GroundTerm} (hs : c.sortOf (.list k.sort (e :: es)) = some k.sort) :
    c.sortOf e = some k.key ∧ c.sortOf (.list k.sort es) = some k.sort := by
  have h := (sortOf_listK R.coll R.kind).mp hs
  exact ⟨h e (List.mem_cons_self ..),
    (sortOf_listK R.coll R.kind).mpr fun e' he' => h e' (List.mem_cons_of_mem _ he')⟩

omit hI in
theorem list_one {a : GroundTerm} (ha : c.sortOf a = some k.key) : c.sortOf (.list k.sort [a]) = some k.sort :=
  (sortOf_listK R.coll R.kind).mpr fun e he => by rw [mem_one he]; exact ha

/-- An item, at values: `elem(⟦a⟧)` is the one-item list's element. -/
theorem elem_valL {a : GroundTerm} (ha : c.sortOf a = some k.key) (m : M) :
    SymE I (c.symName k.elem) [elemOf c I a] m ↔ m = elemOf c I (.list k.sort [a]) := by
  rw [← den_sing hI (list_one R ha) KoreAML.val0 m, den_listOneK_eq R.coll]
  exact (interp_symList _ _ _ (.cons (den_sing hI ha _) .nil) m).symm

/-- A list's element, its first item split off: `concat(elem(⟦a⟧), ⟦rest⟧)` holds it. -/
theorem list_firstK {a : GroundTerm} {es : List GroundTerm} (hs : c.sortOf (.list k.sort (a :: es)) = some k.sort) :
    ∃ y, SymE I (c.symName k.elem) [elemOf c I a] y ∧
      SymE I (c.symName k.concat) [y, elemOf c I (.list k.sort es)] (elemOf c I (.list k.sort (a :: es))) := by
  obtain ⟨ha, hsr⟩ := list_tail R hs
  cases es with
  | nil =>
    exact ⟨_, (elem_valL hI R ha _).mpr rfl, (R.catV hs hsr _).mpr ⟨_, R.catOne ha, hs, rfl⟩⟩
  | cons e' es =>
    have hx := (den_sing hI hs KoreAML.val0 _).mpr rfl
    rw [den_listConsK_eq R.coll] at hx
    exact (interp_concatItem _ _ (den_sing hI ha _) (den_sing hI hsr _) _).mp hx

/-- **Splitting a list value's element.** If a list's element is in `concat(l₁, l₂)`, for elements
`l₁`, `l₂` of its sort, they are lists' elements: by induction on the list, through
`listUnitSplitAx` at the empty list and `listDecompAx` at its first item. -/
theorem list_splitK : ∀ (es : List GroundTerm), c.sortOf (.list k.sort es) = some k.sort →
    ∀ {l₁ l₂ : M}, InS I (c.sortName k.sort) l₁ → InS I (c.sortName k.sort) l₂ →
    SymE I (c.symName k.concat) [l₁, l₂] (elemOf c I (.list k.sort es)) →
    ∃ w₁ w₂, c.sortOf w₁ = some k.sort ∧ c.sortOf w₂ = some k.sort ∧ l₁ = elemOf c I w₁ ∧ l₂ = elemOf c I w₂
  | [], hs, l₁, l₂, h1, h2, hx => by
    have hD := defOK hI
    have hu := (den_listNilK R.coll KoreAML.val0 _).mp ((den_sing hI hs KoreAML.val0 _).mpr rfl)
    obtain ⟨u1, u2⟩ := axL_unitSplit hD (sat_colls hI) R.mem R.kind h1 h2 hu hx
    exact ⟨_, _, hs, hs, (den_sing hI hs KoreAML.val0 _).mp ((den_listNilK R.coll KoreAML.val0 _).mpr u1),
      (den_sing hI hs KoreAML.val0 _).mp ((den_listNilK R.coll KoreAML.val0 _).mpr u2)⟩
  | a :: es, hs, l₁, l₂, h1, h2, hx => by
    have hD := defOK hI
    obtain ⟨ha, hsr⟩ := list_tail R hs
    have h0 : c.sortOf (.list k.sort []) = some k.sort := (sortOf_listK R.coll R.kind).mpr fun e he => by cases he
    have haS : InS I (c.sortName k.key) (elemOf c I a) := (elemOf_spec hI ha KoreAML.val0).2
    have hrS : InS I (c.sortName k.sort) (elemOf c I (.list k.sort es)) := (elemOf_spec hI hsr KoreAML.val0).2
    rcases axL_decomp hD (sat_colls hI) R.mem R.kind haS hrS h1 h2 (list_firstK hI R hs) hx with
      ⟨hu, hl⟩ | ⟨y, hy, hm, hr⟩
    · refine ⟨_, _, h0, hs, (den_sing hI h0 KoreAML.val0 _).mp ((den_listNilK R.coll KoreAML.val0 _).mpr hu), ?_⟩
      exact ((hl _).mpr (list_firstK hI R hs)).symm
    · obtain ⟨u₁, u₂, hu₁, hu₂, rfl, rfl⟩ := list_splitK es hsr hy h2 ((hr _).mp rfl)
      obtain ⟨y', hy', hc⟩ := (hm l₁).mp rfl
      rw [(elem_valL hI R ha y').mp hy'] at hc
      obtain ⟨u, -, hus, rfl⟩ := (R.catV (list_one R ha) hu₁ l₁).mp hc
      exact ⟨u, u₂, hus, hu₂, rfl, rfl⟩

variable (hg : genWf c = true) [OvlOK c] (htr : ∀ a b d, (a, b) ∈ c.subsorts → (b, d) ∈ c.subsorts → (a, d) ∈ c.subsorts)
include hg htr

/-- The unit holds no value's element but the empty list's. -/
theorem list_unitK {w : GroundTerm} (hw : c.sortOf w = some k.sort)
    (hu : I.evalSymb (.symbol (c.symName k.unit)) (elemOf c I w)) : w = .list k.sort [] := by
  have h0 : c.sortOf (.list k.sort []) = some k.sort := (sortOf_listK R.coll R.kind).mpr fun e he => by cases he
  have he := (den_sing hI h0 KoreAML.val0 _).mp ((den_listNilK R.coll KoreAML.val0 _).mpr hu)
  exact values_apart hI hg htr (apartSort_of_sorted hg hw) hw h0 he

/-- **An item holding a value's element**: the list has one item, whose element the item's
argument is (`listElemNotUnitAx`, `listElemAtomAx`). -/
theorem list_elemK : ∀ (es : List GroundTerm), c.sortOf (.list k.sort es) = some k.sort →
    ∀ {b : M}, InS I (c.sortName k.key) b → SymE I (c.symName k.elem) [b] (elemOf c I (.list k.sort es)) →
    ∃ e, es = [e] ∧ c.sortOf e = some k.key ∧ b = elemOf c I e
  | [], hs, b, hb, hx => by
    have hD := defOK hI
    have hu := (den_listNilK R.coll KoreAML.val0 _).mp ((den_sing hI hs KoreAML.val0 _).mpr rfl)
    exact (axL_elemNotUnit hD (sat_colls hI) R.mem R.kind hb hu hx).elim
  | e :: es, hs, b, hb, hx => by
    have hD := defOK hI
    obtain ⟨he, hsr⟩ := list_tail R hs
    have heS : InS I (c.sortName k.key) (elemOf c I e) := (elemOf_spec hI he KoreAML.val0).2
    have hrS : InS I (c.sortName k.sort) (elemOf c I (.list k.sort es)) := (elemOf_spec hI hsr KoreAML.val0).2
    obtain ⟨h1, h2⟩ := axL_elemAtom hD (sat_colls hI) R.mem R.kind heS hb hrS hx (list_firstK hI R hs)
    have hnil := list_unitK hI R hg htr hsr h2
    cases hnil
    exact ⟨e, rfl, he, h1.symm⟩

end

/-- The symbol `f` with the signature `k0` is the unit, the element or the concatenation of the
list collection `k`, with its signature. -/
def ListRole (k : CollSig) (f : Sym) (k0 : CtorSig) : Prop :=
  (f = k.unit ∧ k0 = ⟨k.unit, [], k.sort⟩) ∨ (f = k.elem ∧ k0 = ⟨k.elem, [k.key], k.sort⟩) ∨
    (f = k.concat ∧ k0 = ⟨k.concat, [k.sort, k.sort], k.sort⟩)

section
variable {c : Semantics} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} {k : CollSig}

theorem ListRole.ite (R : ListReading c I k) {f : Sym} {k0 : CtorSig} (h : ListRole k f k0) :
    iteSort? (c.symName f) = none := by
  rcases h with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩
  · exact R.ite _ (List.mem_cons_self ..)
  · exact R.ite _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  · exact R.ite _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))

theorem ListRole.sig (R : ListReading c I k) {f : Sym} {k0 : CtorSig} (h : ListRole k f k0) :
    k0 ∈ kernelSyms c ∧ k0.name = f := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨R.sigs.1, rfl⟩
  · exact ⟨R.sigs.2.1, rfl⟩
  · exact ⟨R.sigs.2.2, rfl⟩

variable (hI : I ⊧ᴵP Γ c) (R : ListReading c I k) (hg : genWf c = true) [OvlOK c]
  (htr : ∀ a b d, (a, b) ∈ c.subsorts → (b, d) ∈ c.subsorts → (a, d) ∈ c.subsorts)
include hI R hg htr

/-- **A list collection's symbol holding a value's element**, as `mapK_back`. -/
theorem listK_back {f : Sym} {k0 : CtorSig} (hr : ListRole k f k0) {w : GroundTerm} (hw : c.sortOf w = some k0.result)
    {bs : List M} (hbl : bs.length = (k0.args.map c.sortName).length)
    (hbs : ∀ (i : Nat) x s, bs[i]? = some x → (k0.args.map c.sortName)[i]? = some s → InS I s x)
    (hm : SymE I (c.symName f) bs (elemOf c I w)) :
    ∃ ws, c.sortsOf ws = some k0.args ∧ bs = ws.map (elemOf c I) ∧ c.collVal f ws = some w := by
  have hshape : ∀ {w : GroundTerm}, c.sortOf w = some k.sort → ∃ es, w = .list k.sort es := fun hw => by
    rcases coll_shape R.coll hg R.sortOK hw with ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, h⟩
    · rcases h with h | h <;> (rw [R.kind] at h; cases h)
    · rw [R.kind] at h; cases h
    · exact h
  rcases hr with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · match bs, hbl with
    | [], _ =>
      obtain ⟨a, ha, rfl⟩ := hm
      have := list_unitK hI R hg htr hw ha
      subst this
      exact ⟨[], sortsOf_nil, rfl, R.unitV⟩
  · match bs, hbl with
    | [b₁], _ =>
      obtain ⟨es, rfl⟩ := hshape hw
      obtain ⟨e, rfl, he, rfl⟩ := list_elemK hI R hg htr es hw (hbs 0 b₁ _ rfl rfl) hm
      exact ⟨[e], sortsOf_cons.mpr ⟨_, _, he, sortsOf_nil, rfl⟩, rfl, R.elemV he⟩
  · match bs, hbl with
    | [b₁, b₂], _ =>
      obtain ⟨es, rfl⟩ := hshape hw
      obtain ⟨w₁, w₂, hw₁, hw₂, rfl, rfl⟩ :=
        list_splitK hI R es hw (hbs 0 b₁ _ rfl rfl) (hbs 1 b₂ _ rfl rfl) hm
      obtain ⟨u, hu, hsu, he⟩ := (R.catV hw₁ hw₂ _).mp hm
      have := values_apart hI hg htr (apartSort_of_sorted hg hw) hw hsu he
      subst this
      exact ⟨[w₁, w₂], sortsOf_two hw₁ hw₂, rfl, hu⟩

end

/-! ## The list collections of a semantics -/

/-- The library's list collection. -/
def listColl : CollSig := ⟨Srt.list, .list, Srt.kitem, none, listUnit, listElem, listConcat⟩

theorem listColl_mem (c : Semantics) : listColl ∈ c.allColls :=
  List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))

theorem collOf_listColl (c : Semantics) : c.collOf Srt.list = some listColl := rfl

theorem hook_listConcat_eq (vs : List GroundTerm) :
    hook listConcat vs = some (match vs with
      | [.list _ a, .list _ b] => some (.list Srt.list (a ++ b)) | _ => none) := rfl

section
variable {c : Semantics} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hI : I ⊧ᴵP Γ c) [OvlOK c]
include hI

/-- The library's `List` is read downwards. -/
theorem listReading_lib (hso : collSortOK c Srt.list = true) : ListReading c I listColl where
  mem := listColl_mem c
  kind := rfl
  coll := collOf_listColl c
  sortOK := hso
  ite := by
    intro f hf
    simp only [listColl, List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl <;> exact iteSort_reg (by decide) (by decide)
  sigs := ⟨kernel_hook (by decide), kernel_hook (by decide), kernel_hook (by decide)⟩
  unitV := by
    show c.collVal listUnit [] = some (.list Srt.list [])
    rw [collVal_hook rfl]; rfl
  elemV := fun {a} _ => by
    show c.collVal listElem [a] = some (.list Srt.list [a])
    rw [collVal_hook rfl]; rfl
  catV := fun {w₁ w₂} h1 h2 m => by
    show SymE I (c.symName listConcat) _ m ↔ ∃ u, c.collVal listConcat [w₁, w₂] = some u ∧ c.sortOf u = some Srt.list ∧ _
    have hks : lookupSig hookSigs listConcat = some ⟨listConcat, [Srt.list, Srt.list], Srt.list⟩ := by decide
    rw [hook2_val hI hks (iteSort_reg (by decide) (by decide)) (silentKey_of_collPatternHook rfl) h1 h2 m,
      collVal_hook rfl]
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨u, join_some.mpr hu, hook_sorted (fun he => absurd he (by decide)) hks (sortsOf_two h1 h2) hu, rfl⟩
    · rintro ⟨u, hu, -, rfl⟩
      exact ⟨u, join_some.mp hu, rfl⟩
  catOne := fun {a} _ => by
    show c.collVal listConcat [.list Srt.list [a], .list Srt.list []] = some (.list Srt.list [a])
    rw [collVal_hook rfl]; rfl

/-- A list collection of the definition is read downwards. -/
theorem listReading_cell {k : CollSig} (hkc : k ∈ c.colls) (hok : collSymsOK c k = true)
    (hso : collSortOK c k.sort = true) (hkind : k.kind = .list) : ListReading c I k := by
  obtain ⟨hco, hsyms, hpu, hpe, hpc⟩ := collSymsOK_spec hok
  rw [hkind, show (builtinColl CollKind.list).unit = listUnit from rfl] at hpu
  rw [hkind, show (builtinColl CollKind.list).elem = listElem from rfl] at hpe
  rw [hkind, show (builtinColl CollKind.list).concat = listConcat from rfl] at hpc
  have hea : elemArgs k = [k.key] := by unfold elemArgs; rw [hkind]
  rw [hea] at hpe
  have hnh : ∀ f ∈ [k.unit, k.elem, k.concat], isHook f = false := fun f hf => (hsyms f hf).1
  have hsorted : ∀ {es : List GroundTerm}, (∀ e ∈ es, c.sortOf e = some k.key) →
      c.sortOf (.list k.sort es) = some k.sort := fun h => (sortOf_listK hco hkind).mpr h
  have hU := hnh _ (List.mem_cons_self ..)
  have hE := hnh _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  have hC := hnh _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
  have hitC := (hsyms _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))).2
  exact {
    mem := List.mem_append_right _ hkc
    kind := hkind
    coll := hco
    sortOK := hso
    ite := fun f hf => (hsyms f hf).2
    sigs := ⟨kernel_param (lookupParam_mem hpu), kernel_param (lookupParam_mem hpe), kernel_param (lookupParam_mem hpc)⟩
    unitV := by
      rw [collVal_param hU, paramVal_impl hpu rfl _ (silentKey_of_mem rfl) (by decide) (carrier_of_collSortOK hso)]
      exact filter_sorted (hsorted fun e he => by cases he)
    elemV := fun {a} ha => by
      rw [collVal_param hE, paramVal_impl hpe rfl _ (silentKey_of_mem rfl) (by decide) (carrier_of_collSortOK hso)]
      exact filter_sorted (hsorted fun e he => by rw [mem_one he]; exact ha)
    catV := fun {w₁ w₂} h1 h2 m => by
      rw [param2_val hI hpc rfl hitC h1 h2 m, collVal_param hC]
      constructor
      · rintro ⟨u, hu, rfl⟩
        obtain ⟨k', hk', hsu⟩ := c.paramVal_sorted hu
        rw [hpc] at hk'; cases hk'
        exact ⟨u, hu, hsu, rfl⟩
      · rintro ⟨u, hu, -, rfl⟩
        exact ⟨u, hu, rfl⟩
    catOne := fun {a} ha => by
      rw [collVal_param hC, paramVal_impl hpc rfl _ (silentKey_of_mem rfl) (by decide) (carrier_of_collSortOK hso)]
      exact filter_sorted (hsorted fun e he => by rw [mem_one he]; exact ha) }

end

/-! ## A set collection, read in a model -/

theorem collAxioms_set {c : Semantics} {k : CollSig} (h : k.kind = .set) : collAxioms c k = setCollAxioms c k := by
  unfold collAxioms; rw [h]

section
variable {c : Semantics} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
  (hD : DefOK I) (hC : I ⊧ᴵP ΓColls c) {k : CollSig} (hk : k ∈ c.allColls) (hkind : k.kind = .set)
include hD hC hk hkind

/-- `setUnitSplitAx`, read: the parts of the unit's element under `concat` are the unit's. -/
theorem axS_unitSplit {s₁ s₂ x : M} (h1 : InS I (c.sortName k.sort) s₁) (h2 : InS I (c.sortName k.sort) s₂)
    (hu : I.evalSymb (.symbol (c.symName k.unit)) x) (hx : SymE I (c.symName k.concat) [s₁, s₂] x) :
    I.evalSymb (.symbol (c.symName k.unit)) s₁ ∧ I.evalSymb (.symbol (c.symName k.unit)) s₂ := by
  have hax := hC (setUnitSplitAx c k) ⟨k, hk, by rw [collAxioms_set hkind]; exact List.mem_cons_self ..⟩
    (listVal [s₁, s₂]) default
  unfold setUnitSplitAx at hax
  dsimp only at hax
  have hb := KoreAML.interp_guarded hax (fun w hw => by
    rcases mem_two hw with rfl | rfl
    · exact guard_at hD (s := k.sort) h1 _
    · exact guard_at hD (s := k.sort) h2 _)
  have hc := hb ((KoreAML.interp_defined hD).mpr ⟨x, by
    rw [interpret_conj]
    exact ⟨hu, (interp_symList _ _ [s₁, s₂] (.cons (ev_list [s₁, s₂] 1) (.cons (ev_list [s₁, s₂] 2) .nil)) x).mpr hx⟩⟩)
  rw [interpret_conj, KoreAML.interp_equal hD, KoreAML.interp_equal hD] at hc
  exact ⟨(hc.1 s₁).mp rfl, (hc.2 s₂).mp rfl⟩

/-- `setElemNotUnitAx`, read. -/
theorem axS_elemNotUnit {a x : M} (ha : InS I (c.sortName k.key) a)
    (hu : I.evalSymb (.symbol (c.symName k.unit)) x) (hx : SymE I (c.symName k.elem) [a] x) : False := by
  have hax := hC (setElemNotUnitAx c k)
    ⟨k, hk, by rw [collAxioms_set hkind]; exact List.mem_cons_of_mem _ (List.mem_cons_self ..)⟩ (listVal [a]) default
  unfold setElemNotUnitAx at hax
  dsimp only at hax
  have hb' := KoreAML.interp_guarded hax (fun w hw => by
    rw [mem_one hw]
    exact guard_at hD (s := k.key) ha _)
  rw [interpret_neg] at hb'
  exact hb' ((KoreAML.interp_defined hD).mpr ⟨x, by
    rw [interpret_conj]
    exact ⟨hu, (interp_symList _ _ [a] (.cons (ev_list [a] 1) .nil) x).mpr hx⟩⟩)

/-- `setElemAtomAx`, read. -/
theorem axS_elemAtom {a a' r x : M} (ha : InS I (c.sortName k.key) a) (ha' : InS I (c.sortName k.key) a')
    (hr : InS I (c.sortName k.sort) r) (hx1 : SymE I (c.symName k.elem) [a'] x)
    (hx2 : ∃ y, SymE I (c.symName k.elem) [a] y ∧ SymE I (c.symName k.concat) [y, r] x) :
    a = a' ∧ I.evalSymb (.symbol (c.symName k.unit)) r := by
  let L := [a, a', r]
  have hax := hC (setElemAtomAx c k) ⟨k, hk, by
    rw [collAxioms_set hkind]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))⟩
    (listVal L) default
  unfold setElemAtomAx at hax
  dsimp only at hax
  have hg := KoreAML.interp_guarded hax (fun w hw => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl
    · exact guard_at hD (s := k.key) ha _
    · exact guard_at hD (s := k.key) ha' _
    · exact guard_at hD (s := k.sort) hr _)
  have hc := hg ((KoreAML.interp_defined hD).mpr ⟨x, by
    rw [interpret_conj]
    refine ⟨(interp_symList _ _ [a'] (.cons (ev_list L 2) .nil) x).mpr hx1, ?_⟩
    exact (interp_concatItem _ _ (ev_list L 1) (ev_list L 3) x).mpr hx2⟩)
  rw [interpret_conj, KoreAML.interp_equal hD, KoreAML.interp_equal hD] at hc
  exact ⟨(hc.1 a).mp rfl, (hc.2 r).mp rfl⟩

/-- `setDecompAx`, read. -/
theorem axS_decomp {a r s₁ s₂ x : M} (ha : InS I (c.sortName k.key) a) (hr : InS I (c.sortName k.sort) r)
    (h1 : InS I (c.sortName k.sort) s₁) (h2 : InS I (c.sortName k.sort) s₂)
    (hx1 : ∃ y, SymE I (c.symName k.elem) [a] y ∧ SymE I (c.symName k.concat) [y, r] x)
    (hx2 : SymE I (c.symName k.concat) [s₁, s₂] x) :
    (∃ y, InS I (c.sortName k.sort) y ∧
      (∀ z, z = s₁ ↔ ∃ y', SymE I (c.symName k.elem) [a] y' ∧ SymE I (c.symName k.concat) [y', y] z) ∧
      ∀ z, z = r ↔ SymE I (c.symName k.concat) [y, s₂] z) ∨
    (∃ y, InS I (c.sortName k.sort) y ∧
      (∀ z, z = s₂ ↔ ∃ y', SymE I (c.symName k.elem) [a] y' ∧ SymE I (c.symName k.concat) [y', y] z) ∧
      ∀ z, z = r ↔ SymE I (c.symName k.concat) [s₁, y] z) := by
  let L := [a, r, s₁, s₂]
  have hax := hC (setDecompAx c k) ⟨k, hk, by
    rw [collAxioms_set hkind]
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))⟩
    (listVal L) default
  unfold setDecompAx at hax
  dsimp only at hax
  have hg := KoreAML.interp_guarded hax (fun w hw => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl
    · exact guard_at hD (s := k.key) ha _
    · exact guard_at hD (s := k.sort) hr _
    · exact guard_at hD (s := k.sort) h1 _
    · exact guard_at hD (s := k.sort) h2 _)
  have hc := hg ((KoreAML.interp_defined hD).mpr ⟨x, by
    rw [interpret_conj]
    refine ⟨(interp_concatItem _ _ (ev_list L 1) (ev_list L 2) x).mpr hx1, ?_⟩
    exact (interp_symList _ _ [s₁, s₂] (.cons (ev_list L 3) (.cons (ev_list L 4) .nil)) x).mpr hx2⟩)
  rw [interpret_disj, KoreAML.interp_sExists, KoreAML.interp_sExists] at hc
  have hy : ∀ y : M, ((⟨5⟩ : EVar) ∈∈ KoreAML.inhOf (sortP (c.sortName k.sort)) : KoreAML.P).interpret I
      (listValAt L 5 y) default → InS I (c.sortName k.sort) y := fun y h => by
    rw [KoreAML.interp_member hD] at h
    have h' := (inS_iff _).mp h
    unfold listValAt at h'
    simpa using h'
  rcases hc with ⟨y, hym, hyb⟩ | ⟨y, hym, hyb⟩
  · left
    have hyb' : (_ : KoreAML.P).interpret I (listValAt L 5 y) default := hyb
    rw [interpret_conj, KoreAML.interp_equal hD, KoreAML.interp_equal hD] at hyb'
    refine ⟨y, hy y hym, fun z => ?_, fun z => ?_⟩
    · exact (ev_listAt L 5 y (j := 3) (by decide) z).symm.trans ((hyb'.1 z).trans
        (interp_concatItem _ _ (ev_listAt L 5 y (j := 1) (by decide)) (ev_listAt_self L 5 y) z))
    · exact (ev_listAt L 5 y (j := 2) (by decide) z).symm.trans ((hyb'.2 z).trans
        (interp_symList _ _ [y, s₂] (.cons (ev_listAt_self L 5 y) (.cons (ev_listAt L 5 y (j := 4) (by decide)) .nil)) z))
  · right
    have hyb' : (_ : KoreAML.P).interpret I (listValAt L 5 y) default := hyb
    rw [interpret_conj, KoreAML.interp_equal hD, KoreAML.interp_equal hD] at hyb'
    refine ⟨y, hy y hym, fun z => ?_, fun z => ?_⟩
    · exact (ev_listAt L 5 y (j := 4) (by decide) z).symm.trans ((hyb'.1 z).trans
        (interp_concatItem _ _ (ev_listAt L 5 y (j := 1) (by decide)) (ev_listAt_self L 5 y) z))
    · exact (ev_listAt L 5 y (j := 2) (by decide) z).symm.trans ((hyb'.2 z).trans
        (interp_symList _ _ [s₁, y] (.cons (ev_listAt L 5 y (j := 3) (by decide)) (.cons (ev_listAt_self L 5 y) .nil)) z))

end

section
variable {c : Semantics} {k : CollSig} (hco : c.collOf k.sort = some k)
include hco

theorem sortOf_setK (hkind : k.kind = .set) {es : List GroundTerm} :
    c.sortOf (.set k.sort es) = some k.sort ↔ elemsSorted es = true ∧ ∀ e ∈ es, c.sortOf e = some k.key := by
  rw [sortOf_setS]
  constructor
  · rintro ⟨k', hk', -, hs, h, -⟩
    rw [hco] at hk'; cases hk'; exact ⟨hs, h⟩
  · rintro ⟨hs, h⟩
    exact ⟨k, hco, hkind, hs, h, rfl⟩

theorem den_setNilK {M : Type} {I : Interpretation KoreAML.Sym M} (e : Valuation M) (m : M) :
    (den c (.set k.sort [])).interpret I e m ↔ I.evalSymb (.symbol (c.symName k.unit)) m := by
  unfold den KoreAML.den
  rw [GroundTerm.kore, collSig_eq .set hco, GroundTerm.koreElems]
  unfold KoreAML.ap
  rw [KoreAML.tr_app0, KoreAML.trArgs_nil]
  exact Iff.rfl

theorem den_setOneK_eq (a : GroundTerm) :
    den c (.set k.sort [a]) = KoreAML.appList (symP (c.symName k.elem)) [den c a] := by
  unfold den KoreAML.den
  rw [GroundTerm.kore, collSig_eq .set hco, GroundTerm.koreElems]
  unfold KoreAML.ap
  rw [KoreAML.tr_app0, trArgs_appList]
  rfl

theorem den_setConsK_eq (a e' : GroundTerm) (es : List GroundTerm) :
    den c (.set k.sort (a :: e' :: es)) = KoreAML.appList (symP (c.symName k.concat))
      [KoreAML.appList (symP (c.symName k.elem)) [den c a], den c (.set k.sort (e' :: es))] := by
  have h2 : den c (.set k.sort (e' :: es)) = KoreAML.tr ⟨[], []⟩ (GroundTerm.koreElems c k (e' :: es)) := by
    unfold den KoreAML.den; rw [GroundTerm.kore, collSig_eq .set hco]
  rw [h2]
  unfold den KoreAML.den
  rw [GroundTerm.kore, collSig_eq .set hco, GroundTerm.koreElems.eq_3 c k a (e' :: es) (List.cons_ne_nil _ _)]
  unfold KoreAML.ap
  rw [KoreAML.tr_app0, trArgs_appList]
  simp only [List.map_cons, List.map_nil]
  rw [KoreAML.tr_app0, trArgs_appList]
  rfl

end

/-- **What the downward reading takes of a set collection `k` in a model `I`**: as `MapReading`,
with the empty set, the one-member set and the union of two disjoint sets. -/
structure SetReading (c : Semantics) {M : Type} [Inhabited M] (I : Interpretation KoreAML.Sym M) (k : CollSig) :
    Prop where
  mem : k ∈ c.allColls
  kind : k.kind = .set
  coll : c.collOf k.sort = some k
  sortOK : collSortOK c k.sort = true
  ite : ∀ f ∈ [k.unit, k.elem, k.concat], iteSort? (c.symName f) = none
  sigs : (⟨k.unit, [], k.sort⟩ : CtorSig) ∈ kernelSyms c ∧ (⟨k.elem, [k.key], k.sort⟩ : CtorSig) ∈ kernelSyms c ∧
    (⟨k.concat, [k.sort, k.sort], k.sort⟩ : CtorSig) ∈ kernelSyms c
  unitV : c.collVal k.unit [] = some (.set k.sort [])
  elemV : ∀ {a : GroundTerm}, c.sortOf a = some k.key → c.collVal k.elem [a] = some (.set k.sort [a])
  catV : ∀ {w₁ w₂ : GroundTerm}, c.sortOf w₁ = some k.sort → c.sortOf w₂ = some k.sort → ∀ m,
    SymE I (c.symName k.concat) [elemOf c I w₁, elemOf c I w₂] m ↔
      ∃ u, c.collVal k.concat [w₁, w₂] = some u ∧ c.sortOf u = some k.sort ∧ m = elemOf c I u
  catOne : ∀ {a : GroundTerm}, c.sortOf a = some k.key →
    c.collVal k.concat [.set k.sort [a], .set k.sort []] = some (.set k.sort [a])

section
variable {c : Semantics} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hI : I ⊧ᴵP Γ c) [OvlOK c]
  {k : CollSig} (R : SetReading c I k)
include hI R

omit hI in
theorem set_tail {e : GroundTerm} {es : List GroundTerm} (hs : c.sortOf (.set k.sort (e :: es)) = some k.sort) :
    c.sortOf e = some k.key ∧ c.sortOf (.set k.sort es) = some k.sort := by
  obtain ⟨hso, h⟩ := (sortOf_setK R.coll R.kind).mp hs
  exact ⟨h e (List.mem_cons_self ..), (sortOf_setK R.coll R.kind).mpr
    ⟨elemsSorted_iff.mpr (elemsSorted_iff.mp hso).of_cons, fun e' he' => h e' (List.mem_cons_of_mem _ he')⟩⟩

omit hI in
theorem set_one {a : GroundTerm} (ha : c.sortOf a = some k.key) : c.sortOf (.set k.sort [a]) = some k.sort :=
  (sortOf_setK R.coll R.kind).mpr ⟨rfl, fun e he => by rw [mem_one he]; exact ha⟩

/-- A set's element, at values: `elem(⟦a⟧)` is the one-member set's element. -/
theorem elem_valS {a : GroundTerm} (ha : c.sortOf a = some k.key) (m : M) :
    SymE I (c.symName k.elem) [elemOf c I a] m ↔ m = elemOf c I (.set k.sort [a]) := by
  rw [← den_sing hI (set_one R ha) KoreAML.val0 m, den_setOneK_eq R.coll]
  exact (interp_symList _ _ _ (.cons (den_sing hI ha _) .nil) m).symm

/-- A set's element, its first member split off: `concat(elem(⟦a⟧), ⟦rest⟧)` holds it. -/
theorem set_firstK {a : GroundTerm} {es : List GroundTerm} (hs : c.sortOf (.set k.sort (a :: es)) = some k.sort) :
    ∃ y, SymE I (c.symName k.elem) [elemOf c I a] y ∧
      SymE I (c.symName k.concat) [y, elemOf c I (.set k.sort es)] (elemOf c I (.set k.sort (a :: es))) := by
  obtain ⟨ha, hsr⟩ := set_tail R hs
  cases es with
  | nil =>
    exact ⟨_, (elem_valS hI R ha _).mpr rfl, (R.catV hs hsr _).mpr ⟨_, R.catOne ha, hs, rfl⟩⟩
  | cons e' es =>
    have hx := (den_sing hI hs KoreAML.val0 _).mpr rfl
    rw [den_setConsK_eq R.coll] at hx
    exact (interp_concatItem _ _ (den_sing hI ha _) (den_sing hI hsr _) _).mp hx

variable (hg : genWf c = true) (htr : ∀ a b d, (a, b) ∈ c.subsorts → (b, d) ∈ c.subsorts → (a, d) ∈ c.subsorts)
include hg htr

/-- The unit holds no value's element but the empty set's. -/
theorem set_unitK {w : GroundTerm} (hw : c.sortOf w = some k.sort)
    (hu : I.evalSymb (.symbol (c.symName k.unit)) (elemOf c I w)) : w = .set k.sort [] := by
  have h0 : c.sortOf (.set k.sort []) = some k.sort := (sortOf_setK R.coll R.kind).mpr ⟨rfl, fun e he => by cases he⟩
  have he := (den_sing hI h0 KoreAML.val0 _).mp ((den_setNilK R.coll KoreAML.val0 _).mpr hu)
  exact values_apart hI hg htr (apartSort_of_sorted hg hw) hw h0 he

omit hg htr in
/-- **Splitting a set value's element.** If a set's element is in `concat(s₁, s₂)`, for elements
`s₁`, `s₂` of its sort, they are sets' elements: by induction on the set's members, through
`setUnitSplitAx` at the empty set and `setDecompAx` at its first member. -/
theorem set_splitK : ∀ (es : List GroundTerm), c.sortOf (.set k.sort es) = some k.sort →
    ∀ {s₁ s₂ : M}, InS I (c.sortName k.sort) s₁ → InS I (c.sortName k.sort) s₂ →
    SymE I (c.symName k.concat) [s₁, s₂] (elemOf c I (.set k.sort es)) →
    ∃ w₁ w₂, c.sortOf w₁ = some k.sort ∧ c.sortOf w₂ = some k.sort ∧ s₁ = elemOf c I w₁ ∧ s₂ = elemOf c I w₂
  | [], hs, s₁, s₂, h1, h2, hx => by
    have hD := defOK hI
    have hu := (den_setNilK R.coll KoreAML.val0 _).mp ((den_sing hI hs KoreAML.val0 _).mpr rfl)
    obtain ⟨u1, u2⟩ := axS_unitSplit hD (sat_colls hI) R.mem R.kind h1 h2 hu hx
    exact ⟨_, _, hs, hs, (den_sing hI hs KoreAML.val0 _).mp ((den_setNilK R.coll KoreAML.val0 _).mpr u1),
      (den_sing hI hs KoreAML.val0 _).mp ((den_setNilK R.coll KoreAML.val0 _).mpr u2)⟩
  | a :: es, hs, s₁, s₂, h1, h2, hx => by
    have hD := defOK hI
    obtain ⟨ha, hsr⟩ := set_tail R hs
    have h1s : c.sortOf (.set k.sort [a]) = some k.sort := set_one R ha
    have haS : InS I (c.sortName k.key) (elemOf c I a) := (elemOf_spec hI ha KoreAML.val0).2
    have hrS : InS I (c.sortName k.sort) (elemOf c I (.set k.sort es)) := (elemOf_spec hI hsr KoreAML.val0).2
    rcases axS_decomp hD (sat_colls hI) R.mem R.kind haS hrS h1 h2 (set_firstK hI R hs) hx with
      ⟨y, hy, hm, hr⟩ | ⟨y, hy, hm, hr⟩
    · obtain ⟨u₁, u₂, hu₁, hu₂, rfl, rfl⟩ := set_splitK es hsr hy h2 ((hr _).mp rfl)
      obtain ⟨y', hy', hc⟩ := (hm s₁).mp rfl
      rw [(elem_valS hI R ha y').mp hy'] at hc
      obtain ⟨u, -, hus, rfl⟩ := (R.catV h1s hu₁ s₁).mp hc
      exact ⟨u, u₂, hus, hu₂, rfl, rfl⟩
    · obtain ⟨u₁, u₂, hu₁, hu₂, rfl, rfl⟩ := set_splitK es hsr h1 hy ((hr _).mp rfl)
      obtain ⟨y', hy', hc⟩ := (hm s₂).mp rfl
      rw [(elem_valS hI R ha y').mp hy'] at hc
      obtain ⟨u, -, hus, rfl⟩ := (R.catV h1s hu₂ s₂).mp hc
      exact ⟨u₁, u, hu₁, hus, rfl, rfl⟩

/-- **A set's element holding a value's element**: the set has one member, whose element the
element's argument is (`setElemNotUnitAx`, `setElemAtomAx`). -/
theorem set_elemK : ∀ (es : List GroundTerm), c.sortOf (.set k.sort es) = some k.sort →
    ∀ {b : M}, InS I (c.sortName k.key) b → SymE I (c.symName k.elem) [b] (elemOf c I (.set k.sort es)) →
    ∃ e, es = [e] ∧ c.sortOf e = some k.key ∧ b = elemOf c I e
  | [], hs, b, hb, hx => by
    have hD := defOK hI
    have hu := (den_setNilK R.coll KoreAML.val0 _).mp ((den_sing hI hs KoreAML.val0 _).mpr rfl)
    exact (axS_elemNotUnit hD (sat_colls hI) R.mem R.kind hb hu hx).elim
  | e :: es, hs, b, hb, hx => by
    have hD := defOK hI
    obtain ⟨he, hsr⟩ := set_tail R hs
    have heS : InS I (c.sortName k.key) (elemOf c I e) := (elemOf_spec hI he KoreAML.val0).2
    have hrS : InS I (c.sortName k.sort) (elemOf c I (.set k.sort es)) := (elemOf_spec hI hsr KoreAML.val0).2
    obtain ⟨h1, h3⟩ := axS_elemAtom hD (sat_colls hI) R.mem R.kind heS hb hrS hx (set_firstK hI R hs)
    have hnil := set_unitK hI R hg htr hsr h3
    cases hnil
    exact ⟨e, rfl, he, h1.symm⟩

end

/-- The symbol `f` with the signature `k0` is the unit, the element or the concatenation of the
set collection `k`, with its signature. -/
def SetRole (k : CollSig) (f : Sym) (k0 : CtorSig) : Prop :=
  (f = k.unit ∧ k0 = ⟨k.unit, [], k.sort⟩) ∨ (f = k.elem ∧ k0 = ⟨k.elem, [k.key], k.sort⟩) ∨
    (f = k.concat ∧ k0 = ⟨k.concat, [k.sort, k.sort], k.sort⟩)

section
variable {c : Semantics} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} {k : CollSig}

theorem SetRole.ite (R : SetReading c I k) {f : Sym} {k0 : CtorSig} (h : SetRole k f k0) :
    iteSort? (c.symName f) = none := by
  rcases h with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩
  · exact R.ite _ (List.mem_cons_self ..)
  · exact R.ite _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  · exact R.ite _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))

theorem SetRole.sig (R : SetReading c I k) {f : Sym} {k0 : CtorSig} (h : SetRole k f k0) :
    k0 ∈ kernelSyms c ∧ k0.name = f := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨R.sigs.1, rfl⟩
  · exact ⟨R.sigs.2.1, rfl⟩
  · exact ⟨R.sigs.2.2, rfl⟩

variable (hI : I ⊧ᴵP Γ c) [OvlOK c] (R : SetReading c I k) (hg : genWf c = true)
  (htr : ∀ a b d, (a, b) ∈ c.subsorts → (b, d) ∈ c.subsorts → (a, d) ∈ c.subsorts)
include hI R hg htr

/-- **A set collection's symbol holding a value's element**, as `mapK_back`. -/
theorem setK_back {f : Sym} {k0 : CtorSig} (hr : SetRole k f k0) {w : GroundTerm} (hw : c.sortOf w = some k0.result)
    {bs : List M} (hbl : bs.length = (k0.args.map c.sortName).length)
    (hbs : ∀ (i : Nat) x s, bs[i]? = some x → (k0.args.map c.sortName)[i]? = some s → InS I s x)
    (hm : SymE I (c.symName f) bs (elemOf c I w)) :
    ∃ ws, c.sortsOf ws = some k0.args ∧ bs = ws.map (elemOf c I) ∧ c.collVal f ws = some w := by
  have hshape : ∀ {w : GroundTerm}, c.sortOf w = some k.sort → ∃ es, w = .set k.sort es := fun hw => by
    rcases coll_shape R.coll hg R.sortOK hw with ⟨h, -⟩ | ⟨-, h⟩ | ⟨h, -⟩
    · rcases h with h | h <;> (rw [R.kind] at h; cases h)
    · exact h
    · rw [R.kind] at h; cases h
  rcases hr with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · match bs, hbl with
    | [], _ =>
      obtain ⟨a, ha, rfl⟩ := hm
      have := set_unitK hI R hg htr hw ha
      subst this
      exact ⟨[], sortsOf_nil, rfl, R.unitV⟩
  · match bs, hbl with
    | [b₁], _ =>
      obtain ⟨es, rfl⟩ := hshape hw
      obtain ⟨e, rfl, he, rfl⟩ := set_elemK hI R hg htr es hw (hbs 0 b₁ _ rfl rfl) hm
      exact ⟨[e], sortsOf_cons.mpr ⟨_, _, he, sortsOf_nil, rfl⟩, rfl, R.elemV he⟩
  · match bs, hbl with
    | [b₁, b₂], _ =>
      obtain ⟨es, rfl⟩ := hshape hw
      obtain ⟨w₁, w₂, hw₁, hw₂, rfl, rfl⟩ :=
        set_splitK hI R es hw (hbs 0 b₁ _ rfl rfl) (hbs 1 b₂ _ rfl rfl) hm
      obtain ⟨u, hu, hsu, he⟩ := (R.catV hw₁ hw₂ _).mp hm
      have := values_apart hI hg htr (apartSort_of_sorted hg hw) hw hsu he
      subst this
      exact ⟨[w₁, w₂], sortsOf_two hw₁ hw₂, rfl, hu⟩

end

/-! ## The set collections of a semantics -/

/-- The library's set collection. -/
def setColl : CollSig := ⟨Srt.set, .set, Srt.kitem, none, setUnit, setElem, setConcat⟩

theorem setColl_mem (c : Semantics) : setColl ∈ c.allColls :=
  List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))

theorem collOf_setColl (c : Semantics) : c.collOf Srt.set = some setColl := rfl

theorem concatS_one (a : GroundTerm) : concatS [a] [] = some [a] := rfl

section
variable {c : Semantics} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hI : I ⊧ᴵP Γ c) [OvlOK c]
include hI

/-- The library's `Set` is read downwards. -/
theorem setReading_lib (hso : collSortOK c Srt.set = true) : SetReading c I setColl where
  mem := setColl_mem c
  kind := rfl
  coll := collOf_setColl c
  sortOK := hso
  ite := by
    intro f hf
    simp only [setColl, List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl <;> exact iteSort_reg (by decide) (by decide)
  sigs := ⟨kernel_hook (by decide), kernel_hook (by decide), kernel_hook (by decide)⟩
  unitV := by
    show c.collVal setUnit [] = some (.set Srt.set [])
    rw [collVal_hook rfl]; rfl
  elemV := fun {a} _ => by
    show c.collVal setElem [a] = some (.set Srt.set [a])
    rw [collVal_hook rfl]; rfl
  catV := fun {w₁ w₂} h1 h2 m => by
    show SymE I (c.symName setConcat) _ m ↔ ∃ u, c.collVal setConcat [w₁, w₂] = some u ∧ c.sortOf u = some Srt.set ∧ _
    have hks : lookupSig hookSigs setConcat = some ⟨setConcat, [Srt.set, Srt.set], Srt.set⟩ := by decide
    rw [hook2_val hI hks (iteSort_reg (by decide) (by decide)) (silentKey_of_collPatternHook rfl) h1 h2 m,
      collVal_hook rfl]
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨u, join_some.mpr hu, hook_sorted (fun he => absurd he (by decide)) hks (sortsOf_two h1 h2) hu, rfl⟩
    · rintro ⟨u, hu, -, rfl⟩
      exact ⟨u, join_some.mp hu, rfl⟩
  catOne := fun {a} _ => by
    show c.collVal setConcat [.set Srt.set [a], .set Srt.set []] = some (.set Srt.set [a])
    rw [collVal_hook rfl]; rfl

/-- A set collection of the definition (a cell set) is read downwards. -/
theorem setReading_cell {k : CollSig} (hkc : k ∈ c.colls) (hok : collSymsOK c k = true)
    (hso : collSortOK c k.sort = true) (hkind : k.kind = .set) : SetReading c I k := by
  obtain ⟨hco, hsyms, hpu, hpe, hpc⟩ := collSymsOK_spec hok
  rw [hkind, show (builtinColl CollKind.set).unit = setUnit from rfl] at hpu
  rw [hkind, show (builtinColl CollKind.set).elem = setElem from rfl] at hpe
  rw [hkind, show (builtinColl CollKind.set).concat = setConcat from rfl] at hpc
  have hea : elemArgs k = [k.key] := by unfold elemArgs; rw [hkind]
  rw [hea] at hpe
  have hnh : ∀ f ∈ [k.unit, k.elem, k.concat], isHook f = false := fun f hf => (hsyms f hf).1
  have hone : ∀ {a : GroundTerm}, c.sortOf a = some k.key → c.sortOf (.set k.sort [a]) = some k.sort :=
    fun ha => (sortOf_setK hco hkind).mpr ⟨rfl, fun e he => by rw [mem_one he]; exact ha⟩
  have hU := hnh _ (List.mem_cons_self ..)
  have hE := hnh _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  have hC := hnh _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
  have hitC := (hsyms _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))).2
  exact {
    mem := List.mem_append_right _ hkc
    kind := hkind
    coll := hco
    sortOK := hso
    ite := fun f hf => (hsyms f hf).2
    sigs := ⟨kernel_param (lookupParam_mem hpu), kernel_param (lookupParam_mem hpe), kernel_param (lookupParam_mem hpc)⟩
    unitV := by
      rw [collVal_param hU, paramVal_impl hpu rfl _ (silentKey_of_mem rfl) (by decide) (carrier_of_collSortOK hso)]
      exact filter_sorted ((sortOf_setK hco hkind).mpr ⟨rfl, fun e he => by cases he⟩)
    elemV := fun {a} ha => by
      rw [collVal_param hE, paramVal_impl hpe rfl _ (silentKey_of_mem rfl) (by decide) (carrier_of_collSortOK hso)]
      exact filter_sorted (hone ha)
    catV := fun {w₁ w₂} h1 h2 m => by
      rw [param2_val hI hpc rfl hitC h1 h2 m, collVal_param hC]
      constructor
      · rintro ⟨u, hu, rfl⟩
        obtain ⟨k', hk', hsu⟩ := c.paramVal_sorted hu
        rw [hpc] at hk'; cases hk'
        exact ⟨u, hu, hsu, rfl⟩
      · rintro ⟨u, hu, -, rfl⟩
        exact ⟨u, hu, rfl⟩
    catOne := fun {a} ha => by
      rw [collVal_param hC, paramVal_impl hpc rfl _ (silentKey_of_mem rfl) (by decide) (carrier_of_collSortOK hso)]
      exact filter_sorted (hone ha) }

end

/-! ## Collection pattern symbols -/

/-- **The collection a pattern symbol reads**: the unit, element or concatenation of a map, list
or set collection read downwards. -/
def HeadReading (c : Semantics) {M : Type} [Inhabited M] (I : Interpretation KoreAML.Sym M) (f : Sym) (k0 : CtorSig) :
    Prop :=
  (∃ k, MapReading c I k ∧ MapRole k f k0) ∨ (∃ k, ListReading c I k ∧ ListRole k f k0) ∨
    (∃ k, SetReading c I k ∧ SetRole k f k0)

section
variable {c : Semantics} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}

theorem HeadReading.ite {f : Sym} {k0 : CtorSig} (h : HeadReading c I f k0) : iteSort? (c.symName f) = none := by
  rcases h with ⟨k, R, hr⟩ | ⟨k, R, hr⟩ | ⟨k, R, hr⟩
  · exact MapRole.ite R hr
  · exact ListRole.ite R hr
  · exact SetRole.ite R hr

theorem HeadReading.sig {f : Sym} {k0 : CtorSig} (h : HeadReading c I f k0) : k0 ∈ kernelSyms c ∧ k0.name = f := by
  rcases h with ⟨k, R, hr⟩ | ⟨k, R, hr⟩ | ⟨k, R, hr⟩
  · exact MapRole.sig R hr
  · exact ListRole.sig R hr
  · exact SetRole.sig R hr

/-- **A collection pattern symbol holding a value's element.** If a value's element is what the
symbol gives on elements of its argument sorts, the elements are values', on which the symbol's
value (`collVal`) is the value. -/
theorem head_back (hI : I ⊧ᴵP Γ c) (hg : genWf c = true) [OvlOK c]
    (htr : ∀ a b d, (a, b) ∈ c.subsorts → (b, d) ∈ c.subsorts → (a, d) ∈ c.subsorts)
    {f : Sym} {k0 : CtorSig} (h : HeadReading c I f k0) {w : GroundTerm} (hw : c.sortOf w = some k0.result)
    {bs : List M} (hbl : bs.length = (k0.args.map c.sortName).length)
    (hbs : ∀ (i : Nat) x s, bs[i]? = some x → (k0.args.map c.sortName)[i]? = some s → InS I s x)
    (hm : SymE I (c.symName f) bs (elemOf c I w)) :
    ∃ ws, c.sortsOf ws = some k0.args ∧ bs = ws.map (elemOf c I) ∧ c.collVal f ws = some w := by
  rcases h with ⟨k, R, hr⟩ | ⟨k, R, hr⟩ | ⟨k, R, hr⟩
  · exact mapK_back hI R hg htr hr hw hbl hbs hm
  · exact listK_back hI R hg htr hr hw hbl hbs hm
  · exact setK_back hI R hg htr hr hw hbl hbs hm

end

section
variable {c : Semantics} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hI : I ⊧ᴵP Γ c) [OvlOK c]
  (hph : patHooksApart c = true) (hcs : collsOK c = true) (hcso : collSortsOK c = true)
include hI hph hcs hcso

/-- **Every symbol the downward reading covers reads a collection**: a map pattern symbol the
library's `Map`, the library's set and list symbols its `Set` and `List`, a parameter implemented
by a map, set or list pattern symbol a collection of the definition of that kind. -/
theorem head_reading {f : Sym} {k0 : CtorSig} (hnc : c.isCtor f = false) (hno : c.isOvl f = false)
    (hd : downHead c f = true) (hk : lookupSig c.patCtxAll.heads f = some k0) : HeadReading c I f k0 := by
  unfold downHead at hd
  simp only [Bool.or_eq_true] at hd
  replace hd : patternHooks.contains f = true ∨ c.isCollPat f = true := by
    rcases hd with (h | h) | h
    · exact .inl h
    · exact .inr h
    · rw [hno] at h; cases h
  rcases hd with hp | hcp
  · refine Or.inl ⟨mapColl, mapReading_lib hI (collSortsOK_mem hcso (mapColl_mem c)), ?_⟩
    have hks := patAll_lookup_hook hph hp hk
    rcases Exec.patternHooks_cases hp with rfl | rfl | rfl
    · rw [show lookupSig hookSigs mapUnit = some ⟨mapUnit, [], Srt.map⟩ by decide] at hks; cases hks
      exact Or.inl ⟨rfl, rfl⟩
    · rw [show lookupSig hookSigs mapElem = some ⟨mapElem, [Srt.kitem, Srt.kitem], Srt.map⟩ by decide] at hks; cases hks
      exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    · rw [show lookupSig hookSigs mapConcat = some ⟨mapConcat, [Srt.map, Srt.map], Srt.map⟩ by decide] at hks
      cases hks
      exact Or.inr (Or.inr ⟨rfl, rfl⟩)
  cases hh : isHook f with
  | true =>
    have hks := patAll_lookup_collHook hnc hcp hh hk
    have hcm : collPatternHooks.contains f = true := by
      unfold Semantics.isCollPat at hcp
      rw [hh, if_pos rfl] at hcp
      simp only [Bool.and_eq_true] at hcp
      exact hcp.2
    have hmem : f ∈ collPatternHooks := List.contains_iff_mem.mp hcm
    simp only [collPatternHooks, listPatternHooks, List.mem_cons, List.not_mem_nil, or_false] at hmem
    have hlist := listReading_lib (I := I) hI (collSortsOK_mem hcso (listColl_mem c))
    have hset := setReading_lib (I := I) hI (collSortsOK_mem hcso (setColl_mem c))
    rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [show lookupSig hookSigs setUnit = some ⟨setUnit, [], Srt.set⟩ by decide] at hks; cases hks
      exact Or.inr (Or.inr ⟨setColl, hset, Or.inl ⟨rfl, rfl⟩⟩)
    · rw [show lookupSig hookSigs setElem = some ⟨setElem, [Srt.kitem], Srt.set⟩ by decide] at hks; cases hks
      exact Or.inr (Or.inr ⟨setColl, hset, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩)
    · rw [show lookupSig hookSigs setConcat = some ⟨setConcat, [Srt.set, Srt.set], Srt.set⟩ by decide] at hks
      cases hks
      exact Or.inr (Or.inr ⟨setColl, hset, Or.inr (Or.inr ⟨rfl, rfl⟩)⟩)
    · rw [show lookupSig hookSigs listUnit = some ⟨listUnit, [], Srt.list⟩ by decide] at hks; cases hks
      exact Or.inr (Or.inl ⟨listColl, hlist, Or.inl ⟨rfl, rfl⟩⟩)
    · rw [show lookupSig hookSigs listElem = some ⟨listElem, [Srt.kitem], Srt.list⟩ by decide] at hks; cases hks
      exact Or.inr (Or.inl ⟨listColl, hlist, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩)
    · rw [show lookupSig hookSigs listConcat = some ⟨listConcat, [Srt.list, Srt.list], Srt.list⟩ by decide] at hks
      cases hks
      exact Or.inr (Or.inl ⟨listColl, hlist, Or.inr (Or.inr ⟨rfl, rfl⟩)⟩)
  | false =>
    obtain ⟨kp, hkp, hkpm, rfl, hkn⟩ := patAll_lookup_collParam hnc hcp hh hk
    have hci : collImpl kp = true := by
      unfold Semantics.isCollPat at hcp
      rw [hh, if_neg (by simp), hkp] at hcp
      simp only [Bool.and_eq_true] at hcp
      unfold collImpl
      exact hcp.2
    obtain ⟨k, hkc, hrole⟩ := collsOK_params hcs hkpm hci
    have hok := collsOK_colls hcs hkc
    obtain ⟨hco, -, hpu, hpe, hpc⟩ := collSymsOK_spec hok
    have hso := collSortsOK_mem hcso (List.mem_append_right _ hkc)
    cases hkk : k.kind with
    | set =>
      refine Or.inr (Or.inr ⟨k, setReading_cell hI hkc hok hso hkk, ?_⟩)
      have hea : elemArgs k = [k.key] := by unfold elemArgs; rw [hkk]
      rcases hrole with h | h | h
      · rw [h] at hkn; rw [← hkn, hpu] at hkp; cases hkp; exact Or.inl ⟨hkn.symm, rfl⟩
      · rw [h] at hkn; rw [← hkn, hpe] at hkp; cases hkp; exact Or.inr (Or.inl ⟨hkn.symm, by rw [hea]⟩)
      · rw [h] at hkn; rw [← hkn, hpc] at hkp; cases hkp; exact Or.inr (Or.inr ⟨hkn.symm, rfl⟩)
    | map =>
      refine Or.inl ⟨k, mapReading_cell hI hkc hok hso hkk, ?_⟩
      have hea : elemArgs k = [k.key, valSort k] := by unfold elemArgs; rw [hkk]
      rcases hrole with h | h | h
      · rw [h] at hkn; rw [← hkn, hpu] at hkp; cases hkp; exact Or.inl ⟨hkn.symm, rfl⟩
      · rw [h] at hkn; rw [← hkn, hpe] at hkp; cases hkp; exact Or.inr (Or.inl ⟨hkn.symm, by rw [hea]⟩)
      · rw [h] at hkn; rw [← hkn, hpc] at hkp; cases hkp; exact Or.inr (Or.inr ⟨hkn.symm, rfl⟩)
    | list =>
      refine Or.inr (Or.inl ⟨k, listReading_cell hI hkc hok hso hkk, ?_⟩)
      have hea : elemArgs k = [k.key] := by unfold elemArgs; rw [hkk]
      rcases hrole with h | h | h
      · rw [h] at hkn; rw [← hkn, hpu] at hkp; cases hkp; exact Or.inl ⟨hkn.symm, rfl⟩
      · rw [h] at hkn; rw [← hkn, hpe] at hkp; cases hkp; exact Or.inr (Or.inl ⟨hkn.symm, by rw [hea]⟩)
      · rw [h] at hkn; rw [← hkn, hpc] at hkp; cases hkp; exact Or.inr (Or.inr ⟨hkn.symm, rfl⟩)
    | rangeMap =>
      -- a range map's symbols are implemented by RANGEMAP's, no collection pattern symbol
      exfalso
      rcases hrole with h | h | h
      · rw [h] at hkn; rw [← hkn, hpu] at hkp; cases hkp
        simp only [collImpl, hkk] at hci; exact absurd hci (by decide)
      · rw [h] at hkn; rw [← hkn, hpe] at hkp; cases hkp
        simp only [collImpl, hkk] at hci; exact absurd hci (by decide)
      · rw [h] at hkn; rw [← hkn, hpc] at hkp; cases hkp
        simp only [collImpl, hkk] at hci; exact absurd hci (by decide)

end

theorem isCollPat_of_down {c : Semantics} {f : Sym} (hd : downHead c f = true) (hno : c.isOvl f = false)
    (hp : patternHooks.contains f = false) : c.isCollPat f = true := by
  unfold downHead at hd
  rw [hp, hno] at hd
  simpa using hd

theorem hook_of_collVal {c : Semantics} {f : Sym} {ws : List GroundTerm} {w : GroundTerm} (h : isHook f = true)
    (hv : c.collVal f ws = some w) : hook f ws = some (some w) := by
  rw [collVal_hook h] at hv; exact join_some.mp hv

/-! ## Collection patterns read downwards -/

mutual
  /-- A pattern of constructors, injections, aliases, variables, domain values and the collection
  pattern symbols the downward reading covers (`downHead`). -/
  def collPat (c : Semantics) : Term → Bool
    | .var _ => true
    | .dv _ _ => true
    | .app f ts => (c.isCtor f || downHead c f) && collPats c ts
    | .inj _ _ t => collPat c t
    | .as t _ => collPat c t
    termination_by structural t => t
  def collPats (c : Semantics) : List Term → Bool
    | [] => true
    | t :: ts => collPat c t && collPats c ts
    termination_by structural ts => ts
end

section
variable {c : Semantics} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}

/-- G-arity of a symbol with a signature in `Γ`, at elements of its argument sorts. -/
theorem kernel_arity (hI : I ⊧ᴵP Γ c) [OvlOK c] {f : Sym} {k : CtorSig} (hkm : k ∈ kernelSyms c) (hkn : k.name = f)
    (hit0 : iteSort? (c.symName f) = none) {bs : List M} (hbl : bs.length = (k.args.map c.sortName).length)
    (hbs : ∀ (i : Nat) x s, bs[i]? = some x → (k.args.map c.sortName)[i]? = some s → InS I s x) {m : M}
    (hm : SymE I (c.symName f) bs m) : InS I (c.sortName k.result) m := by
  have hD := defOK hI
  have hit := sat_sigItem hI (sig_arity (c := c) (k := k) hkm)
  unfold symArityItem at hit
  rw [show iteSort? (c.symName k.name) = none by rw [hkn]; exact hit0] at hit
  dsimp only at hit
  unfold KoreAML.arityItem at hit
  dsimp only [KoreAML.paramTable, List.map_nil] at hit
  have hinc := (KoreAML.interp_included hD).mp (hit KoreAML.val0 default) m
  unfold srtOf at hinc
  rw [trSort_srt] at hinc
  apply hinc
  obtain ⟨a, ha, hm⟩ := hm
  rw [interp_appList]
  refine ⟨a, by rw [hkn]; exact ha, bs, ?_, hm⟩
  clear ha hm hinc hit
  have : ∀ (ss : List Srt) (bs : List M), bs.length = (ss.map c.sortName).length →
      (∀ (i : Nat) x s, bs[i]? = some x → (ss.map c.sortName)[i]? = some s → InS I s x) →
      All2 (fun φ b => φ.interpret I KoreAML.val0 b)
        ((ss.map (srtOf c)).map fun s => KoreAML.inhOf (KoreAML.trSort [] s)) bs := by
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
        unfold srtOf; dsimp only; rw [trSort_srt]
        exact hb 0 b (c.sortName s) rfl rfl
  exact this k.args bs hbl hbs

end

section
variable {c : Semantics} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hI : I ⊧ᴵP Γ c) [OvlOK c]
  (hph : patHooksApart c = true) (hcs : collsOK c = true) (hcso : collSortsOK c = true) (hg : genWf c = true)
  (htr : ∀ a b d, (a, b) ∈ c.subsorts → (b, d) ∈ c.subsorts → (a, d) ∈ c.subsorts)
  (hnm : NamesPlain c) {vars : List Srt} {vs : List KoreAML.Var} {tbl : VarTable} {e : Valuation M}
  (hvs : vs.length = vars.length)
  (hin : ∀ i < vars.length, InS I (c.sortName (vars.getD i 0)) (e.evalEvar (tbl.ev (keyAt vs i))))
include hI hph hcs hcso hg htr hnm hvs hin

mutual
  /-- The elements of a pattern's translation, collection pattern symbols included, at a valuation
  of its variables in their sorts, lie in the pattern's sort (the G-arity of the symbols). -/
  theorem patSortC : ∀ {p : Term} {s : Srt}, collPat c p = true → sortOfTerm c.patCtxNF vars p = some s →
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
      have hnfo := (patCtxNF_lookup.mp hk').2
      replace hk' := (patCtxNF_lookup.mp hk').1
      rw [collPat] at hp
      simp only [Bool.and_eq_true, Bool.or_eq_true] at hp
      obtain ⟨hhd, hps⟩ := hp
      cases hc : c.isCtor f with
      | true =>
        obtain ⟨k0, hk0⟩ := Option.isSome_iff_exists.mp hc
        have hkk := lookup_patCtxAll hk0 hk'
        subst hkk
        rw [kore_app_plain hnm hk0, trArgs_appList, interp_appList] at hm
        obtain ⟨a, ha, bs, hbs, hm⟩ := hm
        have hsorts := patSortsC hps hargs hbs
        exact ctor_arity hI hnm hk0 hsorts.1 hsorts.2 ⟨a, by
          show (KoreAML.sym (.symbol (c.symName k.name))).interpret I KoreAML.val0 a
          rw [(lookupSig_spec hk0).2]; exact ha, hm⟩
      | false =>
        have hd : downHead c f = true := by rw [hc] at hhd; simpa using hhd
        cases hov : c.isOvl f with
        | true =>
          obtain ⟨o, hlo, rfl⟩ := patAll_lookup_ovl hov hk'
          obtain ⟨hom, hn, -, hit, -⟩ := OvlLaws.ovl_parts (OvlOK.ok (c := c)) hlo
          rw [kore_app, tr_symApp, symHead_none hit, trArgs_appList, interp_appList] at hm
          obtain ⟨a, ha, bs, hbs, hm⟩ := hm
          have hsorts := patSortsC hps hargs hbs
          exact kernel_arity hI (List.mem_append_right _ (List.mem_map_of_mem hom)) hn hit hsorts.1 hsorts.2
            ⟨a, ha, hm⟩
        | false =>
        have hR := head_reading hI hph hcs hcso hc hov hd hk'
        have hit := hR.ite
        obtain ⟨hkm, hkn⟩ := hR.sig
        rw [kore_app, tr_symApp, symHead_none hit, trArgs_appList, interp_appList] at hm
        obtain ⟨a, ha, bs, hbs, hm⟩ := hm
        have hsorts := patSortsC hps hargs hbs
        exact kernel_arity hI hkm hkn hit hsorts.1 hsorts.2 ⟨a, ha, hm⟩
    | .inj a b p, s, hp, ht, m, hm => by
      obtain ⟨hab, ht', rfl⟩ := sortOfTerm_inj.mp ht
      rw [collPat] at hp
      rw [Term.kore, KoreAML.tr_injP, interp_injApp] at hm
      obtain ⟨x, hx, hm⟩ := hm
      have hxs := patSortC hp ht' x hx
      obtain ⟨y, hy, hys⟩ := gen_fun hI (genWf_sub hg hab).1 (gensF_inj hab) rfl (xs := [x]) rfl (single_sorts hxs)
      rw [(hys m).mp hm]; exact hy
    | .as p i, s, hp, ht, m, hm => by
      obtain ⟨-, ht'⟩ := Exec.sortOfTerm_as ht
      rw [collPat] at hp
      rw [tr_kore_as hI hg htr hnm hvs hin] at hm
      exact patSortC hp ht' m hm.1
  theorem patSortsC : ∀ {ps : List Term} {ss : List Srt} {bs : List M}, collPats c ps = true →
      sortsOfTerms c.patCtxNF vars ps = some ss →
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
      rw [collPats] at hp
      simp only [Bool.and_eq_true] at hp
      rw [Term.koreList, List.map_cons] at hbs
      cases hbs with
      | cons hb hbs =>
        have ih := patSortsC hp.2 h2 hbs
        refine ⟨by simp [ih.1], fun i x s' hx hs' => ?_⟩
        cases i with
        | zero =>
          simp at hx hs'; subst hx; subst hs'
          exact patSortC hp.1 h1 _ hb
        | succ i => exact ih.2 i x s' (by simpa using hx) (by simpa using hs')
end

end

section
variable {c : Semantics} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hI : I ⊧ᴵP Γ c) [OvlOK c]
  (hph : patHooksApart c = true) (hcs : collsOK c = true) (hcso : collSortsOK c = true) (hg : genWf c = true)
  (htr : ∀ a b d, (a, b) ∈ c.subsorts → (b, d) ∈ c.subsorts → (a, d) ∈ c.subsorts)
  (hnm : NamesPlain c) {vars : List Srt} {vs : List KoreAML.Var} {tbl : VarTable} {e : Valuation M}
  (hvs : vs.length = vars.length)
  (hin : ∀ i < vars.length, InS I (c.sortName (vars.getD i 0)) (e.evalEvar (tbl.ev (keyAt vs i))))
include hI hph hcs hcso hg htr hnm hvs hin

mutual
  /-- **Collection patterns, downwards, in a model of `Γ`.** If the element of a value of a
  pattern's sort lies in the pattern's translation, collection pattern symbols included, at a valuation of
  its variables in their sorts, the pattern denotes the value under the valuation's substitution,
  and the valuation gives each of the pattern's variables the element of a value of its sort. A
  collection pattern symbol is read through `head_back`: the parts of a value's element under it are
  values' elements, on which the symbol's hook gives the value. -/
  theorem patVal_backC : ∀ {p : Term} {s : Srt} {w : GroundTerm}, collPat c p = true →
      sortOfTerm c.patCtxNF vars p = some s → c.sortOf w = some s →
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
      have hnfo := (patCtxNF_lookup.mp hk').2
      replace hk' := (patCtxNF_lookup.mp hk').1
      rw [collPat] at hp
      simp only [Bool.and_eq_true, Bool.or_eq_true] at hp
      obtain ⟨hhd, hps⟩ := hp
      cases hc : c.isCtor f with
      | true =>
        obtain ⟨k0, hk0⟩ := Option.isSome_iff_exists.mp hc
        have hkk := lookup_patCtxAll hk0 hk'
        subst hkk
        rw [kore_app_plain hnm hk0, trArgs_appList, interp_appList] at hm
        obtain ⟨a, ha, bs, hbs, hm⟩ := hm
        have hsorts := patSortsC hI hph hcs hcso hg htr hnm hvs hin hps hargs hbs
        obtain ⟨ws, rfl, hws, rfl⟩ := ctor_back hI hg htr hk0 hw hsorts.1 hsorts.2 ⟨a, by
          show (KoreAML.sym (.symbol (c.symName k.name))).interpret I KoreAML.val0 a
          rw [(lookupSig_spec hk0).2]; exact ha, hm⟩
        have ih := patVals_backC hps hargs hws hbs
        exact ⟨.ctor hc ih.1, fun j hj => ih.2 j (by rw [varOccs] at hj; exact hj)⟩
      | false =>
        have hd : downHead c f = true := by rw [hc] at hhd; simpa using hhd
        cases hov : c.isOvl f with
        | true =>
          obtain ⟨o, hlo, rfl⟩ := patAll_lookup_ovl hov hk'
          obtain ⟨hom, hn, -, hit, -⟩ := OvlLaws.ovl_parts (OvlOK.ok (c := c)) hlo
          rw [kore_app, tr_symApp, symHead_none hit, trArgs_appList, interp_appList] at hm
          obtain ⟨a, ha, bs, hbs, hm⟩ := hm
          have hsorts := patSortsC hI hph hcs hcso hg htr hnm hvs hin hps hargs hbs
          have H := (inferInstance : OvlOK c).hyp htr
          obtain ⟨-, -, -, -, hks, -⟩ := OvlLaws.ovl_facts_ovlF H.fnFacts hlo
          obtain ⟨ws, hws, rfl, hv⟩ := ovl_back hI htr hg _ o.sig hks (OvlLaws.ovlRank_le _)
            (by rw [hn]; exact OvlLaws.noFnOver_of_not_fnOvl hnfo) hw hsorts.1 hsorts.2
            ⟨a, by rw [← hn] at ha; exact ha, hm⟩
          have ih := patVals_backC hps hargs hws hbs
          refine ⟨.ovl hc hov ih.1 (by rw [← hn]; exact hv), fun j hj => ih.2 j (by rw [varOccs] at hj; exact hj)⟩
        | false =>
        have hR := head_reading hI hph hcs hcso hc hov hd hk'
        have hit := hR.ite
        rw [kore_app, tr_symApp, symHead_none hit, trArgs_appList, interp_appList] at hm
        obtain ⟨a, ha, bs, hbs, hm⟩ := hm
        have hsorts := patSortsC hI hph hcs hcso hg htr hnm hvs hin hps hargs hbs
        obtain ⟨ws, hws, rfl, hv⟩ := head_back hI hg htr hR hw hsorts.1 hsorts.2 ⟨a, ha, hm⟩
        have ih := patVals_backC hps hargs hws hbs
        refine ⟨?_, fun j hj => ih.2 j (by rw [varOccs] at hj; exact hj)⟩
        cases hpf : patternHooks.contains f with
        | true => exact .hook hpf ih.1 (hook_of_collVal (isHook_patHook hpf) hv)
        | false => exact .coll hc (isCollPat_of_down hd hov hpf) ih.1 hv
    | .inj a b p, s, w, hp, ht, hw, hm => by
      obtain ⟨hab, ht', rfl⟩ := sortOfTerm_inj.mp ht
      rw [collPat] at hp
      rw [Term.kore, KoreAML.tr_injP, interp_injApp] at hm
      obtain ⟨x, hx, hm⟩ := hm
      have hxs := patSortC hI hph hcs hcso hg htr hnm hvs hin hp ht' x hx
      obtain ⟨w', hw', rfl, rfl⟩ := inj_back hI hg htr w hab hw hxs hm
      have ih := patVal_backC hp ht' hw' hx
      exact ⟨.inj ih.1, fun j hj => ih.2 j (by rw [varOccs] at hj; exact hj)⟩
    | .as p i, s, w, hp, ht, hw, hm => by
      obtain ⟨hvi, ht'⟩ := Exec.sortOfTerm_as ht
      rw [collPat] at hp
      rw [tr_kore_as hI hg htr hnm hvs hin] at hm
      have ih := patVal_backC hp ht' hw hm.1
      refine ⟨.as ih.1 (substOf_var hI hg htr hnm hvs hin hvi hw hm.2), fun j hj => ?_⟩
      rw [varOccs] at hj
      rcases List.mem_append.mp hj with hj | hj
      · exact ih.2 j hj
      · rw [mem_one hj]; exact witnessed_of hvi hw hm.2
  theorem patVals_backC : ∀ {ps : List Term} {ss : List Srt} {ws : List GroundTerm}, collPats c ps = true →
      sortsOfTerms c.patCtxNF vars ps = some ss → c.sortsOf ws = some ss →
      All2 (fun φ b => φ.interpret I e b) ((Term.koreList c vs ps).map (KoreAML.tr ⟨tbl, []⟩)) (ws.map (elemOf c I)) →
      PatVals c (substOf c I tbl vs vars e) ps ws ∧ ∀ i ∈ varOccsList ps, Witnessed c I tbl vs vars e i
    | [], ss, ws, _, ht, hws, _ => by
      rw [sortsOfTerms_nil.mp ht] at hws
      rw [sortsOf_nil_eq hws]
      exact ⟨.nil, fun j hj => by rw [varOccsList] at hj; cases hj⟩
    | p :: ps, ss, ws, hp, ht, hws, hbs => by
      obtain ⟨s, ss', h1, h2, rfl⟩ := sortsOfTerms_cons.mp ht
      rw [collPats] at hp
      simp only [Bool.and_eq_true] at hp
      cases ws with
      | nil => rw [sortsOf_nil] at hws; cases hws
      | cons w ws =>
        obtain ⟨s0, ss0, hw, hws', he⟩ := sortsOf_cons.mp hws
        cases he
        rw [Term.koreList, List.map_cons, List.map_cons] at hbs
        cases hbs with
        | cons hb hbs =>
          have ih1 := patVal_backC hp.1 h1 hw hb
          have ih2 := patVals_backC hp.2 h2 hws' hbs
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
  (hph : patHooksApart c = true) (hcs : collsOK c = true) (hcso : collSortsOK c = true) (hg : genWf c = true)
  (htr : ∀ a b d, (a, b) ∈ c.subsorts → (b, d) ∈ c.subsorts → (a, d) ∈ c.subsorts)
  (hnm : NamesPlain c)
include hI hph hcs hcso hg htr

include hnm in
/-- **The core lemma for clauses, collection patterns included**, in a model of `Γ`. At
arguments where a clause fails in the model, its exclusion
`∃ȳ. ⌈req = true⌉ ∧ X̄ ∈ p̄` is empty, at a valuation that gives each formal argument `Xⱼ` the
element of the argument and the sort variable `R` a sort. -/
theorem exclusion_emptyC {fn : Fn} {cl : Clause} (hpre : cl.pre = .top)
    (hpats : sortsOfTerms c.patCtxNF cl.vars cl.pats = some fn.args)
    (hbinds : ∀ i < cl.vars.length, i ∈ varOccsList cl.pats) (hplain : collPats c cl.pats = true)
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
  obtain ⟨hpv, hwit⟩ := patVals_backC hI hph hcs hcso hg htr hnm (canonVars_length c cl.vars) hin hplain hpats hws hall
  obtain ⟨hws', hagr⟩ := substOf_ok hI hg htr (canonVars_length c cl.vars) (fun i hi => hwit i (hbinds i hi))
  obtain ⟨t, r, ht, hr, hrs, hden⟩ := hfail _ hws' hpv tbl e' hagr
  rw [ht] at hreq
  exact reqFalse_empty hI (S' := KoreAML.R) (fun a => by rw [trSort_R, KoreAML.interp_evar, he'R, hR]) hσR hr hrs hden m hreq

include hnm in
/-- **The core lemma for rules, collection patterns included**, in a model of `Γ`. If a rule
does not apply to a configuration in the model, the
configuration's element is not in the rule's `applies` pattern `∃x̄. (lhs ∧ ⌈req = true⌉)`. -/
theorem applies_emptyC {r : Rule} (hlhs : sortOfTerm c.patCtxNF r.vars r.lhs = some topCellSort)
    (hbinds : ∀ i < r.vars.length, i ∈ varOccs r.lhs) (hplain : collPat c r.lhs = true)
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
  obtain ⟨hpv, hwit⟩ := patVal_backC hI hph hcs hcso hg htr hnm (canonVars_length c r.vars) hin hplain hlhs hx hl
  obtain ⟨hws', hagr⟩ := substOf_ok hI hg htr (canonVars_length c r.vars) (fun i hi => hwit i (hbinds i hi))
  obtain ⟨t, v, ht, hv, hvs, hden⟩ := hfail _ hws' hpv tbl e' hagr
  rw [ht] at hreq
  obtain ⟨σC, hσC1, hσC2⟩ := sortSing hI (top_numbered (c := c))
  exact reqFalse_empty hI (S' := srtOf c topCellSort) (fun a => by unfold srtOf; rw [trSort_srt]; exact hσC1 a) hσC2
    hv hvs hden _ hreq


end

end Faithful

end KCore
