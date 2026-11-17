/-
  KCore. The value model satisfies the collections (`SatCollsGoal`). An element of a map sort is
  a canonical map value, its unit the empty map, `elem(a, b)` the one-entry map, `concat` the
  union of two maps (`union`), nothing where their keys meet; a list sort's elements are list
  values, `concat` their concatenation; a set sort's elements are set values (sorted, without
  repetition), `concat` the union of two sets with no member in common (`concatS`), nothing where
  they share one. Each axiom of `ΓColls` is then a fact about canonical maps (one representation
  per finite map: `entries_canon`), about lists, or about canonical sets (one representation per
  finite set: `Set.ext`; `concatS_single`, `set_decomp`).
-/
import KcoreSpec.ModelDomains
import KcoreSpec.Collections

set_option autoImplicit false

namespace KCore

namespace Faithful

namespace Model

open ML

variable {c : Semantics}

/-! ## Canonical maps -/

theorem entriesOK_iff {ks vs : Srt} : ∀ {es : Entries},
    c.entriesOK ks vs es = true ↔ ∀ e ∈ es, c.entryOK ks vs e = true
  | [] => ⟨(fun _ _ h => nomatch h), (fun _ => rfl)⟩
  | e :: es => by
    rw [entriesOK_cons', entriesOK_iff]
    constructor
    · rintro ⟨h1, h2⟩ x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact h1
      · exact h2 x hx
    · intro h
      exact ⟨h e (List.mem_cons_self ..), fun x hx => h x (List.mem_cons_of_mem _ hx)⟩

theorem cmp_ne_swap {x y : GroundTerm} (h : GroundTerm.cmp x y ≠ .eq) : GroundTerm.cmp y x ≠ .eq := fun h' =>
  h (by rw [GroundTerm.cmp_swap, h']; rfl)

theorem union_nil {a b : Entries} (h : union a b = some []) : a = [] ∧ b = [] := by
  have hm := (union_spec h).1
  constructor
  · exact List.eq_nil_iff_forall_not_mem.mpr fun e he => by simpa using (hm e).mpr (.inl he)
  · exact List.eq_nil_iff_forall_not_mem.mpr fun e he => by simpa using (hm e).mpr (.inr he)

theorem union_single {p q : GroundTerm × GroundTerm} {rs : Entries} (h : union [p] rs = some [q]) :
    rs = [] ∧ p = q := by
  obtain ⟨hm, -, -, hap⟩ := union_spec h
  have hp : p = q := by simpa using (hm p).mpr (.inl (List.mem_singleton_self _))
  refine ⟨List.eq_nil_iff_forall_not_mem.mpr fun e he => ?_, hp⟩
  have he' : e = q := by simpa using (hm e).mpr (.inr he)
  have := hap p (List.mem_singleton_self _) e he
  rw [he', ← hp, GroundTerm.cmp_refl] at this
  exact this rfl

/-- Two entries of a sorted map with keys `cmp`-equal are one entry. -/
theorem sorted_key_unique : ∀ {es : Entries}, keysSorted es = true → ∀ {p q : GroundTerm × GroundTerm},
    p ∈ es → q ∈ es → GroundTerm.cmp p.1 q.1 = .eq → p = q := by
  intro es hs
  have hpw := sorted_pairwise hs
  clear hs
  induction hpw with
  | nil => intro p q hp; exact nomatch hp
  | @cons x l hx _ ih =>
    intro p q hp hq hpq
    rcases List.mem_cons.mp hp with hp1 | hp1 <;> rcases List.mem_cons.mp hq with hq1 | hq1
    · rw [hp1, hq1]
    · subst hp1; rw [hx q hq1] at hpq; cases hpq
    · subst hq1; have := hx p hp1; rw [GroundTerm.cmp_swap, hpq] at this; cases this
    · exact ih hp1 hq1 hpq

/-- The entries of a map without the key `a`. -/
def dropKey (a : GroundTerm) (es : Entries) : Entries := es.filter fun e => !(GroundTerm.cmp e.1 a == .eq)

theorem dropKey_sublist (a : GroundTerm) (es : Entries) : (dropKey a es).Sublist es := List.filter_sublist

theorem mem_dropKey {a : GroundTerm} {es : Entries} {e : GroundTerm × GroundTerm} :
    e ∈ dropKey a es ↔ e ∈ es ∧ GroundTerm.cmp e.1 a ≠ .eq := by
  simp [dropKey]

/-- **A map entry of a union is an entry of one part.** If `{a ↦ b} ∪ rs` and `m₁ ∪ m₂` are one
map, the part holding the key `a` is `{a ↦ b} ∪ ys` for `ys` that part without `a`, and `rs` is
`ys` united with the other part. -/
theorem map_decomp {a b : GroundTerm} {rs es1 es2 M : Entries} (hrs : keysSorted rs = true)
    (h1s : keysSorted es1 = true) (h2s : keysSorted es2 = true)
    (hl : union [(a, b)] rs = some M) (hr : union es1 es2 = some M) :
    (union [(a, b)] (dropKey a es1) = some es1 ∧ union (dropKey a es1) es2 = some rs) ∨
      (union [(a, b)] (dropKey a es2) = some es2 ∧ union es1 (dropKey a es2) = some rs) := by
  obtain ⟨hlm, -, -, hlap⟩ := union_spec hl
  obtain ⟨hrm, -, -, hrap⟩ := union_spec hr
  have hMs : keysSorted M = true := union_sorted h2s hr
  have hab : (a, b) ∈ es1 ∨ (a, b) ∈ es2 := (hrm _).mp ((hlm _).mpr (.inl (List.mem_singleton_self _)))
  have hsing : KeysApart [(a, b)] := List.pairwise_singleton _ _
  have hdrop_ap : ∀ es : Entries, ∀ e' ∈ dropKey a es, GroundTerm.cmp a e'.1 ≠ .eq := fun es e' he' =>
    cmp_ne_swap (mem_dropKey.mp he').2
  -- the part holding `a` is `{a ↦ b}` and the rest of it
  have hpart : ∀ es : Entries, keysSorted es = true → (a, b) ∈ es → union [(a, b)] (dropKey a es) = some es := by
    intro es hs habm
    obtain ⟨m', hm', hmm'⟩ := union_exists (b := dropKey a es) hsing (by
      intro e he e' he'; rw [List.mem_singleton.mp he]; exact hdrop_ap es e' he')
    rw [hm']
    congr 1
    refine entries_canon (union_sorted (sorted_sublist (dropKey_sublist _ _) hs) hm') hs fun e => ?_
    rw [hmm', List.mem_singleton, mem_dropKey]
    constructor
    · rintro (rfl | ⟨he, -⟩)
      · exact habm
      · exact he
    · intro he
      by_cases hk : GroundTerm.cmp e.1 a = .eq
      · exact .inl (sorted_key_unique hs he habm hk)
      · exact .inr ⟨he, hk⟩
  have hMa : ∀ e ∈ M, GroundTerm.cmp e.1 a ≠ .eq → e ∈ rs := fun e he hk => by
    rcases (hlm e).mp he with he' | he'
    · rw [List.mem_singleton.mp he'] at hk; exact absurd (GroundTerm.cmp_refl a) hk
    · exact he'
  have hrsa : ∀ e ∈ rs, GroundTerm.cmp e.1 a ≠ .eq := fun e he =>
    cmp_ne_swap (hlap _ (List.mem_singleton_self _) e he)
  rcases hab with hab | hab
  · left
    refine ⟨hpart es1 h1s hab, ?_⟩
    obtain ⟨m'', hm'', hmm''⟩ := union_exists (a := dropKey a es1) (b := es2)
      (sorted_apart (sorted_sublist (dropKey_sublist _ _) h1s))
      (fun e he e' he' => hrap e (mem_dropKey.mp he).1 e' he')
    rw [hm'']
    congr 1
    refine entries_canon (union_sorted h2s hm'') hrs fun e => ?_
    rw [hmm'', mem_dropKey]
    constructor
    · rintro (⟨he, hk⟩ | he)
      · exact hMa e ((hrm e).mpr (.inl he)) hk
      · refine hMa e ((hrm e).mpr (.inr he)) fun hk => ?_
        have := hrap _ hab e he
        rw [GroundTerm.cmp_swap, hk] at this
        exact this rfl
    · intro he
      rcases (hrm e).mp ((hlm e).mpr (.inr he)) with he1 | he2
      · exact .inl ⟨he1, hrsa e he⟩
      · exact .inr he2
  · right
    refine ⟨hpart es2 h2s hab, ?_⟩
    obtain ⟨m'', hm'', hmm''⟩ := union_exists (a := es1) (b := dropKey a es2) (sorted_apart h1s)
      (fun e he e' he' => hrap e he e' (mem_dropKey.mp he').1)
    rw [hm'']
    congr 1
    refine entries_canon (union_sorted (sorted_sublist (dropKey_sublist _ _) h2s) hm'') hrs fun e => ?_
    rw [hmm'', mem_dropKey]
    constructor
    · rintro (he | ⟨he, hk⟩)
      · refine hMa e ((hrm e).mpr (.inl he)) fun hk => ?_
        have := hrap e he _ hab
        rw [hk] at this
        exact this rfl
      · exact hMa e ((hrm e).mpr (.inr he)) hk
    · intro he
      rcases (hrm e).mp ((hlm e).mpr (.inr he)) with he1 | he2
      · exact .inl he1
      · exact .inr ⟨he2, hrsa e he⟩

/-! ## The collection symbols at values, where a hook may be undefined -/

/-- What a collection's symbol gives is what its library hook gives, where that hook has no silent
point (at one, the result may be the interpretation's value). -/
theorem coll_sym_inv (h : HypModelCore c) {k : CollSig} (hk : k ∈ c.allColls) {f g : Sym} {args : List Srt}
    (hf : (f = k.unit ∧ g = (builtinColl k.kind).unit ∧ args = []) ∨
      (f = k.elem ∧ g = (builtinColl k.kind).elem ∧ args = elemArgs k) ∨
      (f = k.concat ∧ g = (builtinColl k.kind).concat ∧ args = [k.sort, k.sort]))
    (hsg : silentKey g = false)
    {kf : CtorSig} (hkfn : kf.name = f) {vs : List GroundTerm} {m : Elem} (hr : result c kf vs m) :
    ∃ v, hook g vs = some (some v) := by
  have hfm : f ∈ [k.unit, k.elem, k.concat] := by
    rcases hf with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp
  have hnc := h.collNotCtor hk hfm
  rw [← hkfn] at hnc
  rcases List.mem_append.mp hk with hb | hu
  · have hfg : f = g ∧ isHook f = true := by
      simp only [builtinColls, List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl | rfl | rfl <;>
        rcases hf with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;> decide
    obtain ⟨rfl, hh⟩ := hfg
    rw [← hkfn] at hh
    rw [result_hook hnc hh] at hr
    obtain ⟨v, -, hv⟩ := hr
    rw [hkfn, Semantics.hookRes_of_notKey hsg] at hv
    exact ⟨v, hv⟩
  · have hs := collSymsOK_spec (collsOK_colls h.collsOK hu)
    have hlp : c.lookupParam f = some { sig := ⟨f, args, k.sort⟩, impl := some g } := by
      rcases hf with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
      · exact hs.2.2.1
      · exact hs.2.2.2.1
      · exact hs.2.2.2.2
    have hh : isHook kf.name = false := by rw [hkfn]; exact (hs.2.1 f hfm).1
    have hp : c.isParam kf.name = true := by rw [hkfn]; simp [Semantics.isParam, hlp]
    rw [result_param hnc hh hp] at hr
    obtain ⟨v, -, hv⟩ := hr
    rw [hkfn] at hv
    unfold Semantics.paramVal at hv
    rw [hlp] at hv
    dsimp only at hv
    have hcg : Semantics.rawArgHooks.contains g = true := by
      rcases hf with ⟨-, rfl, -⟩ | ⟨-, rfl, -⟩ | ⟨-, rfl, -⟩ <;> generalize k.kind = K <;> cases K <;> decide
    rw [Semantics.libArgs_coll c hcg, Semantics.hookRes_of_notKey hsg] at hv
    cases hg : hook g vs with
    | none => rw [hg] at hv; simp at hv
    | some r =>
      cases r with
      | none => rw [hg] at hv; simp at hv
      | some v' => exact ⟨v', rfl⟩

/-! ## Readings in a map collection -/

section
variable (h : HypModelCore c) {k : CollSig} (hk : k ∈ c.allColls) (hkind : k.kind = .map)
include h hk hkind

theorem map_val {w : GroundTerm} (hw : c.sortOf w = some k.sort) :
    ∃ es, w = .map k.sort es ∧ keysSorted es = true ∧ c.entriesOK k.key (valSort k) es = true := by
  have hco := h.collOf_self hk
  rcases h.coll_shape' hco (collSortsOK_mem h.collSortsOK hk) hw with
    ⟨-, es, rfl⟩ | ⟨h2, -⟩ | ⟨h2, -⟩
  · obtain ⟨-, h2, h3⟩ := (sortOf_map_iff hco (h.mapVal hk hkind) hkind).mp hw
    exact ⟨es, rfl, h2, h3⟩
  · rw [hkind] at h2; cases h2
  · rw [hkind] at h2; cases h2

namespace AtT

variable {T : GroundTerm → GroundTerm → Prop}

theorem U_map (e : Valuation Elem) (x : Elem) :
    (collU c k).interpret (stdI_T c T) e x ↔ x = .val (.map k.sort []) := by
  have hco := h.collOf_self hk
  have := coll_symE (T := T) h hk (Or.inl ⟨rfl, rfl, rfl⟩) (vs := []) rfl (r := .map Srt.map [])
    (by rw [hkind, builtinColl_map, Exec.hook_unit_eq]) (by rw [hkind, builtinColl_map]; rfl)
    ((sortOf_map_iff hco (h.mapVal hk hkind) hkind).mpr ⟨hkind, rfl, rfl⟩) x
  refine Iff.trans ?_ this
  unfold collU symP SymE
  constructor
  · intro hx; exact ⟨x, hx, rfl⟩
  · rintro ⟨a, ha, hx⟩; have : x = a := hx; subst this; exact ha

end AtT

theorem U_map (e : Valuation Elem) (x : Elem) :
    (collU c k).interpret (stdI c) e x ↔ x = .val (.map k.sort []) :=
  AtT.U_map (c := c) (T := StepM c) (e := e) (x := x) (h := h) (hk := hk) (hkind := hkind)

namespace AtT

variable {T : GroundTerm → GroundTerm → Prop}

theorem E_map {e : Valuation Elem} {A B : EVar} {a b : GroundTerm} (ha : c.sortOf a = some k.key)
    (hb : c.sortOf b = some (valSort k)) (hA : e.evalEvar A = .val a) (hB : e.evalEvar B = .val b) (x : Elem) :
    (collE c k (.evar A) (.evar B)).interpret (stdI_T c T) e x ↔ x = .val (.map k.sort [(a, b)]) := by
  have hco := h.collOf_self hk
  unfold collE symP
  rw [interp_symList _ _ [.val a, .val b]
    (.cons (fun m => by rw [KoreAML.interp_evar, hA]) (.cons (fun m => by rw [KoreAML.interp_evar, hB]) .nil)) x]
  exact coll_symE h hk (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)) (vs := [a, b]) (elemArgs_length hkind).symm
    (r := .map Srt.map [(a, b)]) (by rw [hkind, builtinColl_map, Exec.hook_elem_eq])
    (by rw [hkind, builtinColl_map]; rfl)
    ((sortOf_map_iff hco (h.mapVal hk hkind) hkind).mpr ⟨hkind, rfl, by simp [Semantics.entriesOK, Semantics.entryOK, ha, hb]⟩) x

end AtT

theorem E_map {e : Valuation Elem} {A B : EVar} {a b : GroundTerm} (ha : c.sortOf a = some k.key)
    (hb : c.sortOf b = some (valSort k)) (hA : e.evalEvar A = .val a) (hB : e.evalEvar B = .val b) (x : Elem) :
    (collE c k (.evar A) (.evar B)).interpret (stdI c) e x ↔ x = .val (.map k.sort [(a, b)]) :=
  AtT.E_map (c := c) (T := StepM c) (e := e) (A := A) (B := B) (a := a) (b := b) (ha := ha) (hb := hb) (hA := hA) (hB := hB) (x := x) (h := h) (hk := hk) (hkind := hkind)

namespace AtT

variable {T : GroundTerm → GroundTerm → Prop}

theorem C_map {e : Valuation Elem} {φ ψ : KoreAML.P} {es1 es2 : Entries}
    (h1 : keysSorted es1 = true ∧ c.entriesOK k.key (valSort k) es1 = true)
    (h2 : keysSorted es2 = true ∧ c.entriesOK k.key (valSort k) es2 = true)
    (hφ : ∀ m, φ.interpret (stdI_T c T) e m ↔ m = .val (.map k.sort es1))
    (hψ : ∀ m, ψ.interpret (stdI_T c T) e m ↔ m = .val (.map k.sort es2)) (x : Elem) :
    (collC c k φ ψ).interpret (stdI_T c T) e x ↔ ∃ u, union es1 es2 = some u ∧ x = .val (.map k.sort u) := by
  have hco := h.collOf_self hk
  have hcc : (c.symName k.concat = c.symName k.concat ∧ (builtinColl k.kind).concat = (builtinColl k.kind).concat ∧
      [k.sort, k.sort] = [k.sort, k.sort]) := ⟨rfl, rfl, rfl⟩
  obtain ⟨kf, hkf, hkfn, hkfa, hres⟩ := coll_sym h hk (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩))
  unfold collC symP
  rw [interp_symList _ _ [.val (.map k.sort es1), .val (.map k.sort es2)] (.cons hφ (.cons hψ .nil)) x,
    show [Elem.val (.map k.sort es1), Elem.val (.map k.sort es2)] = [GroundTerm.map k.sort es1, .map k.sort es2].map Elem.val
      from rfl, ← hkfn, symE_vals h.namesK hkf (by rw [hkfa]; rfl)]
  have hhook : hook (builtinColl k.kind).concat [.map k.sort es1, .map k.sort es2] =
      some ((union es1 es2).map (GroundTerm.map Srt.map)) := by
    rw [hkind, builtinColl_map, Exec.hook_concat_eq]
  have hsr : ∀ u, union es1 es2 = some u → c.sortOf ((GroundTerm.map Srt.map u).withSort k.sort) = some k.sort :=
    fun u hu => by
      refine (sortOf_map_iff hco (h.mapVal hk hkind) hkind).mpr ⟨hkind, union_sorted h2.1 hu, entriesOK_iff.mpr fun e he => ?_⟩
      rcases (union_spec hu).1 e |>.mp he with he | he
      · exact entriesOK_iff.mp h1.2 e he
      · exact entriesOK_iff.mp h2.2 e he
  constructor
  · intro hr
    obtain ⟨v, hv⟩ := coll_sym_inv h hk (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩))
      (by rw [hkind]; exact silentKey_of_mem rfl) hkfn hr
    have hv0 := hv
    rw [hhook] at hv0
    obtain ⟨u, hu, rfl⟩ := Option.map_eq_some_iff.mp (Option.some.inj hv0)
    exact ⟨u, hu, (hres hv (by rw [hkind, builtinColl_map]; rfl) (hsr u hu) x).mp hr⟩
  · rintro ⟨u, hu, rfl⟩
    have hv : hook (builtinColl k.kind).concat [.map k.sort es1, .map k.sort es2] = some (some (.map Srt.map u)) := by
      rw [hhook, hu]; rfl
    exact (hres hv (by rw [hkind, builtinColl_map]; rfl) (hsr u hu) _).mpr rfl

end AtT

theorem C_map {e : Valuation Elem} {φ ψ : KoreAML.P} {es1 es2 : Entries}
    (h1 : keysSorted es1 = true ∧ c.entriesOK k.key (valSort k) es1 = true)
    (h2 : keysSorted es2 = true ∧ c.entriesOK k.key (valSort k) es2 = true)
    (hφ : ∀ m, φ.interpret (stdI c) e m ↔ m = .val (.map k.sort es1))
    (hψ : ∀ m, ψ.interpret (stdI c) e m ↔ m = .val (.map k.sort es2)) (x : Elem) :
    (collC c k φ ψ).interpret (stdI c) e x ↔ ∃ u, union es1 es2 = some u ∧ x = .val (.map k.sort u) :=
  AtT.C_map (c := c) (T := StepM c) (e := e) (φ := φ) (ψ := ψ) (es1 := es1) (es2 := es2) (h1 := h1) (h2 := h2) (hφ := hφ) (hψ := hψ) (x := x) (h := h) (hk := hk) (hkind := hkind)

end

/-! ## Valuations -/

theorem upd_ne {e : Valuation Elem} {i j : Nat} (hij : i ≠ j) (a : Elem) :
    Function.update e.evalEvar (⟨j⟩ : EVar) a ⟨i⟩ = e.evalEvar ⟨i⟩ :=
  Function.update_noteq (fun h => hij (by cases h; rfl)) _ _

namespace AtT

variable {T : GroundTerm → GroundTerm → Prop}

theorem evar_eq_iff {e : Valuation Elem} {x : EVar} {φ : KoreAML.P} {w : Elem} (hx : e.evalEvar x = w)
    (hφ : ∀ m, φ.interpret (stdI_T c T) e m ↔ m = w) (m : Elem) :
    (Pattern.evar x ≡ φ : KoreAML.P).interpret (stdI_T c T) e m := by
  rw [KoreAML.interp_equal defOK_std]
  intro a
  rw [KoreAML.interp_evar, hx, hφ]

end AtT

theorem evar_eq_iff {e : Valuation Elem} {x : EVar} {φ : KoreAML.P} {w : Elem} (hx : e.evalEvar x = w)
    (hφ : ∀ m, φ.interpret (stdI c) e m ↔ m = w) (m : Elem) :
    (Pattern.evar x ≡ φ : KoreAML.P).interpret (stdI c) e m :=
  AtT.evar_eq_iff (c := c) (T := StepM c) (e := e) (x := x) (φ := φ) (w := w) (hx := hx) (hφ := hφ) (m := m)

namespace AtT

variable {T : GroundTerm → GroundTerm → Prop}

theorem guard_val (hn : NamesApartK c) {s : Srt} (hs : s < nRegSorts + c.sortNames.length) {x : EVar}
    {e : Valuation Elem} {m : Elem} (hg : (x ∈∈ inSort c s : KoreAML.P).interpret (stdI_T c T) e m) :
    ∃ v, e.evalEvar x = .val v ∧ c.sortOf v = some s := by
  rw [KoreAML.interp_member defOK_std] at hg
  unfold inSort sortP at hg
  exact inSort_val ((inhOf_sort hn hs e _).mp hg)

end AtT

theorem guard_val (hn : NamesApartK c) {s : Srt} (hs : s < nRegSorts + c.sortNames.length) {x : EVar}
    {e : Valuation Elem} {m : Elem} (hg : (x ∈∈ inSort c s : KoreAML.P).interpret (stdI c) e m) :
    ∃ v, e.evalEvar x = .val v ∧ c.sortOf v = some s :=
  AtT.guard_val (c := c) (T := StepM c) (hn := hn) (s := s) (hs := hs) (x := x) (e := e) (m := m) (hg := hg)

/-! ## The map axioms -/

section
variable (h : HypModelCore c) {k : CollSig} (hk : k ∈ c.allColls) (hkind : k.kind = .map)
include h hk hkind

namespace AtT

variable {T : GroundTerm → GroundTerm → Prop}

theorem sat_mapUnitSplit : stdI_T c T ⊧ᴵ mapUnitSplitAx c k := by
  obtain ⟨hsS, -, -⟩ := h.collSorts hk
  intro e m
  unfold mapUnitSplitAx
  dsimp only
  refine guarded_intro fun hg => ?_
  obtain ⟨w1, h1, hw1⟩ := guard_val (T := T) h.namesK hsS (hg _ (List.mem_cons_self ..))
  obtain ⟨w2, h2, hw2⟩ := guard_val (T := T) h.namesK hsS (hg _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
  obtain ⟨es1, rfl, hs1, he1⟩ := map_val h hk hkind hw1
  obtain ⟨es2, rfl, hs2, he2⟩ := map_val h hk hkind hw2
  rw [interpret_impl, defined_app]
  rintro ⟨x, hx⟩
  rw [interpret_conj, U_map h hk hkind, C_map h hk hkind ⟨hs1, he1⟩ ⟨hs2, he2⟩
    (fun m => by rw [KoreAML.interp_evar, h1]) (fun m => by rw [KoreAML.interp_evar, h2])] at hx
  obtain ⟨rfl, u, hu, hx⟩ := hx
  cases hx
  obtain ⟨rfl, rfl⟩ := union_nil hu
  rw [interpret_conj]
  exact ⟨evar_eq_iff h1 (U_map h hk hkind e) m, evar_eq_iff h2 (U_map h hk hkind e) m⟩

end AtT

theorem sat_mapUnitSplit : stdI c ⊧ᴵ mapUnitSplitAx c k :=
  AtT.sat_mapUnitSplit (c := c) (T := StepM c) (h := h) (hk := hk) (hkind := hkind)

namespace AtT

variable {T : GroundTerm → GroundTerm → Prop}

theorem sat_mapElemNotUnit : stdI_T c T ⊧ᴵ mapElemNotUnitAx c k := by
  obtain ⟨-, hsK, hsV⟩ := h.collSorts hk
  intro e m
  unfold mapElemNotUnitAx
  dsimp only
  refine guarded_intro fun hg => ?_
  obtain ⟨a, ha, hwa⟩ := guard_val (T := T) h.namesK hsK (hg _ (List.mem_cons_self ..))
  obtain ⟨b, hb, hwb⟩ := guard_val (T := T) h.namesK hsV (hg _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
  rw [interpret_neg, defined_app]
  rintro ⟨x, hx⟩
  rw [interpret_conj, U_map h hk hkind, E_map h hk hkind hwa hwb ha hb] at hx
  obtain ⟨rfl, hx⟩ := hx
  cases hx

end AtT

theorem sat_mapElemNotUnit : stdI c ⊧ᴵ mapElemNotUnitAx c k :=
  AtT.sat_mapElemNotUnit (c := c) (T := StepM c) (h := h) (hk := hk) (hkind := hkind)

namespace AtT

variable {T : GroundTerm → GroundTerm → Prop}

theorem sat_mapElemAtom : stdI_T c T ⊧ᴵ mapElemAtomAx c k := by
  obtain ⟨hsS, hsK, hsV⟩ := h.collSorts hk
  intro e m
  unfold mapElemAtomAx
  dsimp only
  refine guarded_intro fun hg => ?_
  have g := fun i (hi : i < 5) => hg _ (List.getElem_mem (l := [(⟨1⟩ : EVar) ∈∈ inSort c k.key, (⟨2⟩ : EVar) ∈∈ inSort c (valSort k),
    (⟨3⟩ : EVar) ∈∈ inSort c k.key, (⟨4⟩ : EVar) ∈∈ inSort c (valSort k), (⟨5⟩ : EVar) ∈∈ inSort c k.sort]) hi)
  obtain ⟨a, ha, hwa⟩ := guard_val (T := T) h.namesK hsK (g 0 (by decide))
  obtain ⟨b, hb, hwb⟩ := guard_val (T := T) h.namesK hsV (g 1 (by decide))
  obtain ⟨a', ha', hwa'⟩ := guard_val (T := T) h.namesK hsK (g 2 (by decide))
  obtain ⟨b', hb', hwb'⟩ := guard_val (T := T) h.namesK hsV (g 3 (by decide))
  obtain ⟨w, hr, hw⟩ := guard_val (T := T) h.namesK hsS (g 4 (by decide))
  obtain ⟨rs, rfl, hrs, hre⟩ := map_val h hk hkind hw
  rw [interpret_impl, defined_app]
  rintro ⟨x, hx⟩
  rw [interpret_conj, E_map h hk hkind hwa' hwb' ha' hb',
    C_map h hk hkind ⟨rfl, by simp [Semantics.entriesOK, Semantics.entryOK, hwa, hwb]⟩ ⟨hrs, hre⟩
      (E_map h hk hkind hwa hwb ha hb) (fun m => by rw [KoreAML.interp_evar, hr])] at hx
  obtain ⟨rfl, u, hu, hx⟩ := hx
  cases hx
  obtain ⟨rfl, hp⟩ := union_single hu
  cases hp
  simp only [interpret_conj]
  exact ⟨⟨evar_eq_iff ha (fun m => by rw [KoreAML.interp_evar, ha']) m,
    evar_eq_iff hb (fun m => by rw [KoreAML.interp_evar, hb']) m⟩, evar_eq_iff hr (U_map h hk hkind e) m⟩

end AtT

theorem sat_mapElemAtom : stdI c ⊧ᴵ mapElemAtomAx c k :=
  AtT.sat_mapElemAtom (c := c) (T := StepM c) (h := h) (hk := hk) (hkind := hkind)

namespace AtT

variable {T : GroundTerm → GroundTerm → Prop}

theorem sat_mapDecomp : stdI_T c T ⊧ᴵ mapDecompAx c k := by
  obtain ⟨hsS, hsK, hsV⟩ := h.collSorts hk
  intro e m
  unfold mapDecompAx
  dsimp only
  refine guarded_intro fun hg => ?_
  have g := fun i (hi : i < 5) => hg _ (List.getElem_mem (l := [(⟨1⟩ : EVar) ∈∈ inSort c k.key, (⟨2⟩ : EVar) ∈∈ inSort c (valSort k),
    (⟨3⟩ : EVar) ∈∈ inSort c k.sort, (⟨4⟩ : EVar) ∈∈ inSort c k.sort, (⟨5⟩ : EVar) ∈∈ inSort c k.sort]) hi)
  obtain ⟨a, ha, hwa⟩ := guard_val (T := T) h.namesK hsK (g 0 (by decide))
  obtain ⟨b, hb, hwb⟩ := guard_val (T := T) h.namesK hsV (g 1 (by decide))
  obtain ⟨wr, hr, hwr⟩ := guard_val (T := T) h.namesK hsS (g 2 (by decide))
  obtain ⟨w1, h1, hw1⟩ := guard_val (T := T) h.namesK hsS (g 3 (by decide))
  obtain ⟨w2, h2, hw2⟩ := guard_val (T := T) h.namesK hsS (g 4 (by decide))
  obtain ⟨rs, rfl, hrs, hre⟩ := map_val h hk hkind hwr
  obtain ⟨es1, rfl, hs1, he1⟩ := map_val h hk hkind hw1
  obtain ⟨es2, rfl, hs2, he2⟩ := map_val h hk hkind hw2
  have hab : keysSorted [(a, b)] = true ∧ c.entriesOK k.key (valSort k) [(a, b)] = true :=
    ⟨rfl, by simp [Semantics.entriesOK, Semantics.entryOK, hwa, hwb]⟩
  rw [interpret_impl, defined_app]
  rintro ⟨x, hx⟩
  rw [interpret_conj, C_map h hk hkind hab ⟨hrs, hre⟩ (E_map h hk hkind hwa hwb ha hb)
      (fun m => by rw [KoreAML.interp_evar, hr]),
    C_map h hk hkind ⟨hs1, he1⟩ ⟨hs2, he2⟩ (fun m => by rw [KoreAML.interp_evar, h1])
      (fun m => by rw [KoreAML.interp_evar, h2])] at hx
  obtain ⟨⟨u, hu, rfl⟩, u', hu', hx⟩ := hx
  cases hx
  have hdrop : ∀ es : Entries, keysSorted es = true → c.entriesOK k.key (valSort k) es = true →
      keysSorted (dropKey a es) = true ∧ c.entriesOK k.key (valSort k) (dropKey a es) = true := fun es hs he =>
    ⟨sorted_sublist (dropKey_sublist _ _) hs,
      entriesOK_iff.mpr fun e' he' => entriesOK_iff.mp he e' (mem_dropKey.mp he').1⟩
  have hsy : ∀ ys : Entries, keysSorted ys = true → c.entriesOK k.key (valSort k) ys = true →
      c.sortOf (.map k.sort ys) = some k.sort := fun ys h1 h2 =>
    (sortOf_map_iff (h.collOf_self hk) (h.mapVal hk hkind) hkind).mpr ⟨hkind, h1, h2⟩
  -- the valuation with `y` (index 6) set to the element of `ys`
  have hval : ∀ ys : Entries, ∀ i, i ≠ 6 →
      (⟨Function.update e.evalEvar ⟨6⟩ (.val (.map k.sort ys)), e.evalSvar⟩ : Valuation Elem).evalEvar ⟨i⟩ =
        e.evalEvar ⟨i⟩ := fun ys i hi => upd_ne hi _
  rw [interpret_disj]
  rcases map_decomp hrs hs1 hs2 hu hu' with ⟨hl, hrr⟩ | ⟨hl, hrr⟩
  · left
    obtain ⟨hys, hye⟩ := hdrop es1 hs1 he1
    rw [KoreAML.interp_sExists]
    refine ⟨.val (.map k.sort (dropKey a es1)), ?_, ?_⟩
    · rw [KoreAML.interp_member defOK_std]
      simp only [Function.update_same]
      exact (inhOf_sort h.namesK hsS _ _).mpr (hsy _ hys hye)
    · have hy : ∀ m, (Pattern.evar (⟨6⟩ : EVar) : KoreAML.P).interpret (stdI_T c T)
          ⟨Function.update e.evalEvar ⟨6⟩ (.val (.map k.sort (dropKey a es1))), e.evalSvar⟩ m ↔
            m = .val (.map k.sort (dropKey a es1)) := fun m => by
        rw [KoreAML.interp_evar]; simp only [Function.update_same]
      rw [interpret_conj]
      constructor
      · refine evar_eq_iff ((hval _ 4 (by decide)).trans h1) (fun m => ?_) m
        rw [C_map h hk hkind hab ⟨hys, hye⟩ (E_map h hk hkind hwa hwb ((hval _ 1 (by decide)).trans ha)
          ((hval _ 2 (by decide)).trans hb)) hy]
        constructor
        · rintro ⟨u0, hu0, rfl⟩; rw [hl] at hu0; cases hu0; rfl
        · rintro rfl; exact ⟨_, hl, rfl⟩
      · refine evar_eq_iff ((hval _ 3 (by decide)).trans hr) (fun m => ?_) m
        rw [C_map h hk hkind ⟨hys, hye⟩ ⟨hs2, he2⟩ hy
          (fun m => by rw [KoreAML.interp_evar, (hval _ 5 (by decide)).trans h2])]
        constructor
        · rintro ⟨u0, hu0, rfl⟩; rw [hrr] at hu0; cases hu0; rfl
        · rintro rfl; exact ⟨_, hrr, rfl⟩
  · right
    obtain ⟨hys, hye⟩ := hdrop es2 hs2 he2
    rw [KoreAML.interp_sExists]
    refine ⟨.val (.map k.sort (dropKey a es2)), ?_, ?_⟩
    · rw [KoreAML.interp_member defOK_std]
      simp only [Function.update_same]
      exact (inhOf_sort h.namesK hsS _ _).mpr (hsy _ hys hye)
    · have hy : ∀ m, (Pattern.evar (⟨6⟩ : EVar) : KoreAML.P).interpret (stdI_T c T)
          ⟨Function.update e.evalEvar ⟨6⟩ (.val (.map k.sort (dropKey a es2))), e.evalSvar⟩ m ↔
            m = .val (.map k.sort (dropKey a es2)) := fun m => by
        rw [KoreAML.interp_evar]; simp only [Function.update_same]
      rw [interpret_conj]
      constructor
      · refine evar_eq_iff ((hval _ 5 (by decide)).trans h2) (fun m => ?_) m
        rw [C_map h hk hkind hab ⟨hys, hye⟩ (E_map h hk hkind hwa hwb ((hval _ 1 (by decide)).trans ha)
          ((hval _ 2 (by decide)).trans hb)) hy]
        constructor
        · rintro ⟨u0, hu0, rfl⟩; rw [hl] at hu0; cases hu0; rfl
        · rintro rfl; exact ⟨_, hl, rfl⟩
      · refine evar_eq_iff ((hval _ 3 (by decide)).trans hr) (fun m => ?_) m
        rw [C_map h hk hkind ⟨hs1, he1⟩ ⟨hys, hye⟩
          (fun m => by rw [KoreAML.interp_evar, (hval _ 4 (by decide)).trans h1]) hy]
        constructor
        · rintro ⟨u0, hu0, rfl⟩; rw [hrr] at hu0; cases hu0; rfl
        · rintro rfl; exact ⟨_, hrr, rfl⟩

end AtT

theorem sat_mapDecomp : stdI c ⊧ᴵ mapDecompAx c k :=
  AtT.sat_mapDecomp (c := c) (T := StepM c) (h := h) (hk := hk) (hkind := hkind)

end

/-! ## Readings in a list collection -/

section
variable (h : HypModelCore c) {k : CollSig} (hk : k ∈ c.allColls) (hkind : k.kind = .list)
include h hk hkind

theorem sortOf_list_iff {l : List GroundTerm} :
    c.sortOf (.list k.sort l) = some k.sort ↔ ∀ z ∈ l, c.sortOf z = some k.key := by
  have hev : elemsVal k l = .list k.sort l := by unfold elemsVal; rw [hkind]
  rw [← hev, sortOf_elems_iff (h.collOf_self hk) (.inr hkind)]
  constructor
  · exact fun h => h.2
  · intro h2; exact ⟨(fun h1 => by rw [hkind] at h1; cases h1), h2⟩

theorem list_val {w : GroundTerm} (hw : c.sortOf w = some k.sort) :
    ∃ l, w = .list k.sort l ∧ ∀ z ∈ l, c.sortOf z = some k.key := by
  have hco := h.collOf_self hk
  rcases h.coll_shape' hco (collSortsOK_mem h.collSortsOK hk) hw with
    ⟨h2, -⟩ | ⟨h2, -⟩ | ⟨-, l, rfl⟩
  · rcases h2 with h2 | h2 <;> (rw [hkind] at h2; cases h2)
  · rw [hkind] at h2; cases h2
  · exact ⟨l, rfl, (sortOf_list_iff h hk hkind).mp hw⟩

namespace AtT

variable {T : GroundTerm → GroundTerm → Prop}

theorem U_list (e : Valuation Elem) (x : Elem) :
    (collU c k).interpret (stdI_T c T) e x ↔ x = .val (.list k.sort []) := by
  have := coll_symE (T := T) h hk (Or.inl ⟨rfl, rfl, rfl⟩) (vs := []) rfl (r := .list Srt.list [])
    (by rw [hkind, builtinColl_list, hook_listUnit_eq]) (by rw [hkind, builtinColl_list]; rfl)
    ((sortOf_list_iff h hk hkind).mpr fun _ h => nomatch h) x
  refine Iff.trans ?_ this
  unfold collU symP SymE
  constructor
  · intro hx; exact ⟨x, hx, rfl⟩
  · rintro ⟨a, ha, hx⟩; have : x = a := hx; subst this; exact ha

end AtT

theorem U_list (e : Valuation Elem) (x : Elem) :
    (collU c k).interpret (stdI c) e x ↔ x = .val (.list k.sort []) :=
  AtT.U_list (c := c) (T := StepM c) (e := e) (x := x) (h := h) (hk := hk) (hkind := hkind)

namespace AtT

variable {T : GroundTerm → GroundTerm → Prop}

theorem I_list {e : Valuation Elem} {A : EVar} {a : GroundTerm} (ha : c.sortOf a = some k.key)
    (hA : e.evalEvar A = .val a) (x : Elem) :
    (collI c k (.evar A)).interpret (stdI_T c T) e x ↔ x = .val (.list k.sort [a]) := by
  unfold collI symP
  rw [interp_symList _ _ [.val a] (.cons (fun m => by rw [KoreAML.interp_evar, hA]) .nil) x]
  exact coll_symE h hk (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)) (vs := [a]) (elemArgs_length' (.inr hkind)).symm
    (r := .list Srt.list [a]) (by rw [hkind, builtinColl_list, hook_listElem_eq])
    (by rw [hkind, builtinColl_list]; rfl)
    ((sortOf_list_iff h hk hkind).mpr fun z hz => (List.mem_singleton.mp hz) ▸ ha) x

end AtT

theorem I_list {e : Valuation Elem} {A : EVar} {a : GroundTerm} (ha : c.sortOf a = some k.key)
    (hA : e.evalEvar A = .val a) (x : Elem) :
    (collI c k (.evar A)).interpret (stdI c) e x ↔ x = .val (.list k.sort [a]) :=
  AtT.I_list (c := c) (T := StepM c) (e := e) (A := A) (a := a) (ha := ha) (hA := hA) (x := x) (h := h) (hk := hk) (hkind := hkind)

namespace AtT

variable {T : GroundTerm → GroundTerm → Prop}

theorem C_list {e : Valuation Elem} {φ ψ : KoreAML.P} {l1 l2 : List GroundTerm}
    (h1 : ∀ z ∈ l1, c.sortOf z = some k.key) (h2 : ∀ z ∈ l2, c.sortOf z = some k.key)
    (hφ : ∀ m, φ.interpret (stdI_T c T) e m ↔ m = .val (.list k.sort l1))
    (hψ : ∀ m, ψ.interpret (stdI_T c T) e m ↔ m = .val (.list k.sort l2)) (x : Elem) :
    (collC c k φ ψ).interpret (stdI_T c T) e x ↔ x = .val (.list k.sort (l1 ++ l2)) := by
  unfold collC symP
  rw [interp_symList _ _ [.val (.list k.sort l1), .val (.list k.sort l2)] (.cons hφ (.cons hψ .nil)) x]
  exact coll_symE h hk (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩)) (vs := [.list k.sort l1, .list k.sort l2]) rfl
    (r := .list Srt.list (l1 ++ l2)) (by rw [hkind, builtinColl_list, hook_listConcat_eq])
    (by rw [hkind, builtinColl_list]; rfl)
    ((sortOf_list_iff h hk hkind).mpr fun z hz => by
      rcases List.mem_append.mp hz with hz | hz
      · exact h1 z hz
      · exact h2 z hz) x

end AtT

theorem C_list {e : Valuation Elem} {φ ψ : KoreAML.P} {l1 l2 : List GroundTerm}
    (h1 : ∀ z ∈ l1, c.sortOf z = some k.key) (h2 : ∀ z ∈ l2, c.sortOf z = some k.key)
    (hφ : ∀ m, φ.interpret (stdI c) e m ↔ m = .val (.list k.sort l1))
    (hψ : ∀ m, ψ.interpret (stdI c) e m ↔ m = .val (.list k.sort l2)) (x : Elem) :
    (collC c k φ ψ).interpret (stdI c) e x ↔ x = .val (.list k.sort (l1 ++ l2)) :=
  AtT.C_list (c := c) (T := StepM c) (e := e) (φ := φ) (ψ := ψ) (l1 := l1) (l2 := l2) (h1 := h1) (h2 := h2) (hφ := hφ) (hψ := hψ) (x := x) (h := h) (hk := hk) (hkind := hkind)

/-! ## The list axioms -/

namespace AtT

variable {T : GroundTerm → GroundTerm → Prop}

theorem sat_listUnitSplit : stdI_T c T ⊧ᴵ listUnitSplitAx c k := by
  obtain ⟨hsS, -, -⟩ := h.collSorts hk
  intro e m
  unfold listUnitSplitAx
  dsimp only
  refine guarded_intro fun hg => ?_
  obtain ⟨w1, h1, hw1⟩ := guard_val (T := T) h.namesK hsS (hg _ (List.mem_cons_self ..))
  obtain ⟨w2, h2, hw2⟩ := guard_val (T := T) h.namesK hsS (hg _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
  obtain ⟨l1, rfl, hl1⟩ := list_val h hk hkind hw1
  obtain ⟨l2, rfl, hl2⟩ := list_val h hk hkind hw2
  rw [interpret_impl, defined_app]
  rintro ⟨x, hx⟩
  rw [interpret_conj, U_list h hk hkind, C_list h hk hkind hl1 hl2
    (fun m => by rw [KoreAML.interp_evar, h1]) (fun m => by rw [KoreAML.interp_evar, h2])] at hx
  obtain ⟨rfl, hx⟩ := hx
  simp only [Elem.val.injEq, GroundTerm.list.injEq, true_and, List.singleton_append] at hx
  obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.mp hx.symm
  rw [interpret_conj]
  exact ⟨evar_eq_iff h1 (U_list h hk hkind e) m, evar_eq_iff h2 (U_list h hk hkind e) m⟩

end AtT

theorem sat_listUnitSplit : stdI c ⊧ᴵ listUnitSplitAx c k :=
  AtT.sat_listUnitSplit (c := c) (T := StepM c) (h := h) (hk := hk) (hkind := hkind)

namespace AtT

variable {T : GroundTerm → GroundTerm → Prop}

theorem sat_listElemNotUnit : stdI_T c T ⊧ᴵ listElemNotUnitAx c k := by
  obtain ⟨-, hsK, -⟩ := h.collSorts hk
  intro e m
  unfold listElemNotUnitAx
  dsimp only
  refine guarded_intro fun hg => ?_
  obtain ⟨a, ha, hwa⟩ := guard_val (T := T) h.namesK hsK (hg _ (List.mem_cons_self ..))
  rw [interpret_neg, defined_app]
  rintro ⟨x, hx⟩
  rw [interpret_conj, U_list h hk hkind, I_list h hk hkind hwa ha] at hx
  obtain ⟨rfl, hx⟩ := hx
  cases hx

end AtT

theorem sat_listElemNotUnit : stdI c ⊧ᴵ listElemNotUnitAx c k :=
  AtT.sat_listElemNotUnit (c := c) (T := StepM c) (h := h) (hk := hk) (hkind := hkind)

namespace AtT

variable {T : GroundTerm → GroundTerm → Prop}

theorem sat_listElemAtom : stdI_T c T ⊧ᴵ listElemAtomAx c k := by
  obtain ⟨hsS, hsK, -⟩ := h.collSorts hk
  intro e m
  unfold listElemAtomAx
  dsimp only
  refine guarded_intro fun hg => ?_
  obtain ⟨a, ha, hwa⟩ := guard_val (T := T) h.namesK hsK (hg _ (List.mem_cons_self ..))
  obtain ⟨a', ha', hwa'⟩ := guard_val (T := T) h.namesK hsK (hg _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
  obtain ⟨w, hr, hw⟩ := guard_val (T := T) h.namesK hsS
    (hg _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))
  obtain ⟨rs, rfl, hrs⟩ := list_val h hk hkind hw
  rw [interpret_impl, defined_app]
  rintro ⟨x, hx⟩
  rw [interpret_conj, I_list h hk hkind hwa' ha',
    C_list h hk hkind (fun z hz => by rw [List.mem_singleton.mp hz]; exact hwa) hrs
      (I_list h hk hkind hwa ha) (fun m => by rw [KoreAML.interp_evar, hr])] at hx
  obtain ⟨rfl, hx⟩ := hx
  simp only [Elem.val.injEq, GroundTerm.list.injEq, true_and, List.singleton_append] at hx
  obtain ⟨rfl, rfl⟩ := List.cons.inj hx
  rw [interpret_conj]
  exact ⟨evar_eq_iff ha (fun m => by rw [KoreAML.interp_evar, ha']) m, evar_eq_iff hr (U_list h hk hkind e) m⟩

end AtT

theorem sat_listElemAtom : stdI c ⊧ᴵ listElemAtomAx c k :=
  AtT.sat_listElemAtom (c := c) (T := StepM c) (h := h) (hk := hk) (hkind := hkind)

namespace AtT

variable {T : GroundTerm → GroundTerm → Prop}

theorem sat_listElemAtomBack : stdI_T c T ⊧ᴵ listElemAtomBackAx c k := by
  obtain ⟨hsS, hsK, -⟩ := h.collSorts hk
  intro e m
  unfold listElemAtomBackAx
  dsimp only
  refine guarded_intro fun hg => ?_
  obtain ⟨a, ha, hwa⟩ := guard_val (T := T) h.namesK hsK (hg _ (List.mem_cons_self ..))
  obtain ⟨a', ha', hwa'⟩ := guard_val (T := T) h.namesK hsK (hg _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
  obtain ⟨w, hr, hw⟩ := guard_val (T := T) h.namesK hsS
    (hg _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))
  obtain ⟨rs, rfl, hrs⟩ := list_val h hk hkind hw
  rw [interpret_impl, defined_app]
  rintro ⟨x, hx⟩
  rw [interpret_conj, I_list h hk hkind hwa' ha',
    C_list h hk hkind hrs (fun z hz => by rw [List.mem_singleton.mp hz]; exact hwa)
      (fun m => by rw [KoreAML.interp_evar, hr]) (I_list h hk hkind hwa ha)] at hx
  obtain ⟨rfl, hx⟩ := hx
  simp only [Elem.val.injEq, GroundTerm.list.injEq, true_and, List.singleton_append] at hx
  have heq := hx
  have hrs0 : rs = [] ∧ a' = a := by
    cases rs with
    | nil => exact ⟨rfl, (List.cons.inj heq).1⟩
    | cons z rs' =>
      have := (List.cons.inj heq).2
      exact absurd this.symm (by simp)
  obtain ⟨rfl, rfl⟩ := hrs0
  rw [interpret_conj]
  exact ⟨evar_eq_iff ha (fun m => by rw [KoreAML.interp_evar, ha']) m, evar_eq_iff hr (U_list h hk hkind e) m⟩

end AtT

theorem sat_listElemAtomBack : stdI c ⊧ᴵ listElemAtomBackAx c k :=
  AtT.sat_listElemAtomBack (c := c) (T := StepM c) (h := h) (hk := hk) (hkind := hkind)

namespace AtT

variable {T : GroundTerm → GroundTerm → Prop}

theorem sat_listDecomp : stdI_T c T ⊧ᴵ listDecompAx c k := by
  obtain ⟨hsS, hsK, -⟩ := h.collSorts hk
  intro e m
  unfold listDecompAx
  dsimp only
  refine guarded_intro fun hg => ?_
  have g := fun i (hi : i < 4) => hg _ (List.getElem_mem (l := [(⟨1⟩ : EVar) ∈∈ inSort c k.key,
    (⟨2⟩ : EVar) ∈∈ inSort c k.sort, (⟨3⟩ : EVar) ∈∈ inSort c k.sort, (⟨4⟩ : EVar) ∈∈ inSort c k.sort]) hi)
  obtain ⟨a, ha, hwa⟩ := guard_val (T := T) h.namesK hsK (g 0 (by decide))
  obtain ⟨wr, hr, hwr⟩ := guard_val (T := T) h.namesK hsS (g 1 (by decide))
  obtain ⟨w1, h1, hw1⟩ := guard_val (T := T) h.namesK hsS (g 2 (by decide))
  obtain ⟨w2, h2, hw2⟩ := guard_val (T := T) h.namesK hsS (g 3 (by decide))
  obtain ⟨rs, rfl, hrs⟩ := list_val h hk hkind hwr
  obtain ⟨l1, rfl, hl1⟩ := list_val h hk hkind hw1
  obtain ⟨l2, rfl, hl2⟩ := list_val h hk hkind hw2
  have ha1 : ∀ z ∈ [a], c.sortOf z = some k.key := fun z hz => by rw [List.mem_singleton.mp hz]; exact hwa
  rw [interpret_impl, defined_app]
  rintro ⟨x, hx⟩
  rw [interpret_conj, C_list h hk hkind ha1 hrs (I_list h hk hkind hwa ha) (fun m => by rw [KoreAML.interp_evar, hr]),
    C_list h hk hkind hl1 hl2 (fun m => by rw [KoreAML.interp_evar, h1])
      (fun m => by rw [KoreAML.interp_evar, h2])] at hx
  obtain ⟨rfl, hx⟩ := hx
  simp only [Elem.val.injEq, GroundTerm.list.injEq, true_and, List.singleton_append] at hx
  have heq := hx
  rw [interpret_disj]
  cases l1 with
  | nil =>
    left
    simp only [List.nil_append] at heq
    subst heq
    rw [interpret_conj]
    exact ⟨evar_eq_iff h1 (U_list h hk hkind e) m,
      evar_eq_iff h2 (C_list h hk hkind ha1 hrs (I_list h hk hkind hwa ha) (fun m => by rw [KoreAML.interp_evar, hr])) m⟩
  | cons z l1' =>
    right
    obtain ⟨rfl, rfl⟩ := List.cons.inj heq
    have hl1' : ∀ z ∈ l1', c.sortOf z = some k.key := fun z hz => hl1 z (List.mem_cons_of_mem _ hz)
    rw [KoreAML.interp_sExists]
    refine ⟨.val (.list k.sort l1'), ?_, ?_⟩
    · rw [KoreAML.interp_member defOK_std]
      simp only [Function.update_same]
      exact (inhOf_sort h.namesK hsS _ _).mpr ((sortOf_list_iff h hk hkind).mpr hl1')
    · have hy : ∀ m, (Pattern.evar (⟨5⟩ : EVar) : KoreAML.P).interpret (stdI_T c T)
          ⟨Function.update e.evalEvar ⟨5⟩ (.val (.list k.sort l1')), e.evalSvar⟩ m ↔
            m = .val (.list k.sort l1') := fun m => by
        rw [KoreAML.interp_evar]; simp only [Function.update_same]
      have hval : ∀ i, i ≠ 5 →
          (⟨Function.update e.evalEvar ⟨5⟩ (.val (.list k.sort l1')), e.evalSvar⟩ : Valuation Elem).evalEvar ⟨i⟩ =
            e.evalEvar ⟨i⟩ := fun i hi => upd_ne hi _
      rw [interpret_conj]
      constructor
      · exact evar_eq_iff ((hval 3 (by decide)).trans h1)
          (C_list h hk hkind ha1 hl1' (I_list h hk hkind hwa ((hval 1 (by decide)).trans ha)) hy) m
      · exact evar_eq_iff ((hval 2 (by decide)).trans hr)
          (C_list h hk hkind hl1' hl2 hy (fun m => by rw [KoreAML.interp_evar, (hval 4 (by decide)).trans h2])) m

end AtT

theorem sat_listDecomp : stdI c ⊧ᴵ listDecompAx c k :=
  AtT.sat_listDecomp (c := c) (T := StepM c) (h := h) (hk := hk) (hkind := hkind)

end

/-! ## Readings in a set collection -/

/-- `_Set_`'s value: the union of two sets with no member in common. -/
theorem concatS_iff {a b u : List GroundTerm} :
    concatS a b = some u ↔ (∀ x ∈ a, x ∉ b) ∧ unionS a b = u := by
  have hall : (a.all fun x => !memS x b) = true ↔ ∀ x ∈ a, x ∉ b := by
    rw [List.all_eq_true]
    refine forall_congr' fun x => imp_congr_right fun _ => ?_
    rw [Bool.not_eq_true', Bool.eq_false_iff, ne_eq, Set.memS_iff]
  unfold concatS
  split
  · rename_i hd
    simp only [Option.some.injEq]
    exact ⟨fun h => ⟨hall.mp hd, h⟩, fun h => h.2⟩
  · rename_i hd
    exact ⟨fun h => (nomatch h), fun h => absurd (hall.mpr h.1) hd⟩

theorem concatS_mem {a b u : List GroundTerm} (h : concatS a b = some u) (x : GroundTerm) :
    x ∈ u ↔ x ∈ a ∨ x ∈ b := by
  rw [← (concatS_iff.mp h).2, Set.mem_union]

/-- A set whose members are those of two disjoint canonical sets is their `_Set_`. -/
theorem concatS_of {a b u : List GroundTerm} (hb : Set.Canon b) (hu : Set.Canon u) (hd : ∀ x ∈ a, x ∉ b)
    (hm : ∀ x, x ∈ u ↔ x ∈ a ∨ x ∈ b) : concatS a b = some u :=
  concatS_iff.mpr ⟨hd, Set.ext (Set.union_canon hb) hu fun x => by rw [Set.mem_union, hm]⟩

theorem concatS_nil {a b : List GroundTerm} (h : concatS a b = some []) : a = [] ∧ b = [] := by
  have hm := concatS_mem h
  constructor
  · exact List.eq_nil_iff_forall_not_mem.mpr fun e he => by simpa using (hm e).mpr (.inl he)
  · exact List.eq_nil_iff_forall_not_mem.mpr fun e he => by simpa using (hm e).mpr (.inr he)

/-- A one-member set is a `_Set_` with its member only: `{a} ⊎ rs = {a'}` makes `a = a'` and `rs`
empty. -/
theorem concatS_single {a a' : GroundTerm} {rs : List GroundTerm} (h : concatS [a] rs = some [a']) :
    a = a' ∧ rs = [] := by
  have hm := concatS_mem h
  have hd := (concatS_iff.mp h).1 a (List.mem_singleton_self _)
  have ha : a = a' := by simpa using (hm a).mpr (.inl (List.mem_singleton_self _))
  refine ⟨ha, List.eq_nil_iff_forall_not_mem.mpr fun e he => ?_⟩
  have he' : e = a' := by simpa using (hm e).mpr (.inr he)
  rw [he', ← ha] at he
  exact hd he

/-- The members of a set but `a`. -/
def dropS (a : GroundTerm) (s : List GroundTerm) : List GroundTerm := s.filter fun x => !(GroundTerm.cmp x a == .eq)

theorem mem_dropS {a x : GroundTerm} {s : List GroundTerm} : x ∈ dropS a s ↔ x ∈ s ∧ x ≠ a := by
  simp [dropS, cmp_eq_iff]

/-- **A member of a `_Set_` is a member of one part.** If `{a} ⊎ rs` and `s₁ ⊎ s₂` are one set,
the part holding `a` is `{a} ⊎ ys` for `ys` that part without `a`, and `rs` is `ys` united with
the other part. -/
theorem set_decomp {a : GroundTerm} {rs s1 s2 T : List GroundTerm} (hrs : Set.Canon rs) (h1s : Set.Canon s1)
    (h2s : Set.Canon s2) (hl : concatS [a] rs = some T) (hr : concatS s1 s2 = some T) :
    (concatS [a] (dropS a s1) = some s1 ∧ concatS (dropS a s1) s2 = some rs) ∨
      (concatS [a] (dropS a s2) = some s2 ∧ concatS s1 (dropS a s2) = some rs) := by
  have hlm := concatS_mem hl
  have hrm := concatS_mem hr
  have hla := (concatS_iff.mp hl).1 a (List.mem_singleton_self _)
  have hrd := (concatS_iff.mp hr).1
  have haT : a ∈ T := (hlm a).mpr (.inl (List.mem_singleton_self _))
  have hT : ∀ x, x ∈ T → x ≠ a → x ∈ rs := fun x hx hxa => by
    rcases (hlm x).mp hx with h | h
    · exact absurd (List.mem_singleton.mp h) hxa
    · exact h
  have hpart : ∀ s, Set.Canon s → a ∈ s → concatS [a] (dropS a s) = some s := fun s hs has =>
    concatS_of (Set.filter_canon hs _) hs (fun x hx hxd => by
      rw [List.mem_singleton.mp hx] at hxd; exact (mem_dropS.mp hxd).2 rfl) fun x => by
      rw [List.mem_singleton, mem_dropS]
      by_cases hxa : x = a
      · subst hxa; simp [has]
      · simp [hxa]
  rcases (hrm a).mp haT with ha1 | ha2
  · left
    refine ⟨hpart s1 h1s ha1, concatS_of h2s hrs (fun x hx hx2 => hrd x (mem_dropS.mp hx).1 hx2) fun x => ?_⟩
    rw [mem_dropS]
    constructor
    · intro hx
      have hxa : x ≠ a := fun e => hla (e ▸ hx)
      rcases (hrm x).mp ((hlm x).mpr (.inr hx)) with h | h
      · exact .inl ⟨h, hxa⟩
      · exact .inr h
    · rintro (⟨hx, hxa⟩ | hx)
      · exact hT x ((hrm x).mpr (.inl hx)) hxa
      · exact hT x ((hrm x).mpr (.inr hx)) fun e => hrd a ha1 (e ▸ hx)
  · right
    refine ⟨hpart s2 h2s ha2, concatS_of (Set.filter_canon h2s _) hrs
      (fun x hx hx2 => hrd x hx (mem_dropS.mp hx2).1) fun x => ?_⟩
    rw [mem_dropS]
    constructor
    · intro hx
      have hxa : x ≠ a := fun e => hla (e ▸ hx)
      rcases (hrm x).mp ((hlm x).mpr (.inr hx)) with h | h
      · exact .inl h
      · exact .inr ⟨h, hxa⟩
    · rintro (hx | ⟨hx, hxa⟩)
      · exact hT x ((hrm x).mpr (.inl hx)) fun e => hrd a (e ▸ hx) ha2
      · exact hT x ((hrm x).mpr (.inr hx)) hxa

section
variable (h : HypModelCore c) {k : CollSig} (hk : k ∈ c.allColls) (hkind : k.kind = .set)
include h hk hkind

theorem sortOf_set_iff {l : List GroundTerm} :
    c.sortOf (.set k.sort l) = some k.sort ↔ elemsSorted l = true ∧ ∀ z ∈ l, c.sortOf z = some k.key := by
  have hev : elemsVal k l = .set k.sort l := by unfold elemsVal; rw [hkind]
  rw [← hev, sortOf_elems_iff (h.collOf_self hk) (.inl hkind)]
  constructor
  · exact fun h => ⟨h.1 hkind, h.2⟩
  · intro h2; exact ⟨fun _ => h2.1, h2.2⟩

theorem set_val {w : GroundTerm} (hw : c.sortOf w = some k.sort) :
    ∃ l, w = .set k.sort l ∧ elemsSorted l = true ∧ ∀ z ∈ l, c.sortOf z = some k.key := by
  have hco := h.collOf_self hk
  rcases h.coll_shape' hco (collSortsOK_mem h.collSortsOK hk) hw with
    ⟨h2, -⟩ | ⟨-, l, rfl⟩ | ⟨h2, -⟩
  · rcases h2 with h2 | h2 <;> (rw [hkind] at h2; cases h2)
  · exact ⟨l, rfl, (sortOf_set_iff h hk hkind).mp hw⟩
  · rw [hkind] at h2; cases h2

namespace AtT

variable {T : GroundTerm → GroundTerm → Prop}

theorem U_set (e : Valuation Elem) (x : Elem) :
    (collU c k).interpret (stdI_T c T) e x ↔ x = .val (.set k.sort []) := by
  have := coll_symE (T := T) h hk (Or.inl ⟨rfl, rfl, rfl⟩) (vs := []) rfl (r := .set Srt.set [])
    (by rw [hkind, builtinColl_set, hook_setUnit_eq]) (by rw [hkind, builtinColl_set]; rfl)
    ((sortOf_set_iff h hk hkind).mpr ⟨rfl, fun _ h => nomatch h⟩) x
  refine Iff.trans ?_ this
  unfold collU symP SymE
  constructor
  · intro hx; exact ⟨x, hx, rfl⟩
  · rintro ⟨a, ha, hx⟩; have : x = a := hx; subst this; exact ha

end AtT

theorem U_set (e : Valuation Elem) (x : Elem) :
    (collU c k).interpret (stdI c) e x ↔ x = .val (.set k.sort []) :=
  AtT.U_set (c := c) (T := StepM c) (e := e) (x := x) (h := h) (hk := hk) (hkind := hkind)

namespace AtT

variable {T : GroundTerm → GroundTerm → Prop}

theorem I_set {e : Valuation Elem} {A : EVar} {a : GroundTerm} (ha : c.sortOf a = some k.key)
    (hA : e.evalEvar A = .val a) (x : Elem) :
    (collI c k (.evar A)).interpret (stdI_T c T) e x ↔ x = .val (.set k.sort [a]) := by
  unfold collI symP
  rw [interp_symList _ _ [.val a] (.cons (fun m => by rw [KoreAML.interp_evar, hA]) .nil) x]
  exact coll_symE h hk (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)) (vs := [a]) (elemArgs_length' (.inl hkind)).symm
    (r := .set Srt.set [a]) (by rw [hkind, builtinColl_set, hook_setElem_eq])
    (by rw [hkind, builtinColl_set]; rfl)
    ((sortOf_set_iff h hk hkind).mpr ⟨rfl, fun z hz => (List.mem_singleton.mp hz) ▸ ha⟩) x

end AtT

theorem I_set {e : Valuation Elem} {A : EVar} {a : GroundTerm} (ha : c.sortOf a = some k.key)
    (hA : e.evalEvar A = .val a) (x : Elem) :
    (collI c k (.evar A)).interpret (stdI c) e x ↔ x = .val (.set k.sort [a]) :=
  AtT.I_set (c := c) (T := StepM c) (e := e) (A := A) (a := a) (ha := ha) (hA := hA) (x := x) (h := h) (hk := hk) (hkind := hkind)

namespace AtT

variable {T : GroundTerm → GroundTerm → Prop}

theorem C_set {e : Valuation Elem} {φ ψ : KoreAML.P} {l1 l2 : List GroundTerm}
    (h1 : ∀ z ∈ l1, c.sortOf z = some k.key) (hs2 : elemsSorted l2 = true) (h2 : ∀ z ∈ l2, c.sortOf z = some k.key)
    (hφ : ∀ m, φ.interpret (stdI_T c T) e m ↔ m = .val (.set k.sort l1))
    (hψ : ∀ m, ψ.interpret (stdI_T c T) e m ↔ m = .val (.set k.sort l2)) (x : Elem) :
    (collC c k φ ψ).interpret (stdI_T c T) e x ↔ ∃ u, concatS l1 l2 = some u ∧ x = .val (.set k.sort u) := by
  obtain ⟨kf, hkf, hkfn, hkfa, hres⟩ := coll_sym h hk (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩))
  unfold collC symP
  rw [interp_symList _ _ [.val (.set k.sort l1), .val (.set k.sort l2)] (.cons hφ (.cons hψ .nil)) x,
    show [Elem.val (.set k.sort l1), Elem.val (.set k.sort l2)] = [GroundTerm.set k.sort l1, .set k.sort l2].map Elem.val
      from rfl, ← hkfn, symE_vals h.namesK hkf (by rw [hkfa]; rfl)]
  have hhook : hook (builtinColl k.kind).concat [.set k.sort l1, .set k.sort l2] =
      some ((concatS l1 l2).map (GroundTerm.set Srt.set)) := by
    rw [hkind, builtinColl_set, hook_setConcat_eq]
  have hsr : ∀ u, concatS l1 l2 = some u → c.sortOf ((GroundTerm.set Srt.set u).withSort k.sort) = some k.sort :=
    fun u hu => by
      rw [← (concatS_iff.mp hu).2]
      exact (sortOf_set_iff h hk hkind).mpr ⟨elemsSorted_iff.mpr (unionS_sorted (elemsSorted_iff.mp hs2)),
        fun z hz => by
          rcases unionS_mem hz with hz | hz
          · exact h1 z hz
          · exact h2 z hz⟩
  constructor
  · intro hr
    obtain ⟨v, hv⟩ := coll_sym_inv h hk (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩))
      (by rw [hkind]; exact silentKey_of_mem rfl) hkfn hr
    have hv0 := hv
    rw [hhook] at hv0
    obtain ⟨u, hu, rfl⟩ := Option.map_eq_some_iff.mp (Option.some.inj hv0)
    exact ⟨u, hu, (hres hv (by rw [hkind, builtinColl_set]; rfl) (hsr u hu) x).mp hr⟩
  · rintro ⟨u, hu, rfl⟩
    have hv : hook (builtinColl k.kind).concat [.set k.sort l1, .set k.sort l2] = some (some (.set Srt.set u)) := by
      rw [hhook, hu]; rfl
    exact (hres hv (by rw [hkind, builtinColl_set]; rfl) (hsr u hu) _).mpr rfl

end AtT

theorem C_set {e : Valuation Elem} {φ ψ : KoreAML.P} {l1 l2 : List GroundTerm}
    (h1 : ∀ z ∈ l1, c.sortOf z = some k.key) (hs2 : elemsSorted l2 = true) (h2 : ∀ z ∈ l2, c.sortOf z = some k.key)
    (hφ : ∀ m, φ.interpret (stdI c) e m ↔ m = .val (.set k.sort l1))
    (hψ : ∀ m, ψ.interpret (stdI c) e m ↔ m = .val (.set k.sort l2)) (x : Elem) :
    (collC c k φ ψ).interpret (stdI c) e x ↔ ∃ u, concatS l1 l2 = some u ∧ x = .val (.set k.sort u) :=
  AtT.C_set (c := c) (T := StepM c) (e := e) (φ := φ) (ψ := ψ) (l1 := l1) (l2 := l2) (h1 := h1) (hs2 := hs2) (h2 := h2) (hφ := hφ) (hψ := hψ) (x := x) (h := h) (hk := hk) (hkind := hkind)

/-! ## The set axioms -/

namespace AtT

variable {T : GroundTerm → GroundTerm → Prop}

theorem sat_setUnitSplit : stdI_T c T ⊧ᴵ setUnitSplitAx c k := by
  obtain ⟨hsS, -, -⟩ := h.collSorts hk
  intro e m
  unfold setUnitSplitAx
  dsimp only
  refine guarded_intro fun hg => ?_
  obtain ⟨w1, h1, hw1⟩ := guard_val (T := T) h.namesK hsS (hg _ (List.mem_cons_self ..))
  obtain ⟨w2, h2, hw2⟩ := guard_val (T := T) h.namesK hsS (hg _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
  obtain ⟨l1, rfl, -, he1⟩ := set_val h hk hkind hw1
  obtain ⟨l2, rfl, hs2, he2⟩ := set_val h hk hkind hw2
  rw [interpret_impl, defined_app]
  rintro ⟨x, hx⟩
  rw [interpret_conj, U_set h hk hkind, C_set h hk hkind he1 hs2 he2
    (fun m => by rw [KoreAML.interp_evar, h1]) (fun m => by rw [KoreAML.interp_evar, h2])] at hx
  obtain ⟨rfl, u, hu, hx⟩ := hx
  cases hx
  obtain ⟨rfl, rfl⟩ := concatS_nil hu
  rw [interpret_conj]
  exact ⟨evar_eq_iff h1 (U_set h hk hkind e) m, evar_eq_iff h2 (U_set h hk hkind e) m⟩

end AtT

theorem sat_setUnitSplit : stdI c ⊧ᴵ setUnitSplitAx c k :=
  AtT.sat_setUnitSplit (c := c) (T := StepM c) (h := h) (hk := hk) (hkind := hkind)

namespace AtT

variable {T : GroundTerm → GroundTerm → Prop}

theorem sat_setElemNotUnit : stdI_T c T ⊧ᴵ setElemNotUnitAx c k := by
  obtain ⟨-, hsK, -⟩ := h.collSorts hk
  intro e m
  unfold setElemNotUnitAx
  dsimp only
  refine guarded_intro fun hg => ?_
  obtain ⟨a, ha, hwa⟩ := guard_val (T := T) h.namesK hsK (hg _ (List.mem_cons_self ..))
  rw [interpret_neg, defined_app]
  rintro ⟨x, hx⟩
  rw [interpret_conj, U_set h hk hkind, I_set h hk hkind hwa ha] at hx
  obtain ⟨rfl, hx⟩ := hx
  cases hx

end AtT

theorem sat_setElemNotUnit : stdI c ⊧ᴵ setElemNotUnitAx c k :=
  AtT.sat_setElemNotUnit (c := c) (T := StepM c) (h := h) (hk := hk) (hkind := hkind)

namespace AtT

variable {T : GroundTerm → GroundTerm → Prop}

theorem sat_setElemAtom : stdI_T c T ⊧ᴵ setElemAtomAx c k := by
  obtain ⟨hsS, hsK, -⟩ := h.collSorts hk
  intro e m
  unfold setElemAtomAx
  dsimp only
  refine guarded_intro fun hg => ?_
  obtain ⟨a, ha, hwa⟩ := guard_val (T := T) h.namesK hsK (hg _ (List.mem_cons_self ..))
  obtain ⟨a', ha', hwa'⟩ := guard_val (T := T) h.namesK hsK (hg _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
  obtain ⟨w, hr, hw⟩ := guard_val (T := T) h.namesK hsS
    (hg _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))
  obtain ⟨rs, rfl, hrso, hrs⟩ := set_val h hk hkind hw
  rw [interpret_impl, defined_app]
  rintro ⟨x, hx⟩
  rw [interpret_conj, I_set h hk hkind hwa' ha',
    C_set h hk hkind (fun z hz => by rw [List.mem_singleton.mp hz]; exact hwa) hrso hrs
      (I_set h hk hkind hwa ha) (fun m => by rw [KoreAML.interp_evar, hr])] at hx
  obtain ⟨rfl, u, hu, hx⟩ := hx
  simp only [Elem.val.injEq, GroundTerm.set.injEq, true_and] at hx
  subst hx
  obtain ⟨rfl, rfl⟩ := concatS_single hu
  rw [interpret_conj]
  exact ⟨evar_eq_iff ha (fun m => by rw [KoreAML.interp_evar, ha']) m, evar_eq_iff hr (U_set h hk hkind e) m⟩

end AtT

theorem sat_setElemAtom : stdI c ⊧ᴵ setElemAtomAx c k :=
  AtT.sat_setElemAtom (c := c) (T := StepM c) (h := h) (hk := hk) (hkind := hkind)

namespace AtT

variable {T : GroundTerm → GroundTerm → Prop}

theorem sat_setDecomp : stdI_T c T ⊧ᴵ setDecompAx c k := by
  obtain ⟨hsS, hsK, -⟩ := h.collSorts hk
  intro e m
  unfold setDecompAx
  dsimp only
  refine guarded_intro fun hg => ?_
  have g := fun i (hi : i < 4) => hg _ (List.getElem_mem (l := [(⟨1⟩ : EVar) ∈∈ inSort c k.key,
    (⟨2⟩ : EVar) ∈∈ inSort c k.sort, (⟨3⟩ : EVar) ∈∈ inSort c k.sort, (⟨4⟩ : EVar) ∈∈ inSort c k.sort]) hi)
  obtain ⟨a, ha, hwa⟩ := guard_val (T := T) h.namesK hsK (g 0 (by decide))
  obtain ⟨wr, hr, hwr⟩ := guard_val (T := T) h.namesK hsS (g 1 (by decide))
  obtain ⟨w1, h1, hw1⟩ := guard_val (T := T) h.namesK hsS (g 2 (by decide))
  obtain ⟨w2, h2, hw2⟩ := guard_val (T := T) h.namesK hsS (g 3 (by decide))
  obtain ⟨rs, rfl, hrs, hre⟩ := set_val h hk hkind hwr
  obtain ⟨s1, rfl, hs1, he1⟩ := set_val h hk hkind hw1
  obtain ⟨s2, rfl, hs2, he2⟩ := set_val h hk hkind hw2
  have ha1 : ∀ z ∈ [a], c.sortOf z = some k.key := fun z hz => by rw [List.mem_singleton.mp hz]; exact hwa
  rw [interpret_impl, defined_app]
  rintro ⟨x, hx⟩
  rw [interpret_conj, C_set h hk hkind ha1 hrs hre (I_set h hk hkind hwa ha)
      (fun m => by rw [KoreAML.interp_evar, hr]),
    C_set h hk hkind he1 hs2 he2 (fun m => by rw [KoreAML.interp_evar, h1])
      (fun m => by rw [KoreAML.interp_evar, h2])] at hx
  obtain ⟨⟨u, hu, rfl⟩, u', hu', hx⟩ := hx
  cases hx
  have hdrop : ∀ s : List GroundTerm, elemsSorted s = true → (∀ z ∈ s, c.sortOf z = some k.key) →
      elemsSorted (dropS a s) = true ∧ ∀ z ∈ dropS a s, c.sortOf z = some k.key := fun s hs he =>
    ⟨Set.filter_canon hs _, fun z hz => he z (mem_dropS.mp hz).1⟩
  have hsy : ∀ ys : List GroundTerm, elemsSorted ys = true → (∀ z ∈ ys, c.sortOf z = some k.key) →
      c.sortOf (.set k.sort ys) = some k.sort := fun ys h1 h2 => (sortOf_set_iff h hk hkind).mpr ⟨h1, h2⟩
  -- the valuation with `y` (index 5) set to the element of `ys`
  have hval : ∀ ys : List GroundTerm, ∀ i, i ≠ 5 →
      (⟨Function.update e.evalEvar ⟨5⟩ (.val (.set k.sort ys)), e.evalSvar⟩ : Valuation Elem).evalEvar ⟨i⟩ =
        e.evalEvar ⟨i⟩ := fun ys i hi => upd_ne hi _
  rw [interpret_disj]
  rcases set_decomp hrs hs1 hs2 hu hu' with ⟨hl, hrr⟩ | ⟨hl, hrr⟩
  · left
    obtain ⟨hys, hye⟩ := hdrop s1 hs1 he1
    rw [KoreAML.interp_sExists]
    refine ⟨.val (.set k.sort (dropS a s1)), ?_, ?_⟩
    · rw [KoreAML.interp_member defOK_std]
      simp only [Function.update_same]
      exact (inhOf_sort h.namesK hsS _ _).mpr (hsy _ hys hye)
    · have hy : ∀ m, (Pattern.evar (⟨5⟩ : EVar) : KoreAML.P).interpret (stdI_T c T)
          ⟨Function.update e.evalEvar ⟨5⟩ (.val (.set k.sort (dropS a s1))), e.evalSvar⟩ m ↔
            m = .val (.set k.sort (dropS a s1)) := fun m => by
        rw [KoreAML.interp_evar]; simp only [Function.update_same]
      rw [interpret_conj]
      constructor
      · refine evar_eq_iff ((hval _ 3 (by decide)).trans h1) (fun m => ?_) m
        rw [C_set h hk hkind ha1 hys hye (I_set h hk hkind hwa ((hval _ 1 (by decide)).trans ha)) hy]
        constructor
        · rintro ⟨u0, hu0, rfl⟩; rw [hl] at hu0; cases hu0; rfl
        · rintro rfl; exact ⟨_, hl, rfl⟩
      · refine evar_eq_iff ((hval _ 2 (by decide)).trans hr) (fun m => ?_) m
        rw [C_set h hk hkind hye hs2 he2 hy
          (fun m => by rw [KoreAML.interp_evar, (hval _ 4 (by decide)).trans h2])]
        constructor
        · rintro ⟨u0, hu0, rfl⟩; rw [hrr] at hu0; cases hu0; rfl
        · rintro rfl; exact ⟨_, hrr, rfl⟩
  · right
    obtain ⟨hys, hye⟩ := hdrop s2 hs2 he2
    rw [KoreAML.interp_sExists]
    refine ⟨.val (.set k.sort (dropS a s2)), ?_, ?_⟩
    · rw [KoreAML.interp_member defOK_std]
      simp only [Function.update_same]
      exact (inhOf_sort h.namesK hsS _ _).mpr (hsy _ hys hye)
    · have hy : ∀ m, (Pattern.evar (⟨5⟩ : EVar) : KoreAML.P).interpret (stdI_T c T)
          ⟨Function.update e.evalEvar ⟨5⟩ (.val (.set k.sort (dropS a s2))), e.evalSvar⟩ m ↔
            m = .val (.set k.sort (dropS a s2)) := fun m => by
        rw [KoreAML.interp_evar]; simp only [Function.update_same]
      rw [interpret_conj]
      constructor
      · refine evar_eq_iff ((hval _ 4 (by decide)).trans h2) (fun m => ?_) m
        rw [C_set h hk hkind ha1 hys hye (I_set h hk hkind hwa ((hval _ 1 (by decide)).trans ha)) hy]
        constructor
        · rintro ⟨u0, hu0, rfl⟩; rw [hl] at hu0; cases hu0; rfl
        · rintro rfl; exact ⟨_, hl, rfl⟩
      · refine evar_eq_iff ((hval _ 2 (by decide)).trans hr) (fun m => ?_) m
        rw [C_set h hk hkind he1 hys hye
          (fun m => by rw [KoreAML.interp_evar, (hval _ 3 (by decide)).trans h1]) hy]
        constructor
        · rintro ⟨u0, hu0, rfl⟩; rw [hrr] at hu0; cases hu0; rfl
        · rintro rfl; exact ⟨_, hrr, rfl⟩

end AtT

theorem sat_setDecomp : stdI c ⊧ᴵ setDecompAx c k :=
  AtT.sat_setDecomp (c := c) (T := StepM c) (h := h) (hk := hk) (hkind := hkind)

end

namespace AtT

variable {T : GroundTerm → GroundTerm → Prop}

/-- **`SatCollsGoal`**: the value model satisfies the collections' axioms. -/
theorem satCollsGoal (h : HypModelCore c) : (stdI_T c T ⊧ᴵP ΓColls c) := by
  rintro φ ⟨k, hk, hφ⟩
  unfold collAxioms at hφ
  cases hkind : k.kind with
  | map =>
    rw [hkind] at hφ
    simp only [mapCollAxioms, List.mem_cons, List.not_mem_nil, or_false] at hφ
    rcases hφ with rfl | rfl | rfl | rfl
    · exact sat_mapUnitSplit h hk hkind
    · exact sat_mapElemNotUnit h hk hkind
    · exact sat_mapElemAtom h hk hkind
    · exact sat_mapDecomp h hk hkind
  | set =>
    rw [hkind] at hφ
    simp only [setCollAxioms, List.mem_cons, List.not_mem_nil, or_false] at hφ
    rcases hφ with rfl | rfl | rfl | rfl
    · exact sat_setUnitSplit h hk hkind
    · exact sat_setElemNotUnit h hk hkind
    · exact sat_setElemAtom h hk hkind
    · exact sat_setDecomp h hk hkind
  | list =>
    rw [hkind] at hφ
    simp only [listCollAxioms, List.mem_cons, List.not_mem_nil, or_false] at hφ
    rcases hφ with rfl | rfl | rfl | rfl | rfl
    · exact sat_listUnitSplit h hk hkind
    · exact sat_listElemNotUnit h hk hkind
    · exact sat_listElemAtom h hk hkind
    · exact sat_listElemAtomBack h hk hkind
    · exact sat_listDecomp h hk hkind
  | rangeMap =>
    rw [hkind] at hφ
    exact absurd hφ List.not_mem_nil

end AtT

/-- **`SatCollsGoal`**: the value model satisfies the collections' axioms. -/
theorem satCollsGoal (h : HypModelCore c) : SatCollsGoal c :=
  AtT.satCollsGoal (c := c) (T := StepM c) (h := h)

end Model

end Faithful

end KCore
