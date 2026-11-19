/-
  KCore. The intended model reads every value as itself: `den c v` denotes exactly `{val v}` in
  `stdI c` (`den_val`, the goal `DenGoal`).

  A sort symbol `SortX` denotes the numbered sort named `X`; a symbol of the semantics, applied to
  the elements of values, gives what the symbol gives on those values (`result`); so a constructor
  term denotes itself, an injection of a value that is not one denotes itself (`injNormal`), a
  literal denotes the one literal of its sort with its text (`LitsApart`), and a collection, built
  from its unit by adding its entries one at a time in key order, denotes itself, the union of a
  one-entry collection with a collection of larger keys being the collection of both.
-/
import KcoreSpec.ModelCarrier
import KcoreSpec.OvlLawsFn
import KcoreSpec.FloatLaws
import KcoreSpec.OpenValues

set_option autoImplicit false

namespace KCore

namespace Faithful

namespace Model

open ML

variable {c : Semantics}

/-! ## Lists of values -/

theorem vals_map : ∀ vs : List GroundTerm, vals (vs.map Elem.val) = some vs
  | [] => rfl
  | v :: vs => by simp [vals, vals_map vs]

/-! ## Symbols by name -/

/-- A list of arguments that does not start with a sort: `resolve` reads the name alone. -/
theorem resolve_plain (n : String) (args : List Elem) (h : ∀ s, args.head? ≠ some (.srt s)) :
    resolve c n args = ((kernelSyms c).find? fun k => c.symName k.name == n).map (·, 0) := by
  unfold resolve
  split
  · rename_i s _; exact absurd rfl (h s)
  · rfl

/-- What `instPrefix` finds: a symbol of `kernelSyms` named as an instance of the head at more
sorts than the arguments. -/
theorem instPrefix_spec {n : String} {args : List Elem} (h : instPrefix c n args = true) :
    ∃ k ∈ kernelSyms c, ∃ xs, instDecode? (c.symName k.name) = some (n, xs) ∧ args.length < xs.length ∧
      leadSorts c args.length args = some (xs.take args.length) := by
  obtain ⟨k, hk, hp⟩ := List.any_eq_true.mp h
  refine ⟨k, hk, ?_⟩
  cases hd : instDecode? (c.symName k.name) with
  | none => rw [hd] at hp; cases hp
  | some p =>
    obtain ⟨h', xs⟩ := p
    rw [hd] at hp
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hp
    obtain ⟨⟨rfl, hl⟩, he⟩ := hp
    exact ⟨xs, rfl, hl, he⟩

/-- What `instAt` finds: the symbol's name decodes to the head at the sort names the arguments
begin with. -/
theorem instAt_spec {n : String} {args : List Elem} {k : CtorSig} {p : Nat} (h : instAt c n args k = some p) :
    ∃ xs, instDecode? (c.symName k.name) = some (n, xs) ∧ xs.length = p ∧ leadSorts c p args = some xs := by
  unfold instAt at h
  cases hd : instDecode? (c.symName k.name) with
  | none => rw [hd] at h; cases h
  | some q =>
    obtain ⟨h', xs⟩ := q
    rw [hd] at h
    dsimp only at h
    split at h
    · rename_i hc
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      obtain ⟨rfl, he⟩ := hc
      cases h
      exact ⟨xs, rfl, rfl, he⟩
    · cases h

/-- A list that begins with `m` sorts has their names as `leadSorts`, and at least `m` elements. -/
theorem leadSorts_length : ∀ {m : Nat} {args : List Elem} {xs : List String}, leadSorts c m args = some xs →
    xs.length = m ∧ m ≤ args.length
  | 0, _, _, h => by cases h; exact ⟨rfl, Nat.zero_le _⟩
  | m + 1, [], _, h => by cases h
  | m + 1, .val _ :: _, _, h => by cases h
  | m + 1, .app _ _ :: _, _, h => by cases h
  | m + 1, .srt s :: es, xs, h => by
    simp only [leadSorts, Option.map_eq_some_iff] at h
    obtain ⟨ys, hy, rfl⟩ := h
    have := leadSorts_length hy
    simp only [List.length_cons]
    omega

/-- The sort elements of a list of sorts, before anything, have the sorts' names as `leadSorts`. -/
theorem leadSorts_srts : ∀ (ss : List Srt) (tail : List Elem),
    leadSorts c ss.length (ss.map Elem.srt ++ tail) = some (ss.map c.sortName)
  | [], _ => rfl
  | s :: ss, tail => by
    simp only [List.length_cons, List.map_cons, List.cons_append, leadSorts, leadSorts_srts ss tail, Option.map_some]

/-- A symbol of the semantics is the first one of its name. -/
theorem find_name (hn : NamesApartK c) {k : CtorSig} (hk : k ∈ kernelSyms c) :
    (kernelSyms c).find? (fun k' => c.symName k'.name == c.symName k.name) = some k := by
  cases h : (kernelSyms c).find? (fun k' => c.symName k'.name == c.symName k.name) with
  | none =>
    have := List.find?_eq_none.mp h k hk
    simp at this
  | some k' =>
    have h1 := List.find?_some h
    have h2 := List.mem_of_find?_eq_some h
    rw [hn.1 k' h2 k hk (by simpa using h1)]

theorem resolve_sym (hn : NamesApartK c) {k : CtorSig} (hk : k ∈ kernelSyms c) (args : List Elem)
    (h : ∀ s, args.head? ≠ some (.srt s)) : resolve c (c.symName k.name) args = some (k, 0) := by
  rw [resolve_plain _ _ h, find_name hn hk]; rfl

theorem evalSymb_symbol {n : String} (h : n ≠ "inj") :
    evalSymb c (.symbol n) = match resolve c n [] with
      | some (k, 0) => if k.args = [] then result c k [] else fun x => x = .app (.sym n) []
      | _ => fun x => x = .app (.sym n) [] := by
  rw [evalSymb.eq_6]
  exact evalSymb.match_4.eq_6 _ _ _ _ _ _ _ _ _ _ _ _ _ h


theorem evalSymb_inj (x : Elem) : evalSymb c (.symbol "inj") x ↔ x = .app .inj [] := by
  rw [evalSymb.eq_5]; exact Iff.rfl

/-- A set chosen by a condition, at an element. -/
theorem ite_mem {p : Prop} [h : Decidable p] (a b : Set Elem) (x : Elem) :
    (@ite (Set Elem) p h a b) x ↔ @ite Prop p h (a x) (b x) := by
  cases h <;> exact Iff.rfl

theorem evalSymb_sym (hn : NamesApartK c) {k : CtorSig} (hk : k ∈ kernelSyms c) (x : Elem) :
    evalSymb c (.symbol (c.symName k.name)) x ↔
      if k.args = [] then result c k [] x else x = .app (.sym (c.symName k.name)) [] := by
  rw [evalSymb_symbol (hn.2.1 k hk), resolve_sym hn hk [] (by simp)]
  exact ite_mem _ _ x

theorem symAt_partial {n : String} {args : List Elem} {k : CtorSig} {p : Nat}
    (hr : resolve c n args = some (k, p)) (hl : args.length < p + k.args.length) (x : Elem) :
    symAt c n args x ↔ x = .app (.sym n) args := by
  unfold symAt
  rw [hr]
  refine (ite_mem _ _ x).trans ?_
  rw [if_pos hl]

theorem symAt_full {n : String} {args : List Elem} {k : CtorSig} {p : Nat} {vs : List GroundTerm}
    (hr : resolve c n args = some (k, p)) (hl : args.length = p + k.args.length)
    (hv : vals (args.drop p) = some vs) (x : Elem) :
    symAt c n args x ↔ result c k vs x := by
  unfold symAt
  rw [hr]
  refine (ite_mem _ _ x).trans ?_
  rw [if_neg (by omega)]
  refine (ite_mem _ _ x).trans ?_
  rw [if_pos hl, hv]

/-- No arguments: `resolve` reads the name alone. -/
theorem resolve_nil (n : String) :
    resolve c n [] = ((kernelSyms c).find? fun k => c.symName k.name == n).map (·, 0) :=
  resolve_plain n [] (by simp)

/-- What `symAt` holds: the partial application of the name, or, where a symbol resolves at the
arguments and those after its sort arguments are values, a result of that symbol at them. -/
theorem symAt_cases {n : String} {args : List Elem} {x : Elem} (hx : symAt c n args x) :
    x = .app (.sym n) args ∨
      ∃ k p vs, resolve c n args = some (k, p) ∧ vals (args.drop p) = some vs ∧ result c k vs x := by
  unfold symAt at hx
  cases hr : resolve c n args with
  | none =>
    rw [hr] at hx
    left
    have hx' := (ite_mem _ _ _).mp hx
    split at hx'
    · rename_i ha; rw [ha]; exact hx'
    · have hx2 := (ite_mem _ _ _).mp hx'
      split at hx2
      · exact hx2
      · exact hx2.elim
  | some kp =>
    obtain ⟨k, p⟩ := kp
    rw [hr] at hx
    have hx' := (ite_mem _ _ _).mp hx
    by_cases hl : args.length < p + k.args.length
    · rw [if_pos hl] at hx'; exact .inl hx'
    · rw [if_neg hl] at hx'
      have hx2 := (ite_mem _ _ _).mp hx'
      by_cases hl2 : args.length = p + k.args.length
      · rw [if_pos hl2] at hx2
        cases hv : vals (args.drop p) with
        | none => rw [hv] at hx2; exact hx2.elim
        | some vs => rw [hv] at hx2; exact .inr ⟨k, p, vs, rfl, hv, hx2⟩
      · rw [if_neg hl2] at hx2; exact hx2.elim

/-- Where no symbol resolves at the arguments, `symAt` holds at most the partial application of
the name. -/
theorem symAt_none_app {n : String} {args : List Elem} {x : Elem} (hr : resolve c n args = none)
    (hx : symAt c n args x) : x = .app (.sym n) args := by
  rcases symAt_cases hx with h | ⟨k, p, vs, hr', -⟩
  · exact h
  · rw [hr] at hr'; cases hr'

/-- Where no symbol resolves at arguments, `symAt` holds something there only where the arguments
are sorts, fewer than and the first of the sorts of an instance of the head (`instPrefix`). -/
theorem symAt_none_late {n : String} {args : List Elem} {x : Elem} (hr : resolve c n args = none)
    (ha : args ≠ []) (hx : symAt c n args x) : instPrefix c n args = true := by
  unfold symAt at hx
  rw [hr] at hx
  have hx' := (ite_mem _ _ _).mp hx
  rw [if_neg ha] at hx'
  have hx2 := (ite_mem _ _ _).mp hx'
  split at hx2
  · assumption
  · exact hx2.elim

/-- The head of an instance before all its sort arguments is its partial application. -/
theorem symAt_instPrefix {n : String} {args : List Elem} (hr : resolve c n args = none) (ha : args ≠ [])
    (hp : instPrefix c n args = true) (x : Elem) : symAt c n args x ↔ x = .app (.sym n) args := by
  unfold symAt
  rw [hr]
  show (if args = [] then (fun x => x = Elem.app (.sym n) []) else
    if instPrefix c n args = true then (fun x => x = Elem.app (.sym n) args) else fun _ => False) x ↔ _
  rw [if_neg ha, if_pos hp]

/-- Where no symbol of `kernelSyms` is an instance at the head `n` and no symbol resolves at two
arguments or more, `symAt` holds nothing there. -/
theorem symAt_none_noInst {n : String} {args : List Elem} (hr : resolve c n args = none)
    (hi : ∀ k ∈ kernelSyms c, ∀ xs, instDecode? (c.symName k.name) ≠ some (n, xs))
    (hl : 2 ≤ args.length) (x : Elem) : ¬ symAt c n args x := fun hx => by
  obtain ⟨k, hk, xs, hd, -⟩ := instPrefix_spec (symAt_none_late hr (fun h => by rw [h] at hl; cases hl) hx)
  exact hi k hk xs hd


namespace AtT

variable {T : GroundTerm → GroundTerm → Prop}

/-- A symbol applied to the elements of values, one at a time, from a partial application. -/
theorem appE_sym {n : String} {k : CtorSig}
    (hres : ∀ args : List Elem, (∀ s, args.head? ≠ some (.srt s)) → resolve c n args = some (k, 0)) :
    ∀ (pre rest : List GroundTerm), pre.length < k.args.length → pre.length + rest.length = k.args.length →
      ∀ m, AppE (stdI_T c T) (.app (.sym n) (pre.map Elem.val)) (rest.map Elem.val) m ↔ result c k (pre ++ rest) m
  | pre, [], hlt, hlen, _ => by simp at hlen; omega
  | pre, w :: rest, hlt, hlen, m => by
    have hv2 : pre.map Elem.val ++ [Elem.val w] = (pre ++ [w]).map Elem.val := by simp
    have hr := hres ((pre ++ [w]).map Elem.val) (by intro s; cases pre <;> simp)
    have hl2 : ((pre ++ [w]).map Elem.val).length = pre.length + 1 := by simp
    have hev : ∀ x, (stdI_T c T).evalApp (.app (.sym n) (pre.map Elem.val)) (.val w) x ↔
        symAt c n ((pre ++ [w]).map Elem.val) x := fun x => by rw [← hv2]; exact Iff.rfl
    simp only [List.map_cons, AppE, hev]
    by_cases hl : pre.length + 1 < k.args.length
    · have ih := appE_sym hres (pre ++ [w]) rest (by simpa using hl) (by simp at hlen ⊢; omega) m
      simp only [List.append_assoc, List.singleton_append] at ih
      simp only [symAt_partial hr (by rw [hl2]; omega)]
      constructor
      · rintro ⟨a', ha', h⟩; rw [ha'] at h; exact ih.mp h
      · intro h; exact ⟨_, rfl, ih.mpr h⟩
    · have hrest : rest = [] := by
        cases rest with
        | nil => rfl
        | cons _ _ => simp at hlen; omega
      subst hrest
      simp only [symAt_full hr (by rw [hl2]; omega) (by rw [List.drop_zero, vals_map])]
      simp only [AppE, List.map_nil]
      constructor
      · rintro ⟨a', ha', rfl⟩; exact ha'
      · intro h; exact ⟨m, h, rfl⟩

end AtT

/-- A symbol applied to the elements of values, one at a time, from a partial application. -/
theorem appE_sym {n : String} {k : CtorSig}
    (hres : ∀ args : List Elem, (∀ s, args.head? ≠ some (.srt s)) → resolve c n args = some (k, 0)) :
    ∀ (pre rest : List GroundTerm), pre.length < k.args.length → pre.length + rest.length = k.args.length →
      ∀ m, AppE (stdI c) (.app (.sym n) (pre.map Elem.val)) (rest.map Elem.val) m ↔ result c k (pre ++ rest) m :=
  AtT.appE_sym (c := c) (T := StepM c) (n := n) (k := k) (hres := hres)

namespace AtT

variable {T : GroundTerm → GroundTerm → Prop}

/-- **A symbol of the semantics, at values**: the symbol of a name, applied to the elements of
values, gives what the symbol gives on the values (`result`). -/
theorem symE_vals (hn : NamesApartK c) {k : CtorSig} (hk : k ∈ kernelSyms c) {vs : List GroundTerm}
    (hl : vs.length = k.args.length) (m : Elem) :
    SymE (stdI_T c T) (c.symName k.name) (vs.map Elem.val) m ↔ result c k vs m := by
  have hinj : c.symName k.name ≠ "inj" := hn.2.1 k hk
  have hres := resolve_sym hn hk
  unfold SymE
  show (∃ a, evalSymb c (.symbol _) a ∧ _) ↔ _
  simp only [evalSymb_sym hn hk]
  by_cases h0 : k.args = []
  · simp only [if_pos h0]
    rw [h0] at hl
    obtain rfl : vs = [] := List.eq_nil_of_length_eq_zero hl
    simp only [List.map_nil, AppE]
    constructor
    · rintro ⟨a, ha, rfl⟩; exact ha
    · intro h; exact ⟨m, h, rfl⟩
  · simp only [if_neg h0]
    have := appE_sym (T := T) hres [] vs (by simp; exact List.length_pos_iff.mpr h0) (by simpa using hl) m
    simp only [List.map_nil, List.nil_append] at this
    constructor
    · rintro ⟨a, ha, h⟩; rw [ha] at h; exact this.mp h
    · intro h; exact ⟨_, rfl, this.mpr h⟩

end AtT

/-- **A symbol of the semantics, at values**: the symbol of a name, applied to the elements of
values, gives what the symbol gives on the values (`result`). -/
theorem symE_vals (hn : NamesApartK c) {k : CtorSig} (hk : k ∈ kernelSyms c) {vs : List GroundTerm}
    (hl : vs.length = k.args.length) (m : Elem) :
    SymE (stdI c) (c.symName k.name) (vs.map Elem.val) m ↔ result c k vs m :=
  AtT.symE_vals (c := c) (T := StepM c) (hn := hn) (k := k) (hk := hk) (vs := vs) (hl := hl) (m := m)

/-! ## Sorts by name -/

/-- A numbered sort is the one sort of its name. -/
theorem sortOfName_eq (hn : NamesApartK c) {s : Srt} (hs : s < nRegSorts + c.sortNames.length) :
    sortOfName c ("Sort" ++ c.sortName s) = some s := by
  have hm : s ∈ kernelSorts c := List.mem_range.mpr hs
  unfold sortOfName
  cases h : (kernelSorts c).find? (fun s' => "Sort" ++ c.sortName s' == "Sort" ++ c.sortName s) with
  | none =>
    have := List.find?_eq_none.mp h s hm
    simp at this
  | some s' =>
    have h1 := List.find?_some h
    have h2 := List.mem_of_find?_eq_some h
    rw [hn.2.2 s' h2 s hm (append_cancel (a := "Sort") (by simpa using h1))]

namespace AtT

variable {T : GroundTerm → GroundTerm → Prop}

theorem sort_den (hn : NamesApartK c) {s : Srt} (hs : s < nRegSorts + c.sortNames.length)
    (e : Valuation Elem) (m : Elem) :
    (KoreAML.sym (.sort ("Sort" ++ c.sortName s))).interpret (stdI_T c T) e m ↔ m = .srt s := by
  show (∃ s', sortOfName c _ = some s' ∧ m = .srt s') ↔ _
  rw [sortOfName_eq hn hs]
  simp

end AtT

theorem sort_den (hn : NamesApartK c) {s : Srt} (hs : s < nRegSorts + c.sortNames.length)
    (e : Valuation Elem) (m : Elem) :
    (KoreAML.sym (.sort ("Sort" ++ c.sortName s))).interpret (stdI c) e m ↔ m = .srt s :=
  AtT.sort_den (c := c) (T := StepM c) (hn := hn) (s := s) (hs := hs) (e := e) (m := m)

/-! ## Literals -/

theorem intRepr_inj {i j : Int} (h : intRepr i = intRepr j) : i = j := by
  have := intLit?_intRepr i
  rw [h, intLit?_intRepr j] at this
  exact (Option.some.inj this).symm

/-- **A literal is the one literal of its sort with its text** (`LitsApart`): Int, Bool and Float
literals are told apart by their text (`KFloat.text_inj`), and no token or byte sort is Int, Bool
or Float. -/
theorem lit_unique_self (hl : LitsApart c = true) {s : Srt} (hs : c.lib.carrier s = s) {l l' : Lit} (h1 : dvOK c.lib s l = true)
    (h2 : dvOK c.lib s l' = true) (ht : l.text = l'.text) : l = l' := by
  simp only [LitsApart, Bool.and_eq_true, Bool.not_eq_true', List.contains_append, Bool.or_eq_false_iff] at hl
  obtain ⟨⟨hi, hb⟩, hf⟩ := hl
  have tok : ∀ t, dvOK c.lib s (.tok t) = true → s ≠ Srt.int ∧ s ≠ Srt.bool ∧ s ≠ Srt.float := by
    intro t h
    simp only [dvOK_self hs, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true] at h
    have key : ∀ x, c.lib.tokenSorts.contains x = false → c.lib.byteSorts.contains x = false →
        x ≠ Srt.kconfigVar → x ≠ Srt.string → x ≠ Srt.bytes → s ≠ x := by
      intro x h1 h2 h3 h4 h5 hx
      subst hx
      rcases h with ((h | h) | h) | ⟨h | h, -⟩
      · exact h3 h
      · exact h4 h
      · rw [h1] at h; cases h
      · exact h5 h
      · rw [h2] at h; cases h
    exact ⟨key _ hi.1 hi.2 (by decide) (by decide) (by decide), key _ hb.1 hb.2 (by decide) (by decide) (by decide),
      key _ hf.1 hf.2 (by decide) (by decide) (by decide)⟩
  have hint : ∀ i, dvOK c.lib s (.int i) = true → s = Srt.int := fun i h => by simp only [dvOK_self hs] at h; exact beq_iff_eq.mp h
  have hbool : ∀ b, dvOK c.lib s (.bool b) = true → s = Srt.bool := fun b h => by simp only [dvOK_self hs] at h; exact beq_iff_eq.mp h
  have hfl : ∀ p e b, dvOK c.lib s (.float p e b) = true → s = Srt.float ∧ KFloat.ok p e b = true := fun p e b h => by
    simp only [dvOK_self hs, Bool.and_eq_true, beq_iff_eq] at h; exact h
  cases l with
  | int i =>
    cases l' with
    | int j => simp only [Lit.text] at ht; rw [intRepr_inj ht]
    | bool b => exact absurd ((hint i h1).symm.trans (hbool b h2)) (by decide)
    | tok t => exact absurd (hint i h1) (tok t h2).1
    | float _ _ _ => exact absurd ((hint i h1).symm.trans (hfl _ _ _ h2).1) (by decide)
  | bool a =>
    cases l' with
    | int j => exact absurd ((hint j h2).symm.trans (hbool a h1)) (by decide)
    | bool b => simp only [Lit.text] at ht; cases a <;> cases b <;> first | rfl | exact absurd ht (by decide)
    | tok t => exact absurd (hbool a h1) (tok t h2).2.1
    | float _ _ _ => exact absurd ((hbool a h1).symm.trans (hfl _ _ _ h2).1) (by decide)
  | tok t =>
    cases l' with
    | int j => exact absurd (hint j h2) (tok t h1).1
    | bool b => exact absurd (hbool b h2) (tok t h1).2.1
    | tok t' => simp only [Lit.text] at ht; rw [ht]
    | float _ _ _ => exact absurd (hfl _ _ _ h2).1 (tok t h1).2.2
  | float p e b =>
    cases l' with
    | int j => exact absurd ((hint j h2).symm.trans (hfl _ _ _ h1).1) (by decide)
    | bool a => exact absurd ((hbool a h2).symm.trans (hfl _ _ _ h1).1) (by decide)
    | tok t => exact absurd (hfl _ _ _ h1).1 (tok t h2).2.2
    | float p' e' b' =>
      simp only [Lit.text] at ht
      obtain ⟨rfl, rfl, rfl⟩ := KFloat.text_inj (hfl _ _ _ h1).2 (hfl _ _ _ h2).2 ht
      rfl


/-! ## What `HypModelCore` gives -/

theorem HypModelCore.namesK (h : HypModelCore c) : NamesApartK c := namesApartK_spec h.names

theorem HypModelCore.collsOK (h : HypModelCore c) : collsOK c = true := h.sound.2.2.2.2.2.2.1

theorem HypModelCore.mapVal (h : HypModelCore c) {k : CollSig} (hk : k ∈ c.allColls) (hkind : k.kind = .map) :
    k.val = some (valSort k) :=
  collsOK_val h.collsOK hk hkind

/-- Every sort of a kernel symbol is numbered. -/
theorem HypModelCore.symSorts (h : HypModelCore c) {k : CtorSig} (hk : k ∈ kernelSyms c) :
    ∀ s ∈ k.result :: k.args, s < nRegSorts + c.sortNames.length := by
  have := h.sorts
  simp only [sortsNumbered, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at this
  exact this.1.1.1 k hk

theorem HypModelCore.subSorts (h : HypModelCore c) {a b : Srt} (hab : (a, b) ∈ c.subsorts) :
    a < nRegSorts + c.sortNames.length ∧ b < nRegSorts + c.sortNames.length := by
  have := h.sorts
  simp only [sortsNumbered, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at this
  exact this.1.1.2 (a, b) hab

theorem HypModelCore.litSorts (h : HypModelCore c) {s : Srt} (hs : s ∈ c.lib.tokenSorts ++ c.lib.byteSorts) :
    s < nRegSorts + c.sortNames.length := by
  have := h.sorts
  simp only [sortsNumbered, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at this
  exact this.1.2 s (List.mem_append_left _ hs)

theorem HypModelCore.carrierSorts (h : HypModelCore c) {p : Srt × Srt} (hp : p ∈ c.lib.carriers) :
    p.1 < nRegSorts + c.sortNames.length := by
  have := h.sorts
  simp only [sortsNumbered, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at this
  exact this.1.2 p.1 (List.mem_append_right _ (List.mem_map.mpr ⟨p, hp, rfl⟩))

theorem HypModelCore.collSorts (h : HypModelCore c) {k : CollSig} (hk : k ∈ c.allColls) :
    k.sort < nRegSorts + c.sortNames.length ∧ k.key < nRegSorts + c.sortNames.length ∧
      (valSort k) < nRegSorts + c.sortNames.length := by
  have := h.sorts
  simp only [sortsNumbered, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at this
  exact (and_assoc).mp (this.2 k hk)

theorem HypModelCore.collNotCtor (h : HypModelCore c) {k : CollSig} (hk : k ∈ c.allColls) {f : Sym}
    (hf : f ∈ [k.unit, k.elem, k.concat]) : c.isCtor f = false := by
  have := List.all_eq_true.mp (List.all_eq_true.mp h.collCtors k hk) f hf
  simpa using this

/-- **A literal is the one literal of its sort with its text**: of its carrier's (`lit_unique_self`). -/
theorem lit_unique (hl : LitsApart c = true) {s : Srt} {l l' : Lit} (h1 : dvOK c.lib s l = true)
    (h2 : dvOK c.lib s l' = true) (ht : l.text = l'.text) : l = l' :=
  lit_unique_self hl (Lib.carrier_carrier _ s) (dvOK_carrier.trans h1) (dvOK_carrier.trans h2) ht

/-- The sort of a domain value is numbered. -/
theorem HypModelCore.dvSort (h : HypModelCore c) {s : Srt} {l : Lit} (hd : dvOK c.lib s l = true) :
    s < nRegSorts + c.sortNames.length := by
  by_cases hcar : c.lib.carriers.all (·.1 != s) = false
  · have : ∃ p ∈ c.lib.carriers, p.1 = s := by
      refine Classical.byContradiction fun hn => ?_
      have : c.lib.carriers.all (·.1 != s) = true := List.all_eq_true.mpr fun p hp => by
        have : p.1 ≠ s := fun he => hn ⟨p, hp, he⟩
        simpa using this
      rw [this] at hcar; cases hcar
    obtain ⟨p, hp, rfl⟩ := this
    exact h.carrierSorts hp
  have hs := Lib.carrier_of_not _ (by rw [Bool.not_eq_false] at hcar; exact hcar)
  cases l with
  | int _ => simp only [dvOK_self hs] at hd; rw [beq_iff_eq.mp hd]; exact Nat.lt_of_lt_of_le (by decide) (Nat.le_add_right _ _)
  | bool _ => simp only [dvOK_self hs] at hd; rw [beq_iff_eq.mp hd]; exact Nat.lt_of_lt_of_le (by decide) (Nat.le_add_right _ _)
  | tok t =>
    simp only [dvOK_self hs, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true] at hd
    rcases hd with ((hd | hd) | hd) | ⟨hd | hd, -⟩
    · rw [hd]; exact Nat.lt_of_lt_of_le (by decide) (Nat.le_add_right _ _)
    · rw [hd]; exact Nat.lt_of_lt_of_le (by decide) (Nat.le_add_right _ _)
    · exact h.litSorts (List.mem_append_left _ (List.contains_iff_mem.mp hd))
    · rw [hd]; exact Nat.lt_of_lt_of_le (by decide) (Nat.le_add_right _ _)
    · exact h.litSorts (List.mem_append_right _ (List.contains_iff_mem.mp hd))
  | float _ _ _ =>
    simp only [dvOK_self hs, Bool.and_eq_true, beq_iff_eq] at hd
    rw [hd.1]; exact Nat.lt_of_lt_of_le (by decide) (Nat.le_add_right _ _)

/-! ## What a symbol gives, by kind -/

theorem result_ctor {k : CtorSig} {vs : List GroundTerm} (hc : c.isCtor k.name = true) (x : Elem) :
    result c k vs x ↔ x = .val (.ctor k.name vs) := by
  unfold result; simp [hc]

/-- The library collections' symbols have no silent points, but the range map's element symbol (at a
range that is no proper Int range) and concatenation (at two maps with a key in common). -/
theorem silentKey_builtinColl (K : CollKind) (hK : K ≠ .rangeMap) :
    silentKey (builtinColl K).unit = false ∧ silentKey (builtinColl K).elem = false ∧
      silentKey (builtinColl K).concat = false := by
  cases K <;> first
    | exact absurd rfl hK
    | exact ⟨silentKey_of_mem rfl, silentKey_of_mem rfl, silentKey_of_mem rfl⟩
    | exact ⟨by decide, by decide, by decide⟩

theorem result_hook {k : CtorSig} {vs : List GroundTerm} (hc : c.isCtor k.name = false)
    (hh : isHook k.name = true) (x : Elem) :
    result c k vs x ↔ ∃ v, x = .val v ∧ c.hookRes k.name vs = some (some v) := by
  unfold result; simp [hc, hh]

theorem result_param {k : CtorSig} {vs : List GroundTerm} (hc : c.isCtor k.name = false)
    (hh : isHook k.name = false) (hp : c.isParam k.name = true) (x : Elem) :
    result c k vs x ↔ ∃ v, x = .val v ∧ c.paramVal k.name vs = some v := by
  unfold result; simp [hc, hh, hp]

/-- Where no function overload covers the arguments, an overloading symbol gives the normal form. -/
theorem ovlRes_none {f : Sym} {vs : List GroundTerm} (hnf : c.fnCover f vs = none) (x : Elem) :
    ovlRes c f vs x = (x = .val (c.norm f vs)) := by
  unfold ovlRes; rw [hnf]

/-- Where the function overload `kg` covers the arguments, an overloading symbol gives that
function's results at the stripped arguments, lifted to the symbol's result sort. -/
theorem ovlRes_some {f : Sym} {vs : List GroundTerm} {o : OvlSig} {kg : CtorSig}
    (hlo : c.lookupOvl f = some o) (hcov : c.fnCover f vs = some kg) (x : Elem) :
    ovlRes c f vs x ↔ ∃ v, x = .val (lift kg.result o.sig.result v) ∧
      Eval c kg.name (stripAll kg.args o.sig.args vs) (some v) := by
  unfold ovlRes; rw [hcov]
  constructor
  · rintro ⟨o', v, ho', hx, hv⟩
    rw [hlo] at ho'; cases ho'
    exact ⟨v, hx, hv⟩
  · rintro ⟨v, hx, hv⟩; exact ⟨o, v, hlo, hx, hv⟩

theorem result_ovlRes {k : CtorSig} {vs : List GroundTerm} (ho : c.isOvl k.name = true) (x : Elem) :
    result c k vs x ↔ ovlRes c k.name vs x := by
  obtain ⟨hc, hh, hp, -, -⟩ := c.isOvl_parts ho
  unfold result; simp [hc, hh, hp, ho]

theorem result_ovl {k : CtorSig} {vs : List GroundTerm} (ho : c.isOvl k.name = true)
    (hnf : c.fnCover k.name vs = none) (x : Elem) :
    result c k vs x ↔ x = .val (c.norm k.name vs) := by
  rw [result_ovlRes ho, ovlRes_none hnf]

/-- **A function-covered application, in the model**: an overloading symbol at arguments the
function overload `kg` covers gives the values `lift v`, `v` a result of that function at the
stripped arguments. -/
theorem result_ovlFn {k : CtorSig} {vs : List GroundTerm} {o : OvlSig} {kg : CtorSig}
    (ho : c.isOvl k.name = true) (hlo : c.lookupOvl k.name = some o) (hcov : c.fnCover k.name vs = some kg)
    (x : Elem) :
    result c k vs x ↔ ∃ v, x = .val (lift kg.result o.sig.result v) ∧
      Eval c kg.name (stripAll kg.args o.sig.args vs) (some v) := by
  rw [result_ovlRes ho, ovlRes_some hlo hcov]

theorem result_fn {k : CtorSig} {vs : List GroundTerm} (hc : c.isCtor k.name = false)
    (hh : isHook k.name = false) (hp : c.isParam k.name = false) (ho : c.isOvl k.name = false) (x : Elem) :
    result c k vs x ↔ ∃ v, x = .val v ∧ Eval c k.name vs (some v) := by
  unfold result; simp [hc, hh, hp, ho]

/-! ## The collection symbols -/

/-- **A collection's symbol, in the model**: the unit, element or concatenation of a collection is
a symbol of the semantics whose result on values is its library hook's value, at the collection's
sort (a library collection's hook builds a value of that sort already). -/
theorem coll_sym (h : HypModelCore c) {k : CollSig} (hk : k ∈ c.allColls) {f g : Sym} {args : List Srt}
    (hf : (f = k.unit ∧ g = (builtinColl k.kind).unit ∧ args = []) ∨
      (f = k.elem ∧ g = (builtinColl k.kind).elem ∧ args = elemArgs k) ∨
      (f = k.concat ∧ g = (builtinColl k.kind).concat ∧ args = [k.sort, k.sort])) :
    ∃ kf ∈ kernelSyms c, kf.name = f ∧ kf.args = args ∧ ∀ {vs : List GroundTerm} {v : GroundTerm},
      hook g vs = some (some v) → v.withSort (builtinColl k.kind).sort = v →
        c.sortOf (v.withSort k.sort) = some k.sort → ∀ m, (result c kf vs m ↔ m = .val (v.withSort k.sort)) := by
  have hfm : f ∈ [k.unit, k.elem, k.concat] := by
    rcases hf with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp
  have hnc := h.collNotCtor hk hfm
  rcases List.mem_append.mp hk with hb | hu
  · have hk' : k = builtinColl k.kind := by
      simp only [builtinColls, List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl | rfl | rfl <;> rfl
    have hfg : f = g ∧ (⟨f, args, k.sort⟩ : CtorSig) ∈ hookSigs ∧ isHook f = true := by
      simp only [builtinColls, List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl | rfl | rfl <;>
        rcases hf with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;> decide
    obtain ⟨rfl, hmem, hh⟩ := hfg
    refine ⟨⟨f, args, k.sort⟩, kernel_hook hmem, rfl, rfl, fun {vs v} hv hws _ m => ?_⟩
    have hws' : v.withSort k.sort = v := by rw [hk']; exact hws
    rw [result_hook hnc hh, hws']
    constructor
    · rintro ⟨v', rfl, hv'⟩; rw [Semantics.hookRes_of_value hv] at hv'; cases hv'; rfl
    · rintro rfl; exact ⟨v, rfl, Semantics.hookRes_of_value hv⟩
  · have hs := collSymsOK_spec (collsOK_colls h.collsOK hu)
    have hlp : c.lookupParam f = some { sig := ⟨f, args, k.sort⟩, impl := some g } := by
      rcases hf with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
      · exact hs.2.2.1
      · exact hs.2.2.2.1
      · exact hs.2.2.2.2
    have hmem : ({ sig := ⟨f, args, k.sort⟩, impl := some g } : ParamSig) ∈ c.params := by
      rw [Semantics.lookupParam_eq] at hlp; exact List.mem_of_find?_eq_some hlp
    have hh : isHook f = false := (hs.2.1 f hfm).1
    have hp : c.isParam f = true := by simp [Semantics.isParam, hlp]
    refine ⟨⟨f, args, k.sort⟩, kernel_param hmem, rfl, rfl, fun {vs v} hv _ hsv m => ?_⟩
    rw [result_param hnc hh hp]
    have hcg : Semantics.rawArgHooks.contains g = true := by
      rcases hf with ⟨-, rfl, -⟩ | ⟨-, rfl, -⟩ | ⟨-, rfl, -⟩ <;> generalize k.kind = K <;> cases K <;> decide
    have hcs : c.lib.carrier k.sort = k.sort := carrier_of_collSortOK (collSortsOK_mem h.sound.2.2.2.2.2.1 hk)
    have hpv : c.paramVal f vs = some (v.withSort k.sort) := by
      simp [Semantics.paramVal, hlp, Semantics.libArgs_coll c hcg, GroundTerm.asSort_of_self hcs,
        Semantics.hookRes_of_value hv, Option.filter, hsv]
    rw [hpv]
    constructor
    · rintro ⟨v', rfl, hv'⟩; cases hv'; rfl
    · rintro rfl; exact ⟨_, rfl, rfl⟩

/-! ## Collections of values -/

/-- A map whose keys are sorted is the union of its first entry with the rest. -/
theorem union_first {p : GroundTerm × GroundTerm} {es : Entries} (h : keysSorted (p :: es) = true) :
    union [p] es = some (p :: es) := by
  obtain ⟨x, y⟩ := p
  have hlt := keysSorted_lt_all h
  have hk : hasKey x es = false := by
    unfold hasKey
    rw [List.any_eq_false]
    intro e he
    rw [hlt e he]
    decide
  show (union [] es).bind (addNew x y) = _
  simp only [union, Option.bind_some, addNew, hk]
  cases es with
  | nil => rfl
  | cons e es =>
    obtain ⟨k', v'⟩ := e
    have : GroundTerm.cmp x k' = .lt := hlt _ (List.mem_cons_self ..)
    simp [insertE, this]

/-- A set whose elements are sorted is its first element inserted into the rest. -/
theorem sortOf_map_iff {s : Srt} {k : CollSig} (hco : c.collOf s = some k) (hval : k.val = some (valSort k))
    (hkind : k.kind = .map) {es : Entries} :
    c.sortOf (.map s es) = some s ↔ k.kind = .map ∧ keysSorted es = true ∧ c.entriesOK k.key (valSort k) es = true := by
  simp only [Semantics.sortOf, hco, hval, hkind]
  constructor
  · intro h
    split at h
    · rename_i hc; simpa [and_assoc] using hc
    · cases h
  · rintro ⟨-, h2, h3⟩
    simp [h2, h3]

/-- At a collection of kind `.rangeMap`, the library's or the definition's own, the map values of
its sort are the maps of maximal intervals in order with entries of its key and value sorts. -/
theorem sortOf_rmK_iff {k : CollSig} (hco : c.collOf k.sort = some k) (hkind : k.kind = .rangeMap)
    {vs : Srt} (hval : k.val = some vs) {es : Entries} :
    c.sortOf (.map k.sort es) = some k.sort ↔ rangesOK es = true ∧ c.entriesOK k.key vs es = true := by
  simp only [Semantics.sortOf, hco, hval, hkind]
  constructor
  · intro h
    split at h
    · rename_i hc; simpa using hc
    · cases h
  · rintro ⟨h2, h3⟩
    simp [h2, h3]

theorem entriesOK_cons' {ks vs : Srt} {x : GroundTerm × GroundTerm} {es : Entries} :
    c.entriesOK ks vs (x :: es) = true ↔ c.entryOK ks vs x = true ∧ c.entriesOK ks vs es = true := by
  simp [Semantics.entriesOK]

theorem entryOK_iff {ks vs : Srt} {a b : GroundTerm} :
    c.entryOK ks vs (a, b) = true ↔ c.sortOf a = some ks ∧ c.sortOf b = some vs := by
  simp [Semantics.entryOK]

theorem sortsOf_all {es : List GroundTerm} {s : Srt} :
    (∃ ss, c.sortsOf es = some ss ∧ ss.all (· == s) = true) ↔ ∀ e ∈ es, c.sortOf e = some s := by
  induction es with
  | nil => simp [sortsOf_nil]
  | cons e es ih =>
    constructor
    · rintro ⟨ss, hss, hall⟩
      obtain ⟨s', ss', h1, h2, rfl⟩ := sortsOf_cons.mp hss
      simp only [List.all_cons, Bool.and_eq_true, beq_iff_eq] at hall
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · rw [h1, hall.1]
      · exact ih.mp ⟨ss', h2, hall.2⟩ x hx
    · intro h
      obtain ⟨ss', h2, hall⟩ := ih.mpr fun x hx => h x (List.mem_cons_of_mem _ hx)
      refine ⟨s :: ss', sortsOf_cons.mpr ⟨s, ss', h e (List.mem_cons_self ..), h2, rfl⟩, ?_⟩
      simp [hall]

/-- The value of the set or list collection `k` with the elements `es`. -/
def elemsVal (k : CollSig) (es : List GroundTerm) : GroundTerm :=
  match k.kind with
  | .set => .set k.sort es
  | _ => .list k.sort es

theorem sortOf_elems_iff {k : CollSig} (hco : c.collOf k.sort = some k) (hkind : k.kind = .set ∨ k.kind = .list)
    {es : List GroundTerm} :
    c.sortOf (elemsVal k es) = some k.sort ↔
      (k.kind = .set → elemsSorted es = true) ∧ ∀ e ∈ es, c.sortOf e = some k.key := by
  rw [← sortsOf_all]
  rcases hkind with hkind | hkind
  · have hv : elemsVal k es = .set k.sort es := by unfold elemsVal; rw [hkind]
    rw [hv, Semantics.sortOf]
    cases hss : c.sortsOf es with
    | none => rw [hco]; simp
    | some ss =>
      rw [hco]
      dsimp only
      rw [hkind]
      constructor
      · intro h
        split at h
        · rename_i hc
          simp only [Bool.and_eq_true] at hc
          exact ⟨fun _ => hc.1.2, ss, rfl, hc.2⟩
        · cases h
      · rintro ⟨h1, ss1, hss1, h2⟩
        cases hss1
        rw [if_pos]
        simp only [Bool.and_eq_true]
        exact ⟨⟨rfl, h1 rfl⟩, h2⟩
  · have hv : elemsVal k es = .list k.sort es := by unfold elemsVal; rw [hkind]
    rw [hv, Semantics.sortOf]
    cases hss : c.sortsOf es with
    | none => rw [hco]; simp
    | some ss =>
      rw [hco]
      dsimp only
      rw [hkind]
      constructor
      · intro h
        split at h
        · rename_i hc
          simp only [Bool.and_eq_true] at hc
          exact ⟨(fun h => nomatch h), ss, rfl, hc.2⟩
        · cases h
      · rintro ⟨-, ss1, hss1, h2⟩
        cases hss1
        rw [if_pos]
        simp only [Bool.and_eq_true]
        exact ⟨rfl, h2⟩

/-! ## The KORE of values, unfolded -/

theorem tr_ap (f : String) (ps : List Kore.Pattern) :
    KoreAML.tr ⟨[], []⟩ (KoreAML.ap f ps) =
      KoreAML.appList (KoreAML.sym (.symbol f)) (ps.map (KoreAML.tr ⟨[], []⟩)) := by
  unfold KoreAML.ap
  rw [KoreAML.tr_app0, trArgs_appList]

namespace AtT

variable {T : GroundTerm → GroundTerm → Prop}

theorem stdI_symb (σ : KoreAML.Sym) : (stdI_T c T).evalSymb σ = evalSymb c σ := rfl

end AtT

theorem stdI_symb (σ : KoreAML.Sym) : (stdI c).evalSymb σ = evalSymb c σ :=
  AtT.stdI_symb (c := c) (T := StepM c) (σ := σ)
namespace AtT

variable {T : GroundTerm → GroundTerm → Prop}

theorem stdI_app : (stdI_T c T).evalApp = evalApp_T c T := rfl

end AtT

theorem stdI_app : (stdI c).evalApp = evalApp c :=
  AtT.stdI_app (c := c) (T := StepM c)

theorem injNormal_plain {a b : Srt} {t : GroundTerm} (h : t.isInj = false) : injNormal a b t = .inj a b t := by
  cases t <;> first | rfl | cases h



theorem builtinColl_map : builtinColl .map = ⟨Srt.map, .map, Srt.kitem, some Srt.kitem, mapUnit, mapElem, mapConcat⟩ := rfl
theorem builtinColl_set : builtinColl .set = ⟨Srt.set, .set, Srt.kitem, none, setUnit, setElem, setConcat⟩ := rfl
theorem builtinColl_list : builtinColl .list = ⟨Srt.list, .list, Srt.kitem, none, listUnit, listElem, listConcat⟩ := rfl

theorem hook_setUnit_eq (vs : List GroundTerm) :
    hook setUnit vs = some (match vs with | [] => some (.set Srt.set []) | _ => none) := rfl
theorem hook_setElem_eq (vs : List GroundTerm) :
    hook setElem vs = some (match vs with | [k] => some (.set Srt.set [k]) | _ => none) := rfl
theorem hook_setConcat_eq (vs : List GroundTerm) :
    hook setConcat vs = some (match vs with | [.set _ a, .set _ b] => (concatS a b).map (.set Srt.set) | _ => none) := rfl
theorem hook_listUnit_eq (vs : List GroundTerm) :
    hook listUnit vs = some (match vs with | [] => some (.list Srt.list []) | _ => none) := rfl
theorem hook_listElem_eq (vs : List GroundTerm) :
    hook listElem vs = some (match vs with | [k] => some (.list Srt.list [k]) | _ => none) := rfl
theorem hook_listConcat_eq (vs : List GroundTerm) :
    hook listConcat vs = some (match vs with | [.list _ a, .list _ b] => some (.list Srt.list (a ++ b)) | _ => none) := rfl

namespace AtT

variable {T : GroundTerm → GroundTerm → Prop}

theorem evalApp_inj0 (b : Elem) : evalApp_T c T (.app .inj []) b = fun x => x = .app .inj [b] := rfl

end AtT

theorem evalApp_inj0 (b : Elem) : evalApp c (.app .inj []) b = fun x => x = .app .inj [b] :=
  AtT.evalApp_inj0 (c := c) (T := StepM c) (b := b)
namespace AtT

variable {T : GroundTerm → GroundTerm → Prop}

theorem evalApp_inj1 (a b : Elem) : evalApp_T c T (.app .inj [a]) b = fun x => x = .app .inj [a, b] := rfl

end AtT

theorem evalApp_inj1 (a b : Elem) : evalApp c (.app .inj [a]) b = fun x => x = .app .inj [a, b] :=
  AtT.evalApp_inj1 (c := c) (T := StepM c) (a := a) (b := b)
namespace AtT

variable {T : GroundTerm → GroundTerm → Prop}

theorem evalApp_inj2 (a b : Srt) (v : GroundTerm) :
    evalApp_T c T (.app .inj [.srt a, .srt b]) (.val v) = fun x => x = .val (injNormal a b v) := rfl

end AtT

theorem evalApp_inj2 (a b : Srt) (v : GroundTerm) :
    evalApp c (.app .inj [.srt a, .srt b]) (.val v) = fun x => x = .val (injNormal a b v) :=
  AtT.evalApp_inj2 (c := c) (T := StepM c) (a := a) (b := b) (v := v)

namespace AtT

variable {T : GroundTerm → GroundTerm → Prop}

/-- A collection's symbol applied to patterns that denote values: the value its library hook gives,
at the collection's sort. -/
theorem coll_app (h : HypModelCore c) {k : CollSig} (hk : k ∈ c.allColls) {f g : Sym} {args : List Srt}
    (hf : (f = k.unit ∧ g = (builtinColl k.kind).unit ∧ args = []) ∨
      (f = k.elem ∧ g = (builtinColl k.kind).elem ∧ args = elemArgs k) ∨
      (f = k.concat ∧ g = (builtinColl k.kind).concat ∧ args = [k.sort, k.sort]))
    {vs : List GroundTerm} {φs : List KoreAML.P} {e : Valuation Elem}
    (H : All2 (fun φ x => ∀ m, φ.interpret (stdI_T c T) e m ↔ m = x) φs (vs.map Elem.val))
    (hlen : vs.length = args.length) {r : GroundTerm} (hv : hook g vs = some (some r))
    (hws : r.withSort (builtinColl k.kind).sort = r) (hsr : c.sortOf (r.withSort k.sort) = some k.sort)
    (m : Elem) :
    (KoreAML.appList (KoreAML.sym (.symbol (c.symName f))) φs).interpret (stdI_T c T) e m ↔
      m = .val (r.withSort k.sort) := by
  obtain ⟨kf, hkf, hkfn, hkfa, hres⟩ := coll_sym h hk hf
  rw [interp_symList _ φs _ H m, ← hkfn, symE_vals h.namesK hkf (by rw [hkfa]; exact hlen)]
  exact hres hv hws hsr m

end AtT

/-- A collection's symbol applied to patterns that denote values: the value its library hook gives,
at the collection's sort. -/
theorem coll_app (h : HypModelCore c) {k : CollSig} (hk : k ∈ c.allColls) {f g : Sym} {args : List Srt}
    (hf : (f = k.unit ∧ g = (builtinColl k.kind).unit ∧ args = []) ∨
      (f = k.elem ∧ g = (builtinColl k.kind).elem ∧ args = elemArgs k) ∨
      (f = k.concat ∧ g = (builtinColl k.kind).concat ∧ args = [k.sort, k.sort]))
    {vs : List GroundTerm} {φs : List KoreAML.P} {e : Valuation Elem}
    (H : All2 (fun φ x => ∀ m, φ.interpret (stdI c) e m ↔ m = x) φs (vs.map Elem.val))
    (hlen : vs.length = args.length) {r : GroundTerm} (hv : hook g vs = some (some r))
    (hws : r.withSort (builtinColl k.kind).sort = r) (hsr : c.sortOf (r.withSort k.sort) = some k.sort)
    (m : Elem) :
    (KoreAML.appList (KoreAML.sym (.symbol (c.symName f))) φs).interpret (stdI c) e m ↔
      m = .val (r.withSort k.sort) :=
  AtT.coll_app (c := c) (T := StepM c) (h := h) (k := k) (hk := hk) (f := f) (g := g) (args := args) (hf := hf) (vs := vs) (φs := φs) (e := e) (H := H) (hlen := hlen) (r := r) (hv := hv) (hws := hws) (hsr := hsr) (m := m)

theorem elemArgs_length {k : CollSig} (hk : k.kind = .map) : (elemArgs k).length = 2 := by
  unfold elemArgs; rw [hk]; rfl

theorem elemArgs_length' {k : CollSig} (hk : k.kind = .set ∨ k.kind = .list) : (elemArgs k).length = 1 := by
  unfold elemArgs; rcases hk with hk | hk <;> rw [hk] <;> rfl

theorem sortOf_set_some {s0 s : Srt} {es : List GroundTerm} (h : c.sortOf (.set s0 es) = some s) :
    s = s0 ∧ ∃ k, c.collOf s0 = some k ∧ k.kind = .set := by
  rw [Semantics.sortOf] at h
  split at h
  · rename_i k ss hco _
    split at h
    · rename_i hc
      cases h
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      exact ⟨rfl, k, hco, hc.1.1⟩
    · cases h
  · cases h

theorem sortOf_list_some {s0 s : Srt} {es : List GroundTerm} (h : c.sortOf (.list s0 es) = some s) :
    s = s0 ∧ ∃ k, c.collOf s0 = some k ∧ k.kind = .list := by
  rw [Semantics.sortOf] at h
  split at h
  · rename_i k ss hco _
    split at h
    · rename_i hc
      cases h
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      exact ⟨rfl, k, hco, hc.1⟩
    · cases h
  · cases h

theorem collOf_spec {s : Srt} {k : CollSig} (h : c.collOf s = some k) : k ∈ c.allColls ∧ k.sort = s := by
  unfold Semantics.collOf at h
  exact ⟨List.mem_of_find?_eq_some h, by simpa using List.find?_some h⟩


namespace AtT

variable {T : GroundTerm → GroundTerm → Prop}

/-- A one-element set or list, from the reading of its element. -/
theorem den_elem1 (h : HypModelCore c) (k : CollSig) (hk : k ∈ c.allColls) (hco : c.collOf k.sort = some k)
    (hkind : k.kind = .set ∨ k.kind = .list) (x : GroundTerm) (hs : c.sortOf (elemsVal k [x]) = some k.sort)
    {e : Valuation Elem} (hx : ∀ m, (den c x).interpret (stdI_T c T) e m ↔ m = .val x) :
    ∀ m, (KoreAML.tr ⟨[], []⟩ (GroundTerm.koreElems c k [x])).interpret (stdI_T c T) e m ↔ m = .val (elemsVal k [x]) := by
  rw [GroundTerm.koreElems.eq_2, tr_ap]
  have H : All2 (fun φ x => ∀ m, φ.interpret (stdI_T c T) e m ↔ m = x)
      ([GroundTerm.kore c x].map (KoreAML.tr ⟨[], []⟩)) ([x].map Elem.val) := .cons hx .nil
  have hl := (elemArgs_length' hkind).symm
  rcases hkind with hkind | hkind
  · have hev : elemsVal k [x] = .set k.sort [x] := by unfold elemsVal; rw [hkind]
    rw [hev] at hs ⊢
    exact coll_app h hk (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)) H hl (r := .set Srt.set [x])
      (by rw [hkind, builtinColl_set, hook_setElem_eq]) (by rw [hkind, builtinColl_set]; rfl) hs
  · have hev : elemsVal k [x] = .list k.sort [x] := by unfold elemsVal; rw [hkind]
    rw [hev] at hs ⊢
    exact coll_app h hk (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)) H hl (r := .list Srt.list [x])
      (by rw [hkind, builtinColl_list, hook_listElem_eq]) (by rw [hkind, builtinColl_list]; rfl) hs

end AtT

/-- A one-element set or list, from the reading of its element. -/
theorem den_elem1 (h : HypModelCore c) (k : CollSig) (hk : k ∈ c.allColls) (hco : c.collOf k.sort = some k)
    (hkind : k.kind = .set ∨ k.kind = .list) (x : GroundTerm) (hs : c.sortOf (elemsVal k [x]) = some k.sort)
    {e : Valuation Elem} (hx : ∀ m, (den c x).interpret (stdI c) e m ↔ m = .val x) :
    ∀ m, (KoreAML.tr ⟨[], []⟩ (GroundTerm.koreElems c k [x])).interpret (stdI c) e m ↔ m = .val (elemsVal k [x]) :=
  AtT.den_elem1 (c := c) (T := StepM c) (h := h) (k := k) (hk := hk) (hco := hco) (hkind := hkind) (x := x) (hs := hs) (e := e) (hx := hx)

/-- What the laws of the overloading symbols' normal forms read (OvlLaws.lean): `overloadsOK`, and
transitive, irreflexive subsorts. -/
theorem HypModelCore.ovlHyp (h : HypModelCore c) : OvlLaws.OvlHyp c :=
  ⟨h.ovlOK, (sortCtx_of_allClEx h.hyp.1 h.hyp.2.1 h.ovlCase).trans,
    fun s hs => (genWf_sub h.sound.2.2.2.1 hs).2 rfl⟩

/-! ## The reading -/

/-- `φ` denotes the one element `x` at the valuation `e`. -/
abbrev Sing (c : Semantics) (e : Valuation Elem) (φ : KoreAML.P) (x : Elem) : Prop := ∀ m, φ.interpret (stdI c) e m ↔ m = x

/-- An open generator is the parameter its symbol names, with no registry hook: `lookupParam`
finds the raw parameter itself (`raw_lookup`, from `idsOK` and the number outside the registry
`lookupOpen` reads), and `paramsPlain`'s `raw` branch gives it no hook (`raw_of_sortedOKCl`). -/
theorem HypModelCore.open_param (h : HypModelCore c) {f : Sym} {kp : ParamSig} (hko : c.lookupOpen f = some kp) :
    c.lookupParam f = some kp ∧ kp.impl = none := by
  obtain ⟨hkp, hraw, rfl, hreg⟩ := c.lookupOpen_spec hko
  exact ⟨(Semantics.raw_lookup h.ids hkp hraw hreg).1, (Semantics.raw_of_sortedOKClEx h.sound.1 hkp hraw).1⟩

namespace AtT

/-- `φ` denotes exactly `x` in the value model at the transition `T`. -/
abbrev Sing (c : Semantics) (T : GroundTerm → GroundTerm → Prop) (e : ML.Valuation Elem) (φ : KoreAML.P)
    (x : Elem) : Prop :=
  ∀ m, φ.interpret (stdI_T c T) e m ↔ m = x

end AtT

namespace AtT

variable {T : GroundTerm → GroundTerm → Prop}

/-- **An open generator's raw value denotes itself**: the symbol applied to its arguments' elements
is the parameter's value (`result`), which is the raw application where the interpretation leaves
it raw (`paramVal_raw_sorted`). From the parameter the symbol names (`hlp`), with no registry hook
(`hi`), and the arguments' reading (`hargs`). -/
theorem den_open (h : HypModelCore c) {f : Sym} {ts : List GroundTerm} {kp : ParamSig}
    (hko : c.lookupOpen f = some kp) (hlp : c.lookupParam f = some kp) (hi : kp.impl = none)
    (hts : c.sortsOf ts = some kp.sig.args) (hkr : c.keepsRaw f ts = true)
    (hv : c.sortOf (.ctor f ts) = some kp.sig.result) (e : Valuation Elem)
    (hargs : All2 (fun φ x => Sing c T e φ x) ((GroundTerm.koreList c ts).map (KoreAML.tr ⟨[], []⟩)) (ts.map Elem.val)) :
    Sing c T e (den c (.ctor f ts)) (.val (.ctor f ts)) := by
  obtain ⟨hkp, hraw, hn, -⟩ := c.lookupOpen_spec hko
  have hd : den c (.ctor f ts) = KoreAML.appList (KoreAML.sym (.symbol (c.symName f)))
      ((GroundTerm.koreList c ts).map (KoreAML.tr ⟨[], []⟩)) := by
    unfold den KoreAML.den; rw [GroundTerm.kore]; exact tr_ap _ _
  have hks : kp.sig ∈ kernelSyms c :=
    List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (List.mem_map_of_mem hkp)))
  have hkinds : c.isCtor kp.sig.name = false ∧ isHook kp.sig.name = false := by
    have := h.kinds
    simp only [kindsApart, Bool.and_eq_true, List.all_eq_true] at this
    simpa using this.2 kp hkp
  have hp : c.isParam kp.sig.name = true := by
    unfold Semantics.isParam; rw [hn, hlp]; rfl
  have hraw' : (c.hooks.app f ts).getD (.ctor f ts) = .ctor f ts := by
    unfold Semantics.keepsRaw at hkr
    cases ha : c.hooks.app f ts with
    | none => rfl
    | some w =>
      rw [ha] at hkr
      exact GroundTerm.cmp_eq _ _ (by simpa using hkr)
  have hpv : c.paramVal f ts = some (.ctor f ts) :=
    (paramVal_raw_sorted hlp hraw hi).mpr ⟨hraw'.symm, hv⟩
  intro m
  rw [hd, interp_symList _ _ _ hargs m, ← hn, symE_vals h.namesK hks (sortsOf_length hts),
    result_param hkinds.1 hkinds.2 hp, hn, hpv]
  constructor
  · rintro ⟨v, rfl, hv'⟩; cases hv'; rfl
  · rintro rfl; exact ⟨_, rfl, rfl⟩

mutual

/-- **Every value denotes itself.** -/
theorem den_val (h : HypModelCore c) : ∀ (v : GroundTerm) {s : Srt}, c.sortOf v = some s →
    ∀ (e : Valuation Elem), Sing c T e (den c v) (.val v)
  | .ctor f ts, s, hv, e => by
    have hd : den c (.ctor f ts) = KoreAML.appList (KoreAML.sym (.symbol (c.symName f)))
        ((GroundTerm.koreList c ts).map (KoreAML.tr ⟨[], []⟩)) := by
      unfold den KoreAML.den; rw [GroundTerm.kore]; exact tr_ap _ _
    rcases c.sortOf_ctor_iff.mp hv with ⟨k, hk, hts', -⟩ | ⟨hk, o, ho, hts', hu, -⟩ | ⟨-, -, kp, hko, hts', hkr, rfl⟩
    rotate_right
    · obtain ⟨hlp, hi⟩ := h.open_param hko
      exact den_open h hko hlp hi hts' hkr hv e (den_list h ts hts' e)
    · obtain ⟨hkm, hkn⟩ := lookupSig_spec hk
      have hks : k ∈ kernelSyms c :=
        List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hkm)))
      have hc : c.isCtor k.name = true := by unfold Semantics.isCtor; rw [hkn, hk]; rfl
      intro m
      rw [hd, interp_symList _ _ _ (den_list h ts hts' e) m, ← hkn,
        symE_vals h.namesK hks (sortsOf_length hts'), result_ctor hc]
    · -- a raw overloading application: the symbol's normal form, which is itself (`norm_fixed_ovlF`)
      have H := h.ovlHyp
      obtain ⟨hom, hon, hio, -⟩ := OvlLaws.ovl_facts_ovlF H.fnFacts ho
      have hks : o.sig ∈ kernelSyms c := List.mem_append_right _ (List.mem_map_of_mem hom)
      have hfix := OvlLaws.norm_fixed_ovlF H H.fnFacts ho hv
      intro m
      rw [hd, interp_symList _ _ _ (den_list h ts hts' e) m, ← hon,
        symE_vals h.namesK hks (sortsOf_length hts'), result_ovl (by rw [hon]; exact hio)
          (by rw [hon]; exact OvlLaws.fnCover_none_of_uncovered hu), hon, hfix]
  | .inj a b t, s, hv, e => by
    rw [Semantics.sortOf] at hv
    split at hv
    · rename_i hc
      cases hv
      simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at hc
      obtain ⟨⟨hab, hni⟩, hta⟩ := hc
      obtain ⟨ha, hb⟩ := h.subSorts (List.contains_iff_mem.mp hab)
      have hd : den c (.inj a b t) = KoreAML.appList (KoreAML.sym (.symbol "inj"))
          [KoreAML.sym (.sort ("Sort" ++ c.sortName a)), KoreAML.sym (.sort ("Sort" ++ c.sortName b)), den c t] := by
        unfold den KoreAML.den; rw [GroundTerm.kore, KoreAML.tr_injP]; rfl
      intro m
      rw [hd, interp_appList_sing _ _ [.srt a, .srt b, .val t]
        (.cons (sort_den h.namesK ha e) (.cons (sort_den h.namesK hb e) (.cons (den_val h t hta e) .nil))) m]
      simp only [KoreAML.interp_sym, stdI_symb, evalSymb_inj, AppE, stdI_app, exists_eq_left,
        evalApp_inj0, evalApp_inj1, evalApp_inj2, injNormal_plain hni]
    · cases hv
  | .dv s0 lit, s, hv, e => by
    rw [Semantics.sortOf] at hv
    split at hv
    · rename_i hd0
      cases hv
      have hd : den c (.dv s0 lit) =
          KoreAML.sym (.dv lit.text) ⬝ KoreAML.sym (.sort ("Sort" ++ c.sortName s0)) := by
        unfold den KoreAML.den; rw [GroundTerm.kore, KoreAML.tr_dv]; rfl
      intro m
      rw [hd, KoreAML.interp_app]
      simp only [KoreAML.interp_sym, stdI_symb, sort_den h.namesK (h.dvSort hd0) e, stdI_app]
      constructor
      · rintro ⟨a, b, ha, rfl, hab⟩
        have ha' : a = .app (.dv lit.text) [] := ha
        subst ha'
        have hab' : ∃ l, m = .val (.dv s0 l) ∧ l.text = lit.text ∧ dvOK c.lib s0 l = true := hab
        obtain ⟨l, rfl, ht, hl⟩ := hab'
        rw [lit_unique h.lits hl hd0 ht]
      · rintro rfl
        exact ⟨_, _, rfl, rfl, lit, rfl, rfl, hd0⟩
    · cases hv
  | .map s0 es, s, hv, e => by
    obtain ⟨k, vs, hco, hkind, hval, hks, hent, rfl⟩ := sortOf_mapS_fwd hv
    obtain ⟨hk, hks0⟩ := collOf_spec hco
    rcases hkind with hkind | hkind
    rotate_left
    · subst hks0
      have hvs : vs = valSort k := by simp [valSort, hval]
      subst hvs
      obtain ⟨hr, -⟩ := (sortOf_rmK_iff hco hkind hval).mp hv
      have hd : den c (.map k.sort es) = KoreAML.tr ⟨[], []⟩ (GroundTerm.koreEntries c k es) := by
        unfold den KoreAML.den; rw [GroundTerm.kore]; unfold Semantics.collSig; rw [hco]; rfl
      rw [hd]
      exact den_rmEntriesK h k hk hco hkind hval es hr hent e
    subst hks0
    have hvs : vs = valSort k := by simp [valSort, hval]
    subst hvs
    have hd : den c (.map k.sort es) = KoreAML.tr ⟨[], []⟩ (GroundTerm.koreEntries c k es) := by
      unfold den KoreAML.den; rw [GroundTerm.kore]; unfold Semantics.collSig; rw [hco]; rfl
    rw [hd]
    exact den_entries h k hk hco hkind es hks hent e
  | .set s0 es, s, hv, e => by
    obtain ⟨rfl, k, hco, hkind⟩ := sortOf_set_some hv
    obtain ⟨hk, hks0⟩ := collOf_spec hco
    subst hks0
    have hev : elemsVal k es = .set k.sort es := by unfold elemsVal; rw [hkind]
    have hd : den c (.set k.sort es) = KoreAML.tr ⟨[], []⟩ (GroundTerm.koreElems c k es) := by
      unfold den KoreAML.den; rw [GroundTerm.kore]; unfold Semantics.collSig; rw [hco]; rfl
    rw [hd, ← hev]
    exact den_elems h k hk hco (.inl hkind) es (by rw [hev]; exact hv) e
  | .list s0 es, s, hv, e => by
    obtain ⟨rfl, k, hco, hkind⟩ := sortOf_list_some hv
    obtain ⟨hk, hks0⟩ := collOf_spec hco
    subst hks0
    have hev : elemsVal k es = .list k.sort es := by unfold elemsVal; rw [hkind]
    have hd : den c (.list k.sort es) = KoreAML.tr ⟨[], []⟩ (GroundTerm.koreElems c k es) := by
      unfold den KoreAML.den; rw [GroundTerm.kore]; unfold Semantics.collSig; rw [hco]; rfl
    rw [hd, ← hev]
    exact den_elems h k hk hco (.inr hkind) es (by rw [hev]; exact hv) e
  termination_by structural v => v

theorem den_list (h : HypModelCore c) : ∀ (ts : List GroundTerm) {ss : List Srt}, c.sortsOf ts = some ss →
    ∀ (e : Valuation Elem), All2 (fun φ x => Sing c T e φ x)
      ((GroundTerm.koreList c ts).map (KoreAML.tr ⟨[], []⟩)) (ts.map Elem.val)
  | [], _, _, _ => .nil
  | t :: ts, _, hts, e => by
    obtain ⟨s, ss', h1, h2, -⟩ := sortsOf_cons.mp hts
    exact .cons (den_val h t h1 e) (den_list h ts h2 e)
  termination_by structural ts => ts

theorem den_entries (h : HypModelCore c) (k : CollSig) (hk : k ∈ c.allColls) (hco : c.collOf k.sort = some k)
    (hkind : k.kind = .map) : ∀ (es : List (GroundTerm × GroundTerm)), keysSorted es = true →
      c.entriesOK k.key (valSort k) es = true → ∀ (e : Valuation Elem),
      Sing c T e (KoreAML.tr ⟨[], []⟩ (GroundTerm.koreEntries c k es)) (.val (.map k.sort es))
  | [], _, _, e => by
    rw [GroundTerm.koreEntries, tr_ap]
    exact coll_app h hk (Or.inl ⟨rfl, rfl, rfl⟩) (vs := []) .nil rfl (r := .map Srt.map [])
      (by rw [hkind, builtinColl_map, Exec.hook_unit_eq]) (by rw [hkind, builtinColl_map]; rfl) ((sortOf_map_iff hco (h.mapVal hk hkind) hkind).mpr ⟨hkind, rfl, rfl⟩)
  | [x], _, hent, e => by
    rw [GroundTerm.koreEntries.eq_2]
    exact den_entry h k hk hco hkind x (entriesOK_cons'.mp hent).1 e
  | x :: y :: es, hs, hent, e => by
    obtain ⟨hx, hent'⟩ := entriesOK_cons'.mp hent
    have hs' := keysSorted_tail hs
    rw [GroundTerm.koreEntries.eq_3 c k x (y :: es) (List.cons_ne_nil _ _), tr_ap]
    exact coll_app h hk (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩)) (vs := [.map k.sort [x], .map k.sort (y :: es)])
      (.cons (den_entry h k hk hco hkind x hx e) (.cons (den_entries h k hk hco hkind (y :: es) hs' hent' e) .nil))
      rfl (r := .map Srt.map (x :: y :: es))
      (by rw [hkind, builtinColl_map, Exec.hook_concat_eq]; show some ((union [x] (y :: es)).map (GroundTerm.map Srt.map)) = _; rw [union_first hs]; rfl)
      (by rw [hkind, builtinColl_map]; rfl) ((sortOf_map_iff hco (h.mapVal hk hkind) hkind).mpr ⟨hkind, hs, hent⟩)
  termination_by structural es => es

theorem den_entry (h : HypModelCore c) (k : CollSig) (hk : k ∈ c.allColls) (hco : c.collOf k.sort = some k)
    (hkind : k.kind = .map) : ∀ (x : GroundTerm × GroundTerm), c.entryOK k.key (valSort k) x = true →
      ∀ (e : Valuation Elem), Sing c T e (KoreAML.tr ⟨[], []⟩ (GroundTerm.koreEntry c k x)) (.val (.map k.sort [x]))
  | (a, b), hx, e => by
    obtain ⟨ha, hb⟩ := entryOK_iff.mp hx
    rw [GroundTerm.koreEntry, tr_ap]
    exact coll_app h hk (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)) (vs := [a, b])
      (.cons (den_val h a ha e) (.cons (den_val h b hb e) .nil)) (elemArgs_length hkind).symm
      (r := .map Srt.map [(a, b)]) (by rw [hkind, builtinColl_map, Exec.hook_elem_eq]) (by rw [hkind, builtinColl_map]; rfl)
      ((sortOf_map_iff hco (h.mapVal hk hkind) hkind).mpr ⟨hkind, rfl, by simp [Semantics.entriesOK, hx]⟩)
  termination_by structural x => x

/-- A range map value of a collection of kind `.rangeMap`, the library's or the definition's own,
denotes itself: the unit, or its first entry's element concatenated with the rest. -/
theorem den_rmEntriesK (h : HypModelCore c) (k : CollSig) (hk : k ∈ c.allColls) (hco : c.collOf k.sort = some k)
    (hkind : k.kind = .rangeMap) (hval : k.val = some (valSort k)) :
    ∀ (es : List (GroundTerm × GroundTerm)), rangesOK es = true →
      c.entriesOK k.key (valSort k) es = true → ∀ (e : Valuation Elem),
      Sing c T e (KoreAML.tr ⟨[], []⟩ (GroundTerm.koreEntries c k es)) (.val (.map k.sort es))
  | [], _, _, e => by
    rw [GroundTerm.koreEntries, tr_ap]
    exact coll_app h hk (Or.inl ⟨rfl, rfl, rfl⟩) (vs := []) .nil rfl (r := rmV [])
      (by rw [hkind]; exact rmM_unit) (by rw [hkind]; rfl) ((sortOf_rmK_iff hco hkind hval).mpr ⟨rfl, rfl⟩)
  | [x], hr, hent, e => by
    rw [GroundTerm.koreEntries.eq_2]
    exact den_rmEntryK h k hk hco hkind hval x (by obtain ⟨_, _⟩ := x; exact rangesOK_head hr)
      (entriesOK_cons'.mp hent).1 e
  | x :: y :: es, hr, hent, e => by
    obtain ⟨hx, hent'⟩ := entriesOK_cons'.mp hent
    have hr' := rmM_tail hr
    rw [GroundTerm.koreEntries.eq_3 c _ x (y :: es) (List.cons_ne_nil _ _), tr_ap]
    exact coll_app h hk (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩)) (vs := [.map k.sort [x], .map k.sort (y :: es)])
      (.cons (den_rmEntryK h k hk hco hkind hval x (by obtain ⟨_, _⟩ := x; exact rangesOK_head hr) hx e)
        (.cons (den_rmEntriesK h k hk hco hkind hval (y :: es) hr' hent' e) .nil))
      rfl (r := rmV (x :: y :: es)) (by rw [hkind]; exact rmM_concat_sortK hr) (by rw [hkind]; rfl)
      ((sortOf_rmK_iff hco hkind hval).mpr ⟨hr, hent⟩)
  termination_by structural es => es

/-- One entry of a range map of a collection of kind `.rangeMap`: the element symbol at its proper
range and its value. -/
theorem den_rmEntryK (h : HypModelCore c) (k : CollSig) (hk : k ∈ c.allColls) (hco : c.collOf k.sort = some k)
    (hkind : k.kind = .rangeMap) (hval : k.val = some (valSort k)) :
    ∀ (x : GroundTerm × GroundTerm), (asRange x.1).isSome = true →
      c.entryOK k.key (valSort k) x = true → ∀ (e : Valuation Elem),
      Sing c T e (KoreAML.tr ⟨[], []⟩ (GroundTerm.koreEntry c k x)) (.val (.map k.sort [x]))
  | (a, b), hr, hx, e => by
    obtain ⟨ha, hb⟩ := entryOK_iff.mp hx
    rw [GroundTerm.koreEntry, tr_ap]
    exact coll_app h hk (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)) (vs := [a, b])
      (.cons (den_val h a ha e) (.cons (den_val h b hb e) .nil)) (by unfold elemArgs; rw [hkind]; rfl)
      (r := rmV [(a, b)]) (by rw [hkind]; exact rmM_elem hr) (by rw [hkind]; rfl)
      ((sortOf_rmK_iff hco hkind hval).mpr ⟨by simpa [rangesOK] using hr, by simp [Semantics.entriesOK, hx]⟩)
  termination_by structural x => x

theorem den_elems (h : HypModelCore c) (k : CollSig) (hk : k ∈ c.allColls) (hco : c.collOf k.sort = some k)
    (hkind : k.kind = .set ∨ k.kind = .list) : ∀ (es : List GroundTerm),
      c.sortOf (elemsVal k es) = some k.sort → ∀ (e : Valuation Elem),
      Sing c T e (KoreAML.tr ⟨[], []⟩ (GroundTerm.koreElems c k es)) (.val (elemsVal k es))
  | [], hs, e => by
    rw [GroundTerm.koreElems, tr_ap]
    rcases hkind with hkind | hkind
    · have hev : elemsVal k [] = .set k.sort [] := by unfold elemsVal; rw [hkind]
      rw [hev] at hs ⊢
      exact coll_app h hk (Or.inl ⟨rfl, rfl, rfl⟩) (vs := []) .nil rfl (r := .set Srt.set [])
        (by rw [hkind, builtinColl_set, hook_setUnit_eq]) (by rw [hkind, builtinColl_set]; rfl) hs
    · have hev : elemsVal k [] = .list k.sort [] := by unfold elemsVal; rw [hkind]
      rw [hev] at hs ⊢
      exact coll_app h hk (Or.inl ⟨rfl, rfl, rfl⟩) (vs := []) .nil rfl (r := .list Srt.list [])
        (by rw [hkind, builtinColl_list, hook_listUnit_eq]) (by rw [hkind, builtinColl_list]; rfl) hs
  | [x], hs, e => by
    have hx : c.sortOf x = some k.key := ((sortOf_elems_iff hco hkind).mp hs).2 x (List.mem_singleton_self _)
    rw [GroundTerm.koreElems.eq_2, tr_ap]
    have H : All2 (fun φ x => Sing c T e φ x) ([GroundTerm.kore c x].map (KoreAML.tr ⟨[], []⟩)) ([x].map Elem.val) :=
      .cons (den_val h x hx e) .nil
    have hl := (elemArgs_length' hkind).symm
    rcases hkind with hkind | hkind
    · have hev : elemsVal k [x] = .set k.sort [x] := by unfold elemsVal; rw [hkind]
      rw [hev] at hs ⊢
      exact coll_app h hk (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)) H hl (r := .set Srt.set [x])
        (by rw [hkind, builtinColl_set, hook_setElem_eq]) (by rw [hkind, builtinColl_set]; rfl) hs
    · have hev : elemsVal k [x] = .list k.sort [x] := by unfold elemsVal; rw [hkind]
      rw [hev] at hs ⊢
      exact coll_app h hk (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)) H hl (r := .list Srt.list [x])
        (by rw [hkind, builtinColl_list, hook_listElem_eq]) (by rw [hkind, builtinColl_list]; rfl) hs
  | x :: y :: es, hs, e => by
    obtain ⟨hso, hall⟩ := (sortOf_elems_iff hco hkind).mp hs
    have hx : c.sortOf x = some k.key := hall x (List.mem_cons_self ..)
    have hs1 : c.sortOf (elemsVal k [x]) = some k.sort :=
      (sortOf_elems_iff hco hkind).mpr ⟨fun _ => rfl, fun z hz => by rw [List.mem_singleton.mp hz]; exact hx⟩
    have hs2 : c.sortOf (elemsVal k (y :: es)) = some k.sort :=
      (sortOf_elems_iff hco hkind).mpr ⟨fun hk' => by
        have := hso hk'; simp only [elemsSorted, Bool.and_eq_true] at this; exact this.2,
        fun z hz => hall z (List.mem_cons_of_mem _ hz)⟩
    rw [GroundTerm.koreElems.eq_3 c k x (y :: es) (List.cons_ne_nil _ _), tr_ap]
    have H1 : Sing c T e (KoreAML.tr ⟨[], []⟩ (KoreAML.ap (c.symName k.elem) [GroundTerm.kore c x]))
        (.val (elemsVal k [x])) := by
      rw [← GroundTerm.koreElems.eq_2]
      exact den_elem1 h k hk hco hkind x hs1 (den_val h x hx e)
    have H2 := den_elems h k hk hco hkind (y :: es) hs2 e
    rcases hkind with hkind | hkind
    · have hev : ∀ l, elemsVal k l = .set k.sort l := fun l => by unfold elemsVal; rw [hkind]
      rw [hev] at hs H1 H2 ⊢
      exact coll_app h hk (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩)) (vs := [.set k.sort [x], .set k.sort (y :: es)])
        (.cons H1 (.cons H2 .nil)) rfl (r := .set Srt.set (x :: y :: es))
        (by rw [hkind, builtinColl_set, hook_setConcat_eq]; show some ((concatS [x] (y :: es)).map (GroundTerm.set Srt.set)) = _
            rw [concatS_first (elemsSorted_iff.mp (hso hkind))]; rfl)
        (by rw [hkind, builtinColl_set]; rfl) hs
    · have hev : ∀ l, elemsVal k l = .list k.sort l := fun l => by unfold elemsVal; rw [hkind]
      rw [hev] at hs H1 H2 ⊢
      exact coll_app h hk (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩)) (vs := [.list k.sort [x], .list k.sort (y :: es)])
        (.cons H1 (.cons H2 .nil)) rfl (r := .list Srt.list (x :: y :: es))
        (by rw [hkind, builtinColl_list, hook_listConcat_eq]; rfl) (by rw [hkind, builtinColl_list]; rfl) hs
  termination_by structural es => es

end

end AtT

/-- **An open generator's raw value denotes itself** (`AtT.den_open` at the value model). -/
theorem den_open (h : HypModelCore c) {f : Sym} {ts : List GroundTerm} {kp : ParamSig}
    (hko : c.lookupOpen f = some kp) (hlp : c.lookupParam f = some kp) (hi : kp.impl = none)
    (hts : c.sortsOf ts = some kp.sig.args) (hkr : c.keepsRaw f ts = true)
    (hv : c.sortOf (.ctor f ts) = some kp.sig.result) (e : Valuation Elem)
    (hargs : All2 (fun φ x => Sing c e φ x) ((GroundTerm.koreList c ts).map (KoreAML.tr ⟨[], []⟩)) (ts.map Elem.val)) :
    Sing c e (den c (.ctor f ts)) (.val (.ctor f ts)) :=
  AtT.den_open (c := c) (T := StepM c) h hko hlp hi hts hkr hv e hargs

/-- **Every value denotes itself.** -/
theorem den_val (h : HypModelCore c) : ∀ (v : GroundTerm) {s : Srt}, c.sortOf v = some s →
    ∀ (e : Valuation Elem), Sing c e (den c v) (.val v) :=
  AtT.den_val (c := c) (T := StepM c) (h := h)

theorem den_list (h : HypModelCore c) : ∀ (ts : List GroundTerm) {ss : List Srt}, c.sortsOf ts = some ss →
    ∀ (e : Valuation Elem), All2 (fun φ x => Sing c e φ x)
      ((GroundTerm.koreList c ts).map (KoreAML.tr ⟨[], []⟩)) (ts.map Elem.val) :=
  AtT.den_list (c := c) (T := StepM c) (h := h)

theorem den_entries (h : HypModelCore c) (k : CollSig) (hk : k ∈ c.allColls) (hco : c.collOf k.sort = some k)
    (hkind : k.kind = .map) : ∀ (es : List (GroundTerm × GroundTerm)), keysSorted es = true →
      c.entriesOK k.key (valSort k) es = true → ∀ (e : Valuation Elem),
      Sing c e (KoreAML.tr ⟨[], []⟩ (GroundTerm.koreEntries c k es)) (.val (.map k.sort es)) :=
  AtT.den_entries (c := c) (T := StepM c) (h := h) (k := k) (hk := hk) (hco := hco) (hkind := hkind)

theorem den_entry (h : HypModelCore c) (k : CollSig) (hk : k ∈ c.allColls) (hco : c.collOf k.sort = some k)
    (hkind : k.kind = .map) : ∀ (x : GroundTerm × GroundTerm), c.entryOK k.key (valSort k) x = true →
      ∀ (e : Valuation Elem), Sing c e (KoreAML.tr ⟨[], []⟩ (GroundTerm.koreEntry c k x)) (.val (.map k.sort [x])) :=
  AtT.den_entry (c := c) (T := StepM c) (h := h) (k := k) (hk := hk) (hco := hco) (hkind := hkind)

/-- A range map value of a collection of kind `.rangeMap`, the library's or the definition's own,
denotes itself: the unit, or its first entry's element concatenated with the rest. -/
theorem den_rmEntriesK (h : HypModelCore c) (k : CollSig) (hk : k ∈ c.allColls) (hco : c.collOf k.sort = some k)
    (hkind : k.kind = .rangeMap) (hval : k.val = some (valSort k)) :
    ∀ (es : List (GroundTerm × GroundTerm)), rangesOK es = true →
      c.entriesOK k.key (valSort k) es = true → ∀ (e : Valuation Elem),
      Sing c e (KoreAML.tr ⟨[], []⟩ (GroundTerm.koreEntries c k es)) (.val (.map k.sort es)) :=
  AtT.den_rmEntriesK (c := c) (T := StepM c) (h := h) (k := k) (hk := hk) (hco := hco) (hkind := hkind) (hval := hval)

/-- One entry of a range map of a collection of kind `.rangeMap`: the element symbol at its proper
range and its value. -/
theorem den_rmEntryK (h : HypModelCore c) (k : CollSig) (hk : k ∈ c.allColls) (hco : c.collOf k.sort = some k)
    (hkind : k.kind = .rangeMap) (hval : k.val = some (valSort k)) :
    ∀ (x : GroundTerm × GroundTerm), (asRange x.1).isSome = true →
      c.entryOK k.key (valSort k) x = true → ∀ (e : Valuation Elem),
      Sing c e (KoreAML.tr ⟨[], []⟩ (GroundTerm.koreEntry c k x)) (.val (.map k.sort [x])) :=
  AtT.den_rmEntryK (c := c) (T := StepM c) (h := h) (k := k) (hk := hk) (hco := hco) (hkind := hkind) (hval := hval)

theorem den_elems (h : HypModelCore c) (k : CollSig) (hk : k ∈ c.allColls) (hco : c.collOf k.sort = some k)
    (hkind : k.kind = .set ∨ k.kind = .list) : ∀ (es : List GroundTerm),
      c.sortOf (elemsVal k es) = some k.sort → ∀ (e : Valuation Elem),
      Sing c e (KoreAML.tr ⟨[], []⟩ (GroundTerm.koreElems c k es)) (.val (elemsVal k es)) :=
  AtT.den_elems (c := c) (T := StepM c) (h := h) (k := k) (hk := hk) (hco := hco) (hkind := hkind)

/-- A range map value of the library's sort denotes itself (`den_rmEntriesK` at `builtinColls`'
range-map row). -/
theorem den_rmEntries (h : HypModelCore c) : ∀ (es : List (GroundTerm × GroundTerm)), rangesOK es = true →
      c.entriesOK Srt.range Srt.kitem es = true → ∀ (e : Valuation Elem),
      Sing c e (KoreAML.tr ⟨[], []⟩ (GroundTerm.koreEntries c (builtinColl .rangeMap) es))
        (.val (.map Srt.rangeMap es)) :=
  den_rmEntriesK h _ rmM_mem collOf_rangeMap rfl rfl

/-- One entry of a range map of the library's sort (`den_rmEntryK` at the library's row). -/
theorem den_rmEntry (h : HypModelCore c) : ∀ (x : GroundTerm × GroundTerm), (asRange x.1).isSome = true →
      c.entryOK Srt.range Srt.kitem x = true → ∀ (e : Valuation Elem),
      Sing c e (KoreAML.tr ⟨[], []⟩ (GroundTerm.koreEntry c (builtinColl .rangeMap) x)) (.val (.map Srt.rangeMap [x])) :=
  den_rmEntryK h _ rmM_mem collOf_rangeMap rfl rfl

namespace AtT

variable {T : GroundTerm → GroundTerm → Prop}

/-- **`DenGoal`**: under `HypModelCore`, every value of a sort denotes exactly its own element. -/
theorem denGoal (h : HypModelCore c) : DenGoalT c T :=
  fun v _ hv e m => den_val h v hv e m

end AtT

/-- **`DenGoal`**: under `HypModelCore`, every value of a sort denotes exactly its own element. -/
theorem denGoal (h : HypModelCore c) : DenGoal c :=
  AtT.denGoal (c := c) (T := StepM c) (h := h)


end Model

end Faithful

end KCore
