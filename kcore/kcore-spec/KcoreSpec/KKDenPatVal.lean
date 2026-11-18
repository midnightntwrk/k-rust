import KcoreSpec.KKMatchColSpec

/-!
# A substitution of `kore.k`'s `match` against `PatVal`, collection patterns included

`den_patVal`: where, under a substitution `B`, the encoding of a pattern `p` is the encoding of a
value `v` of `p`'s sort (`DenF`, what `matchF_den` gives of every substitution `match` returns),
`B` gives every variable of `p` the encoding of a value of the variable's sort, and under every
`σ` that reads `B` (`BindRep`) the pattern denotes `v` (`PatVal`). `matchF_col_sound` and
`matchTsF_col_sound` are `matchF_sound` and `matchTsF_sound` without `noCb`, from it and
`matchF_den`; `matchF_col_wellSorted` and `matchTsF_col_wellSorted` give the well-sorted `σ`.

A collection pattern is read part by part. `encTerm` writes the parts of nested concatenations of
one collection as one list, for a `Map` or a `Set` the elements first; `DenColF` says which
elements of the value's encoding each part takes. `parts_ground_cdp` gives the parts back in the
pattern's order, each with the items of the value it takes: an element part one item, any other
part a sub-collection. The induction on the pattern then gives each concatenation the
sub-collection of the items its parts take, and the concatenation symbol builds it from the two
arguments' sub-collections (`collVal_concat_cdp`): a `Map`'s keys and a `Set`'s elements are
apart, since they are items of one value.

What is read of the semantics `c`, beyond what `matchF_sound` reads (`Exec.MatchCtxO c`, no
overloading symbol): `collsOK c`. It gives the signature of a parameter that is a collection
symbol (`collSig_cdp`): its result sort is a collection sort of the symbol's kind, the element
symbol's argument sorts are the collection's key and value sorts, and the concatenation's are the
collection's sort twice. Without it a frame at an argument of a concatenation declared at another
sort would be bound to a collection that is no value of the frame's sort. The library's symbols
have these signatures by `hookSigs`.

The order of a `Map`'s and a `Set`'s elements is read twice. The value's own order (`keysSorted`,
`elemsSorted`) makes a sub-collection a value of the collection's sort (`SubCtx_cdp.sub`).
`kore.k`'s order (`sortK`) is strict on the encodings of a sorted value's items (`enc_canonical`),
so a stretch of the encoding's elements is the encoding of the sub-collection of its items
(`SubCtx_cdp.frame`), which is what a part that is no element is matched against.
-/

set_option autoImplicit false

namespace KCore.KK

open KCore.Exec (MatchCtxO termSize termSizeList)
open KCore.CExec (content build CanonI pairOf oneOf)
open KCore.Faithful (collsOK collSymsOK elemArgs valSort collImpl)

/-! ## Lists -/

theorem perm_map_inv_cdp {α β : Type} (f : α → β) {l' : List β} {l : List α}
    (h : l'.Perm (l.map f)) : ∃ l'' : List α, l''.Perm l ∧ l''.map f = l' := by
  generalize hm : l.map f = m at h
  induction h generalizing l with
  | nil => exact ⟨[], by cases l <;> simp_all, rfl⟩
  | cons x _ ih =>
    cases l with
    | nil => cases hm
    | cons a l =>
      simp only [List.map_cons, List.cons.injEq] at hm
      obtain ⟨rfl, hm⟩ := hm
      obtain ⟨l'', h1, h2⟩ := ih hm
      exact ⟨a :: l'', h1.cons a, by simp [h2]⟩
  | swap x y l₀ =>
    match l, hm with
    | a :: b :: l, hm =>
      simp only [List.map_cons, List.cons.injEq] at hm
      obtain ⟨rfl, rfl, rfl⟩ := hm
      exact ⟨b :: a :: l, .swap a b l, rfl⟩
  | trans _ _ ih₁ ih₂ =>
    obtain ⟨l₂, h1, h2⟩ := ih₂ hm
    obtain ⟨l₁, h3, h4⟩ := ih₁ h2
    exact ⟨l₁, h3.trans h1, h4⟩

theorem perm_pairwise_eq_cdp {α : Type} {R : α → α → Prop} (hasym : ∀ a b, R a b → R b a → False) :
    ∀ {l₁ l₂ : List α}, l₁.Pairwise R → l₂.Pairwise R → l₁.Perm l₂ → l₁ = l₂
  | [], _, _, _, h => h.nil_eq
  | _ :: _, [], _, _, h => (List.cons_ne_nil _ _ h.eq_nil).elim
  | a :: l₁, b :: l₂, h1, h2, h => by
    rw [List.pairwise_cons] at h1 h2
    have hab : a = b := by
      have ha : a ∈ b :: l₂ := h.subset (List.mem_cons_self ..)
      have hb : b ∈ a :: l₁ := h.symm.subset (List.mem_cons_self ..)
      rcases List.mem_cons.mp ha with rfl | ha
      · rfl
      · rcases List.mem_cons.mp hb with rfl | hb
        · rfl
        · exact (hasym a b (h1.1 b hb) (h2.1 a ha)).elim
    subst hab
    rw [perm_pairwise_eq_cdp hasym h1.2 h2.2 (List.Perm.cons_inv h)]

/-! ## What a substitution states, by the pattern's form -/

section
variable {S : List (Int × Int)} {B : Bind}

theorem DenF.vr_inv_cdp {x : Int} {t : T} (h : DenF S B (.vr x) t) : lookF x B = some t := by
  cases h with | vr h => exact h

theorem DenF.ap_inv_cdp {f : Int} {ps : List T} {t : T} (h : DenF S B (.ap f ps) t) :
    ∃ ts, t = .ap f ts ∧ DensF S B ps ts := by
  cases h with | ap h => exact ⟨_, rfl, h⟩

theorem DenF.ij_inv_cdp {a b : Int} {p t : T} (h : DenF S B (.ij a b p) t) :
    ∃ c e u, t = .ij c e u ∧
      ((a = c ∧ DenF S B p u) ∨ (a ≠ c ∧ leqF c a S = true ∧ DenF S B p (.ij c a u))) := by
  cases h with
  | ijSame h => exact ⟨_, _, _, rfl, .inl ⟨rfl, h⟩⟩
  | ijSub hne hle h => exact ⟨_, _, _, rfl, .inr ⟨hne, hle, h⟩⟩

theorem DenF.as_inv_cdp {p : T} {x : Int} {t : T} (h : DenF S B (.as p x) t) :
    DenF S B p t ∧ lookF x B = some t := by
  cases h with | as h hx => exact ⟨h, hx⟩

theorem DenF.kv_inv_cdp {p q t : T} (h : DenF S B (.kv p q) t) :
    ∃ a v, t = .kv a v ∧ DenF S B p a ∧ DenF S B q v := by
  cases h with | kv hp hq => exact ⟨_, _, rfl, hp, hq⟩

theorem DenF.el_inv_cdp {p t : T} (h : DenF S B (.el p) t) : ∃ x, t = .el x ∧ DenF S B p x := by
  cases h with | el h => exact ⟨_, rfl, h⟩

theorem DenF.cb_inv_cdp {k : Kind} {c : Int} {ps : List T} {t : T} (h : DenF S B (.cb k c ps) t) :
    ∃ l e es, t = .co l e es ∧ DenColF S B k c ps es := by
  cases h with | cb h => exact ⟨_, _, _, rfl, h⟩

theorem DenF.lit_inv_cdp {s : Srt} {l : Lit} {q t : T} (hq : encLit s l = some q)
    (h : DenF S B q t) : t = q := by
  rcases encLit_some hq with ⟨i, -, -, rfl⟩ | ⟨b, -, -, rfl⟩ | ⟨x, -, rfl⟩ <;> cases h <;> rfl

theorem DenF.hk_inv_cdp {o : Int} {as : List T} {t : T} (h : DenF S B (.hk o as) t) : False := by
  cases h

end

/-! ## The forms `encTerm` writes -/

theorem readApp_cases_cdp {c : Semantics} {f : Sym} {args parts : Option (List T)} {q : T}
    (h : readApp c f args parts = some q) :
    (∃ qs, args = some qs ∧ q = .ap f qs ∧ (c.isCtor f = true ∨ c.isParam f = false)) ∨
    (c.isCtor f = false ∧ ∃ k s r ps, collSymOf c f = some (k, s, r) ∧ parts = some ps ∧
        q = .cb k s (orderParts k ps)) ∨
    ∃ qs o, args = some qs ∧ (q = .hk o qs ∨ q = .hk 22 [.hk 23 qs]) := by
  unfold readApp at h
  split at h
  · rename_i hc
    obtain ⟨qs, rfl, rfl⟩ := Option.map_eq_some_iff.mp h
    exact .inl ⟨qs, rfl, rfl, .inl hc⟩
  · rename_i hc
    split at h
    · rename_i k s r hk
      obtain ⟨ps, rfl, rfl⟩ := Option.map_eq_some_iff.mp h
      exact .inr (.inl ⟨by simpa using hc, k, s, r, ps, hk, rfl, rfl⟩)
    · split at h
      · split at h
        · rename_i o _
          obtain ⟨qs, rfl, rfl⟩ := Option.map_eq_some_iff.mp h
          exact .inr (.inr ⟨qs, o, rfl, .inl rfl⟩)
        · obtain ⟨qs, rfl, h'⟩ := Option.bind_eq_some_iff.mp h
          unfold derivedHook at h'
          split at h'
          · cases h'; exact .inr (.inr ⟨qs, 0, rfl, .inr rfl⟩)
          · cases h'
      · split at h
        · cases h
        · rename_i hp
          split at h
          · obtain ⟨qs, rfl, rfl⟩ := Option.map_eq_some_iff.mp h
            exact .inl ⟨qs, rfl, rfl, .inr (by simpa using hp)⟩
          · cases h

theorem encTerm_notElem_cdp {c : Semantics} {t : Term} {q : T} (h : encTerm c t = some q) :
    isElemT q = false := by
  cases t with
  | var i => rw [encTerm_var_kmf] at h; cases h; rfl
  | dv s l =>
    rw [encTerm_dv_kmf] at h
    rcases encLit_some h with ⟨i, -, -, rfl⟩ | ⟨b, -, -, rfl⟩ | ⟨x, -, rfl⟩ <;> rfl
  | inj a b t => rw [encTerm_inj_kmf] at h; obtain ⟨_, -, rfl⟩ := Option.map_eq_some_iff.mp h; rfl
  | as t i => rw [encTerm_as_kmf] at h; obtain ⟨_, -, rfl⟩ := Option.map_eq_some_iff.mp h; rfl
  | app f ts =>
    rw [encTerm_app_kmf] at h
    rcases readApp_cases_cdp h with ⟨qs, -, rfl, -⟩ | ⟨-, k, s, r, ps, -, -, rfl⟩ |
      ⟨qs, o, -, rfl | rfl⟩ <;> rfl

theorem encPart_cases_cdp {c : Semantics} {k : Kind} {s : Srt} {a : Term} {ps : List T}
    (h : encPartWith c encLit k s a = some ps) :
    (∃ f ts r, a = .app f ts ∧ c.isCtor f = false ∧ collSymOf c f = some (k, s, r) ∧
        encCollWith c encLit k s r ts = some ps) ∨
    ∃ q, encTerm c a = some q ∧ ps = [q] := by
  cases a with
  | var i => rw [encPartWith] at h; cases h; exact .inr ⟨_, encTerm_var_kmf c i, rfl⟩
  | dv s' l =>
    rw [encPartWith] at h
    obtain ⟨q, hq, rfl⟩ := Option.map_eq_some_iff.mp h
    exact .inr ⟨q, by rw [encTerm_dv_kmf]; exact hq, rfl⟩
  | inj a b t =>
    rw [encPartWith] at h
    obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.mp h
    refine .inr ⟨_, ?_, rfl⟩
    rw [encTerm_inj_kmf, show encTerm c t = some p from hp]; rfl
  | as t i =>
    rw [encPartWith] at h
    obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.mp h
    refine .inr ⟨_, ?_, rfl⟩
    rw [encTerm_as_kmf, show encTerm c t = some p from hp]; rfl
  | app f ts =>
    rw [encPartWith] at h
    split at h
    · rename_i k' s' r hct hcy
      split at h
      · rename_i hks
        simp only [Bool.and_eq_true, beq_iff_eq] at hks
        obtain ⟨rfl, rfl⟩ := hks
        exact .inl ⟨f, ts, r, rfl, hct, hcy, h⟩
      · obtain ⟨q, hq, rfl⟩ := Option.map_eq_some_iff.mp h
        exact .inr ⟨q, by rw [encTerm_app_kmf, hcy]; exact hq, rfl⟩
    · obtain ⟨q, hq, rfl⟩ := Option.map_eq_some_iff.mp h
      exact .inr ⟨q, by rw [encTerm_app_kmf]; exact hq, rfl⟩

theorem encColl_cases_cdp {c : Semantics} {k : Kind} {s : Srt} {r : CRole} {ts : List Term}
    {ps : List T} (h : encCollWith c encLit k s r ts = some ps) :
    (r = .unit ∧ ts = [] ∧ ps = []) ∨
    (r = .elem ∧ ∃ qs e, encTermsWith c encLit ts = some qs ∧ ps = [e] ∧
        ((k ≠ .map ∧ ∃ p, qs = [p] ∧ e = .el p) ∨ (k = .map ∧ ∃ p q, qs = [p, q] ∧ e = .kv p q))) ∨
    (r = .concat ∧ ∃ a v pa pb, ts = [a, v] ∧ encPartWith c encLit k s a = some pa ∧
        encPartWith c encLit k s v = some pb ∧ ps = pa ++ pb) := by
  match ts, h with
  | [], h =>
    rw [encCollWith] at h
    split at h
    · rename_i hr; cases h; exact .inl ⟨by simpa using hr, rfl, rfl⟩
    · cases h
  | [x], h =>
    rw [encCollWith] at h
    split at h
    · rename_i hr
      simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hr
      obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.mp h
      refine .inr (.inl ⟨hr.1, [p], .el p, ?_, rfl, .inl ⟨hr.2, p, rfl, rfl⟩⟩)
      simp [encTermsWith, hp]
    · cases h
  | [a, v], h =>
    rw [encCollWith] at h
    split at h
    · rename_i hr
      simp only [Bool.and_eq_true, beq_iff_eq] at hr
      split at h
      · rename_i p q hp hq
        cases h
        exact .inr (.inl ⟨hr.1, [p, q], .kv p q, by simp [encTermsWith, hp, hq], rfl,
          .inr ⟨hr.2, p, q, rfl, rfl⟩⟩)
      · cases h
    · split at h
      · rename_i hr
        split at h
        · rename_i pa pb hpa hpb
          cases h
          exact .inr (.inr ⟨by simpa using hr, a, v, pa, pb, rfl, hpa, hpb, rfl⟩)
        · cases h
      · cases h
  | _ :: _ :: _ :: _, h => rw [encCollWith] at h; cases h

/-! ## The variables of an encoded pattern are the pattern's -/

theorem mem_tvarsLF_cdp {x : Int} : ∀ {ps : List T}, x ∈ tvarsLF ps ↔ ∃ p ∈ ps, x ∈ tvarsF p
  | [] => by simp [tvarsLF]
  | p :: ps => by simp [tvarsLF, mem_tvarsLF_cdp (ps := ps)]

theorem mem_orderParts_cdp {k : Kind} {ps : List T} {p : T} (h : p ∈ orderParts k ps) : p ∈ ps := by
  unfold orderParts at h
  split at h
  · exact h
  · rcases List.mem_append.mp h with h | h <;> exact (List.mem_filter.mp h).1

mutual
/-- Every variable of the encoding of a pattern is a variable of the pattern. -/
theorem tvars_term_cdp (c : Semantics) : ∀ (t : Term) {q : T}, encTerm c t = some q →
    ∀ x ∈ tvarsF q, ∃ i ∈ varOccs t, x = (i : Int)
  | .var i, q, h, x, hx => by
    rw [encTerm_var_kmf] at h; cases h
    simp only [tvarsF, List.mem_singleton] at hx
    exact ⟨i, by simp [varOccs], hx⟩
  | .dv s l, q, h, x, hx => by
    rw [encTerm_dv_kmf] at h
    rcases encLit_some h with ⟨i, -, -, rfl⟩ | ⟨b, -, -, rfl⟩ | ⟨y, -, rfl⟩ <;> simp [tvarsF] at hx
  | .inj a b t, q, h, x, hx => by
    rw [encTerm_inj_kmf] at h
    obtain ⟨q', hq', rfl⟩ := Option.map_eq_some_iff.mp h
    obtain ⟨i, hi, rfl⟩ := tvars_term_cdp c t hq' x (by simpa [tvarsF] using hx)
    exact ⟨i, by simpa [varOccs] using hi, rfl⟩
  | .as t j, q, h, x, hx => by
    rw [encTerm_as_kmf] at h
    obtain ⟨q', hq', rfl⟩ := Option.map_eq_some_iff.mp h
    simp only [tvarsF, List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · obtain ⟨i, hi, rfl⟩ := tvars_term_cdp c t hq' x hx
      exact ⟨i, by simp [varOccs, hi], rfl⟩
    · exact ⟨j, by simp [varOccs], rfl⟩
  | .app f ts, q, h, x, hx => by
    rw [encTerm_app_kmf] at h
    rcases readApp_cases_cdp h with ⟨qs, hqs, rfl, -⟩ | ⟨-, k, s, r, ps, hk, hps, rfl⟩ |
      ⟨qs, o, hqs, rfl | rfl⟩
    · obtain ⟨i, hi, rfl⟩ := tvars_terms_cdp c ts hqs x (by simpa [tvarsF] using hx)
      exact ⟨i, by simpa [varOccs] using hi, rfl⟩
    · rw [hk] at hps
      have hps' : encCollWith c encLit k s r ts = some ps := hps
      have hx' : x ∈ tvarsLF ps := by
        simp only [tvarsF] at hx
        obtain ⟨p, hp, hxp⟩ := mem_tvarsLF_cdp.mp hx
        exact mem_tvarsLF_cdp.mpr ⟨p, mem_orderParts_cdp hp, hxp⟩
      obtain ⟨i, hi, rfl⟩ := tvars_coll_cdp c ts hps' x hx'
      exact ⟨i, by simpa [varOccs] using hi, rfl⟩
    · obtain ⟨i, hi, rfl⟩ := tvars_terms_cdp c ts hqs x (by simpa [tvarsF] using hx)
      exact ⟨i, by simpa [varOccs] using hi, rfl⟩
    · obtain ⟨i, hi, rfl⟩ := tvars_terms_cdp c ts hqs x (by simpa [tvarsF, tvarsLF] using hx)
      exact ⟨i, by simpa [varOccs] using hi, rfl⟩
  termination_by t => 3 * termSize t
  decreasing_by all_goals (simp_wf <;> first | omega | (simp only [termSize]; omega))
theorem tvars_terms_cdp (c : Semantics) : ∀ (ts : List Term) {qs : List T},
    encTermsWith c encLit ts = some qs → ∀ x ∈ tvarsLF qs, ∃ i ∈ varOccsList ts, x = (i : Int)
  | [], qs, h, x, hx => by cases encTerms_nil_kmf c h; simp [tvarsLF] at hx
  | t :: ts, qs, h, x, hx => by
    obtain ⟨q, qs', h1, h2, rfl⟩ := encTerms_cons_kmf c h
    simp only [tvarsLF, List.mem_append] at hx
    have hpos := Exec.termSize_pos t
    rcases hx with hx | hx
    · obtain ⟨i, hi, rfl⟩ := tvars_term_cdp c t h1 x hx
      exact ⟨i, by simp [varOccsList, hi], rfl⟩
    · obtain ⟨i, hi, rfl⟩ := tvars_terms_cdp c ts h2 x hx
      exact ⟨i, by simp [varOccsList, hi], rfl⟩
  termination_by ts => 3 * termSizeList ts + 1
  decreasing_by all_goals (simp_wf <;> first | omega | (simp only [termSizeList]; omega))
theorem tvars_coll_cdp (c : Semantics) : ∀ (ts : List Term) {k : Kind} {s : Srt} {r : CRole}
    {ps : List T}, encCollWith c encLit k s r ts = some ps →
    ∀ x ∈ tvarsLF ps, ∃ i ∈ varOccsList ts, x = (i : Int)
  | ts, k, s, r, ps, h, x, hx => by
    rcases encColl_cases_cdp h with ⟨-, -, rfl⟩ | ⟨-, qs, e, hqs, rfl, hsh⟩ |
      ⟨-, a, v, pa, pb, hts, hpa, hpb, rfl⟩
    · simp [tvarsLF] at hx
    · have hx' : x ∈ tvarsLF qs := by
        rcases hsh with ⟨-, p, rfl, rfl⟩ | ⟨-, p, q, rfl, rfl⟩ <;> simpa [tvarsLF, tvarsF] using hx
      exact tvars_terms_cdp c ts hqs x hx'
    · have hpa' := Exec.termSize_pos a
      have hpb' := Exec.termSize_pos v
      have hsz : termSizeList ts = termSize a + termSize v := by rw [hts]; simp [termSizeList]
      obtain ⟨p, hp, hxp⟩ := mem_tvarsLF_cdp.mp hx
      rw [hts]
      rcases List.mem_append.mp hp with hp | hp
      · obtain ⟨i, hi, rfl⟩ := tvars_part_cdp c a hpa x (mem_tvarsLF_cdp.mpr ⟨p, hp, hxp⟩)
        exact ⟨i, by simp [varOccsList, hi], rfl⟩
      · obtain ⟨i, hi, rfl⟩ := tvars_part_cdp c v hpb x (mem_tvarsLF_cdp.mpr ⟨p, hp, hxp⟩)
        exact ⟨i, by simp [varOccsList, hi], rfl⟩
  termination_by ts => 3 * termSizeList ts + 2
  decreasing_by all_goals (simp_wf <;> omega)
theorem tvars_part_cdp (c : Semantics) : ∀ (a : Term) {k : Kind} {s : Srt} {ps : List T},
    encPartWith c encLit k s a = some ps → ∀ x ∈ tvarsLF ps, ∃ i ∈ varOccs a, x = (i : Int)
  | a, k, s, ps, h, x, hx => by
    rcases encPart_cases_cdp h with ⟨f, ts, r, ha, -, -, hc⟩ | ⟨q, hq, rfl⟩
    · have hsz : termSize a = termSizeList ts + 1 := by rw [ha]; simp [termSize]
      obtain ⟨i, hi, rfl⟩ := tvars_coll_cdp c ts hc x hx
      exact ⟨i, by rw [ha]; simpa [varOccs] using hi, rfl⟩
    · exact tvars_term_cdp c a hq x (by simpa [tvarsLF] using hx)
  termination_by a => 3 * termSize a + 1
  decreasing_by all_goals (simp_wf <;> omega)
end

/-! ## The collection symbols of a semantics -/


theorem libCollOf_cases_cdp {g : Sym} {k : Kind} {s : Srt} {r : CRole}
    (h : libCollOf g = some (k, s, r)) :
    (g, k, s, r) ∈ [(mapUnit, Kind.map, Srt.map, CRole.unit), (mapElem, .map, Srt.map, .elem),
      (mapConcat, .map, Srt.map, .concat), (setUnit, .set, Srt.set, .unit),
      (setElem, .set, Srt.set, .elem), (setConcat, .set, Srt.set, .concat),
      (listUnit, .list, Srt.list, .unit), (listElem, .list, Srt.list, .elem),
      (listConcat, .list, Srt.list, .concat)] := by
  unfold libCollOf at h
  obtain ⟨K, hK, hg⟩ := List.exists_of_findSome?_eq_some h
  simp only [builtinColls, List.mem_cons, List.not_mem_nil, or_false] at hK
  have key : ∀ (u e w : Sym) (kd : Kind) (st : Srt) (a : CRole),
      (if (g == u) = true then some CRole.unit else if (g == e) = true then some CRole.elem
        else if (g == w) = true then some CRole.concat else none) = some a →
      (g = u ∧ a = .unit) ∨ (g = e ∧ a = .elem) ∨ (g = w ∧ a = .concat) := by
    intro u e w kd st a ha
    split at ha
    · rename_i h1; cases ha; exact .inl ⟨beq_iff_eq.mp h1, rfl⟩
    · split at ha
      · rename_i h1; cases ha; exact .inr (.inl ⟨beq_iff_eq.mp h1, rfl⟩)
      · split at ha
        · rename_i h1; cases ha; exact .inr (.inr ⟨beq_iff_eq.mp h1, rfl⟩)
        · cases ha
  rcases hK with rfl | rfl | rfl | rfl
  · simp only [kindOf, Option.bind_some, roleIn, Option.map_eq_some_iff] at hg
    obtain ⟨a, ha, he⟩ := hg
    cases he
    rcases key _ _ _ .map 0 _ ha with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  · simp only [kindOf, Option.bind_some, roleIn, Option.map_eq_some_iff] at hg
    obtain ⟨a, ha, he⟩ := hg
    cases he
    rcases key _ _ _ .map 0 _ ha with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  · simp only [kindOf, Option.bind_some, roleIn, Option.map_eq_some_iff] at hg
    obtain ⟨a, ha, he⟩ := hg
    cases he
    rcases key _ _ _ .map 0 _ ha with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  · simp [kindOf] at hg

/-- The nine library collection symbols. -/
theorem libCollOf_nine_cdp {g : Sym} {k : Kind} {s : Srt} {r : CRole}
    (h : libCollOf g = some (k, s, r)) :
    g = mapUnit ∨ g = mapElem ∨ g = mapConcat ∨ g = setUnit ∨ g = setElem ∨ g = setConcat ∨
      g = listUnit ∨ g = listElem ∨ g = listConcat := by
  have := libCollOf_cases_cdp h
  simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at this
  rcases this with h | h | h | h | h | h | h | h | h
  · exact .inl h.1
  · exact .inr (.inl h.1)
  · exact .inr (.inr (.inl h.1))
  · exact .inr (.inr (.inr (.inl h.1)))
  · exact .inr (.inr (.inr (.inr (.inl h.1))))
  · exact .inr (.inr (.inr (.inr (.inr (.inl h.1)))))
  · exact .inr (.inr (.inr (.inr (.inr (.inr (.inl h.1))))))
  · exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl h.1)))))))
  · exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr h.1)))))))

/-- A collection symbol of `c` is a library collection's symbol, or a parameter one implements,
read at the parameter's result sort. -/
theorem collSym_lib_cdp {c : Semantics} {f : Sym} {k : Kind} {s : Srt} {r : CRole}
    (h : collSymOf c f = some (k, s, r)) :
    ∃ g s₀, libCollOf g = some (k, s₀, r) ∧
      ((isHook f = true ∧ f = g ∧ s = s₀) ∨
       (isHook f = false ∧ ∃ kp, c.lookupParam f = some kp ∧ kp.impl = some g ∧ kp.sig.result = s)) := by
  unfold collSymOf at h
  split at h
  · rename_i hh; exact ⟨f, s, h, .inl ⟨hh, rfl, rfl⟩⟩
  · rename_i hh
    split at h
    · rename_i kp hkp
      obtain ⟨g, hg, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨⟨kd, s₀, r'⟩, hl, he⟩ := Option.map_eq_some_iff.mp h
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl, rfl⟩ := he
      exact ⟨g, s₀, hl, .inr ⟨by simpa using hh, kp, hkp, hg, rfl⟩⟩
    · cases h

theorem lib_hook_facts_cdp {g : Sym} {k : Kind} {s₀ : Srt} {r : CRole}
    (h : libCollOf g = some (k, s₀, r)) :
    isHook g = true ∧ (patternHooks.contains g || collPatternHooks.contains g) = true ∧
      silentKey g = false ∧ Semantics.rawArgHooks.contains g = true := by
  rcases libCollOf_nine_cdp h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem isHook_patHook_cdp {f : Sym} (h : patternHooks.contains f = true) : isHook f = true := by
  have := List.contains_iff_mem.mp h
  simp only [patternHooks, List.mem_cons, List.not_mem_nil, or_false] at this
  rcases this with rfl | rfl | rfl <;> rfl

/-- A collection symbol is a map pattern symbol or a collection pattern symbol. -/
theorem collSym_head_cdp {c : Semantics} {f : Sym} {k : Kind} {s : Srt} {r : CRole}
    (h : collSymOf c f = some (k, s, r)) :
    patternHooks.contains f = true ∨ c.isCollPat f = true := by
  obtain ⟨g, s₀, hl, hcase⟩ := collSym_lib_cdp h
  obtain ⟨-, hpc, -, -⟩ := lib_hook_facts_cdp hl
  rcases hcase with ⟨hh, rfl, -⟩ | ⟨hh, kp, hkp, hg, -⟩
  · cases hp : patternHooks.contains f with
    | true => exact .inl rfl
    | false =>
      refine .inr ?_
      rw [hp, Bool.false_or] at hpc
      unfold Semantics.isCollPat
      simp only [hp, hh, hpc, ↓reduceIte, Bool.not_false, Bool.and_self]
  · refine .inr ?_
    have hp : patternHooks.contains f = false := by
      cases hpf : patternHooks.contains f with
      | false => rfl
      | true => rw [isHook_patHook_cdp hpf] at hh; cases hh
    unfold Semantics.isCollPat
    simp only [hp, hh, hkp, hg]
    simpa using hpc

/-- A collection symbol's pattern denotes the value the symbol builds from its arguments'
values. -/
theorem patVal_coll_cdp {c : Semantics} {σ : Subst} {f : Sym} {k : Kind} {s : Srt} {r : CRole}
    {ps : List Term} {vs : List GroundTerm} {u : GroundTerm} (hct : c.isCtor f = false)
    (hcy : collSymOf c f = some (k, s, r)) (hs : PatVals c σ ps vs)
    (hv : c.collVal f vs = some u) : PatVal c σ (.app f ps) u := by
  rcases collSym_head_cdp hcy with hp | hp
  · refine .hook hp hs ?_
    have hh : isHook f = true := isHook_patHook_cdp hp
    unfold Semantics.collVal at hv
    simp only [hh, ↓reduceIte] at hv
    exact Option.join_eq_some_iff.mp hv
  · exact .coll hct hp hs hv

/-- What a collection symbol of `c` builds, from what the library's symbol builds: the same
collection at the symbol's sort, where that is sorted. -/
theorem collVal_lib_cdp {c : Semantics} {f : Sym} {k : Kind} {s : Srt} {r : CRole}
    (hcy : collSymOf c f = some (k, s, r)) :
    ∃ g s₀, libCollOf g = some (k, s₀, r) ∧ ∀ (ws : List GroundTerm) (u : GroundTerm)
      (K : CollKind) (its : List (List GroundTerm)), hook g ws = some (some u) →
      content u = some (K, s₀, its) → c.sortOf (u.withSort s) = some s →
      c.collVal f ws = some (u.withSort s) := by
  obtain ⟨g, s₀, hl, hcase⟩ := collSym_lib_cdp hcy
  refine ⟨g, s₀, hl, fun ws u K its hu hcu hsu => ?_⟩
  obtain ⟨-, -, hsk, hrc⟩ := lib_hook_facts_cdp hl
  rcases hcase with ⟨hh, rfl, rfl⟩ | ⟨hh, kp, hkp, hg, rfl⟩
  · have hw : u.withSort s = u := by
      cases u with
      | map s' es =>
        simp only [content, Option.some.injEq, Prod.mk.injEq] at hcu
        obtain ⟨-, rfl, -⟩ := hcu; rfl
      | set s' es =>
        simp only [content, Option.some.injEq, Prod.mk.injEq] at hcu
        obtain ⟨-, rfl, -⟩ := hcu; rfl
      | list s' es =>
        simp only [content, Option.some.injEq, Prod.mk.injEq] at hcu
        obtain ⟨-, rfl, -⟩ := hcu; rfl
      | _ => simp only [content] at hcu; cases hcu
    unfold Semantics.collVal
    simp only [hh, ↓reduceIte, hu, hw]; rfl
  · unfold Semantics.collVal
    simp only [hh, Bool.false_eq_true, ↓reduceIte]
    unfold Semantics.paramVal
    rw [hkp]; dsimp only; rw [hg]; dsimp only
    rw [Semantics.libArgs_coll c hrc, Semantics.hookRes_of_notKey hsk, hu]
    have hu' : u.asSort c.lib kp.sig.result = u.withSort kp.sig.result := by
      cases u with
      | dv b lit => simp only [content] at hcu; cases hcu
      | _ => rfl
    rw [show (some (some u)).join = some u from rfl, Option.map_some, hu', Faithful.filter_sorted hsu]

/-- The argument sorts of a collection's symbol of each role. -/
def roleArgs_cdp (K : CollSig) : CRole → List Srt
  | .unit => []
  | .elem => elemArgs K
  | .concat => [K.sort, K.sort]

theorem kindOf_inv_cdp {K : CollKind} {k : Kind} (h : kindOf K = some k) :
    (K = .map ∧ k = .map) ∨ (K = .set ∧ k = .set) ∨ (K = .list ∧ k = .list) := by
  cases K <;> simp [kindOf] at h <;> simp [h]

/-- The library collection's symbols are symbols of its kind, each of its role. -/
theorem builtin_role_cdp {K : CollKind} {k : Kind} {s₀ : Srt} {r : CRole} :
    (libCollOf (builtinColl K).unit = some (k, s₀, r) → kindOf K = some k ∧ r = .unit) ∧
    (libCollOf (builtinColl K).elem = some (k, s₀, r) → kindOf K = some k ∧ r = .elem) ∧
    (libCollOf (builtinColl K).concat = some (k, s₀, r) → kindOf K = some k ∧ r = .concat) := by
  have t1 : (match libCollOf (builtinColl K).unit with
      | some (k', _, r') => kindOf K == some k' && r' == CRole.unit | none => true) = true := by
    cases K <;> rfl
  have t2 : (match libCollOf (builtinColl K).elem with
      | some (k', _, r') => kindOf K == some k' && r' == CRole.elem | none => true) = true := by
    cases K <;> rfl
  have t3 : (match libCollOf (builtinColl K).concat with
      | some (k', _, r') => kindOf K == some k' && r' == CRole.concat | none => true) = true := by
    cases K <;> rfl
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · rw [h] at t1; simpa using t1
  · rw [h] at t2; simpa using t2
  · rw [h] at t3; simpa using t3

/-- **The signature of a collection symbol.** In a left side's context a collection symbol has
the sort `collSymOf` reads, that sort is a collection sort of the symbol's kind, and the symbol's
argument sorts are the collection's: none for the unit, the key and value sorts for the element,
the collection's sort twice for the concatenation. -/
theorem collSig_cdp {c : Semantics} (hmc : MatchCtxO c) (hcs : collsOK c = true) {f : Sym}
    {k : Kind} {s : Srt} {r : CRole} {sg : CtorSig} (hct : c.isCtor f = false)
    (hcy : collSymOf c f = some (k, s, r)) (hsg : lookupSig c.patCtxNF.heads f = some sg) :
    sg.result = s ∧ ∃ Ks, c.collOf s = some Ks ∧ kindOf Ks.kind = some k ∧
      sg.args = roleArgs_cdp Ks r := by
  obtain ⟨g, s₀, hl, hcase⟩ := collSym_lib_cdp hcy
  rcases hcase with ⟨hh, rfl, rfl⟩ | ⟨hh, kp, hkp, hg, rfl⟩
  · have hlk : lookupSig hookSigs f = some sg := by
      rcases collSym_head_cdp hcy with hp | hp
      · exact Det.patCtxNF_hook_lookup hmc hp hsg
      · rcases Det.patCtxNF_collPat_lookup hct hp hsg with ⟨-, h⟩ | ⟨h, -⟩
        · exact h
        · rw [hh] at h; cases h
    have hmem := libCollOf_cases_cdp hl
    simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hmem
    rcases hmem with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
    · rw [show lookupSig hookSigs mapUnit = some ⟨mapUnit, [], Srt.map⟩ by decide] at hlk
      cases hlk; exact ⟨rfl, builtinColl .map, rfl, rfl, rfl⟩
    · rw [show lookupSig hookSigs mapElem = some ⟨mapElem, [Srt.kitem, Srt.kitem], Srt.map⟩ by decide] at hlk
      cases hlk; exact ⟨rfl, builtinColl .map, rfl, rfl, rfl⟩
    · rw [show lookupSig hookSigs mapConcat = some ⟨mapConcat, [Srt.map, Srt.map], Srt.map⟩ by decide] at hlk
      cases hlk; exact ⟨rfl, builtinColl .map, rfl, rfl, rfl⟩
    · rw [show lookupSig hookSigs setUnit = some ⟨setUnit, [], Srt.set⟩ by decide] at hlk
      cases hlk; exact ⟨rfl, builtinColl .set, rfl, rfl, rfl⟩
    · rw [show lookupSig hookSigs setElem = some ⟨setElem, [Srt.kitem], Srt.set⟩ by decide] at hlk
      cases hlk; exact ⟨rfl, builtinColl .set, rfl, rfl, rfl⟩
    · rw [show lookupSig hookSigs setConcat = some ⟨setConcat, [Srt.set, Srt.set], Srt.set⟩ by decide] at hlk
      cases hlk; exact ⟨rfl, builtinColl .set, rfl, rfl, rfl⟩
    · rw [show lookupSig hookSigs listUnit = some ⟨listUnit, [], Srt.list⟩ by decide] at hlk
      cases hlk; exact ⟨rfl, builtinColl .list, rfl, rfl, rfl⟩
    · rw [show lookupSig hookSigs listElem = some ⟨listElem, [Srt.kitem], Srt.list⟩ by decide] at hlk
      cases hlk; exact ⟨rfl, builtinColl .list, rfl, rfl, rfl⟩
    · rw [show lookupSig hookSigs listConcat = some ⟨listConcat, [Srt.list, Srt.list], Srt.list⟩ by decide] at hlk
      cases hlk; exact ⟨rfl, builtinColl .list, rfl, rfl, rfl⟩
  · obtain ⟨-, hpc, -, -⟩ := lib_hook_facts_cdp hl
    have hci : collImpl kp = true := by unfold collImpl; rw [hg]; exact hpc
    have hp : c.isCollPat f = true := (collSym_head_cdp hcy).resolve_left fun hpf => by
      rw [isHook_patHook_cdp hpf] at hh; cases hh
    rcases Det.patCtxNF_collPat_lookup hct hp hsg with ⟨h, -⟩ | ⟨-, kp', hkp', rfl⟩
    · rw [hh] at h; cases h
    rw [hkp] at hkp'; cases hkp'
    have hname : kp.sig.name = f := by
      have := hkp
      rw [Semantics.lookupParam_eq] at this
      simpa using List.find?_some this
    obtain ⟨K, hK, hn⟩ := Faithful.collsOK_params hcs (Faithful.lookupParam_mem hkp) hci
    obtain ⟨hco, -, h1, h2, h3⟩ := Faithful.collSymsOK_spec (Faithful.collsOK_colls hcs hK)
    rw [hname] at hn
    rcases hn with rfl | rfl | rfl
    · rw [hkp] at h1; cases h1
      cases hg
      obtain ⟨hkd, rfl⟩ := builtin_role_cdp.1 hl
      exact ⟨rfl, K, hco, hkd, rfl⟩
    · rw [hkp] at h2; cases h2
      cases hg
      obtain ⟨hkd, rfl⟩ := builtin_role_cdp.2.1 hl
      exact ⟨rfl, K, hco, hkd, rfl⟩
    · rw [hkp] at h3; cases h3
      cases hg
      obtain ⟨hkd, rfl⟩ := builtin_role_cdp.2.2 hl
      exact ⟨rfl, K, hco, hkd, rfl⟩

/-! ## A collection value and its sub-collections -/

/-- An item of a collection value as `kore.k` writes it: a map's entry, a set's or a list's
element. -/
def encIt_cdp : List GroundTerm → T
  | [a, b] => .kv (enc a) (enc b)
  | [e] => .el (enc e)
  | _ => .bot

/-- The elements as `kore.k` holds them: a list's in order, a map's and a set's ordered by
`ckeyF`. -/
def ordK_cdp : Kind → List T → List T
  | .list, L => L
  | _, L => sortK L

/-- `v` is a value of the collection `Ks` of the sort `s`, of `kore.k`'s kind `k`, with the items
`its`, sorted in `c` and with literals `kore.k` has. -/
structure SubCtx_cdp (c : Semantics) (v : GroundTerm) (Ks : CollSig) (k : Kind) (s : Srt)
    (its : List (List GroundTerm)) : Prop where
  cont : content v = some (Ks.kind, s, its)
  sorted : c.sortOf v = some s
  coll : c.collOf s = some Ks
  kind : kindOf Ks.kind = some k
  lits : litsV v = true

theorem filterMap_pair_cdp : ∀ es : List (GroundTerm × GroundTerm),
    (es.map fun e => [e.1, e.2]).filterMap pairOf = es
  | [] => rfl
  | e :: es => by simp [pairOf, filterMap_pair_cdp es]

theorem filterMap_one_cdp : ∀ es : List GroundTerm, (es.map fun e => [e]).filterMap oneOf = es
  | [] => rfl
  | e :: es => by simp [oneOf, filterMap_one_cdp es]

theorem entriesOK_intro_cdp {c : Semantics} {ks vs : Srt} :
    ∀ {es : List (GroundTerm × GroundTerm)},
    (∀ e ∈ es, c.sortOf e.1 = some ks ∧ c.sortOf e.2 = some vs) → c.entriesOK ks vs es = true
  | [], _ => by simp [Semantics.entriesOK]
  | (a, b) :: es, h => by
    have h1 := h (a, b) (List.mem_cons_self ..)
    simp only [Semantics.entriesOK, Semantics.entryOK, Bool.and_eq_true, beq_iff_eq]
    exact ⟨h1, entriesOK_intro_cdp fun e he => h e (List.mem_cons_of_mem _ he)⟩

theorem sortsOf_const_cdp {c : Semantics} {a : Srt} : ∀ {es : List GroundTerm},
    (∀ e ∈ es, c.sortOf e = some a) → c.sortsOf es = some (List.replicate es.length a)
  | [], _ => by simp [Semantics.sortsOf]
  | e :: es, h => by
    have h1 := h e (List.mem_cons_self ..)
    have h2 := sortsOf_const_cdp (es := es) fun x hx => h x (List.mem_cons_of_mem _ hx)
    simp [Semantics.sortsOf, h1, h2, List.replicate_succ]

/-- The three forms of a collection value. -/
theorem SubCtx_cdp.shape {c : Semantics} {v : GroundTerm} {Ks : CollSig} {k : Kind} {s : Srt}
    {its : List (List GroundTerm)} (hx : SubCtx_cdp c v Ks k s its) :
    (∃ es vs, v = .map s es ∧ Ks.kind = .map ∧ k = .map ∧ its = es.map (fun e => [e.1, e.2]) ∧
        Ks.val = some vs ∧ keysSorted es = true ∧
        ∀ e ∈ es, (c.sortOf e.1 = some Ks.key ∧ c.sortOf e.2 = some vs) ∧
          litsV e.1 = true ∧ litsV e.2 = true) ∨
    (∃ es, v = .set s es ∧ Ks.kind = .set ∧ k = .set ∧ its = es.map (fun e => [e]) ∧
        elemsSorted es = true ∧ ∀ e ∈ es, c.sortOf e = some Ks.key ∧ litsV e = true) ∨
    (∃ es, v = .list s es ∧ Ks.kind = .list ∧ k = .list ∧ its = es.map (fun e => [e]) ∧
        ∀ e ∈ es, c.sortOf e = some Ks.key ∧ litsV e = true) := by
  obtain ⟨hc, hs, hK, hk, lv⟩ := hx
  cases v with
  | ctor f vs => simp only [content] at hc; cases hc
  | inj a b u => simp only [content] at hc; cases hc
  | dv s' l => simp only [content] at hc; cases hc
  | map s' es =>
    simp only [content, Option.some.injEq, Prod.mk.injEq] at hc
    obtain ⟨hkd, rfl, rfl⟩ := hc
    obtain ⟨K', vs, hK', hval, -, hent, -⟩ := c.sortOf_map_inv hs
    rw [hK] at hK'; cases hK'
    have hks := (CExec.content_canon (c := c) (w := .map s' es) rfl hs).2
    obtain ⟨es', hes', hmap⟩ := hks
    have : es = es' := CExec.map_inj_of (fun x y (h : [x.1, x.2] = [y.1, y.2]) => by
      simp only [List.cons.injEq, and_true] at h; exact Prod.ext h.1 h.2) hmap
    subst this
    rw [← hkd] at hk
    simp only [litsV, litsVE_iff] at lv
    refine .inl ⟨es, vs, rfl, hkd.symm, by simpa [kindOf] using hk.symm, rfl, hval, hes', fun e he =>
      ⟨entriesOK_mem_kel hent e he, lv e he⟩⟩
  | set s' es =>
    simp only [content, Option.some.injEq, Prod.mk.injEq] at hc
    obtain ⟨hkd, rfl, rfl⟩ := hc
    rw [← hkd] at hk
    simp only [litsV, litsVL_iff] at lv
    simp only [Semantics.sortOf, hK] at hs
    split at hs
    · rename_i K' ss hK' hss
      cases hK'
      split at hs
      · rename_i hcond
        simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at hcond
        refine .inr (.inl ⟨es, rfl, hkd.symm, by simpa [kindOf] using hk.symm, rfl, hcond.1.2, fun e he => ?_⟩)
        obtain ⟨t, ht, h'⟩ := sortsOf_mem_kel hss e he
        exact ⟨by rw [h', hcond.2 t ht], lv e he⟩
      · cases hs
    · cases hs
  | list s' es =>
    simp only [content, Option.some.injEq, Prod.mk.injEq] at hc
    obtain ⟨hkd, rfl, rfl⟩ := hc
    rw [← hkd] at hk
    simp only [litsV, litsVL_iff] at lv
    simp only [Semantics.sortOf, hK] at hs
    split at hs
    · rename_i K' ss hK' hss
      cases hK'
      split at hs
      · rename_i hcond
        simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at hcond
        refine .inr (.inr ⟨es, rfl, hkd.symm, by simpa [kindOf] using hk.symm, rfl, fun e he => ?_⟩)
        obtain ⟨t, ht, h'⟩ := sortsOf_mem_kel hss e he
        exact ⟨by rw [h', hcond.2 t ht], lv e he⟩
      · cases hs
    · cases hs

theorem subCtx_map_cdp {c : Semantics} {Ks : CollSig} {s vs : Srt}
    {es : List (GroundTerm × GroundTerm)} (hK : c.collOf s = some Ks) (hkd : Ks.kind = .map)
    (hval : Ks.val = some vs) (hks : keysSorted es = true)
    (he : ∀ e ∈ es, (c.sortOf e.1 = some Ks.key ∧ c.sortOf e.2 = some vs) ∧
      litsV e.1 = true ∧ litsV e.2 = true) :
    SubCtx_cdp c (.map s es) Ks .map s (es.map fun e => [e.1, e.2]) := by
  refine ⟨by rw [hkd]; rfl, ?_, hK, by rw [hkd]; rfl, ?_⟩
  · have := entriesOK_intro_cdp (c := c) fun e he' => (he e he').1
    simp [Semantics.sortOf, hK, hval, hkd, hks, this]
  · simp only [litsV, litsVE_iff]; exact fun e he' => (he e he').2

theorem subCtx_set_cdp {c : Semantics} {Ks : CollSig} {s : Srt} {es : List GroundTerm}
    (hK : c.collOf s = some Ks) (hkd : Ks.kind = .set) (hks : elemsSorted es = true)
    (he : ∀ e ∈ es, c.sortOf e = some Ks.key ∧ litsV e = true) :
    SubCtx_cdp c (.set s es) Ks .set s (es.map fun e => [e]) := by
  refine ⟨by rw [hkd]; rfl, ?_, hK, by rw [hkd]; rfl, ?_⟩
  · have := sortsOf_const_cdp (c := c) fun e he' => (he e he').1
    simp [Semantics.sortOf, hK, hkd, hks, this]
  · simp only [litsV, litsVL_iff]; exact fun e he' => (he e he').2

theorem subCtx_list_cdp {c : Semantics} {Ks : CollSig} {s : Srt} {es : List GroundTerm}
    (hK : c.collOf s = some Ks) (hkd : Ks.kind = .list)
    (he : ∀ e ∈ es, c.sortOf e = some Ks.key ∧ litsV e = true) :
    SubCtx_cdp c (.list s es) Ks .list s (es.map fun e => [e]) := by
  refine ⟨by rw [hkd]; rfl, ?_, hK, by rw [hkd]; rfl, ?_⟩
  · have := sortsOf_const_cdp (c := c) fun e he' => (he e he').1
    simp [Semantics.sortOf, hK, hkd, this]
  · simp only [litsV, litsVL_iff]; exact fun e he' => (he e he').2

section
variable {c : Semantics} {v : GroundTerm} {Ks : CollSig} {k : Kind} {s : Srt}
  {its : List (List GroundTerm)}

/-- The collection of some of the items of a collection value, in the value's order, is a value
of the same collection. -/
theorem SubCtx_cdp.sub (hx : SubCtx_cdp c v Ks k s its) {Y : List (List GroundTerm)}
    (hY : Y.Sublist its) : SubCtx_cdp c (build Ks.kind s Y) Ks k s Y := by
  rcases hx.shape with ⟨es, vs, rfl, hkd, rfl, rfl, hval, hks, he⟩ | ⟨es, rfl, hkd, rfl, rfl, hks, he⟩ |
    ⟨es, rfl, hkd, rfl, rfl, he⟩
  · obtain ⟨es', hs', rfl⟩ := List.sublist_map_iff.mp hY
    rw [hkd]
    simp only [build, filterMap_pair_cdp]
    exact subCtx_map_cdp hx.coll hkd hval (sorted_sublist hs' hks) fun e he' => he e (hs'.subset he')
  · obtain ⟨es', hs', rfl⟩ := List.sublist_map_iff.mp hY
    rw [hkd]
    simp only [build, filterMap_one_cdp]
    exact subCtx_set_cdp hx.coll hkd (elemsSorted_iff.mpr ((elemsSorted_iff.mp hks).sublist hs'))
      fun e he' => he e (hs'.subset he')
  · obtain ⟨es', hs', rfl⟩ := List.sublist_map_iff.mp hY
    rw [hkd]
    simp only [build, filterMap_one_cdp]
    exact subCtx_list_cdp hx.coll hkd fun e he' => he e (hs'.subset he')

/-- An item of a collection value has the sorts of the collection's element symbol. -/
theorem SubCtx_cdp.item (hx : SubCtx_cdp c v Ks k s its) {it : List GroundTerm} (hit : it ∈ its) :
    c.sortsOf it = some (elemArgs Ks) ∧ litsVL it = true ∧
      ((k = .map ∧ ∃ a b, it = [a, b]) ∨ (k ≠ .map ∧ ∃ e, it = [e])) := by
  rcases hx.shape with ⟨es, vs, rfl, hkd, rfl, rfl, hval, hks, he⟩ | ⟨es, rfl, hkd, rfl, rfl, hks, he⟩ |
    ⟨es, rfl, hkd, rfl, rfl, he⟩
  · obtain ⟨e, he', rfl⟩ := List.mem_map.mp hit
    obtain ⟨⟨h1, h2⟩, l1, l2⟩ := he e he'
    exact ⟨by simp [Semantics.sortsOf, h1, h2, elemArgs, hkd, valSort, hval], by simp [litsVL, l1, l2],
      .inl ⟨rfl, _, _, rfl⟩⟩
  · obtain ⟨e, he', rfl⟩ := List.mem_map.mp hit
    obtain ⟨h1, l1⟩ := he e he'
    exact ⟨by simp [Semantics.sortsOf, h1, elemArgs, hkd], by simp [litsVL, l1],
      .inr ⟨by decide, _, rfl⟩⟩
  · obtain ⟨e, he', rfl⟩ := List.mem_map.mp hit
    obtain ⟨h1, l1⟩ := he e he'
    exact ⟨by simp [Semantics.sortsOf, h1, elemArgs, hkd], by simp [litsVL, l1],
      .inr ⟨by decide, _, rfl⟩⟩

/-- The encoding of a collection value: its items' encodings, as `kore.k` holds them. -/
theorem SubCtx_cdp.enc_eq (hx : SubCtx_cdp c v Ks k s its) :
    enc v = .co k s (ordK_cdp k (its.map encIt_cdp)) := by
  rcases hx.shape with ⟨es, vs, rfl, hkd, rfl, rfl, hval, hks, he⟩ | ⟨es, rfl, hkd, rfl, rfl, hks, he⟩ |
    ⟨es, rfl, hkd, rfl, rfl, he⟩
  · simp only [enc, encKvs_eq_map, ordK_cdp, List.map_map]; rfl
  · simp only [enc, encEls_eq_map, ordK_cdp, List.map_map]; rfl
  · simp only [enc, encEls_eq_map, ordK_cdp, List.map_map]; rfl

theorem SubCtx_cdp.eq_build (hx : SubCtx_cdp c v Ks k s its) : build Ks.kind s its = v :=
  CExec.build_content hx.cont

/-- A map's and a set's items, as `kore.k` holds them, are strictly increasing by `ckeyF`. -/
theorem SubCtx_cdp.strict (hx : SubCtx_cdp c v Ks k s its) (hk : k ≠ .list) :
    (sortK (its.map encIt_cdp)).Pairwise fun a b => ckeyF a b = some (-1) := by
  have := enc_canonical hx.sorted hx.lits
  rw [hx.enc_eq] at this
  simp only [Canon] at this
  have h := this.1 hk
  cases k with
  | list => exact absurd rfl hk
  | map => exact h
  | set => exact h

end

theorem ckeyF_asym_cdp {a b : T} (h1 : ckeyF a b = some (-1)) (h2 : ckeyF b a = some (-1)) :
    False := by
  unfold ckeyF at h1
  split at h1
  · simp only [ckeyF, Option.some.injEq] at h1 h2
    rw [cmpF_swap] at h2; omega
  · simp only [ckeyF, Option.some.injEq] at h1 h2
    rw [cmpF_swap] at h2; omega
  · cases h1

/-- `Y` is the sub-collection of the items `g` of a collection with the items `its`: the items
themselves for a list, and for a map or a set those items in the collection's order. -/
def CanonOf_cdp (K : CollKind) (its g Y : List (List GroundTerm)) : Prop :=
  Y.Sublist its ∧ match K with
    | .list => Y = g
    | _ => Y.Perm g

theorem sublist_perm_pull_cdp {α : Type} {Y a : List α} (h : Y.Perm a) :
    ∀ {a' : List α}, a'.Sublist a → ∃ Y' : List α, Y'.Perm a' ∧ Y'.Sublist Y := by
  induction h with
  | nil => intro a' ha; exact ⟨a', .refl _, ha⟩
  | cons x _ ih =>
    intro a' ha
    rcases List.sublist_cons_iff.mp ha with h | ⟨r, rfl, h⟩
    · obtain ⟨Y', h1, h2⟩ := ih h
      exact ⟨Y', h1, h2.trans (List.sublist_cons_self ..)⟩
    · obtain ⟨Y', h1, h2⟩ := ih h
      exact ⟨x :: Y', h1.cons x, h2.cons_cons x⟩
  | swap x y l =>
    intro a' ha
    rcases List.sublist_cons_iff.mp ha with h | ⟨r, rfl, h⟩
    · rcases List.sublist_cons_iff.mp h with h' | ⟨r, rfl, h'⟩
      · exact ⟨a', .refl _, (h'.trans (List.sublist_cons_self ..)).trans (List.sublist_cons_self ..)⟩
      · exact ⟨y :: r, .refl _, (h'.trans (List.sublist_cons_self x l)).cons_cons y⟩
    · rcases List.sublist_cons_iff.mp h with h' | ⟨r', rfl, h'⟩
      · exact ⟨x :: r, .refl _, (h'.cons_cons x).trans (List.sublist_cons_self ..)⟩
      · exact ⟨y :: x :: r', .swap x y r', (h'.cons_cons x).cons_cons y⟩
  | trans _ _ ih₁ ih₂ =>
    intro a' ha
    obtain ⟨M', h1, h2⟩ := ih₂ ha
    obtain ⟨Y', h3, h4⟩ := ih₁ h2
    exact ⟨Y', h3.trans h1, h4⟩

/-- `Y` is made of `Ya` and `Yb`: in order for a list, whatever the order for a map or a set. -/
def Comb_cdp (K : CollKind) (Y Ya Yb : List (List GroundTerm)) : Prop :=
  match K with
  | .list => Y = Ya ++ Yb
  | _ => Y.Perm (Ya ++ Yb)

/-- The sub-collection of two stretches of items is made of the sub-collections of each. -/
theorem CanonOf_cdp.split {K : CollKind} {its a b Y : List (List GroundTerm)}
    (h : CanonOf_cdp K its (a ++ b) Y) :
    ∃ Ya Yb, CanonOf_cdp K its a Ya ∧ CanonOf_cdp K its b Yb ∧ Comb_cdp K Y Ya Yb := by
  obtain ⟨hs, hm⟩ := h
  have key : Y.Perm (a ++ b) → ∃ Ya Yb, (Ya.Sublist its ∧ Ya.Perm a) ∧ (Yb.Sublist its ∧ Yb.Perm b) ∧
      Y.Perm (Ya ++ Yb) := fun hm => by
    obtain ⟨Ya, h1, h2⟩ := sublist_perm_pull_cdp hm (List.sublist_append_left a b)
    obtain ⟨Yb, h3, h4⟩ := sublist_perm_pull_cdp hm (List.sublist_append_right a b)
    exact ⟨Ya, Yb, ⟨h2.trans hs, h1⟩, ⟨h4.trans hs, h3⟩, hm.trans (h1.append h3).symm⟩
  cases K with
  | list =>
    have hm : Y = a ++ b := hm
    subst hm
    exact ⟨a, b, ⟨(List.sublist_append_left a b).trans hs, rfl⟩,
      ⟨(List.sublist_append_right a b).trans hs, rfl⟩, rfl⟩
  | map => exact key hm
  | set => exact key hm
  | rangeMap => exact key hm

/-- **A sub-collection's encoding.** The encoding of the sub-collection of the items `g` holds
the items' encodings: in `g`'s order for a list, and for a map or a set as a stretch of the
collection's elements in `kore.k`'s order gives them. -/
theorem SubCtx_cdp.frame {c : Semantics} {v : GroundTerm} {Ks : CollSig} {k : Kind} {s : Srt}
    {its : List (List GroundTerm)} (hx : SubCtx_cdp c v Ks k s its) {Y g : List (List GroundTerm)}
    (hY : CanonOf_cdp Ks.kind its g Y) {rest : List T} (hg : g.map encIt_cdp = rest)
    (hr : k ≠ .list → rest.Sublist (sortK (its.map encIt_cdp))) :
    enc (build Ks.kind s Y) = .co k s rest := by
  have hx' := hx.sub hY.1
  rw [hx'.enc_eq]
  congr 1
  obtain ⟨-, hm⟩ := hY
  have key : k ≠ .list → Y.Perm g → sortK (Y.map encIt_cdp) = rest := fun hk hp =>
    perm_pairwise_eq_cdp (fun _ _ => ckeyF_asym_cdp) (hx'.strict hk) ((hx.strict hk).sublist (hr hk))
      ((sortK_perm _).trans (hg ▸ hp.map encIt_cdp))
  rcases kindOf_inv_cdp hx.kind with ⟨h1, rfl⟩ | ⟨h1, rfl⟩ | ⟨h1, rfl⟩ <;> rw [h1] at hm
  · exact key (by decide) hm
  · exact key (by decide) hm
  · have hm : Y = g := hm
    rw [hm]; exact hg

/-! ## The values the collection symbols build -/

theorem kindOf_map_cdp {K : CollKind} (h : kindOf K = some .map) : K = .map := by
  cases K <;> first | rfl | cases h
theorem kindOf_set_cdp {K : CollKind} (h : kindOf K = some .set) : K = .set := by
  cases K <;> first | rfl | cases h
theorem kindOf_list_cdp {K : CollKind} (h : kindOf K = some .list) : K = .list := by
  cases K <;> first | rfl | cases h

section
variable {c : Semantics} {f : Sym} {k : Kind} {s : Srt} {Ks : CollSig}

/-- The unit symbol builds the empty collection. -/
theorem collVal_unit_cdp (hcy : collSymOf c f = some (k, s, .unit)) (hk : kindOf Ks.kind = some k)
    (hs : c.sortOf (build Ks.kind s []) = some s) : c.collVal f [] = some (build Ks.kind s []) := by
  obtain ⟨g, s₀, hl, hval⟩ := collVal_lib_cdp hcy
  have hmem := libCollOf_cases_cdp hl
  simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hmem
  rcases hmem with ⟨rfl, rfl, rfl, -⟩ | ⟨-, -, -, ⟨⟩⟩ | ⟨-, -, -, ⟨⟩⟩ | ⟨rfl, rfl, rfl, -⟩ |
    ⟨-, -, -, ⟨⟩⟩ | ⟨-, -, -, ⟨⟩⟩ | ⟨rfl, rfl, rfl, -⟩ | ⟨-, -, -, ⟨⟩⟩ | ⟨-, -, -, ⟨⟩⟩
  · rw [kindOf_map_cdp hk] at hs ⊢
    exact hval [] (.map Srt.map []) .map [] rfl rfl hs
  · rw [kindOf_set_cdp hk] at hs ⊢
    exact hval [] (.set Srt.set []) .set [] rfl rfl hs
  · rw [kindOf_list_cdp hk] at hs ⊢
    exact hval [] (.list Srt.list []) .list [] rfl rfl hs

/-- The element symbol builds the collection of the one item its arguments are. -/
theorem collVal_elem_cdp (hcy : collSymOf c f = some (k, s, .elem)) (hk : kindOf Ks.kind = some k)
    {it : List GroundTerm} (hit : (k = .map ∧ ∃ a b, it = [a, b]) ∨ (k ≠ .map ∧ ∃ e, it = [e]))
    (hs : c.sortOf (build Ks.kind s [it]) = some s) :
    c.collVal f it = some (build Ks.kind s [it]) := by
  obtain ⟨g, s₀, hl, hval⟩ := collVal_lib_cdp hcy
  have hmem := libCollOf_cases_cdp hl
  simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hmem
  rcases hmem with ⟨-, -, -, ⟨⟩⟩ | ⟨rfl, rfl, rfl, -⟩ | ⟨-, -, -, ⟨⟩⟩ | ⟨-, -, -, ⟨⟩⟩ |
    ⟨rfl, rfl, rfl, -⟩ | ⟨-, -, -, ⟨⟩⟩ | ⟨-, -, -, ⟨⟩⟩ | ⟨rfl, rfl, rfl, -⟩ | ⟨-, -, -, ⟨⟩⟩
  · rw [kindOf_map_cdp hk] at hs ⊢
    rcases hit with ⟨-, a, b, rfl⟩ | ⟨h, -⟩
    · exact hval [a, b] (.map Srt.map [(a, b)]) .map [[a, b]] rfl rfl hs
    · exact absurd rfl h
  · rw [kindOf_set_cdp hk] at hs ⊢
    rcases hit with ⟨h, -⟩ | ⟨-, e, rfl⟩
    · cases h
    · exact hval [e] (.set Srt.set [e]) .set [[e]] rfl rfl hs
  · rw [kindOf_list_cdp hk] at hs ⊢
    rcases hit with ⟨h, -⟩ | ⟨-, e, rfl⟩
    · cases h
    · exact hval [e] (.list Srt.list [e]) .list [[e]] rfl rfl hs

/-- **The concatenation of two sub-collections.** At the sub-collections of two stretches of the
items of a collection value, the concatenation symbol builds the sub-collection of both: a list's
in order, a map's and a set's whatever the order, since the items are apart. -/
theorem collVal_concat_cdp (hcy : collSymOf c f = some (k, s, .concat))
    (hk : kindOf Ks.kind = some k) {its Ya Yb Y : List (List GroundTerm)}
    (hci : CanonI Ks.kind its) (ha : Ya.Sublist its) (hb : Yb.Sublist its) (hY : Y.Sublist its)
    (hc : Comb_cdp Ks.kind Y Ya Yb)
    (hs : c.sortOf (build Ks.kind s Y) = some s) :
    c.collVal f [build Ks.kind s Ya, build Ks.kind s Yb] = some (build Ks.kind s Y) := by
  obtain ⟨g, s₀, hl, hval⟩ := collVal_lib_cdp hcy
  have hmem := libCollOf_cases_cdp hl
  simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hmem
  rcases hmem with ⟨-, -, -, ⟨⟩⟩ | ⟨-, -, -, ⟨⟩⟩ | ⟨rfl, rfl, rfl, -⟩ | ⟨-, -, -, ⟨⟩⟩ |
    ⟨-, -, -, ⟨⟩⟩ | ⟨rfl, rfl, rfl, -⟩ | ⟨-, -, -, ⟨⟩⟩ | ⟨-, -, -, ⟨⟩⟩ | ⟨rfl, rfl, rfl, -⟩
  · rw [kindOf_map_cdp hk] at hs hc hci ⊢
    have hc : Y.Perm (Ya ++ Yb) := hc
    obtain ⟨es, hes, rfl⟩ := hci
    obtain ⟨ea, hsa, rfl⟩ := List.sublist_map_iff.mp ha
    obtain ⟨eb, hsb, rfl⟩ := List.sublist_map_iff.mp hb
    obtain ⟨ey, hsy, rfl⟩ := List.sublist_map_iff.mp hY
    simp only [build, filterMap_pair_cdp] at hs ⊢
    have hp : ey.Perm (ea ++ eb) := by
      have := hc.filterMap pairOf
      simpa only [List.filterMap_append, filterMap_pair_cdp] using this
    have hey := sorted_sublist hsy hes
    have hap : KeysApart (ea ++ eb) := (sorted_apart hey).perm hp
    obtain ⟨hapa, -, hcross⟩ := List.pairwise_append.mp hap
    obtain ⟨m, hm, hmem⟩ := union_exists hapa hcross
    have hms := union_sorted (sorted_sublist hsb hes) hm
    have : m = ey := entries_canon hms hey fun e => by rw [hmem, hp.mem_iff, List.mem_append]
    subst this
    exact hval [.map s ea, .map s eb] (.map Srt.map m) .map (m.map fun e => [e.1, e.2])
      (by rw [Exec.hook_concat_eq]; simp only [hm]; rfl) rfl hs
  · rw [kindOf_set_cdp hk] at hs hc hci ⊢
    have hc : Y.Perm (Ya ++ Yb) := hc
    obtain ⟨es, hes, rfl⟩ := hci
    obtain ⟨ea, hsa, rfl⟩ := List.sublist_map_iff.mp ha
    obtain ⟨eb, hsb, rfl⟩ := List.sublist_map_iff.mp hb
    obtain ⟨ey, hsy, rfl⟩ := List.sublist_map_iff.mp hY
    simp only [build, filterMap_one_cdp] at hs ⊢
    have hp : ey.Perm (ea ++ eb) := by
      have := hc.filterMap oneOf
      simpa only [List.filterMap_append, filterMap_one_cdp] using this
    have hey : elemsSorted ey = true := elemsSorted_iff.mpr ((elemsSorted_iff.mp hes).sublist hsy)
    have heb : elemsSorted eb = true := elemsSorted_iff.mpr ((elemsSorted_iff.mp hes).sublist hsb)
    have hnd : (ea ++ eb).Nodup := hp.nodup_iff.mp (CExec.nodup_of_elemsSorted hey)
    have hdis : ea.all (fun x => !memS x eb) = true := by
      rw [List.all_eq_true]
      intro x hx
      rw [Bool.not_eq_true', Bool.eq_false_iff, ne_eq, KCore.Set.memS_iff]
      intro hx'
      exact (List.nodup_append.mp hnd).2.2 x hx x hx' rfl
    have : unionS ea eb = ey := KCore.Set.ext (KCore.Set.union_canon heb) hey fun x => by
      rw [KCore.Set.mem_union, hp.mem_iff, List.mem_append]
    exact hval [.set s ea, .set s eb] (.set Srt.set ey) .set (ey.map fun e => [e])
      (by rw [Exec.hook_setConcat_eq]; simp only [concatS, hdis, ↓reduceIte, this]; rfl) rfl hs
  · rw [kindOf_list_cdp hk] at hs hc ⊢
    have hc : Y = Ya ++ Yb := hc
    subst hc
    simp only [build, List.filterMap_append] at hs ⊢
    exact hval [.list s (Ya.filterMap oneOf), .list s (Yb.filterMap oneOf)]
      (.list Srt.list (Ya.filterMap oneOf ++ Yb.filterMap oneOf)) .list
      ((Ya.filterMap oneOf ++ Yb.filterMap oneOf).map fun e => [e])
      (by rw [Exec.hook_listConcat_eq]) rfl hs

end

/-! ## The items each part of a collection pattern takes -/

/-- What a part takes of the items of a collection value: an element part one item, which it is;
any other part the sub-collection of the items it takes. -/
def PartDen_cdp (S : List (Int × Int)) (B : Bind) (K : CollKind) (s : Srt)
    (its : List (List GroundTerm)) (p : T) (g : List (List GroundTerm)) : Prop :=
  if isElemT p = true then ∃ it, g = [it] ∧ DenF S B p (encIt_cdp it)
  else ∀ Y, CanonOf_cdp K its g Y → DenF S B p (enc (build K s Y))

/-- The same of the elements of the value's encoding `E`: an element part one element, which it
is; any other part the collection of the elements it takes, for a map or a set a stretch of
`E`. -/
def TakesE_cdp (S : List (Int × Int)) (B : Bind) (k : Kind) (s : Int) (E : List T) (p : T)
    (ch : List T) : Prop :=
  if isElemT p = true then ∃ e, ch = [e] ∧ DenF S B p e
  else DenF S B p (.co k s ch) ∧ (k ≠ .list → ch.Sublist E)

theorem partDen_of_takes_cdp {c : Semantics} {v : GroundTerm} {Ks : CollSig} {k : Kind} {s : Srt}
    {its : List (List GroundTerm)} (hx : SubCtx_cdp c v Ks k s its) {S : List (Int × Int)}
    {B : Bind} {p : T} {g : List (List GroundTerm)}
    (h : TakesE_cdp S B k s (sortK (its.map encIt_cdp)) p (g.map encIt_cdp)) :
    PartDen_cdp S B Ks.kind s its p g := by
  unfold TakesE_cdp at h
  unfold PartDen_cdp
  split
  · rename_i hp
    simp only [hp, ↓reduceIte] at h
    obtain ⟨e, he, hd⟩ := h
    match g, he with
    | [it], he =>
      simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at he
      exact ⟨it, rfl, he ▸ hd⟩
  · rename_i hp
    simp only [hp] at h
    intro Y hY
    rw [hx.frame hY rfl h.2]
    exact h.1

theorem chunks_ground_cdp : ∀ (chT : List (T × List T)) (L : List (List GroundTerm)),
    chT.flatMap (·.2) = L.map encIt_cdp →
    ∃ ch : List (T × List (List GroundTerm)),
      ch.map (fun x => (x.1, x.2.map encIt_cdp)) = chT ∧ ch.flatMap (·.2) = L
  | [], L, h => by
    have : L = [] := by simpa using h.symm
    exact ⟨[], rfl, by simp [this]⟩
  | (p, t) :: chT, L, h => by
    rw [List.flatMap_cons] at h
    obtain ⟨L₁, L₂, rfl, h1, h2⟩ := List.map_eq_append_iff.mp h.symm
    obtain ⟨ch, h3, h4⟩ := chunks_ground_cdp chT L₂ h2.symm
    exact ⟨(p, L₁) :: ch, by simp [h1, h3], by simp [h4]⟩

/-- The parts of a `Map` or `Set` pattern in the pattern's order, from its element parts in
order with the elements they take and the elements its other part takes. -/
theorem assign_cdp {S : List (Int × Int)} {B : Bind} {k : Kind} {s : Int} {E rest : List T}
    (hr : k ≠ .list → rest.Sublist E) : ∀ (ps picked : List T),
    DensF S B (ps.filter isElemT) picked →
    (∀ p ∈ ps, isElemT p = false → DenF S B p (.co k s rest)) →
    ∃ chT : List (T × List T), chT.map (·.1) = ps ∧ (∀ x ∈ chT, TakesE_cdp S B k s E x.1 x.2) ∧
      (chT.flatMap (·.2)).Perm (picked ++ (ps.filter (!isElemT ·)).flatMap fun _ => rest)
  | [], picked, hd, _ => by
    simp only [List.filter_nil] at hd
    cases hd
    exact ⟨[], rfl, (fun _ hx => nomatch hx), by simp⟩
  | p :: ps, picked, hd, hf => by
    cases hp : isElemT p with
    | true =>
      rw [List.filter_cons_of_pos hp] at hd
      cases hd with
      | cons h hs =>
        rename_i e picked'
        obtain ⟨chT, h1, h2, h3⟩ := assign_cdp hr ps picked' hs
          fun q hq => hf q (List.mem_cons_of_mem _ hq)
        refine ⟨(p, [e]) :: chT, by simp [h1], fun x hx => ?_, ?_⟩
        · rcases List.mem_cons.mp hx with rfl | hx
          · unfold TakesE_cdp; simp only [hp, ↓reduceIte]; exact ⟨e, rfl, h⟩
          · exact h2 x hx
        · have hfil : (p :: ps).filter (!isElemT ·) = ps.filter (!isElemT ·) :=
            List.filter_cons_of_neg (by simp [hp])
          rw [hfil]
          simpa using h3.cons e
    | false =>
      rw [List.filter_cons_of_neg (by simp [hp])] at hd
      obtain ⟨chT, h1, h2, h3⟩ := assign_cdp hr ps picked hd
        fun q hq => hf q (List.mem_cons_of_mem _ hq)
      refine ⟨(p, rest) :: chT, by simp [h1], fun x hx => ?_, ?_⟩
      · rcases List.mem_cons.mp hx with rfl | hx
        · unfold TakesE_cdp; simp only [hp, Bool.false_eq_true, ↓reduceIte]
          exact ⟨hf _ (List.mem_cons_self ..) hp, hr⟩
        · exact h2 x hx
      · have hfil : (p :: ps).filter (!isElemT ·) = p :: ps.filter (!isElemT ·) :=
          List.filter_cons_of_pos (by simp [hp])
        rw [hfil, List.flatMap_cons, List.flatMap_cons]
        refine (h3.append_left rest).trans ?_
        rw [← List.append_assoc, ← List.append_assoc]
        exact List.Perm.append_right _ List.perm_append_comm

theorem orderParts_split_cdp {ps els : List T} {f : T}
    (h : ps.filter isElemT ++ ps.filter (!isElemT ·) = els ++ [f])
    (he : ∀ p ∈ els, isElemT p = true) (hf : isElemT f = false) :
    ps.filter isElemT = els ∧ ps.filter (!isElemT ·) = [f] := by
  rcases List.append_eq_append_iff.mp h with ⟨as, h1, h2⟩ | ⟨bs, h1, h2⟩
  · cases as with
    | nil => exact ⟨by simpa using h1.symm, by simpa using h2⟩
    | cons x as =>
      have hx1 : isElemT x = true := he x (by rw [h1]; simp)
      have hx2 : x ∈ ps.filter (!isElemT ·) := by rw [h2]; simp
      have := (List.mem_filter.mp hx2).2
      rw [hx1] at this; cases this
  · cases bs with
    | nil => exact ⟨by simpa using h1, by simpa using h2.symm⟩
    | cons y bs =>
      simp only [List.cons_append, List.cons.injEq] at h2
      obtain ⟨rfl, -⟩ := h2
      have : f ∈ ps.filter isElemT := by rw [h1]; simp
      have := (List.mem_filter.mp this).2
      rw [hf] at this; cases this

/-- **The parts of a collection pattern and the items of the value.** Where the parts of a
collection pattern, in `kore.k`'s order, take the elements of a collection value's encoding, each
part of the pattern, in the pattern's order, takes items of the value, and together they take
every item: in order for a list, each once for a map or a set. -/
theorem parts_ground_cdp {c : Semantics} {v : GroundTerm} {Ks : CollSig} {k : Kind} {s : Srt}
    {its : List (List GroundTerm)} (hx : SubCtx_cdp c v Ks k s its) {S : List (Int × Int)}
    {B : Bind} {parts : List T}
    (h : DenColF S B k s (orderParts k parts) (ordK_cdp k (its.map encIt_cdp))) :
    ∃ ch : List (T × List (List GroundTerm)), ch.map (·.1) = parts ∧
      (∀ x ∈ ch, PartDen_cdp S B Ks.kind s its x.1 x.2) ∧
      CanonOf_cdp Ks.kind its (ch.flatMap (·.2)) its := by
  -- from the parts with the elements they take to the parts with the items they take
  have ground : ∀ (chT : List (T × List T)) (L : List (List GroundTerm)), chT.map (·.1) = parts →
      (∀ x ∈ chT, TakesE_cdp S B k s (sortK (its.map encIt_cdp)) x.1 x.2) →
      chT.flatMap (·.2) = L.map encIt_cdp →
      ∃ ch : List (T × List (List GroundTerm)), ch.map (·.1) = parts ∧
        (∀ x ∈ ch, PartDen_cdp S B Ks.kind s its x.1 x.2) ∧ ch.flatMap (·.2) = L := by
    intro chT L h1 h2 h3
    obtain ⟨ch, h4, h5⟩ := chunks_ground_cdp chT L h3
    refine ⟨ch, ?_, fun x hx' => ?_, h5⟩
    · rw [← h1, ← h4, List.map_map]; rfl
    · refine partDen_of_takes_cdp hx ?_
      exact h2 (x.1, x.2.map encIt_cdp) (by rw [← h4]; exact List.mem_map_of_mem hx')
  by_cases hk : k = .list
  · subst hk
    have hkd := kindOf_list_cdp hx.kind
    have hop : orderParts .list parts = parts := by simp [orderParts]
    rw [hop] at h
    obtain ⟨chs, h1, h2, h3⟩ := h.chunks_list rfl
    obtain ⟨ch, g1, g2, g3⟩ := ground (parts.zip chs) its
      (List.map_fst_zip (by omega))
      (fun x hx' => by
        have := h3 x hx'
        unfold TakesF at this
        unfold TakesE_cdp
        split
        · rename_i hp; simp only [hp, ↓reduceIte] at this; exact this
        · rename_i hp; simp only [hp] at this; exact ⟨this, fun hn => absurd rfl hn⟩)
      (by rw [List.flatMap_def, List.map_snd_zip (by omega)]; exact h1)
    refine ⟨ch, g1, g2, List.Sublist.refl _, ?_⟩
    rw [hkd]; exact g3.symm
  · have hop : orderParts k parts = parts.filter isElemT ++ parts.filter (!isElemT ·) := by
      unfold orderParts
      have hb : (k == Kind.list) = false := by simpa using hk
      simp only [hb, Bool.false_eq_true, ↓reduceIte]
    have hE : ordK_cdp k (its.map encIt_cdp) = sortK (its.map encIt_cdp) := by
      cases k with
      | list => exact absurd rfl hk
      | _ => rfl
    rw [hop, hE] at h
    obtain ⟨picked, rest, hperm, hsub, hcase⟩ := h.chunks_coll hk
    have hfacts : DensF S B (parts.filter isElemT) picked ∧
        (∀ p ∈ parts, isElemT p = false → DenF S B p (.co k s rest)) ∧
        (parts.filter (!isElemT ·)).flatMap (fun _ => rest) = rest := by
      rcases hcase with ⟨hd, rfl, hall⟩ | ⟨els, f, heq, hels, hf, hd, hdf⟩
      · have hnil : parts.filter (!isElemT ·) = [] := by
          rw [List.filter_eq_nil_iff]
          intro p hp hn
          have := hall p (List.mem_append_right _ (List.mem_filter.mpr ⟨hp, hn⟩))
          simp [this] at hn
        rw [hnil, List.append_nil] at hd
        refine ⟨hd, fun p hp hn => ?_, by rw [hnil]; rfl⟩
        have : p ∈ parts.filter (!isElemT ·) := List.mem_filter.mpr ⟨hp, by simp [hn]⟩
        rw [hnil] at this; cases this
      · obtain ⟨h1, h2⟩ := orderParts_split_cdp heq hels hf
        refine ⟨h1 ▸ hd, fun p hp hn => ?_, by rw [h2]; simp⟩
        have : p ∈ parts.filter (!isElemT ·) := List.mem_filter.mpr ⟨hp, by simp [hn]⟩
        rw [h2, List.mem_singleton] at this
        rw [this]; exact hdf
    obtain ⟨hd, hfr, hflat⟩ := hfacts
    obtain ⟨chT, h1, h2, h3⟩ := assign_cdp (E := sortK (its.map encIt_cdp)) (fun _ => hsub) parts picked hd hfr
    rw [hflat] at h3
    obtain ⟨L, hL, hLm⟩ := perm_map_inv_cdp encIt_cdp ((h3.trans hperm).trans (sortK_perm _))
    obtain ⟨ch, g1, g2, g3⟩ := ground chT L h1 h2 hLm.symm
    refine ⟨ch, g1, g2, List.Sublist.refl _, ?_⟩
    rw [g3]
    rcases kindOf_inv_cdp hx.kind with ⟨h', -⟩ | ⟨h', -⟩ | ⟨-, h'⟩
    · rw [h']; exact hL.symm
    · rw [h']; exact hL.symm
    · exact absurd h' hk

/-! ## A substitution that states the match makes the pattern denote the value -/

theorem subCtx_of_cdp {c : Semantics} {v : GroundTerm} {s : Srt} {Ks : CollSig} {k : Kind}
    (hv : c.sortOf v = some s) (lv : litsV v = true) (hK : c.collOf s = some Ks)
    (hkd : kindOf Ks.kind = some k) {l : Kind} {e : Int} {E : List T} (hE : enc v = .co l e E) :
    ∃ its, SubCtx_cdp c v Ks k s its := by
  cases v with
  | ctor f vs => rw [enc_ctor_kmf] at hE; cases hE
  | inj a b u => rw [enc_inj_form_kmf] at hE; cases hE
  | dv s' lit =>
    rcases enc_dv_cases_kkc s' lit with ⟨i, h'⟩ | ⟨b, h'⟩ | ⟨x, y, h'⟩ | h' <;> rw [h'] at hE <;> cases hE
  | map s' es =>
    obtain ⟨rfl, -⟩ := CExec.content_canon (c := c) (w := .map s' es) rfl hv
    obtain ⟨K', vs, hK', -, hcond, -, -⟩ := c.sortOf_map_inv hv
    rw [hK] at hK'; cases hK'
    have hkm : Ks.kind = .map := by
      rcases kindOf_inv_cdp hkd with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
      · exact h
      · rw [h] at hcond; cases hcond
      · rw [h] at hcond; cases hcond
    exact ⟨_, ⟨by rw [hkm]; rfl, hv, hK, hkd, lv⟩⟩
  | set s' es =>
    obtain ⟨rfl, -⟩ := CExec.content_canon (c := c) (w := .set s' es) rfl hv
    obtain ⟨K', ss, hK', hks, -, -⟩ := sortOf_set_inv_kkc hv
    rw [hK] at hK'; cases hK'
    exact ⟨_, ⟨by rw [hks]; rfl, hv, hK, hkd, lv⟩⟩
  | list s' es =>
    obtain ⟨rfl, -⟩ := CExec.content_canon (c := c) (w := .list s' es) rfl hv
    obtain ⟨K', ss, hK', hks, -⟩ := sortOf_list_inv_kkc hv
    rw [hK] at hK'; cases hK'
    exact ⟨_, ⟨by rw [hks]; rfl, hv, hK, hkd, lv⟩⟩

theorem encIt_el_cdp {it : List GroundTerm} {x : T} (h : encIt_cdp it = .el x) :
    ∃ e, it = [e] ∧ x = enc e := by
  unfold encIt_cdp at h
  split at h
  · cases h
  · cases h; exact ⟨_, rfl, rfl⟩
  · cases h

theorem encIt_kv_cdp {it : List GroundTerm} {a b : T} (h : encIt_cdp it = .kv a b) :
    ∃ x y, it = [x, y] ∧ a = enc x ∧ b = enc y := by
  unfold encIt_cdp at h
  split at h
  · cases h; exact ⟨_, _, rfl, rfl, rfl⟩
  · cases h
  · cases h

theorem map_fst_single_cdp {α β : Type} {ch : List (α × β)} {q : α} (h : ch.map (·.1) = [q]) :
    ∃ g, ch = [(q, g)] := by
  match ch, h with
  | [(p, g)], h =>
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at h
    exact ⟨g, by rw [h]⟩

theorem collOf_sort_cdp {c : Semantics} {s : Srt} {Ks : CollSig} (h : c.collOf s = some Ks) :
    Ks.sort = s := by
  unfold Semantics.collOf at h
  simpa using List.find?_some h

/-- Every listed variable has, in `B`, the encoding of a value of its sort whose literals
`kore.k` has. -/
def VarsOK_cdp (c : Semantics) (vars : List Srt) (B : Bind) (is : List Nat) : Prop :=
  ∀ i ∈ is, ∃ (w : GroundTerm) (s : Srt), lookF (i : Int) B = some (enc w) ∧ vars[i]? = some s ∧
    c.sortOf w = some s ∧ litsV w = true

section
variable {c : Semantics} (hmc : MatchCtxO c) (hov : c.ovls = []) (hcs : collsOK c = true)
  {vars : List Srt} {B : Bind}
include hmc hov hcs
set_option linter.unusedSectionVars false

mutual
/-- **A substitution that states the match makes the pattern denote the value.** Where, under
`B`, the encoding of the pattern `p` is the encoding of a value `v` of `p`'s sort (`DenF`): `B`
gives every variable of `p` the encoding of a value of the variable's sort, and under every `σ`
that reads `B` the pattern denotes `v`. A collection pattern included: its parts take the items
of `v`, and the pattern denotes what its symbols build from what the parts denote. -/
theorem den_patVal : ∀ (p : Term) {q : T} {s : Srt} {v : GroundTerm},
    encTerm c p = some q → sortOfTerm c.patCtxNF vars p = some s → c.sortOf v = some s →
    litsV v = true → DenF (subsF c) B q (enc v) →
    VarsOK_cdp c vars B (varOccs p) ∧ ∀ σ, BindRep c vars B σ → PatVal c σ p v
  | .var i, q, s, v, hq, hp, hv, lv, hd => by
    rw [encTerm_var_kmf] at hq; cases hq
    have h1 := hd.vr_inv_cdp
    have hs := sortOfTerm_var.mp hp
    refine ⟨fun j hj => ?_, fun σ hσ => .var (hσ.lookup h1 hv lv)⟩
    simp only [varOccs, List.mem_singleton] at hj
    subst hj
    exact ⟨v, s, h1, hs, hv, lv⟩
  | .dv s' l, q, s, v, hq, hp, hv, lv, hd => by
    rw [encTerm_dv_kmf] at hq
    have he := hd.lit_inv_cdp hq
    have hl : litsV (.dv s' l) = true := by simp [litsV, hq]
    have : v = .dv s' l :=
      enc_inj hv (sortOf_dv_pat_kmf hp) lv hl (he.trans (enc_dv_of_encLit hq).symm)
    subst this
    exact ⟨fun j hj => by simp [varOccs] at hj, fun σ _ => .dv⟩
  | .inj a b p, q, s, v, hq, hp, hv, lv, hd => by
    rw [encTerm_inj_kmf] at hq
    obtain ⟨q', hq', rfl⟩ := Option.map_eq_some_iff.mp hq
    obtain ⟨hab, hp', rfl⟩ := sortOfTerm_inj.mp hp
    obtain ⟨c₁, e₁, t, hv', hcase⟩ := hd.ij_inv_cdp
    obtain ⟨a', b', u, rfl, rfl, rfl, rfl⟩ := enc_eq_ij_kmf hv'
    obtain ⟨ha'b', hu, hus, rfl⟩ := sortOf_inj_kel hv
    have lu : litsV u = true := by simpa [litsV] using lv
    rcases hcase with ⟨hac, hd'⟩ | ⟨hac, hle, hd'⟩
    · have : a = a' := Int.natCast_inj.mp hac
      subst this
      obtain ⟨h1, h2⟩ := den_patVal p hq' hp' hus lu hd'
      refine ⟨fun j hj => h1 j (by simpa [varOccs] using hj), fun σ hσ => ?_⟩
      have := PatVal.inj (a := a) (b := s) (h2 σ hσ)
      rwa [Det.injNormal_of_not_inj hu] at this
    · have hne : a' ≠ a := fun h => hac (by rw [h])
      rw [leqF_subsF hmc.trans] at hle
      simp only [Bool.or_eq_true, beq_iff_eq, hne, false_or] at hle
      have hw : c.sortOf (.inj a' a u) = some a := by
        simp [Semantics.sortOf, List.contains_iff_mem.mp hle, hu, hus]
      have lw : litsV (.inj a' a u) = true := by simpa [litsV] using lu
      rw [← enc_inj_form_kmf] at hd'
      obtain ⟨h1, h2⟩ := den_patVal p hq' hp' hw lw hd'
      exact ⟨fun j hj => h1 j (by simpa [varOccs] using hj),
        fun σ hσ => PatVal.inj (a := a) (b := s) (h2 σ hσ)⟩
  | .as p i, q, s, v, hq, hp, hv, lv, hd => by
    rw [encTerm_as_kmf] at hq
    obtain ⟨q', hq', rfl⟩ := Option.map_eq_some_iff.mp hq
    obtain ⟨hs, hp'⟩ := Exec.sortOfTerm_as hp
    obtain ⟨hd', hl⟩ := hd.as_inv_cdp
    obtain ⟨h1, h2⟩ := den_patVal p hq' hp' hv lv hd'
    refine ⟨fun j hj => ?_, fun σ hσ => .as (h2 σ hσ) (hσ.lookup hl hv lv)⟩
    simp only [varOccs, List.mem_append, List.mem_singleton] at hj
    rcases hj with hj | rfl
    · exact h1 j hj
    · exact ⟨v, s, hl, hs, hv, lv⟩
  | .app f ps, q, s, v, hq, hp, hv, lv, hd => by
    rw [encTerm_app_kmf] at hq
    rcases readApp_cases_cdp hq with ⟨qs, hqs, rfl, hf⟩ | ⟨hct, k, s', r, parts, hcy, hparts, rfl⟩ |
      ⟨qs, o, -, rfl | rfl⟩
    · obtain ⟨ts, hv', hds⟩ := hd.ap_inv_cdp
      obtain ⟨g, vs, rfl, hfg, rfl⟩ := enc_eq_ap_kmf hv'
      have : f = g := Int.natCast_inj.mp hfg
      subst this
      obtain ⟨hc, ss, hps, hvs⟩ := sortOf_ctor_pat_kmf hov hp hv hf
      have lvs : litsVL vs = true := by simpa [litsV] using lv
      obtain ⟨h1, h2⟩ := dens_patVals ps hqs hps hvs lvs hds
      exact ⟨fun j hj => h1 j (by simpa [varOccs] using hj), fun σ hσ => .ctor hc (h2 σ hσ)⟩
    · rw [hcy] at hparts
      have hparts' : encCollWith c encLit k s' r ps = some parts := hparts
      obtain ⟨sg, hsg, -, hs⟩ := sortOfTerm_app.mp hp
      obtain ⟨hres, Ks, hK, hkd, -⟩ := collSig_cdp hmc hcs hct hcy hsg
      have hss : s = s' := hs.trans hres
      subst hss
      obtain ⟨l, e, E, hE, hcol⟩ := hd.cb_inv_cdp
      obtain ⟨its, hx⟩ := subCtx_of_cdp hv lv hK hkd hE
      have hE' := hE.symm.trans hx.enc_eq
      cases hE'
      obtain ⟨ch, g1, g2, g3⟩ := parts_ground_cdp hx hcol
      have := denColl_patVal_cdp ps hct hcy hparts' hp hx g1 g2 g3
      rw [hx.eq_build] at this
      exact ⟨fun j hj => this.1 j (by simpa [varOccs] using hj), this.2⟩
    · exact hd.hk_inv_cdp.elim
    · exact hd.hk_inv_cdp.elim
  termination_by p => 3 * termSize p
  decreasing_by all_goals (first | omega | (simp only [termSize]; omega))
/-- The same of a list of patterns and a list of values of their sorts. -/
theorem dens_patVals : ∀ (ps : List Term) {qs : List T} {ss : List Srt} {vs : List GroundTerm},
    encTermsWith c encLit ps = some qs → sortsOfTerms c.patCtxNF vars ps = some ss →
    c.sortsOf vs = some ss → litsVL vs = true → DensF (subsF c) B qs (encTs vs) →
    VarsOK_cdp c vars B (varOccsList ps) ∧ ∀ σ, BindRep c vars B σ → PatVals c σ ps vs
  | [], qs, ss, vs, hq, hp, hv, _, _ => by
    cases sortsOfTerms_nil.mp hp
    cases Faithful.sortsOf_nil_eq hv
    exact ⟨fun j hj => by simp [varOccsList] at hj, fun σ _ => .nil⟩
  | p :: ps, qs, ss, vs, hq, hp, hv, lv, hd => by
    obtain ⟨q, qs', hq1, hq2, rfl⟩ := encTerms_cons_kmf c hq
    obtain ⟨s, ss', hp1, hp2, rfl⟩ := sortsOfTerms_cons.mp hp
    have hpos := Exec.termSize_pos p
    cases vs with
    | nil => simp [Semantics.sortsOf] at hv
    | cons v vs =>
      obtain ⟨s₁, ss₁, hv1, hv2, he⟩ := sortsOf_cons.mp hv
      cases he
      simp only [litsVL, Bool.and_eq_true] at lv
      rw [encTs_cons_kmf] at hd
      cases hd with
      | cons hd1 hd2 =>
        obtain ⟨h1, h2⟩ := den_patVal p hq1 hp1 hv1 lv.1 hd1
        obtain ⟨g1, g2⟩ := dens_patVals ps hq2 hp2 hv2 lv.2 hd2
        refine ⟨fun j hj => ?_, fun σ hσ => .cons (h2 σ hσ) (g2 σ hσ)⟩
        simp only [varOccsList, List.mem_append] at hj
        rcases hj with hj | hj
        · exact h1 j hj
        · exact g1 j hj
  termination_by ps => 3 * termSizeList ps + 1
  decreasing_by all_goals (first | omega | (simp only [termSizeList]; omega))
/-- The same of a collection symbol's application, at the sub-collection of the items its parts
take of a collection value. -/
theorem denColl_patVal_cdp : ∀ (ts : List Term) {f : Sym} {k : Kind} {s : Srt} {r : CRole}
    {parts : List T} {v : GroundTerm} {Ks : CollSig} {its : List (List GroundTerm)}
    {ch : List (T × List (List GroundTerm))} {Y : List (List GroundTerm)},
    c.isCtor f = false → collSymOf c f = some (k, s, r) →
    encCollWith c encLit k s r ts = some parts →
    sortOfTerm c.patCtxNF vars (.app f ts) = some s → SubCtx_cdp c v Ks k s its →
    ch.map (·.1) = parts → (∀ x ∈ ch, PartDen_cdp (subsF c) B Ks.kind s its x.1 x.2) →
    CanonOf_cdp Ks.kind its (ch.flatMap (·.2)) Y →
    VarsOK_cdp c vars B (varOccsList ts) ∧
      ∀ σ, BindRep c vars B σ → PatVal c σ (.app f ts) (build Ks.kind s Y)
  | ts, f, k, s, r, parts, v, Ks, its, ch, Y, hct, hcy, henc, hp, hx, hch, hden, hY => by
    obtain ⟨sg, hsg, hargs, -⟩ := sortOfTerm_app.mp hp
    obtain ⟨-, Ks', hK', -, hsargs⟩ := collSig_cdp hmc hcs hct hcy hsg
    rw [hx.coll] at hK'; cases hK'
    rw [hsargs] at hargs
    have hxY := hx.sub hY.1
    rcases encColl_cases_cdp henc with ⟨rfl, hts, rfl⟩ | ⟨rfl, qs, e, hqs, rfl, hsh⟩ |
      ⟨rfl, a, b, pa, pb, hts, hpa, hpb, rfl⟩
    · have hch' : ch = [] := by simpa using hch
      subst hch'
      have hYn : Y = [] := by
        obtain ⟨-, hm⟩ := hY
        rcases kindOf_inv_cdp hx.kind with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] at hm <;> simpa using hm
      subst hYn
      rw [hts]
      exact ⟨fun j hj => by simp [varOccsList] at hj,
        fun σ _ => patVal_coll_cdp hct hcy .nil (collVal_unit_cdp hcy hx.kind hxY.sorted)⟩
    · obtain ⟨g, rfl⟩ := map_fst_single_cdp hch
      have hd := hden (e, g) (by simp)
      have hel : isElemT e = true := by
        rcases hsh with ⟨-, p, -, rfl⟩ | ⟨-, p, q, -, rfl⟩ <;> rfl
      unfold PartDen_cdp at hd
      simp only [hel, ↓reduceIte] at hd
      obtain ⟨it, rfl, hde⟩ := hd
      have hYi : Y = [it] := by
        obtain ⟨-, hm⟩ := hY
        rcases kindOf_inv_cdp hx.kind with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] at hm <;> simpa using hm
      subst hYi
      have hit : it ∈ its := hY.1.subset (by simp)
      obtain ⟨hits, lits, hform⟩ := hx.item hit
      have hds : DensF (subsF c) B qs (encTs it) := by
        rcases hsh with ⟨-, p, rfl, rfl⟩ | ⟨-, p, q, rfl, rfl⟩
        · obtain ⟨x, hx1, hx2⟩ := hde.el_inv_cdp
          obtain ⟨e', rfl, rfl⟩ := encIt_el_cdp hx1
          rw [encTs_cons_kmf, encTs]
          exact .cons hx2 .nil
        · obtain ⟨a', v', hx1, hx2, hx3⟩ := hde.kv_inv_cdp
          obtain ⟨x, y, rfl, rfl, rfl⟩ := encIt_kv_cdp hx1
          rw [encTs_cons_kmf, encTs_cons_kmf, encTs]
          exact .cons hx2 (.cons hx3 .nil)
      obtain ⟨h1, h2⟩ := dens_patVals ts hqs hargs hits lits hds
      exact ⟨h1, fun σ hσ => patVal_coll_cdp hct hcy (h2 σ hσ)
        (collVal_elem_cdp hcy hx.kind hform hxY.sorted)⟩
    · have hsort := collOf_sort_cdp hx.coll
      rw [hts] at hargs
      obtain ⟨hsa, hsb⟩ := Det.sortsOfTerms_two hargs
      rw [hsort] at hsa hsb
      obtain ⟨cha, chb, rfl, hca, hcb⟩ := List.map_eq_append_iff.mp hch
      rw [List.flatMap_append] at hY
      obtain ⟨Ya, Yb, hYa, hYb, hcomb⟩ := hY.split
      have hsz : termSizeList ts = termSize a + termSize b := by rw [hts]; simp [termSizeList]
      have hpa' := Exec.termSize_pos a
      have hpb' := Exec.termSize_pos b
      obtain ⟨a1, a2⟩ := denPart_patVal_cdp a hpa hsa hx hca
        (fun x hx' => hden x (List.mem_append_left _ hx')) hYa
      obtain ⟨b1, b2⟩ := denPart_patVal_cdp b hpb hsb hx hcb
        (fun x hx' => hden x (List.mem_append_right _ hx')) hYb
      rw [hts]
      refine ⟨fun j hj => ?_, fun σ hσ => patVal_coll_cdp hct hcy (.cons (a2 σ hσ) (.cons (b2 σ hσ) .nil))
        (collVal_concat_cdp hcy hx.kind (CExec.content_canon hx.cont hx.sorted).2 hYa.1 hYb.1 hY.1
          hcomb hxY.sorted)⟩
      simp only [varOccsList, List.append_nil, List.mem_append] at hj
      rcases hj with hj | hj
      · exact a1 j hj
      · exact b1 j hj
  termination_by ts => 3 * termSizeList ts + 2
  decreasing_by all_goals (omega)
/-- The same of an argument of a concatenation: the parts of a nested construction of the same
collection, or the argument as one part. -/
theorem denPart_patVal_cdp : ∀ (a : Term) {k : Kind} {s : Srt} {parts : List T} {v : GroundTerm}
    {Ks : CollSig} {its : List (List GroundTerm)} {ch : List (T × List (List GroundTerm))}
    {Y : List (List GroundTerm)},
    encPartWith c encLit k s a = some parts → sortOfTerm c.patCtxNF vars a = some s →
    SubCtx_cdp c v Ks k s its → ch.map (·.1) = parts →
    (∀ x ∈ ch, PartDen_cdp (subsF c) B Ks.kind s its x.1 x.2) →
    CanonOf_cdp Ks.kind its (ch.flatMap (·.2)) Y →
    VarsOK_cdp c vars B (varOccs a) ∧ ∀ σ, BindRep c vars B σ → PatVal c σ a (build Ks.kind s Y)
  | a, k, s, parts, v, Ks, its, ch, Y, henc, hp, hx, hch, hden, hY => by
    rcases encPart_cases_cdp henc with ⟨f, ts, r, ha, hct, hcy, hc⟩ | ⟨q, hq, rfl⟩
    · have hsz : termSize a = termSizeList ts + 1 := by rw [ha]; simp [termSize]
      rw [ha] at hp
      have := denColl_patVal_cdp ts hct hcy hc hp hx hch hden hY
      rw [ha]
      exact ⟨fun j hj => this.1 j (by simpa [varOccs] using hj), this.2⟩
    · obtain ⟨g, rfl⟩ := map_fst_single_cdp hch
      have hd := hden (q, g) (by simp)
      unfold PartDen_cdp at hd
      simp only [encTerm_notElem_cdp hq, Bool.false_eq_true, ↓reduceIte] at hd
      have hY' : CanonOf_cdp Ks.kind its g Y := by
        rw [List.flatMap_cons, List.flatMap_nil, List.append_nil] at hY; exact hY
      have hxY := hx.sub hY.1
      exact den_patVal a hq hp hxY.sorted hxY.lits (hd Y hY')
  termination_by a => 3 * termSize a + 1
  decreasing_by all_goals (omega)
end

end

/-! ## `matchF` against `PatVal`, collections included -/

section
variable {c : Semantics} (hmc : MatchCtxO c) (hov : c.ovls = []) (hcs : collsOK c = true)
  {vars : List Srt}
include hmc hov hcs

/-- **`matchF` is sound, collection patterns included.** `matchF_sound`'s statement without
`noCb`: a substitution `B'` that `match` gives at the encoding of the pattern `p` and of a value
`v` of `p`'s sort, from `B`, extends `B`, binds every variable of `p`, holds encodings of values
of the variables' sorts where `B` does, and under every `σ` that reads `B'` the pattern denotes
`v`. -/
theorem matchF_col_sound {p : Term} {q : T} {s : Srt} {v : GroundTerm} {B B' : Bind} {M : Ms}
    (hq : encTerm c p = some q) (hp : sortOfTerm c.patCtxNF vars p = some s)
    (hv : c.sortOf v = some s) (lv : litsV v = true)
    (hm : matchF (subsF c) q (enc v) B = some M) (hB : B' ∈ M) :
    BindExt B B' ∧ (∀ i ∈ varOccs p, (lookF (i : Int) B').isSome = true) ∧
      (BindOK c vars B → BindOK c vars B') ∧ ∀ σ, BindRep c vars B' σ → PatVal c σ p v := by
  obtain ⟨h1, h2, h3⟩ := matchF_den (subsF c) q (enc v) hm hB
  obtain ⟨g1, g2⟩ := den_patVal hmc hov hcs p hq hp hv lv h2
  refine ⟨h1, fun i hi => ?_, fun hok e he => ?_, g2⟩
  · obtain ⟨w, s', hl, -⟩ := g1 i hi
    rw [hl]; rfl
  · rcases h3 e he with h | ⟨hl, hmem⟩
    · exact hok e h
    · obtain ⟨i, hi, hx⟩ := tvars_term_cdp c p hq e.1 hmem
      obtain ⟨w, s', hl', hs', hw, lw⟩ := g1 i hi
      rw [hx, hl'] at hl
      exact ⟨i, w, s', Prod.ext hx (Option.some.inj hl).symm, hs', hw, lw⟩

/-- `matchTs` is sound, collection patterns included: the same of a list of patterns and a list
of values of their sorts. -/
theorem matchTsF_col_sound {ps : List Term} {qs : List T} {ss : List Srt} {vs : List GroundTerm}
    {B B' : Bind} {M : Ms} (hq : encTermsWith c encLit ps = some qs)
    (hp : sortsOfTerms c.patCtxNF vars ps = some ss) (hv : c.sortsOf vs = some ss)
    (lv : litsVL vs = true) (hm : matchTsF (subsF c) qs (encTs vs) B = some M) (hB : B' ∈ M) :
    BindExt B B' ∧ (∀ i ∈ varOccsList ps, (lookF (i : Int) B').isSome = true) ∧
      (BindOK c vars B → BindOK c vars B') ∧ ∀ σ, BindRep c vars B' σ → PatVals c σ ps vs := by
  obtain ⟨h1, h2, h3⟩ := matchTsF_den (subsF c) qs (encTs vs) hm hB
  obtain ⟨g1, g2⟩ := dens_patVals hmc hov hcs ps hq hp hv lv h2
  refine ⟨h1, fun i hi => ?_, fun hok e he => ?_, g2⟩
  · obtain ⟨w, s', hl, -⟩ := g1 i hi
    rw [hl]; rfl
  · rcases h3 e he with h | ⟨hl, hmem⟩
    · exact hok e h
    · obtain ⟨i, hi, hx⟩ := tvars_terms_cdp c ps hq e.1 hmem
      obtain ⟨w, s', hl', hs', hw, lw⟩ := g1 i hi
      rw [hx, hl'] at hl
      exact ⟨i, w, s', Prod.ext hx (Option.some.inj hl).symm, hs', hw, lw⟩

/-- **The bindings are well sorted, collection patterns included** (`matchTsF_wellSorted` without
`noCbL`): a substitution `matchTs` gives from the empty one, at patterns that bind every variable,
is read by a `σ` that gives every variable a value of its sort and under which the patterns
denote the values. -/
theorem matchTsF_col_wellSorted {ps : List Term} {qs : List T} {ss : List Srt}
    {vs : List GroundTerm} {B' : Bind} {M : Ms} (hq : encTermsWith c encLit ps = some qs)
    (hp : sortsOfTerms c.patCtxNF vars ps = some ss) (hv : c.sortsOf vs = some ss)
    (lv : litsVL vs = true) (hb : binds vars.length (varOccsList ps) = true)
    (hm : matchTsF (subsF c) qs (encTs vs) [] = some M) (hB : B' ∈ M) :
    ∃ σ, BindRep c vars B' σ ∧ c.WellSorted vars σ ∧ PatVals c σ ps vs := by
  obtain ⟨-, h2, h3, h4⟩ := matchTsF_col_sound hmc hov hcs hq hp hv lv hm hB
  obtain ⟨σ, hσ⟩ := (h3 (bindOK_nil c vars)).rep
  refine ⟨σ, hσ, fun i s hs => ?_, h4 σ hσ⟩
  have hi : i < vars.length := by
    rcases Nat.lt_or_ge i vars.length with h | h
    · exact h
    · rw [List.getElem?_eq_none h] at hs; cases hs
  obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp (h2 i (Exec.binds_all hb i hi))
  obtain ⟨j, w, s', hij, h5, -, h6, h7, -⟩ := hσ _ _ ht
  have : i = j := Int.natCast_inj.mp hij
  subst this
  rw [hs] at h6; cases h6
  exact ⟨w, h5, h7⟩

/-- The same of one pattern (a rule's left side). -/
theorem matchF_col_wellSorted {p : Term} {q : T} {s : Srt} {v : GroundTerm} {B' : Bind} {M : Ms}
    (hq : encTerm c p = some q) (hp : sortOfTerm c.patCtxNF vars p = some s)
    (hv : c.sortOf v = some s) (lv : litsV v = true)
    (hb : binds vars.length (varOccs p) = true)
    (hm : matchF (subsF c) q (enc v) [] = some M) (hB : B' ∈ M) :
    ∃ σ, BindRep c vars B' σ ∧ c.WellSorted vars σ ∧ PatVal c σ p v := by
  obtain ⟨-, h2, h3, h4⟩ := matchF_col_sound hmc hov hcs hq hp hv lv hm hB
  obtain ⟨σ, hσ⟩ := (h3 (bindOK_nil c vars)).rep
  refine ⟨σ, hσ, fun i s hs => ?_, h4 σ hσ⟩
  have hi : i < vars.length := by
    rcases Nat.lt_or_ge i vars.length with h | h
    · exact h
    · rw [List.getElem?_eq_none h] at hs; cases hs
  obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp (h2 i (Exec.binds_all hb i hi))
  obtain ⟨j, w, s', hij, h5, -, h6, h7, -⟩ := hσ _ _ ht
  have : i = j := Int.natCast_inj.mp hij
  subst this
  rw [hs] at h6; cases h6
  exact ⟨w, h5, h7⟩

end

set_option smartUnfolding false in
/-- The collections' condition of `d₀ d` is that of `d`: it reads no interpretation. -/
theorem collsOK_d₀ (d : Semantics) : collsOK (d₀ d) = collsOK d := rfl


end KCore.KK
