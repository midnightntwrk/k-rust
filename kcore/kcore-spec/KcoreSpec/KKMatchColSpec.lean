import KcoreSpec.KKMatchFSpec

/-!
# What a substitution of `kore.k`'s `match` states, collections included

`DenF S B p a`: under the substitution `B`, the pattern form `p` is the `kore.k` term `a`, read
equation by equation of `match` and `matchCol`: a variable is what `B` gives it; a literal is
itself; an application is the same symbol at arguments its argument patterns are; an injection is
an injection from the same source at what its pattern is, or from a source below at what its
pattern is of the term injected into the pattern's source; an alias is what its pattern is, and
`B` gives its variable that term. A collection pattern is a collection, of any kind and sort, whose
elements its parts take (`DenColF`): an element part of a `Map` or a `Set` any one element, a
`List`'s the first; a last part that is no element the collection of the elements left, at the
pattern's kind and sort; a `List`'s part that is no element, with parts after it, the list of a
prefix.

`matchF_den`: every substitution `match` gives extends the given one, states this of the pattern
and the term, and holds, beyond the given one's entries, entries of the pattern's variables only,
each the one `look` finds. No sort is read and no semantics: the statement is about `kore.k`'s
equations alone.

`DenF.bound`: such a substitution gives every variable of the pattern form a term.
`DenColF.chunks_list` and `DenColF.chunks_coll` read off the elements each part takes: a `List`'s
parts stretches of the elements in order; a `Map`'s or a `Set`'s element parts one element each, no
element twice, and its one other part, the last, the elements left in their order.
-/

set_option autoImplicit false

namespace KCore.KK

/-! ## The variables of a pattern form -/

mutual
/-- The variables of a pattern form: of `vr` and of `as`. -/
def tvarsF : T → List Int
  | .vr x => [x]
  | .as p x => tvarsF p ++ [x]
  | .ap _ as | .hk _ as | .cb _ _ as | .co _ _ as => tvarsLF as
  | .ij _ _ t | .el t => tvarsF t
  | .kv a v | .en a v => tvarsF a ++ tvarsF v
  | .iv _ | .bv _ | .tk _ _ | .bot => []
  termination_by structural t => t
def tvarsLF : List T → List Int
  | [] => []
  | t :: ts => tvarsF t ++ tvarsLF ts
  termination_by structural ts => ts
end

/-! ## What a substitution states of a pattern and a term -/

mutual
/-- Under `B`, the pattern form is the term. -/
inductive DenF (S : List (Int × Int)) (B : Bind) : T → T → Prop where
  | vr {x : Int} {t : T} (h : lookF x B = some t) : DenF S B (.vr x) t
  | iv (i : Int) : DenF S B (.iv i) (.iv i)
  | bv (b : Bool) : DenF S B (.bv b) (.bv b)
  | tk (s : Int) (x : String) : DenF S B (.tk s x) (.tk s x)
  | ap {f : Int} {ps ts : List T} (h : DensF S B ps ts) : DenF S B (.ap f ps) (.ap f ts)
  | ijSame {a b e : Int} {p t : T} (h : DenF S B p t) : DenF S B (.ij a b p) (.ij a e t)
  | ijSub {a b c e : Int} {p t : T} (hne : a ≠ c) (hle : leqF c a S = true)
      (h : DenF S B p (.ij c a t)) : DenF S B (.ij a b p) (.ij c e t)
  | as {p : T} {x : Int} {t : T} (h : DenF S B p t) (hx : lookF x B = some t) : DenF S B (.as p x) t
  | kv {p q a v : T} (hp : DenF S B p a) (hq : DenF S B q v) : DenF S B (.kv p q) (.kv a v)
  | el {p x : T} (h : DenF S B p x) : DenF S B (.el p) (.el x)
  | cb {k l : Kind} {c e : Int} {ps es : List T} (h : DenColF S B k c ps es) :
      DenF S B (.cb k c ps) (.co l e es)
/-- Under `B`, the pattern forms are the terms, one by one. -/
inductive DensF (S : List (Int × Int)) (B : Bind) : List T → List T → Prop where
  | nil : DensF S B [] []
  | cons {p t : T} {ps ts : List T} (h : DenF S B p t) (hs : DensF S B ps ts) :
      DensF S B (p :: ps) (t :: ts)
/-- Under `B`, the parts of a collection pattern of the kind `k` and the sort `c` take the
elements. -/
inductive DenColF (S : List (Int × Int)) (B : Bind) : Kind → Int → List T → List T → Prop where
  | done {k : Kind} {c : Int} : DenColF S B k c [] []
  | choose {k : Kind} {c : Int} {p e : T} {ps l r : List T} (hp : isElemT p = true)
      (hk : k ≠ .list) (h : DenF S B p e) (hs : DenColF S B k c ps (l ++ r)) :
      DenColF S B k c (p :: ps) (l ++ e :: r)
  | head {c : Int} {p e : T} {ps es : List T} (hp : isElemT p = true) (h : DenF S B p e)
      (hs : DenColF S B .list c ps es) : DenColF S B .list c (p :: ps) (e :: es)
  | frame {k : Kind} {c : Int} {f : T} {es : List T} (hf : isElemT f = false)
      (h : DenF S B f (.co k c es)) : DenColF S B k c [f] es
  | split {c : Int} {f p : T} {ps l r : List T} (hf : isElemT f = false)
      (h : DenF S B f (.co .list c l)) (hs : DenColF S B .list c (p :: ps) r) :
      DenColF S B .list c (f :: p :: ps) (l ++ r)
end

mutual
/-- What a substitution states, every substitution that extends it states. -/
theorem DenF.mono {S : List (Int × Int)} {B B' : Bind} (hx : BindExt B B') : ∀ {p a : T},
    DenF S B p a → DenF S B' p a
  | _, _, .vr h => .vr (hx _ _ h)
  | _, _, .iv i => .iv i
  | _, _, .bv b => .bv b
  | _, _, .tk s x => .tk s x
  | _, _, .ap h => .ap (DensF.mono hx h)
  | _, _, .ijSame h => .ijSame (DenF.mono hx h)
  | _, _, .ijSub hne hle h => .ijSub hne hle (DenF.mono hx h)
  | _, _, .as h h' => .as (DenF.mono hx h) (hx _ _ h')
  | _, _, .kv hp hq => .kv (DenF.mono hx hp) (DenF.mono hx hq)
  | _, _, .el h => .el (DenF.mono hx h)
  | _, _, .cb h => .cb (DenColF.mono hx h)
theorem DensF.mono {S : List (Int × Int)} {B B' : Bind} (hx : BindExt B B') : ∀ {ps ts : List T},
    DensF S B ps ts → DensF S B' ps ts
  | _, _, .nil => .nil
  | _, _, .cons h hs => .cons (DenF.mono hx h) (DensF.mono hx hs)
theorem DenColF.mono {S : List (Int × Int)} {B B' : Bind} (hx : BindExt B B') :
    ∀ {k : Kind} {c : Int} {ps es : List T}, DenColF S B k c ps es → DenColF S B' k c ps es
  | _, _, _, _, .done => .done
  | _, _, _, _, .choose hp hk h hs => .choose hp hk (DenF.mono hx h) (DenColF.mono hx hs)
  | _, _, _, _, .head hp h hs => .head hp (DenF.mono hx h) (DenColF.mono hx hs)
  | _, _, _, _, .frame hf h => .frame hf (DenF.mono hx h)
  | _, _, _, _, .split hf h hs => .split hf (DenF.mono hx h) (DenColF.mono hx hs)
end

/-! ## Every variable of the pattern has an entry -/

mutual
/-- A substitution under which a pattern form is a term gives every variable of the form a term. -/
theorem DenF.bound {S : List (Int × Int)} {B : Bind} : ∀ {p a : T}, DenF S B p a →
    ∀ x ∈ tvarsF p, (lookF x B).isSome = true
  | _, _, .vr h, y, hy => by
    simp only [tvarsF, List.mem_singleton] at hy
    subst hy; rw [h]; rfl
  | _, _, .iv _, y, hy => by simp [tvarsF] at hy
  | _, _, .bv _, y, hy => by simp [tvarsF] at hy
  | _, _, .tk _ _, y, hy => by simp [tvarsF] at hy
  | _, _, .ap h, y, hy => DensF.bound h y (by simpa [tvarsF] using hy)
  | _, _, .ijSame h, y, hy => DenF.bound h y (by simpa [tvarsF] using hy)
  | _, _, .ijSub _ _ h, y, hy => DenF.bound h y (by simpa [tvarsF] using hy)
  | _, _, .as h hx, y, hy => by
    simp only [tvarsF, List.mem_append, List.mem_singleton] at hy
    rcases hy with hy | rfl
    · exact DenF.bound h y hy
    · rw [hx]; rfl
  | _, _, .kv hp hq, y, hy => by
    simp only [tvarsF, List.mem_append] at hy
    rcases hy with hy | hy
    · exact DenF.bound hp y hy
    · exact DenF.bound hq y hy
  | _, _, .el h, y, hy => DenF.bound h y (by simpa [tvarsF] using hy)
  | _, _, .cb h, y, hy => DenColF.bound h y (by simpa [tvarsF] using hy)
theorem DensF.bound {S : List (Int × Int)} {B : Bind} : ∀ {ps ts : List T}, DensF S B ps ts →
    ∀ x ∈ tvarsLF ps, (lookF x B).isSome = true
  | _, _, .nil, y, hy => by simp [tvarsLF] at hy
  | _, _, .cons h hs, y, hy => by
    simp only [tvarsLF, List.mem_append] at hy
    rcases hy with hy | hy
    · exact DenF.bound h y hy
    · exact DensF.bound hs y hy
theorem DenColF.bound {S : List (Int × Int)} {B : Bind} : ∀ {k : Kind} {c : Int} {ps es : List T},
    DenColF S B k c ps es → ∀ x ∈ tvarsLF ps, (lookF x B).isSome = true
  | _, _, _, _, .done, y, hy => by simp [tvarsLF] at hy
  | _, _, _, _, .choose _ _ h hs, y, hy => by
    simp only [tvarsLF, List.mem_append] at hy
    rcases hy with hy | hy
    · exact DenF.bound h y hy
    · exact DenColF.bound hs y hy
  | _, _, _, _, .head _ h hs, y, hy => by
    simp only [tvarsLF, List.mem_append] at hy
    rcases hy with hy | hy
    · exact DenF.bound h y hy
    · exact DenColF.bound hs y hy
  | _, _, _, _, .frame _ h, y, hy => DenF.bound h y (by simpa [tvarsLF] using hy)
  | _, _, _, _, .split _ h hs, y, hy => by
    rw [tvarsLF, List.mem_append] at hy
    rcases hy with hy | hy
    · exact DenF.bound h y hy
    · exact DenColF.bound hs y hy
end

/-! ## The elements each part takes -/

/-- What a part takes of a collection of the kind `k` and the sort `c`: an element part one
element, which it is; any other part the collection of the elements it takes. -/
def TakesF (S : List (Int × Int)) (B : Bind) (k : Kind) (c : Int) (p : T) (ch : List T) : Prop :=
  if isElemT p = true then ∃ e, ch = [e] ∧ DenF S B p e else DenF S B p (.co k c ch)

/-- The parts of a `List` pattern take the elements in order, each a stretch of them. -/
theorem DenColF.chunks_list {S : List (Int × Int)} {B : Bind} :
    ∀ {k : Kind} {c : Int} {ps es : List T}, DenColF S B k c ps es → k = .list →
    ∃ chs : List (List T), chs.flatten = es ∧ chs.length = ps.length ∧
      ∀ x ∈ ps.zip chs, TakesF S B .list c x.1 x.2
  | _, _, _, _, .done, _ => ⟨[], rfl, rfl, fun _ hx => nomatch hx⟩
  | _, _, _, _, .choose _ hk _ _, hl => absurd hl hk
  | _, _, _, _, .head (e := e) hp h hs, _ => by
    obtain ⟨chs, h1, h2, h3⟩ := DenColF.chunks_list hs rfl
    refine ⟨[e] :: chs, by simp [h1], by simp [h2], fun x hx => ?_⟩
    rcases List.mem_cons.mp hx with rfl | hx
    · simpa [TakesF, hp] using h
    · exact h3 x hx
  | _, _, _, _, .frame (es := es) hf h, hl => by
    subst hl
    refine ⟨[es], by simp, rfl, fun x hx => ?_⟩
    rcases List.mem_cons.mp hx with rfl | hx
    · simpa [TakesF, hf] using h
    · cases hx
  | _, _, _, _, .split (l := l) hf h hs, _ => by
    obtain ⟨chs, h1, h2, h3⟩ := DenColF.chunks_list hs rfl
    refine ⟨l :: chs, by simp [h1], by simp [h2], fun x hx => ?_⟩
    rcases List.mem_cons.mp hx with rfl | hx
    · simpa [TakesF, hf] using h
    · exact h3 x hx

/-- The parts of a `Map` or `Set` pattern are element parts, then at most one other part: each
element part takes one element, no element twice, and the other part the elements left, in their
order; without one no element is left. -/
theorem DenColF.chunks_coll {S : List (Int × Int)} {B : Bind} :
    ∀ {k : Kind} {c : Int} {ps es : List T}, DenColF S B k c ps es → k ≠ .list →
    ∃ picked rest : List T, (picked ++ rest).Perm es ∧ rest.Sublist es ∧
      ((DensF S B ps picked ∧ rest = [] ∧ ∀ p ∈ ps, isElemT p = true) ∨
        ∃ els f, ps = els ++ [f] ∧ (∀ p ∈ els, isElemT p = true) ∧ isElemT f = false ∧
          DensF S B els picked ∧ DenF S B f (.co k c rest))
  | _, _, _, _, .done, _ => ⟨[], [], by simp, by simp, .inl ⟨.nil, rfl, by simp⟩⟩
  | _, _, _, _, .choose (p := p) (e := e) (l := l) (r := r) hp hk h hs, hn => by
    obtain ⟨pk, rs, h1, h2, h3⟩ := DenColF.chunks_coll hs hn
    refine ⟨e :: pk, rs, (List.Perm.cons e h1).trans List.perm_middle.symm,
      h2.trans (List.Sublist.append (List.Sublist.refl l) (List.sublist_cons_self e r)), ?_⟩
    rcases h3 with ⟨a, b, d⟩ | ⟨els, f, rfl, a, b, d, g⟩
    · refine .inl ⟨.cons h a, b, fun q hq => ?_⟩
      rcases List.mem_cons.mp hq with rfl | hq
      · exact hp
      · exact d q hq
    · refine .inr ⟨p :: els, f, rfl, fun q hq => ?_, b, .cons h d, g⟩
      rcases List.mem_cons.mp hq with rfl | hq
      · exact hp
      · exact a q hq
  | _, _, _, _, .head _ _ _, hn => absurd rfl hn
  | _, _, _, _, .frame (f := f) (es := es) hf h, _ =>
    ⟨[], es, by simp, List.Sublist.refl _, .inr ⟨[], f, rfl, by simp, hf, .nil, h⟩⟩
  | _, _, _, _, .split _ _ _, hn => absurd rfl hn

/-! ## The entries a match adds -/

/-- Every entry of `B'` is one of `B`, or the entry `look` finds in `B'` for a variable of `vs`. -/
def NewIn (vs : List Int) (B B' : Bind) : Prop :=
  ∀ e ∈ B', e ∈ B ∨ (lookF e.1 B' = some e.2 ∧ e.1 ∈ vs)

theorem NewIn.refl (vs : List Int) (B : Bind) : NewIn vs B B := fun _ h => .inl h

theorem NewIn.mono {vs ws : List Int} {B B' : Bind} (h : NewIn vs B B') (hs : ∀ x ∈ vs, x ∈ ws) :
    NewIn ws B B' := fun e he => (h e he).imp id fun ⟨h1, h2⟩ => ⟨h1, hs _ h2⟩

theorem NewIn.trans {vs : List Int} {B B₁ B' : Bind} (h1 : NewIn vs B B₁) (h2 : NewIn vs B₁ B')
    (hx : BindExt B₁ B') : NewIn vs B B' := fun e he => by
  rcases h2 e he with h | h
  · rcases h1 e h with h | ⟨h, h'⟩
    · exact .inl h
    · exact .inr ⟨hx _ _ h, h'⟩
  · exact .inr h

theorem bindVarF_newIn {x : Int} {t : T} {B B' : Bind} (h : B' ∈ bindVarF x t B (lookF x B)) :
    NewIn [x] B B' := by
  obtain ⟨h1, -, h3⟩ := bindVarF_mem h
  rcases h3 with rfl | rfl
  · exact NewIn.refl _ _
  · intro e he
    rcases List.mem_cons.mp he with rfl | he
    · exact .inr ⟨h1, by simp⟩
    · exact .inl he

/-! ## `match` states what it gives -/

section
variable (S : List (Int × Int))

mutual
/-- **A substitution `match` gives states the match.** It extends the given substitution, under it
the pattern form is the term, and its entries beyond the given one's are the entries `look` finds
for variables of the pattern. -/
theorem matchF_den : ∀ (p a : T) {B B' : Bind} {M : Ms}, matchF S p a B = some M → B' ∈ M →
    BindExt B B' ∧ DenF S B' p a ∧ NewIn (tvarsF p) B B'
  | .vr x, a, B, B', M, h, hB => by
    rw [matchF_vr] at h; cases h
    obtain ⟨h1, h2, -⟩ := bindVarF_mem hB
    exact ⟨h2, .vr h1, by simpa [tvarsF] using bindVarF_newIn hB⟩
  | .iv i, a, B, B', M, h, hB => by
    rw [matchF_iv] at h; cases h
    split at hB
    · rename_i ha
      simp only [List.mem_singleton] at hB
      subst hB; subst ha
      exact ⟨BindExt.refl _, .iv i, NewIn.refl _ _⟩
    · cases hB
  | .bv b, a, B, B', M, h, hB => by
    rw [matchF_bv] at h; cases h
    split at hB
    · rename_i ha
      simp only [List.mem_singleton] at hB
      subst hB; subst ha
      exact ⟨BindExt.refl _, .bv b, NewIn.refl _ _⟩
    · cases hB
  | .tk s x, a, B, B', M, h, hB => by
    rw [matchF_tk] at h; cases h
    split at hB
    · rename_i ha
      simp only [List.mem_singleton] at hB
      subst hB; subst ha
      exact ⟨BindExt.refl _, .tk s x, NewIn.refl _ _⟩
    · cases hB
  | .ap f ps, a, B, B', M, h, hB => by
    obtain ⟨ts, rfl, h'⟩ := matchF_ap_inv S h hB
    obtain ⟨h1, h2, h3⟩ := matchTsF_den ps ts h' hB
    exact ⟨h1, .ap h2, by simpa [tvarsF] using h3⟩
  | .ij a b p, u, B, B', M, h, hB => by
    obtain ⟨c, e, t, rfl, hcase⟩ := matchF_ij_inv S h hB
    rcases hcase with ⟨rfl, h'⟩ | ⟨hne, hle, h'⟩
    · obtain ⟨h1, h2, h3⟩ := matchF_den p t h' hB
      exact ⟨h1, .ijSame h2, by simpa [tvarsF] using h3⟩
    · obtain ⟨h1, h2, h3⟩ := matchF_den p (.ij c a t) h' hB
      exact ⟨h1, .ijSub hne hle h2, by simpa [tvarsF] using h3⟩
  | .as p x, a, B, B', M, h, hB => by
    rw [matchF_as] at h
    obtain ⟨M₁, hm₁, rfl⟩ := Option.map_eq_some_iff.mp h
    obtain ⟨B₁, hB₁, hB⟩ := bindAfterF_mem hB
    obtain ⟨h1, h2, h3⟩ := matchF_den p a hm₁ hB₁
    obtain ⟨g1, g2, -⟩ := bindVarF_mem hB
    refine ⟨h1.trans g2, .as (h2.mono g2) g1, ?_⟩
    exact NewIn.trans (h3.mono fun y hy => by simp [tvarsF, hy])
      ((bindVarF_newIn hB).mono fun y hy => by simp [tvarsF, List.mem_singleton.mp hy]) g2
  | .cb k c ps, a, B, B', M, h, hB => by
    obtain ⟨l, e, es, rfl, h'⟩ := matchF_cb_inv S h hB
    obtain ⟨h1, h2, h3⟩ := matchColF_den k c ps es h' hB
    exact ⟨h1, .cb h2, by simpa [tvarsF] using h3⟩
  | .kv p q, a, B, B', M, h, hB => by
    obtain ⟨k, v, rfl, h'⟩ := matchF_kv_inv S h hB
    obtain ⟨h1, h2, h3⟩ := matchTsF_den [p, q] [k, v] h' hB
    refine ⟨h1, ?_, by simpa [tvarsF, tvarsLF] using h3⟩
    cases h2 with
    | cons hp hs => cases hs with
      | cons hq _ => exact .kv hp hq
  | .el p, a, B, B', M, h, hB => by
    obtain ⟨x, rfl, h'⟩ := matchF_el_inv S h hB
    obtain ⟨h1, h2, h3⟩ := matchF_den p x h' hB
    exact ⟨h1, .el h2, by simpa [tvarsF] using h3⟩
  | .hk o as, a, B, B', M, h, hB => by rw [matchF_hk] at h; cases h; cases hB
  | .bot, a, B, B', M, h, hB => by rw [matchF_bot] at h; cases h; cases hB
  | .co k c es, a, B, B', M, h, hB => by rw [matchF_co] at h; cases h; cases hB
  | .en t e, a, B, B', M, h, hB => by rw [matchF_en] at h; cases h; cases hB
  termination_by p => psizeF p
  decreasing_by
    all_goals simp_wf
    all_goals (simp only [psizeF, psizeLF] <;> omega)
/-- The same of `matchTs`: two lists of one length. -/
theorem matchTsF_den : ∀ (ps ts : List T) {B B' : Bind} {M : Ms}, matchTsF S ps ts B = some M →
    B' ∈ M → BindExt B B' ∧ DensF S B' ps ts ∧ NewIn (tvarsLF ps) B B'
  | [], [], B, B', M, h, hB => by
    rw [matchTsF_nil] at h; cases h
    simp only [List.mem_singleton] at hB
    subst hB
    exact ⟨BindExt.refl _, .nil, NewIn.refl _ _⟩
  | [], t :: ts, B, B', M, h, hB => by rw [matchTsF_nil_cons] at h; cases h
  | p :: ps, [], B, B', M, h, hB => by rw [matchTsF_cons_nil] at h; cases h
  | p :: ps, t :: ts, B, B', M, h, hB => by
    rw [matchTsF_cons] at h
    cases hm₁ : matchF S p t B with
    | none => rw [hm₁] at h; cases h
    | some ms =>
      rw [hm₁] at h
      obtain ⟨B₁, hB₁, M₁, hm₂, hB'⟩ := matchKF_mem S h hB
      obtain ⟨h1, h2, h3⟩ := matchF_den p t hm₁ hB₁
      obtain ⟨g1, g2, g3⟩ := matchTsF_den ps ts hm₂ hB'
      exact ⟨h1.trans g1, .cons (h2.mono g1) g2,
        NewIn.trans (h3.mono fun y hy => by simp [tvarsLF, hy])
          (g3.mono fun y hy => by simp [tvarsLF, hy]) g1⟩
  termination_by ps => psizeLF ps
  decreasing_by
    all_goals simp_wf
    all_goals (simp only [psizeLF] <;> omega)
/-- The same of `matchCol`: the parts of a collection pattern and the elements. -/
theorem matchColF_den : ∀ (k : Kind) (c : Int) (ps es : List T) {B B' : Bind} {M : Ms},
    matchColF S k c ps es B = some M → B' ∈ M →
    BindExt B B' ∧ DenColF S B' k c ps es ∧ NewIn (tvarsLF ps) B B'
  | k, c, [], es, B, B', M, h, hB => by
    rw [matchColF_nil] at h; cases h
    split at hB
    · rename_i he
      simp only [List.mem_singleton] at hB
      subst hB; subst he
      exact ⟨BindExt.refl _, .done, NewIn.refl _ _⟩
    · cases hB
  | k, c, p :: ps, es, B, B', M, h, hB => by
    cases hp : isElemT p with
    | true =>
      by_cases hk : k = .list
      · subst hk
        cases es with
        | nil => rw [matchColF_head_nil S hp] at h; cases h; cases hB
        | cons e es =>
          rw [matchColF_head S hp] at h
          cases hm₁ : matchF S p e B with
          | none => rw [hm₁] at h; cases h
          | some ms =>
            rw [hm₁] at h
            obtain ⟨B₁, hB₁, M₁, hm₂, hB'⟩ := restF_mem S h hB
            obtain ⟨h1, h2, h3⟩ := matchF_den p e hm₁ hB₁
            obtain ⟨g1, g2, g3⟩ := matchColF_den .list c ps es hm₂ hB'
            exact ⟨h1.trans g1, .head hp (h2.mono g1) g2,
              NewIn.trans (h3.mono fun y hy => by simp [tvarsLF, hy])
                (g3.mono fun y hy => by simp [tvarsLF, hy]) g1⟩
      · rw [matchColF_choose S hp hk] at h
        obtain ⟨l, e, r, M₁, B₁, M₂, rfl, hm₁, hB₁, hm₂, hB'⟩ := chooseF_mem S h hB
        obtain ⟨h1, h2, h3⟩ := matchF_den p e hm₁ hB₁
        obtain ⟨g1, g2, g3⟩ := matchColF_den k c ps ([] ++ l ++ r) hm₂ hB'
        exact ⟨h1.trans g1, .choose hp hk (h2.mono g1) (by simpa using g2),
          NewIn.trans (h3.mono fun y hy => by simp [tvarsLF, hy])
            (g3.mono fun y hy => by simp [tvarsLF, hy]) g1⟩
    | false =>
      by_cases hnil : ps = []
      · subst hnil
        rw [matchColF_frame S hp] at h
        obtain ⟨h1, h2, h3⟩ := matchF_den p (.co k c es) h hB
        exact ⟨h1, .frame hp h2, h3.mono fun y hy => by simp [tvarsLF, hy]⟩
      · obtain ⟨q, qs, hps⟩ : ∃ q qs, ps = q :: qs := by
          cases ps with
          | nil => exact absurd rfl hnil
          | cons q qs => exact ⟨q, qs, rfl⟩
        by_cases hk : k = .list
        · subst hk
          rw [hps, matchColF_split S hp] at h
          obtain ⟨l, r, M₁, B₁, M₂, rfl, hm₁, hB₁, hm₂, hB'⟩ := splitF_mem S h hB
          obtain ⟨h1, h2, h3⟩ := matchF_den p (.co .list c ([] ++ l)) hm₁ hB₁
          rw [← hps] at hm₂
          obtain ⟨g1, g2, g3⟩ := matchColF_den .list c ps r hm₂ hB'
          refine ⟨h1.trans g1, ?_, NewIn.trans (h3.mono fun y hy => by simp [tvarsLF, hy])
            (g3.mono fun y hy => by simp [tvarsLF, hy]) g1⟩
          rw [hps] at g2 ⊢
          exact .split hp (by simpa using h2.mono g1) g2
        · rw [hps, matchColF_frame_more S hp hk] at h; cases h; cases hB
  termination_by _ _ ps => psizeLF ps
  decreasing_by
    all_goals simp_wf
    all_goals (simp only [psizeLF] <;> omega)
end

end

end KCore.KK
