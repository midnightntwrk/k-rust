/-
  kore.k's `strictHook` at the operation codes of Map (40 to 45), Set (50 to 52) and List (60), on
  kore.k's semantics read from its kompiled text: at the code `o` of an interpreted symbol `f`
  (`hookCodes`) and the encoded arguments, `strictHook` evaluates at `K₀ sig` to the encoding of
  KCore's result, `emb (encR ((d₀ d).hookRes f vs).join)`, for every semantics `d`.

  On kore.k's side each code's equation is read at an argument list whose collection arguments are
  `co` terms of the code's kind, with its right side through the helpers of User.HelpColl,
  User.HelpOrder and User.HelpWalk: `valueOr` (40, 41), `putE` (42), `delE` (43), `hasKey` (44, 50),
  `len` (45, 51, 60) and `union` (52); at any other argument list the equation's pattern fails and
  `op-undef` gives `bot`. `strictHook` adds `hook-bot`, which changes nothing at encodings of values
  whose literals have a kore.k form (they hold no `bot`).

  On KCore's side a map or a set sorted at `Map` or `Set` has its sort as the collection's sort and
  its keys (members) strictly increasing by `GroundTerm.cmp`; its encoding is the list of its
  entries' (members') encodings strictly increasing by `ckeyF` (`sortK`). Keys are compared by
  `cmpF` on kore.k's side and by `GroundTerm.cmp` on KCore's: on encodings of values sorted in one
  semantics whose literals have a kore.k form `cmpF` is 0 exactly between equal values
  (`cmpF_eq_zero_iff`), and `GroundTerm.cmp` is `.eq` exactly between equal values. A list strictly
  increasing by `ckeyF` is fixed by its members (`sortedK_eq_khk`), so the update, the removal and
  the union are compared member by member: `putE` keeps the members of other keys and adds the entry
  (`putEF_ok_khk`), `delE` keeps the members of other keys (`delEF_ok_khk`), `union` of two sets
  holds the members of both (`unionF_set_khk`); `insertE`, `eraseK` and `unionS` do the same on
  sorted entries and members (`insertE_mem_iff_khk`, `eraseK_mem_iff_khk`, `unionS_mem_iff_khk`).

  Hypotheses where the two readings could part: the arguments are sorted at the argument sorts
  `hookSigs` gives the symbol (the collection's sort is then `Map` or `Set`, the one `hook`'s result
  carries, and its keys are sorted values) and their literals have a kore.k form (two keys that
  `enc` writes `bot` compare 0). The sizes (45, 51, 60) need neither and hold at every argument list.
  `hooks_coll` states the ten codes at once (at `opOf f = some o` with `40 ≤ o < 70`),
  `hooks_coll_lookup` … one each.

  The clauses are the semantics' own, as literals tied to `lookupFn` by the kernel (User.HooksScalar).
-/
import User.HooksScalar
import User.HelpColl

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option Elab.async false

namespace KCore.KK

/-! ## Lists strictly increasing by `ckeyF` -/

section ElemsK
open _root_.KK.Kit (ite_pos ite_neg)
variable {c : Semantics} {k : Kind}

/-- No term is below itself by `ckeyF`. -/
theorem ckeyF_irrefl_khk (t : T) : ckeyF t t ≠ some (-1) := by
  cases t <;> simp [ckeyF, cmpF_self]

theorem SortedK_khc.nodup_khk {L : List T} (h : SortedK_khc L) : L.Nodup :=
  h.imp fun {a b} hab he => by subst he; exact ckeyF_irrefl_khk a hab

/-- Two lists strictly increasing by `ckeyF` with the same members are equal. -/
theorem sortedK_eq_khk {L₁ L₂ : List T} (h₁ : SortedK_khc L₁) (h₂ : SortedK_khc L₂)
    (hm : ∀ x, x ∈ L₁ ↔ x ∈ L₂) : L₁ = L₂ :=
  perm_pairwise_eq_cdp (fun _ _ => ckeyF_asym_cdp) h₁ h₂
    ((List.perm_ext_iff_of_nodup h₁.nodup_khk h₂.nodup_khk).mpr hm)

/-- In a list strictly increasing by `ckeyF`, the first member's key is below the others'. -/
theorem sortedK_head_khk {f : T} {fs : List T} (hS : ∀ g ∈ f :: fs, ElemOK_khc c k g)
    (hp : SortedK_khc (f :: fs)) : ∀ g ∈ fs, cmpF (keyT_khc f) (keyT_khc g) = -1 := fun g hg => by
  have h := (List.pairwise_cons.mp hp).1 g hg
  rwa [(hS f (List.mem_cons_self ..)).ckey (hS g (List.mem_cons_of_mem _ hg)), Option.some.injEq] at h

/-- `putE` of an element into a list strictly increasing by `ckeyF`: the element and the members of
other keys, strictly increasing. -/
theorem putEF_ok_khk {e : T} (he : ElemOK_khc c k e) :
    ∀ {es : List T}, (∀ f ∈ es, ElemOK_khc c k f) → SortedK_khc es →
      ∃ L, putEF e es = some L ∧ SortedK_khc L ∧ (∀ f ∈ L, ElemOK_khc c k f) ∧
        ∀ x, x ∈ L ↔ x = e ∨ (x ∈ es ∧ keyT_khc x ≠ keyT_khc e)
  | [], _, _ => ⟨[e], rfl, List.pairwise_singleton _ _,
      fun f hf => by rw [List.mem_singleton] at hf; rw [hf]; exact he, fun x => by simp⟩
  | f :: fs, hS, hp => by
    have hf := hS f (List.mem_cons_self ..)
    have hS' : ∀ g ∈ fs, ElemOK_khc c k g := fun g hg => hS g (List.mem_cons_of_mem _ hg)
    have hp' := List.pairwise_cons.mp hp
    have hfg := sortedK_head_khk hS hp
    rw [putEF, he.ckey hf, Option.bind_some]
    rcases cmpF_range (keyT_khc e) (keyT_khc f) with h | h | h
    · rw [h, ite_pos (by decide)]
      have heg : ∀ g ∈ f :: fs, cmpF (keyT_khc e) (keyT_khc g) = -1 := fun g hg => by
        rcases List.mem_cons.mp hg with rfl | hg
        · exact h
        · exact cmpF_trans_ord he.key hf.key (hS' g hg).key h (hfg g hg)
      refine ⟨e :: f :: fs, rfl, List.Pairwise.cons (fun g hg => by rw [he.ckey (hS g hg), heg g hg]) hp,
        fun g hg => ?_, fun x => ?_⟩
      · rcases List.mem_cons.mp hg with rfl | hg
        · exact he
        · exact hS g hg
      · constructor
        · intro hx
          rcases List.mem_cons.mp hx with rfl | hx
          · exact .inl rfl
          · refine .inr ⟨hx, fun hk => ?_⟩
            have := heg x hx
            rw [hk, cmpF_self] at this
            cases this
        · rintro (rfl | ⟨hx, -⟩)
          · exact List.mem_cons_self ..
          · exact List.mem_cons_of_mem _ hx
    · have hk : keyT_khc e = keyT_khc f := (cmpF_eq_zero_iff_ord he.key hf.key).mp h
      rw [h, ite_neg (by decide), ite_pos rfl]
      refine ⟨e :: fs, rfl, List.Pairwise.cons (fun g hg => by rw [he.ckey (hS' g hg), hk, hfg g hg]) hp'.2,
        fun g hg => ?_, fun x => ?_⟩
      · rcases List.mem_cons.mp hg with rfl | hg
        · exact he
        · exact hS' g hg
      · constructor
        · intro hx
          rcases List.mem_cons.mp hx with rfl | hx
          · exact .inl rfl
          · refine .inr ⟨List.mem_cons_of_mem _ hx, fun hk' => ?_⟩
            have := hfg x hx
            rw [hk', hk, cmpF_self] at this
            cases this
        · rintro (rfl | ⟨hx, hne⟩)
          · exact List.mem_cons_self ..
          · rcases List.mem_cons.mp hx with rfl | hx
            · exact absurd hk.symm hne
            · exact List.mem_cons_of_mem _ hx
    · rw [h, ite_neg (by decide), ite_neg (by decide)]
      obtain ⟨L, hL, hpL, hSL, hmL⟩ := putEF_ok_khk he hS' hp'.2
      rw [hL]
      have hfe : cmpF (keyT_khc f) (keyT_khc e) = -1 := by rw [cmpF_swap, h]
      have hne : keyT_khc f ≠ keyT_khc e := fun hk => by rw [hk, cmpF_self] at hfe; cases hfe
      refine ⟨f :: L, rfl, List.Pairwise.cons (fun g hg => ?_) hpL, fun g hg => ?_, fun x => ?_⟩
      · rw [hf.ckey (hSL g hg)]
        rcases (hmL g).mp hg with rfl | ⟨hg, -⟩
        · rw [hfe]
        · rw [hfg g hg]
      · rcases List.mem_cons.mp hg with rfl | hg
        · exact hf
        · exact hSL g hg
      · rw [List.mem_cons, hmL, List.mem_cons]
        constructor
        · rintro (rfl | rfl | ⟨hx, hne'⟩)
          · exact .inr ⟨.inl rfl, hne⟩
          · exact .inl rfl
          · exact .inr ⟨.inr hx, hne'⟩
        · rintro (rfl | ⟨rfl | hx, hne'⟩)
          · exact .inr (.inl rfl)
          · exact .inl rfl
          · exact .inr (.inr ⟨hx, hne'⟩)

/-- `delE` of an element's key from a list strictly increasing by `ckeyF`: the members of other
keys, in order. -/
theorem delEF_ok_khk {e : T} (he : ElemOK_khc c k e) :
    ∀ {es : List T}, (∀ f ∈ es, ElemOK_khc c k f) → SortedK_khc es →
      ∃ L, delEF e es = some L ∧ L.Sublist es ∧ ∀ x, x ∈ L ↔ x ∈ es ∧ keyT_khc x ≠ keyT_khc e
  | [], _, _ => ⟨[], rfl, .slnil, fun x => by simp⟩
  | f :: fs, hS, hp => by
    have hf := hS f (List.mem_cons_self ..)
    have hS' : ∀ g ∈ fs, ElemOK_khc c k g := fun g hg => hS g (List.mem_cons_of_mem _ hg)
    have hfg := sortedK_head_khk hS hp
    rw [delEF, he.ckey hf, Option.bind_some]
    by_cases h : cmpF (keyT_khc e) (keyT_khc f) = 0
    · have hk := (cmpF_eq_zero_iff_ord he.key hf.key).mp h
      rw [ite_pos h]
      refine ⟨fs, rfl, List.sublist_cons_self _ _, fun x => ⟨fun hx => ⟨List.mem_cons_of_mem _ hx, fun hk' => ?_⟩,
        fun ⟨hx, hne⟩ => ?_⟩⟩
      · have := hfg x hx
        rw [hk', hk, cmpF_self] at this
        cases this
      · rcases List.mem_cons.mp hx with rfl | hx
        · exact absurd hk.symm hne
        · exact hx
    · rw [ite_neg h]
      obtain ⟨L, hL, hsub, hm⟩ := delEF_ok_khk he hS' (List.pairwise_cons.mp hp).2
      rw [hL]
      have hne : keyT_khc f ≠ keyT_khc e := fun hk => h (by rw [hk, cmpF_self])
      refine ⟨f :: L, rfl, hsub.cons_cons f, fun x => ?_⟩
      rw [List.mem_cons, hm, List.mem_cons]
      constructor
      · rintro (rfl | ⟨hx, hne'⟩)
        · exact ⟨.inl rfl, hne⟩
        · exact ⟨.inr hx, hne'⟩
      · rintro ⟨rfl | hx, hne'⟩
        · exact .inl rfl
        · exact .inr ⟨hx, hne'⟩

/-- `hasKey` of an element over elements of its kind: whether a member has its key. -/
theorem hasKeyF_ok_khk {e : T} (he : ElemOK_khc c k e) :
    ∀ {es : List T}, (∀ f ∈ es, ElemOK_khc c k f) →
      hasKeyF e es = some (decide (∃ f ∈ es, keyT_khc f = keyT_khc e))
  | [], _ => by simp [hasKeyF]
  | f :: fs, hS => by
    have hf := hS f (List.mem_cons_self ..)
    rw [hasKeyF, he.ckey hf, Option.bind_some,
      hasKeyF_ok_khk he (fun g hg => hS g (List.mem_cons_of_mem _ hg)), Option.map_some, Option.some.injEq]
    refine Bool.eq_iff_iff.mpr ?_
    rw [Bool.or_eq_true, decide_eq_true_iff, decide_eq_true_iff, decide_eq_true_iff]
    constructor
    · rintro (h | ⟨g, hg, hk⟩)
      · exact ⟨f, List.mem_cons_self .., ((cmpF_eq_zero_iff_ord he.key hf.key).mp h).symm⟩
      · exact ⟨g, List.mem_cons_of_mem _ hg, hk⟩
    · rintro ⟨g, hg, hk⟩
      rcases List.mem_cons.mp hg with rfl | hg
      · exact .inl (by rw [hk, cmpF_self])
      · exact .inr ⟨g, hg, hk⟩

/-- Two members of a set with one key are equal. -/
theorem ElemOK_khc.set_eq_khk {x f : T} (hx : ElemOK_khc c .set x) (hf : ElemOK_khc c .set f)
    (h : keyT_khc x = keyT_khc f) : x = f := by
  obtain ⟨y, rfl, -⟩ := hx
  obtain ⟨z, rfl, -⟩ := hf
  cases h
  rfl

/-- `union` of two sets strictly increasing by `ckeyF`: the members of both, strictly increasing. -/
theorem unionF_set_khk :
    ∀ (fs : List T) {es : List T}, (∀ f ∈ es, ElemOK_khc c .set f) → SortedK_khc es →
      (∀ f ∈ fs, ElemOK_khc c .set f) →
      ∃ L, unionF es fs = some L ∧ SortedK_khc L ∧ ∀ x, x ∈ L ↔ x ∈ es ∨ x ∈ fs
  | [], es, _, hp, _ => ⟨es, rfl, hp, fun x => by simp⟩
  | f :: fs, es, hS, hp, hF => by
    have hf := hF f (List.mem_cons_self ..)
    obtain ⟨L, hL, hpL, hSL, hmL⟩ := putEF_ok_khk hf hS hp
    obtain ⟨L', hL', hpL', hmL'⟩ :=
      unionF_set_khk fs hSL hpL fun g hg => hF g (List.mem_cons_of_mem _ hg)
    refine ⟨L', by rw [unionF, hL, Option.bind_some, hL'], hpL', fun x => ?_⟩
    rw [hmL', hmL, List.mem_cons]
    constructor
    · rintro ((rfl | ⟨hx, -⟩) | hx)
      · exact .inr (.inl rfl)
      · exact .inl hx
      · exact .inr (.inr hx)
    · rintro (hx | rfl | hx)
      · by_cases hk : keyT_khc x = keyT_khc f
        · exact .inl (.inl ((hS x hx).set_eq_khk hf hk))
        · exact .inl (.inr ⟨hx, hk⟩)
      · exact .inl (.inl rfl)
      · exact .inr hx

/-- `valueOr` at a key over entries: the value of the entry whose key compares 0, where only one
value has such a key. -/
theorem valueOrF_some_khk {a v w b : T} :
    ∀ {es : List T}, (∀ f ∈ es, ∃ b' w', f = .kv b' w') → .kv b w ∈ es → cmpF a b = 0 →
      (∀ b' w', .kv b' w' ∈ es → cmpF a b' = 0 → w' = w) → valueOrF a v es = some w
  | [], _, hm, _, _ => nomatch hm
  | f :: fs, hK, hm, hab, hu => by
    obtain ⟨b', w', rfl⟩ := hK f (List.mem_cons_self ..)
    simp only [valueOrF]
    by_cases h : cmpF a b' = 0
    · rw [ite_pos h, hu b' w' (List.mem_cons_self ..) h]
    · rw [ite_neg h]
      rcases List.mem_cons.mp hm with he | hm
      · cases he
        exact absurd hab h
      · exact valueOrF_some_khk (fun g hg => hK g (List.mem_cons_of_mem _ hg)) hm hab
          fun b'' w'' hm' h' => hu b'' w'' (List.mem_cons_of_mem _ hm') h'

/-- `valueOr` at a key no entry's key compares 0 with: the default. -/
theorem valueOrF_none_khk {a v : T} :
    ∀ {es : List T}, (∀ f ∈ es, ∃ b w, f = .kv b w ∧ cmpF a b ≠ 0) → valueOrF a v es = some v
  | [], _ => rfl
  | f :: fs, h => by
    obtain ⟨b, w, rfl, hb⟩ := h f (List.mem_cons_self ..)
    simp only [valueOrF]
    rw [ite_neg hb]
    exact valueOrF_none_khk fun g hg => h g (List.mem_cons_of_mem _ hg)

end ElemsK

/-! ## KCore's sorted maps and sets -/

section KMaps
open _root_.KK.Kit (ite_pos ite_neg)

/-- `findK` off the keys. -/
theorem findK_none_khk {a : GroundTerm} :
    ∀ {es : Entries}, findK a es = none → ∀ e ∈ es, GroundTerm.cmp a e.1 ≠ .eq
  | [], _, _, he, _ => nomatch he
  | (k', v') :: es, h, e, he, hc => by
    simp only [findK] at h
    split at h
    · cases h
    · rename_i hne
      rcases List.mem_cons.mp he with rfl | he
      · exact hne (beq_iff_eq.mpr hc)
      · exact findK_none_khk h e he hc

/-- In entries with keys strictly increasing, an entry is fixed by its key. -/
theorem entry_unique_khk {es : Entries} (hks : keysSorted es = true) {a w : GroundTerm}
    {e : GroundTerm × GroundTerm} (h1 : (a, w) ∈ es) (h2 : e ∈ es) (hk : e.1 = a) : e.2 = w :=
  Classical.byContradiction fun hne => by
    have hne' : (a, w) ≠ e := fun h => hne (h ▸ rfl)
    rcases pairwise_total_kkc (keysSorted_pairwise_kel hks) h1 h2 hne' with h | h <;>
      simp [hk, GroundTerm.cmp_refl] at h

/-- `insertE` on entries with keys strictly increasing: the new entry and the entries of other keys. -/
theorem insertE_mem_iff_khk {a v : GroundTerm} :
    ∀ {es : Entries}, keysSorted es = true →
      ∀ e, e ∈ insertE a v es ↔ e = (a, v) ∨ (e ∈ es ∧ e.1 ≠ a)
  | [], _, e => by simp [insertE]
  | (k', v') :: es, hks, e => by
    have hlt := keysSorted_lt_all hks
    have hks' := (keysSorted_cons.mp hks).1
    have hne_of : ∀ x ∈ es, x.1 ≠ k' := fun x hx hx' => by
      have := hlt x hx
      rw [hx', GroundTerm.cmp_refl] at this
      cases this
    simp only [insertE]
    split
    · rename_i hc
      have hka : k' ≠ a := fun h => by rw [h, GroundTerm.cmp_refl] at hc; cases hc
      have hes : ∀ x ∈ es, x.1 ≠ a := fun x hx hx' => by
        have := GroundTerm.cmp_trans _ _ _ hc (hlt x hx)
        rw [hx', GroundTerm.cmp_refl] at this
        cases this
      simp only [List.mem_cons]
      constructor
      · rintro (h | h | h)
        · exact .inl h
        · subst h; exact .inr ⟨.inl rfl, hka⟩
        · exact .inr ⟨.inr h, hes e h⟩
      · rintro (h | ⟨h | h, -⟩)
        · exact .inl h
        · exact .inr (.inl h)
        · exact .inr (.inr h)
    · rename_i hc
      have hak := GroundTerm.cmp_eq _ _ hc
      subst hak
      simp only [List.mem_cons]
      constructor
      · rintro (h | h)
        · exact .inl h
        · exact .inr ⟨.inr h, hne_of e h⟩
      · rintro (h | ⟨h | h, hne⟩)
        · exact .inl h
        · subst h; exact absurd rfl hne
        · exact .inr h
    · rename_i hc
      have hka : k' ≠ a := fun h => by rw [h, GroundTerm.cmp_refl] at hc; cases hc
      rw [List.mem_cons, insertE_mem_iff_khk hks' e, List.mem_cons]
      constructor
      · rintro (h | h | ⟨h, hne⟩)
        · subst h; exact .inr ⟨.inl rfl, hka⟩
        · exact .inl h
        · exact .inr ⟨.inr h, hne⟩
      · rintro (h | ⟨h | h, hne⟩)
        · exact .inr (.inl h)
        · exact .inl h
        · exact .inr (.inr ⟨h, hne⟩)

/-- `eraseK` on entries with keys strictly increasing: the entries of other keys. -/
theorem eraseK_mem_iff_khk {a : GroundTerm} :
    ∀ {es : Entries}, keysSorted es = true → ∀ e, e ∈ eraseK a es ↔ e ∈ es ∧ e.1 ≠ a
  | [], _, e => by simp [eraseK]
  | (k', v') :: es, hks, e => by
    have hlt := keysSorted_lt_all hks
    have hks' := (keysSorted_cons.mp hks).1
    simp only [eraseK]
    split
    · rename_i hc
      have hak := GroundTerm.cmp_eq _ _ (beq_iff_eq.mp hc)
      subst hak
      rw [List.mem_cons]
      constructor
      · intro h
        refine ⟨.inr h, fun hx => ?_⟩
        have := hlt e h
        rw [hx, GroundTerm.cmp_refl] at this
        cases this
      · rintro ⟨h | h, hne⟩
        · subst h; exact absurd rfl hne
        · exact h
    · rename_i hc
      have hka : k' ≠ a := fun h => hc (by simp [h, GroundTerm.cmp_refl])
      rw [List.mem_cons, eraseK_mem_iff_khk hks' e, List.mem_cons]
      constructor
      · rintro (h | ⟨h, hne⟩)
        · subst h; exact ⟨.inl rfl, hka⟩
        · exact ⟨.inr h, hne⟩
      · rintro ⟨h | h, hne⟩
        · exact .inl h
        · exact .inr ⟨h, hne⟩

/-- `insertS` adds the member. -/
theorem insertS_mem_iff_khk {x : GroundTerm} :
    ∀ {es : List GroundTerm} {e : GroundTerm}, e ∈ insertS x es ↔ e = x ∨ e ∈ es
  | [], e => by simp [insertS]
  | e' :: es, e => by
    simp only [insertS]
    split
    · simp
    · rename_i hc
      have hx := GroundTerm.cmp_eq _ _ hc
      subst hx
      simp only [List.mem_cons]
      constructor
      · intro h; exact .inr h
      · rintro (h | h)
        · exact .inl h
        · exact h
    · rw [List.mem_cons, insertS_mem_iff_khk, List.mem_cons]
      constructor
      · rintro (h | h | h)
        · exact .inr (.inl h)
        · exact .inl h
        · exact .inr (.inr h)
      · rintro (h | h | h)
        · exact .inr (.inl h)
        · exact .inl h
        · exact .inr (.inr h)

/-- `unionS` holds the members of both sets. -/
theorem unionS_mem_iff_khk : ∀ {a b : List GroundTerm} {e : GroundTerm}, e ∈ unionS a b ↔ e ∈ a ∨ e ∈ b
  | [], b, e => by simp [unionS]
  | x :: a, b, e => by
    simp only [unionS, List.foldr_cons]
    rw [insertS_mem_iff_khk]
    have ih := unionS_mem_iff_khk (a := a) (b := b) (e := e)
    simp only [unionS] at ih
    rw [ih, List.mem_cons]
    constructor
    · rintro (h | h | h)
      · exact .inl (.inl h)
      · exact .inl (.inr h)
      · exact .inr h
    · rintro ((h | h) | h)
      · exact .inl h
      · exact .inr (.inl h)
      · exact .inr (.inr h)

/-- A map sorted at `Map`: the collection's sort is `Map`, its keys are strictly increasing, and each
key is sorted with kore.k literals. -/
theorem mapOK_khk {c : Semantics} {s : Srt} {es : Entries} (h : c.sortOf (.map s es) = some Srt.map)
    (l : litsV (.map s es) = true) :
    s = Srt.map ∧ keysSorted es = true ∧ ∀ e ∈ es, ∃ t, c.sortOf e.1 = some t ∧ litsV e.1 = true := by
  obtain ⟨-, -, -, -, -, -, hs⟩ := c.sortOf_map_inv h
  obtain ⟨k, w, -, -, hks, he⟩ := sortOf_map_kel h
  simp only [litsV, litsVE_iff] at l
  exact ⟨hs.symm, hks, fun e hm => ⟨_, (entriesOK_mem_kel he e hm).1, (l e hm).1⟩⟩

/-- A set sorted at `Set`: the collection's sort is `Set`, its members are strictly increasing, and
each is sorted with kore.k literals. -/
theorem setOK_khk {c : Semantics} {s : Srt} {A : List GroundTerm} (h : c.sortOf (.set s A) = some Srt.set)
    (l : litsV (.set s A) = true) :
    s = Srt.set ∧ A.Pairwise (fun a b => GroundTerm.cmp a b = .lt) ∧
      ∀ x ∈ A, ∃ t, c.sortOf x = some t ∧ litsV x = true := by
  obtain ⟨k, ss, -, -, hes, hss⟩ := sortOf_set_inv_kkc h
  have hs : s = Srt.set := by
    simp only [Semantics.sortOf] at h
    split at h
    · split at h
      · exact Option.some.inj h
      · cases h
    · cases h
  simp only [litsV, litsVL_iff] at l
  refine ⟨hs, elemsSorted_iff.mp hes, fun x hx => ?_⟩
  obtain ⟨t, -, ht⟩ := sortsOf_mem_kel hss x hx
  exact ⟨t, ht, l x hx⟩

/-- The encodings of entries whose keys are sorted with kore.k literals and strictly increasing,
put strictly increasing by `sortK`. -/
theorem encKvs_ok_khk {c : Semantics} {es : Entries} (hks : keysSorted es = true)
    (hk : ∀ e ∈ es, ∃ t, c.sortOf e.1 = some t ∧ litsV e.1 = true) :
    SortedK_khc (sortK (encKvs es)) ∧ ∀ f ∈ sortK (encKvs es), ElemOK_khc c .map f := by
  have hS : ∀ f ∈ encKvs es, ElemOK_khc c .map f := fun f hf => by
    rw [encKvs_eq_map] at hf
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hf
    obtain ⟨t, h1, h2⟩ := hk e he
    exact ⟨_, _, rfl, encSorted_enc h1 h2⟩
  refine ⟨sortK_ok_khc hS ?_, fun f hf => hS f (mem_sortK.mp hf)⟩
  have hp1 : (es.map Prod.fst).Pairwise (fun a b => GroundTerm.cmp a b = .lt) :=
    List.pairwise_map.mpr (keysSorted_pairwise_kel hks)
  have hkeys : (es.map Prod.fst).Nodup :=
    hp1.imp fun {a b} h he => by
      subst he; rw [GroundTerm.cmp_refl] at h; cases h
  have e1 : (encKvs es).map keyT_khc = (es.map Prod.fst).map enc := by
    rw [encKvs_eq_map, List.map_map, List.map_map]; rfl
  rw [e1]
  refine nodup_map_khc hkeys fun x hx y hy hxy => ?_
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
  obtain ⟨e', he', rfl⟩ := List.mem_map.mp hy
  obtain ⟨t, h1, l1⟩ := hk e he
  obtain ⟨t', h2, l2⟩ := hk e' he'
  exact enc_inj h1 h2 l1 l2 hxy

/-- The encodings of members sorted with kore.k literals and strictly increasing, put strictly
increasing by `sortK`. -/
theorem encEls_ok_khk {c : Semantics} {A : List GroundTerm} (hp : A.Pairwise (fun a b => GroundTerm.cmp a b = .lt))
    (hk : ∀ x ∈ A, ∃ t, c.sortOf x = some t ∧ litsV x = true) :
    SortedK_khc (sortK (encEls A)) ∧ ∀ f ∈ sortK (encEls A), ElemOK_khc c .set f := by
  have hS : ∀ f ∈ encEls A, ElemOK_khc c .set f := fun f hf => by
    rw [encEls_eq_map] at hf
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hf
    obtain ⟨t, h1, h2⟩ := hk x hx
    exact ⟨_, rfl, encSorted_enc h1 h2⟩
  refine ⟨sortK_ok_khc hS ?_, fun f hf => hS f (mem_sortK.mp hf)⟩
  have hnd : A.Nodup := hp.imp fun {a b} h he => by subst he; rw [GroundTerm.cmp_refl] at h; cases h
  have e1 : (encEls A).map keyT_khc = A.map enc := by
    rw [encEls_eq_map, List.map_map]; rfl
  rw [e1]
  refine nodup_map_khc hnd fun x hx y hy hxy => ?_
  obtain ⟨t, h1, l1⟩ := hk x hx
  obtain ⟨t', h2, l2⟩ := hk y hy
  exact enc_inj h1 h2 l1 l2 hxy

theorem mem_encKvs_khk {es : Entries} {x : T} :
    x ∈ sortK (encKvs es) ↔ ∃ e ∈ es, x = .kv (enc e.1) (enc e.2) := by
  rw [mem_sortK, encKvs_eq_map, List.mem_map]
  exact ⟨fun ⟨e, he, h⟩ => ⟨e, he, h.symm⟩, fun ⟨e, he, h⟩ => ⟨e, he, h.symm⟩⟩

theorem mem_encEls_khk {A : List GroundTerm} {x : T} :
    x ∈ sortK (encEls A) ↔ ∃ y ∈ A, x = .el (enc y) := by
  rw [mem_sortK, encEls_eq_map, List.mem_map]
  exact ⟨fun ⟨e, he, h⟩ => ⟨e, he, h.symm⟩, fun ⟨e, he, h⟩ => ⟨e, he, h.symm⟩⟩

end KMaps

/-! ## Each operation on the encodings -/

section Obj
open _root_.KK.Kit (ite_pos ite_neg)
variable {c : Semantics} {es : Entries}

/-- `valueOr` at a key's encoding over a sorted map's encoding: the encoding of the key's value,
`V` off the keys. -/
theorem valueOrF_map_khk (hks : keysSorted es = true)
    (hk : ∀ e ∈ es, ∃ t, c.sortOf e.1 = some t ∧ litsV e.1 = true) {a : GroundTerm} {t : Srt}
    (ha : c.sortOf a = some t) (la : litsV a = true) (v : T) :
    valueOrF (enc a) v (sortK (encKvs es)) = some ((findK a es).elim v enc) := by
  have hkv : ∀ f ∈ sortK (encKvs es), ∃ b w, f = .kv b w := fun f hf => by
    obtain ⟨e, -, rfl⟩ := mem_encKvs_khk.mp hf
    exact ⟨_, _, rfl⟩
  have hz : ∀ e ∈ es, cmpF (enc a) (enc e.1) = 0 ↔ a = e.1 := fun e he => by
    obtain ⟨t', h1, l1⟩ := hk e he
    exact cmpF_eq_zero_iff ha h1 la l1
  cases hf : findK a es with
  | some w =>
    obtain ⟨k', hk', hm⟩ := findK_key hf
    have hak := GroundTerm.cmp_eq _ _ hk'
    subst hak
    refine valueOrF_some_khk hkv (mem_encKvs_khk.mpr ⟨_, hm, rfl⟩) (cmpF_self _) fun b' w' hm' h0 => ?_
    obtain ⟨e, he, hee⟩ := mem_encKvs_khk.mp hm'
    cases hee
    rw [entry_unique_khk hks hm he ((hz e he).mp h0).symm]
    rfl
  | none =>
    refine valueOrF_none_khk fun f hf' => ?_
    obtain ⟨e, he, rfl⟩ := mem_encKvs_khk.mp hf'
    refine ⟨_, _, rfl, fun h0 => ?_⟩
    have := (hz e he).mp h0
    exact findK_none_khk hf e he (by rw [← this]; exact GroundTerm.cmp_refl a)

/-- `hasKey` of `kv(A, A)` over a sorted map's encoding: whether `A` is a key. -/
theorem hasKeyF_map_khk (hks : keysSorted es = true)
    (hk : ∀ e ∈ es, ∃ t, c.sortOf e.1 = some t ∧ litsV e.1 = true) {a : GroundTerm} {t : Srt}
    (ha : c.sortOf a = some t) (la : litsV a = true) :
    hasKeyF (.kv (enc a) (enc a)) (sortK (encKvs es)) = some (hasKey a es) := by
  obtain ⟨hp, hS⟩ := encKvs_ok_khk hks hk
  rw [hasKeyF_ok_khk (c := c) (k := .map) (e := .kv (enc a) (enc a)) ⟨_, _, rfl, encSorted_enc ha la⟩ hS,
    Option.some.injEq]
  refine Bool.eq_iff_iff.mpr ?_
  rw [decide_eq_true_iff, hasKey, List.any_eq_true]
  constructor
  · rintro ⟨f, hf, hkf⟩
    obtain ⟨e, he, rfl⟩ := mem_encKvs_khk.mp hf
    obtain ⟨t', h1, l1⟩ := hk e he
    have hea : e.1 = a := enc_inj h1 ha l1 la hkf
    exact ⟨e, he, by simp [hea, GroundTerm.cmp_refl]⟩
  · rintro ⟨e, he, hc⟩
    have hae := GroundTerm.cmp_eq _ _ (beq_iff_eq.mp hc)
    exact ⟨_, mem_encKvs_khk.mpr ⟨e, he, rfl⟩, by show enc e.1 = enc a; rw [hae]⟩

/-- `hasKey` of `el(X)` over a sorted set's encoding: whether `X` is a member. -/
theorem hasKeyF_set_khk {A : List GroundTerm} (hp : A.Pairwise (fun a b => GroundTerm.cmp a b = .lt))
    (hk : ∀ x ∈ A, ∃ t, c.sortOf x = some t ∧ litsV x = true) {a : GroundTerm} {t : Srt}
    (ha : c.sortOf a = some t) (la : litsV a = true) :
    hasKeyF (.el (enc a)) (sortK (encEls A)) = some (memS a A) := by
  obtain ⟨-, hS⟩ := encEls_ok_khk hp hk
  rw [hasKeyF_ok_khk (c := c) (k := .set) (e := .el (enc a)) ⟨_, rfl, encSorted_enc ha la⟩ hS, Option.some.injEq]
  refine Bool.eq_iff_iff.mpr ?_
  rw [decide_eq_true_iff, memS, List.any_eq_true]
  constructor
  · rintro ⟨f, hf, hkf⟩
    obtain ⟨y, hy, rfl⟩ := mem_encEls_khk.mp hf
    obtain ⟨t', h1, l1⟩ := hk y hy
    have hya : y = a := enc_inj h1 ha l1 la hkf
    exact ⟨y, hy, by simp [hya, GroundTerm.cmp_refl]⟩
  · rintro ⟨y, hy, hc⟩
    have hay := GroundTerm.cmp_eq _ _ (beq_iff_eq.mp hc)
    exact ⟨_, mem_encEls_khk.mpr ⟨y, hy, rfl⟩, by show enc y = enc a; rw [hay]⟩

/-- `putE` of `kv(A, V)` into a sorted map's encoding: the encoding's elements of the map
`insertE` gives. -/
theorem putEF_map_khk (hks : keysSorted es = true)
    (hk : ∀ e ∈ es, ∃ t, c.sortOf e.1 = some t ∧ litsV e.1 = true) {a : GroundTerm} {t : Srt}
    (ha : c.sortOf a = some t) (la : litsV a = true) (v : GroundTerm) :
    putEF (.kv (enc a) (enc v)) (sortK (encKvs es)) = some (sortK (encKvs (insertE a v es))) := by
  obtain ⟨hp, hS⟩ := encKvs_ok_khk hks hk
  obtain ⟨L, hL, hpL, -, hmL⟩ :=
    putEF_ok_khk (c := c) (k := .map) (e := .kv (enc a) (enc v)) ⟨_, _, rfl, encSorted_enc ha la⟩ hS hp
  have hk' : ∀ e ∈ insertE a v es, ∃ t, c.sortOf e.1 = some t ∧ litsV e.1 = true := fun e he => by
    rcases insertE_mem he with rfl | he
    · exact ⟨t, ha, la⟩
    · exact hk e he
  obtain ⟨hp', -⟩ := encKvs_ok_khk (insertE_sorted hks) hk'
  rw [hL, sortedK_eq_khk hpL hp' fun x => ?_]
  rw [hmL, mem_encKvs_khk, mem_encKvs_khk]
  have hkey : ∀ e ∈ es, (enc e.1 ≠ enc a ↔ e.1 ≠ a) := fun e he => by
    obtain ⟨t', h1, l1⟩ := hk e he
    exact not_congr ⟨enc_inj h1 ha l1 la, congrArg enc⟩
  constructor
  · rintro (rfl | ⟨⟨e, he, rfl⟩, hne⟩)
    · exact ⟨(a, v), (insertE_mem_iff_khk hks _).mpr (.inl rfl), rfl⟩
    · exact ⟨e, (insertE_mem_iff_khk hks _).mpr (.inr ⟨he, (hkey e he).mp hne⟩), rfl⟩
  · rintro ⟨e, he, rfl⟩
    rcases (insertE_mem_iff_khk hks e).mp he with rfl | ⟨he, hne⟩
    · exact .inl rfl
    · exact .inr ⟨⟨e, he, rfl⟩, (hkey e he).mpr hne⟩

/-- `delE` of `kv(A, A)` from a sorted map's encoding: the encoding's elements of the map `eraseK`
gives. -/
theorem delEF_map_khk (hks : keysSorted es = true)
    (hk : ∀ e ∈ es, ∃ t, c.sortOf e.1 = some t ∧ litsV e.1 = true) {a : GroundTerm} {t : Srt}
    (ha : c.sortOf a = some t) (la : litsV a = true) :
    delEF (.kv (enc a) (enc a)) (sortK (encKvs es)) = some (sortK (encKvs (eraseK a es))) := by
  obtain ⟨hp, hS⟩ := encKvs_ok_khk hks hk
  obtain ⟨L, hL, hsub, hmL⟩ :=
    delEF_ok_khk (c := c) (k := .map) (e := .kv (enc a) (enc a)) ⟨_, _, rfl, encSorted_enc ha la⟩ hS hp
  obtain ⟨hp', -⟩ := encKvs_ok_khk (eraseK_sorted hks) fun e he => hk e (eraseK_sublist he)
  rw [hL, sortedK_eq_khk (hp.sublist hsub) hp' fun x => ?_]
  rw [hmL, mem_encKvs_khk, mem_encKvs_khk]
  constructor
  · rintro ⟨⟨e, he, rfl⟩, hne⟩
    exact ⟨e, (eraseK_mem_iff_khk hks e).mpr ⟨he, fun h => hne (by show enc e.1 = enc a; rw [h])⟩, rfl⟩
  · rintro ⟨e, he, rfl⟩
    obtain ⟨he, hne⟩ := (eraseK_mem_iff_khk hks e).mp he
    obtain ⟨t', h1, l1⟩ := hk e he
    exact ⟨⟨e, he, rfl⟩, fun h => hne (enc_inj h1 ha l1 la h)⟩

/-- `union` of two sorted sets' encodings: the encoding's elements of the set `unionS` gives. -/
theorem unionF_set_enc_khk {A B : List GroundTerm} (hpA : A.Pairwise (fun a b => GroundTerm.cmp a b = .lt))
    (hkA : ∀ x ∈ A, ∃ t, c.sortOf x = some t ∧ litsV x = true)
    (hpB : B.Pairwise (fun a b => GroundTerm.cmp a b = .lt))
    (hkB : ∀ x ∈ B, ∃ t, c.sortOf x = some t ∧ litsV x = true) :
    unionF (sortK (encEls A)) (sortK (encEls B)) = some (sortK (encEls (unionS A B))) := by
  obtain ⟨hp, hS⟩ := encEls_ok_khk hpA hkA
  obtain ⟨-, hSB⟩ := encEls_ok_khk hpB hkB
  obtain ⟨L, hL, hpL, hmL⟩ := unionF_set_khk (c := c) _ hS hp hSB
  have hk' : ∀ x ∈ unionS A B, ∃ t, c.sortOf x = some t ∧ litsV x = true := fun x hx => by
    rcases unionS_mem_iff_khk.mp hx with hx | hx
    · exact hkA x hx
    · exact hkB x hx
  obtain ⟨hp', -⟩ := encEls_ok_khk (unionS_sorted hpB) hk'
  rw [hL, sortedK_eq_khk hpL hp' fun x => ?_]
  rw [hmL, mem_encEls_khk, mem_encEls_khk, mem_encEls_khk]
  constructor
  · rintro (⟨y, hy, rfl⟩ | ⟨y, hy, rfl⟩)
    · exact ⟨y, unionS_mem_iff_khk.mpr (.inl hy), rfl⟩
    · exact ⟨y, unionS_mem_iff_khk.mpr (.inr hy), rfl⟩
  · rintro ⟨y, hy, rfl⟩
    rcases unionS_mem_iff_khk.mp hy with hy | hy
    · exact .inl ⟨y, hy, rfl⟩
    · exact .inr ⟨y, hy, rfl⟩

end Obj

/-! ## The patterns -/

section Pats
open KCore.Det _root_.KK _root_.KK.Kit _root_.KK.Facts Terms

/-- `co(P, C, Es)` as a pattern denotes a collection term. -/
theorem pv_co_khk {σ : Subst} {p q r : Term} {t : T} (h : PatVal c₀ σ (.app 416 [p, q, r]) (emb t)) :
    ∃ k n es, t = .co k n es ∧ PatVal c₀ σ p (embK k) ∧ PatVal c₀ σ r (embTs es) := by
  obtain ⟨ws, he, hws⟩ := pv_ctor h
  rw [emb_ctor] at he
  obtain ⟨hh, rfl⟩ := GroundTerm.ctor.inj he
  obtain ⟨k, n, es, rfl⟩ := headOf_eq_co.mp hh
  rcases hws with _ | ⟨h1, _ | ⟨-, _ | ⟨h3, -⟩⟩⟩
  exact ⟨k, n, es, rfl, h1, h3⟩

/-- A kind constant as a pattern denotes that kind. -/
theorem pv_kind_khk {σ : Subst} {g : Sym} {k : Kind} (h : PatVal c₀ σ (.app g []) (embK k))
    (hc : c₀.isCtor g = true := by decide +kernel) (hp : patternHooks.contains g = false := by decide +kernel) :
    embK k = .ctor g [] := by
  obtain ⟨ws, he, hws⟩ := pv_ctor h hc hp
  cases hws
  exact he

theorem pv_as_khk {σ : Subst} {p : Term} {i : Nat} {v : GroundTerm} (h : PatVal c₀ σ (.as p i) v) :
    PatVal c₀ σ p v := by
  cases h with
  | as h _ => exact h

theorem embK_inj_khk {k k' : Kind} (h : embK k = embK k') : k = k' := by
  cases k <;> cases k' <;> first | rfl | (simp [embK] at h)

/-- `map` as a pattern. -/
theorem pv_map_khk {σ : Subst} {k : Kind} (h : PatVal c₀ σ (.app 429 []) (embK k)) : k = .map :=
  embK_inj_khk (pv_kind_khk h)

/-- `set` as a pattern. -/
theorem pv_set_khk {σ : Subst} {k : Kind} (h : PatVal c₀ σ (.app 438 []) (embK k)) : k = .set :=
  embK_inj_khk (pv_kind_khk h)

/-- `list` as a pattern. -/
theorem pv_list_khk {σ : Subst} {k : Kind} (h : PatVal c₀ σ (.app 427 []) (embK k)) : k = .list :=
  embK_inj_khk (pv_kind_khk h)

/-- The encoding of a value is a map's `co` term only at a map. -/
theorem enc_co_map_khk {v : GroundTerm} {n : Int} {es : List T} (h : enc v = .co .map n es) :
    ∃ s m, v = .map s m := by
  cases v with
  | map s m => exact ⟨s, m, rfl⟩
  | dv s l => rcases enc_dv_cases_kkc s l with ⟨_, h'⟩ | ⟨_, h'⟩ | ⟨_, _, h'⟩ | h' <;> rw [h'] at h <;> cases h
  | _ => simp [enc] at h

/-- The encoding of a value is a set's `co` term only at a set. -/
theorem enc_co_set_khk {v : GroundTerm} {n : Int} {es : List T} (h : enc v = .co .set n es) :
    ∃ s A, v = .set s A := by
  cases v with
  | set s A => exact ⟨s, A, rfl⟩
  | dv s l => rcases enc_dv_cases_kkc s l with ⟨_, h'⟩ | ⟨_, h'⟩ | ⟨_, _, h'⟩ | h' <;> rw [h'] at h <;> cases h
  | _ => simp [enc] at h

end Pats

/-! ## `hookOp` at each code -/

section Codes
open KCore.Det _root_.KK _root_.KK.Kit _root_.KK.Facts Terms HooksS

/-- An equation of `hookOp` of priority 50 decides where its patterns hold, at any result. -/
theorem op_clause_any_khk {cl : Clause} {σ : Subst} {o : Int} {ts : List T} {r : Option GroundTerm}
    (hm : cl ∈ opCls) (hσ : c₀.WellSorted cl.vars σ) (hp : PatVals c₀ σ cl.pats [.dv 3 (.int o), embTs ts])
    (hreq : cl.req = none) (hpr : cl.prio = 50)
    (hcl : cl.exs = [] ∧ cl.ens = none ∧ cl.pre = .top ∧ cl.post = .top)
    (hr : EvalTerm c₀ σ cl.rhs r) : Eval c₀ 473 [.dv 3 (.int o), embTs ts] r :=
  clause_kht hookOpDef_lookup (List.mem_append_left _ hm) hσ hp (fun _ h => by rw [hreq] at h; cases h)
    (by rw [hpr]; exact hookOp_low_khs) hcl hr

/-- `op-lookup` (40) at a map's `co` term and a key. -/
theorem hookOp_lookup_khk (n : Int) (es : List T) (a : T) :
    Eval c₀ 473 [.dv 3 (.int 40), embTs [.co .map n es, a]] ((valueOrF a .bot es).map emb) :=
  op_clause_any_khk (σ := enumFrom 0 [emb a, .dv 3 (.int n), embTs es]) (memOp_khs 16 : opLookup ∈ opCls)
    (ws_enum (.cons (emb_sorted_c₀ a) (.cons (sort_int n) (.cons (embTs_sorted_c₀ es) .nil))))
    (.cons .dv (.cons (.ctor ctor_407 (.cons (.ctor ctor_416 (.cons (.ctor ctor_429 .nil)
      (.cons (.var rfl) (.cons (.var rfl) .nil)))) (.cons (.ctor ctor_407 (.cons (.var rfl)
        (.cons (.ctor ctor_406 .nil) .nil))) .nil))) .nil))
    rfl rfl ⟨rfl, rfl, rfl, rfl⟩
    (ev_call (.cons (ev_var rfl) (.cons (ev_ctor .nil ctor_412) (.cons (ev_var rfl) .nil)))
      (valueOr_eval_khc a .bot es) notCtor_517 notHook_517 notParam_517)

/-- `op-lookup-or` (41) at a map's `co` term, a key and a default. -/
theorem hookOp_lookupOr_khk (n : Int) (es : List T) (a v : T) :
    Eval c₀ 473 [.dv 3 (.int 41), embTs [.co .map n es, a, v]] ((valueOrF a v es).map emb) :=
  op_clause_any_khk (σ := enumFrom 0 [.dv 3 (.int n), embTs es, emb a, emb v]) (memOp_khs 17 : opLookupOr ∈ opCls)
    (ws_enum (.cons (sort_int n) (.cons (embTs_sorted_c₀ es) (.cons (emb_sorted_c₀ a) (.cons (emb_sorted_c₀ v) .nil)))))
    (.cons .dv (.cons (.ctor ctor_407 (.cons (.ctor ctor_416 (.cons (.ctor ctor_429 .nil)
      (.cons (.var rfl) (.cons (.var rfl) .nil)))) (.cons (.ctor ctor_407 (.cons (.var rfl)
        (.cons (.ctor ctor_407 (.cons (.var rfl) (.cons (.ctor ctor_406 .nil) .nil))) .nil))) .nil))) .nil))
    rfl rfl ⟨rfl, rfl, rfl, rfl⟩
    (ev_call (.cons (ev_var rfl) (.cons (ev_var rfl) (.cons (ev_var rfl) .nil)))
      (valueOr_eval_khc a v es) notCtor_517 notHook_517 notParam_517)

/-- `op-update` (42) at a map's `co` term, a key and a value, where `putE` has a value. -/
theorem hookOp_update_khk (n : Int) (es : List T) (a v : T) {L : List T} (hL : putEF (.kv a v) es = some L) :
    Eval c₀ 473 [.dv 3 (.int 42), embTs [.co .map n es, a, v]] (some (emb (.co .map n L))) := by
  have hput := putE_eval_kho (.kv a v) es
  rw [hL] at hput
  exact op_clause_any_khk (σ := enumFrom 0 [emb v, embK .map, .dv 3 (.int n), embTs es, emb a])
    (memOp_khs 18 : opUpdate ∈ opCls)
    (ws_enum (.cons (emb_sorted_c₀ v) (.cons (embK_sorted_c₀ .map) (.cons (sort_int n)
      (.cons (embTs_sorted_c₀ es) (.cons (emb_sorted_c₀ a) .nil))))))
    (.cons .dv (.cons (.ctor ctor_407 (.cons (.ctor ctor_416 (.cons (.as (.ctor ctor_429 .nil) rfl)
      (.cons (.var rfl) (.cons (.var rfl) .nil)))) (.cons (.ctor ctor_407 (.cons (.var rfl)
        (.cons (.ctor ctor_407 (.cons (.var rfl) (.cons (.ctor ctor_406 .nil) .nil))) .nil))) .nil))) .nil))
    rfl rfl ⟨rfl, rfl, rfl, rfl⟩
    (ev_ctor (.cons (ev_var rfl) (.cons (ev_var rfl) (.cons (ev_call (.cons (ev_ctor (.cons (ev_var rfl)
      (.cons (ev_var rfl) .nil)) ctor_426) (.cons (ev_var rfl) .nil)) hput notCtor_500 notHook_500 notParam_500)
        .nil))) ctor_416)

/-- `op-remove` (43) at a map's `co` term and a key, where `delE` has a value. -/
theorem hookOp_remove_khk (n : Int) (es : List T) (a : T) {L : List T} (hL : delEF (.kv a a) es = some L) :
    Eval c₀ 473 [.dv 3 (.int 43), embTs [.co .map n es, a]] (some (emb (.co .map n L))) := by
  have hdel := delE_eval_khc (.kv a a) es
  rw [hL] at hdel
  exact op_clause_any_khk (σ := enumFrom 0 [embK .map, .dv 3 (.int n), embTs es, emb a])
    (memOp_khs 19 : opRemove ∈ opCls)
    (ws_enum (.cons (embK_sorted_c₀ .map) (.cons (sort_int n) (.cons (embTs_sorted_c₀ es)
      (.cons (emb_sorted_c₀ a) .nil)))))
    (.cons .dv (.cons (.ctor ctor_407 (.cons (.ctor ctor_416 (.cons (.as (.ctor ctor_429 .nil) rfl)
      (.cons (.var rfl) (.cons (.var rfl) .nil)))) (.cons (.ctor ctor_407 (.cons (.var rfl)
        (.cons (.ctor ctor_406 .nil) .nil))) .nil))) .nil))
    rfl rfl ⟨rfl, rfl, rfl, rfl⟩
    (ev_ctor (.cons (ev_var rfl) (.cons (ev_var rfl) (.cons (ev_call (.cons (ev_ctor (.cons (ev_var rfl)
      (.cons (ev_var rfl) .nil)) ctor_426) (.cons (ev_var rfl) .nil)) hdel notCtor_461 notHook_461 notParam_461)
        .nil))) ctor_416)

/-- `op-in-keys` (44) at a key and a map's `co` term, where `hasKey` has a value. -/
theorem hookOp_inKeys_khk (n : Int) (es : List T) (a : T) {b : Bool} (hb : hasKeyF (.kv a a) es = some b) :
    Eval c₀ 473 [.dv 3 (.int 44), embTs [a, .co .map n es]] (some (emb (.bv b))) := by
  have hhas := hasKey_eval_khc (.kv a a) es
  rw [hb] at hhas
  exact op_clause_any_khk (σ := enumFrom 0 [emb a, .dv 3 (.int n), embTs es]) (memOp_khs 20 : opInKeys ∈ opCls)
    (ws_enum (.cons (emb_sorted_c₀ a) (.cons (sort_int n) (.cons (embTs_sorted_c₀ es) .nil))))
    (.cons .dv (.cons (.ctor ctor_407 (.cons (.var rfl) (.cons (.ctor ctor_407 (.cons (.ctor ctor_416
      (.cons (.ctor ctor_429 .nil) (.cons (.var rfl) (.cons (.var rfl) .nil))))
        (.cons (.ctor ctor_406 .nil) .nil))) .nil))) .nil))
    rfl rfl ⟨rfl, rfl, rfl, rfl⟩
    (ev_ctor (.cons (ev_call (.cons (ev_ctor (.cons (ev_var rfl) (.cons (ev_var rfl) .nil)) ctor_426)
      (.cons (ev_var rfl) .nil)) hhas notCtor_472 notHook_472 notParam_472) .nil) ctor_413)

/-- `op-set-in` (50) at a term and a set's `co` term, where `hasKey` has a value. -/
theorem hookOp_setIn_khk (n : Int) (es : List T) (x : T) {b : Bool} (hb : hasKeyF (.el x) es = some b) :
    Eval c₀ 473 [.dv 3 (.int 50), embTs [x, .co .set n es]] (some (emb (.bv b))) := by
  have hhas := hasKey_eval_khc (.el x) es
  rw [hb] at hhas
  exact op_clause_any_khk (σ := enumFrom 0 [embTs es, emb x, .dv 3 (.int n)]) (memOp_khs 23 : opSetIn ∈ opCls)
    (ws_enum (.cons (embTs_sorted_c₀ es) (.cons (emb_sorted_c₀ x) (.cons (sort_int n) .nil))))
    (.cons .dv (.cons (.ctor ctor_407 (.cons (.var rfl) (.cons (.ctor ctor_407 (.cons (.ctor ctor_416
      (.cons (.ctor ctor_438 .nil) (.cons (.var rfl) (.cons (.var rfl) .nil))))
        (.cons (.ctor ctor_406 .nil) .nil))) .nil))) .nil))
    rfl rfl ⟨rfl, rfl, rfl, rfl⟩
    (ev_ctor (.cons (ev_call (.cons (ev_ctor (.cons (ev_var rfl) .nil) ctor_419)
      (.cons (ev_var rfl) .nil)) hhas notCtor_472 notHook_472 notParam_472) .nil) ctor_413)

/-- `op-union` (52) at two sets' `co` terms, where `union` has a value. -/
theorem hookOp_union_khk (n m : Int) (es fs : List T) {L : List T} (hL : unionF es fs = some L) :
    Eval c₀ 473 [.dv 3 (.int 52), embTs [.co .set n es, .co .set m fs]] (some (emb (.co .set n L))) := by
  have hun := union_eval_kho es fs
  rw [hL] at hun
  exact op_clause_any_khk (σ := enumFrom 0 [embK .set, embTs fs, .dv 3 (.int m), .dv 3 (.int n), embTs es])
    (memOp_khs 25 : opUnion ∈ opCls)
    (ws_enum (.cons (embK_sorted_c₀ .set) (.cons (embTs_sorted_c₀ fs) (.cons (sort_int m)
      (.cons (sort_int n) (.cons (embTs_sorted_c₀ es) .nil))))))
    (.cons .dv (.cons (.ctor ctor_407 (.cons (.ctor ctor_416 (.cons (.as (.ctor ctor_438 .nil) rfl)
      (.cons (.var rfl) (.cons (.var rfl) .nil)))) (.cons (.ctor ctor_407 (.cons (.ctor ctor_416
        (.cons (.as (.ctor ctor_438 .nil) rfl) (.cons (.var rfl) (.cons (.var rfl) .nil))))
          (.cons (.ctor ctor_406 .nil) .nil))) .nil))) .nil))
    rfl rfl ⟨rfl, rfl, rfl, rfl⟩
    (ev_ctor (.cons (ev_var rfl) (.cons (ev_var rfl) (.cons (ev_call (.cons (ev_var rfl) (.cons (ev_var rfl) .nil))
      hun notCtor_515 notHook_515 notParam_515) .nil))) ctor_416)

/-- kore.k's size of a collection term of kind `k`: `iv(len(Es))` at one `co` term of that kind,
`bot` at any other argument list (`op-undef`). -/
def sizeT_khk (k : Kind) : List T → T
  | [.co k' _ es] => if k' = k then .iv (lenF es) else .bot
  | _ => .bot

/-- A size code: its equation at one `co` term of its kind, `op-undef` at any other argument list. -/
theorem hookOp_size_khk {o : Int} {cl : Clause} {k : Kind} {g : Sym} {i j : Nat}
    (hf : opCls.filter (fun c => codeOf c == some o) = [cl])
    (hp : cl.pats = [.dv 3 (.int o), .app 407 [.app 416 [.app g [], .var i, .var j], .app 406 []]])
    (hg : ∀ {σ : Subst} {k' : Kind}, PatVal c₀ σ (.app g []) (embK k') → k' = k)
    (hpos : ∀ n es, Eval c₀ 473 [.dv 3 (.int o), embTs [.co k n es]] (some (emb (.iv (lenF es)))))
    (ts : List T) : Eval c₀ 473 [.dv 3 (.int o), embTs ts] (some (emb (sizeT_khk k ts))) := by
  by_cases hs : ∃ n es, ts = [.co k n es]
  · obtain ⟨n, es, rfl⟩ := hs
    rw [sizeT_khk, ite_pos rfl]
    exact hpos n es
  · have e : sizeT_khk k ts = .bot := by
      unfold sizeT_khk
      split
      · next k' n es =>
        split
        · next he => subst he; exact (hs ⟨n, es, rfl⟩).elim
        · rfl
      · rfl
    rw [e]
    refine hookOp_undef_khs fun c hc => ?_
    rw [hf, List.mem_singleton] at hc
    subst hc
    refine .intro fun σ _ hm => ?_
    rw [hp] at hm
    rcases hm with _ | ⟨-, _ | ⟨h1, -⟩⟩
    obtain ⟨t, ts', rfl, h2, h3⟩ := pv_cons_khs h1
    obtain rfl := pv_nil_khs h3
    obtain ⟨k', n, es, rfl, hk, -⟩ := pv_co_khk h2
    obtain rfl := hg hk
    exact (hs ⟨n, es, rfl⟩).elim

theorem hookOp_sizeMap_khk (ts : List T) :
    Eval c₀ 473 [.dv 3 (.int 45), embTs ts] (some (emb (sizeT_khk .map ts))) :=
  hookOp_size_khk (cl := opSizeMap) rfl rfl pv_map_khk (fun n es => op_clause_any_khk
    (σ := enumFrom 0 [.dv 3 (.int n), embTs es]) (memOp_khs 21 : opSizeMap ∈ opCls)
    (ws_enum (.cons (sort_int n) (.cons (embTs_sorted_c₀ es) .nil)))
    (.cons .dv (.cons (.ctor ctor_407 (.cons (.ctor ctor_416 (.cons (.ctor ctor_429 .nil)
      (.cons (.var rfl) (.cons (.var rfl) .nil)))) (.cons (.ctor ctor_406 .nil) .nil))) .nil))
    rfl rfl ⟨rfl, rfl, rfl, rfl⟩
    (ev_ctor (.cons (ev_call (.cons (ev_var rfl) .nil) (lenF_eval_c₀ es) notCtor_481 notHook_481 notParam_481)
      .nil) ctor_425)) ts

theorem hookOp_sizeSet_khk (ts : List T) :
    Eval c₀ 473 [.dv 3 (.int 51), embTs ts] (some (emb (sizeT_khk .set ts))) :=
  hookOp_size_khk (cl := opSizeSet) rfl rfl pv_set_khk (fun n es => op_clause_any_khk
    (σ := enumFrom 0 [embTs es, .dv 3 (.int n)]) (memOp_khs 24 : opSizeSet ∈ opCls)
    (ws_enum (.cons (embTs_sorted_c₀ es) (.cons (sort_int n) .nil)))
    (.cons .dv (.cons (.ctor ctor_407 (.cons (.ctor ctor_416 (.cons (.ctor ctor_438 .nil)
      (.cons (.var rfl) (.cons (.var rfl) .nil)))) (.cons (.ctor ctor_406 .nil) .nil))) .nil))
    rfl rfl ⟨rfl, rfl, rfl, rfl⟩
    (ev_ctor (.cons (ev_call (.cons (ev_var rfl) .nil) (lenF_eval_c₀ es) notCtor_481 notHook_481 notParam_481)
      .nil) ctor_425)) ts

theorem hookOp_sizeList_khk (ts : List T) :
    Eval c₀ 473 [.dv 3 (.int 60), embTs ts] (some (emb (sizeT_khk .list ts))) :=
  hookOp_size_khk (cl := opSizeList) rfl rfl pv_list_khk (fun n es => op_clause_any_khk
    (σ := enumFrom 0 [.dv 3 (.int n), embTs es]) (memOp_khs 26 : opSizeList ∈ opCls)
    (ws_enum (.cons (sort_int n) (.cons (embTs_sorted_c₀ es) .nil)))
    (.cons .dv (.cons (.ctor ctor_407 (.cons (.ctor ctor_416 (.cons (.ctor ctor_427 .nil)
      (.cons (.var rfl) (.cons (.var rfl) .nil)))) (.cons (.ctor ctor_406 .nil) .nil))) .nil))
    rfl rfl ⟨rfl, rfl, rfl, rfl⟩
    (ev_ctor (.cons (ev_call (.cons (ev_var rfl) .nil) (lenF_eval_c₀ es) notCtor_481 notHook_481 notParam_481)
      .nil) ctor_425)) ts

/-- `op-undef` at a code whose one equation fails. -/
theorem hookOp_fails_khk {o : Int} {cl : Clause} {ts : List T}
    (hf : opCls.filter (fun c => codeOf c == some o) = [cl]) (h : Fails c₀ [.dv 3 (.int o), embTs ts] cl) :
    Eval c₀ 473 [.dv 3 (.int o), embTs ts] (some (emb .bot)) :=
  hookOp_undef_khs fun c hc => by
    rw [hf, List.mem_singleton] at hc
    subst hc
    exact h

end Codes

/-! ## KCore's hooks -/

section Hooks
open KCore.Det

theorem hook_mapLookup_khk (vs : List GroundTerm) :
    hook mapLookup vs = some (match vs with | [.map _ m, k] => findK k m | _ => none) := rfl
theorem hook_mapLookupOr_khk (vs : List GroundTerm) :
    hook mapLookupOrDefault vs = some (match vs with | [.map _ m, k, d] => some ((findK k m).getD d) | _ => none) :=
  rfl
theorem hook_mapUpdate_khk (vs : List GroundTerm) :
    hook mapUpdate vs = some (match vs with | [.map _ m, k, v] => some (.map Srt.map (insertE k v m)) | _ => none) :=
  rfl
theorem hook_mapRemove_khk (vs : List GroundTerm) :
    hook mapRemove vs = some (match vs with | [.map _ m, k] => some (.map Srt.map (eraseK k m)) | _ => none) := rfl
theorem hook_mapInKeys_khk (vs : List GroundTerm) :
    hook mapInKeys vs = some (match vs with | [k, .map _ m] => some (bool (hasKey k m)) | _ => none) := rfl
theorem hook_mapSize_khk (vs : List GroundTerm) :
    hook mapSize vs = some (match vs with | [.map _ m] => some (int m.length) | _ => none) := rfl
theorem hook_setIn_khk (vs : List GroundTerm) :
    hook setIn vs = some (match vs with | [k, .set _ a] => some (bool (memS k a)) | _ => none) := rfl
theorem hook_setSize_khk (vs : List GroundTerm) :
    hook setSize vs = some (match vs with | [.set _ a] => some (int a.length) | _ => none) := rfl
theorem hook_setUnion_khk (vs : List GroundTerm) :
    hook setUnion vs = some (match vs with | [.set _ a, .set _ b] => some (.set Srt.set (unionS a b)) | _ => none) :=
  rfl
theorem hook_listSize_khk (vs : List GroundTerm) :
    hook listSize vs = some (match vs with | [.list _ a] => some (int a.length) | _ => none) := rfl

end Hooks

/-! ## Argument lists sorted at a signature -/

section Args

theorem sortsOf_cons_khk {c : Semantics} {v : GroundTerm} {vs : List GroundTerm} {a : Srt} {as : List Srt}
    (h : c.sortsOf (v :: vs) = some (a :: as)) : c.sortOf v = some a ∧ c.sortsOf vs = some as := by
  simp only [Semantics.sortsOf] at h
  split at h
  · next s ss hv hvs => cases h; exact ⟨hv, hvs⟩
  · cases h

theorem sortsOf_nil_khk {c : Semantics} {vs : List GroundTerm} (h : c.sortsOf vs = some []) : vs = [] := by
  cases vs with
  | nil => rfl
  | cons v vs =>
    simp only [Semantics.sortsOf] at h
    split at h <;> cases h

theorem sortsOf_ne_nil_khk {c : Semantics} {a : Srt} {as : List Srt} (h : c.sortsOf [] = some (a :: as)) : False := by
  simp [Semantics.sortsOf] at h

/-- The argument sorts `hookSigs` gives `f`. -/
theorem sortedArgs_sig_khk {c : Semantics} {f : Sym} {vs : List GroundTerm} {ss : List Srt} {r : Srt}
    (hk : lookupSig hookSigs f = some ⟨f, ss, r⟩) (h : SortedArgs_khs c f vs) : c.sortsOf vs = some ss := by
  obtain ⟨k, hk', hF⟩ := h
  rw [hk] at hk'
  cases hk'
  exact hF

theorem args2_khk {c : Semantics} {vs : List GroundTerm} {s₁ s₂ : Srt} (h : c.sortsOf vs = some [s₁, s₂]) :
    ∃ a b, vs = [a, b] ∧ c.sortOf a = some s₁ ∧ c.sortOf b = some s₂ := by
  match vs, h with
  | [], h => exact (sortsOf_ne_nil_khk h).elim
  | a :: vs', h =>
    obtain ⟨ha, h'⟩ := sortsOf_cons_khk h
    match vs', h' with
    | [], h' => exact (sortsOf_ne_nil_khk h').elim
    | b :: vs'', h' =>
      obtain ⟨hb, h''⟩ := sortsOf_cons_khk h'
      exact ⟨a, b, by rw [sortsOf_nil_khk h''], ha, hb⟩

theorem args3_khk {c : Semantics} {vs : List GroundTerm} {s₁ s₂ s₃ : Srt} (h : c.sortsOf vs = some [s₁, s₂, s₃]) :
    ∃ a b x, vs = [a, b, x] ∧ c.sortOf a = some s₁ ∧ c.sortOf b = some s₂ ∧ c.sortOf x = some s₃ := by
  match vs, h with
  | [], h => exact (sortsOf_ne_nil_khk h).elim
  | a :: vs', h =>
    obtain ⟨ha, h'⟩ := sortsOf_cons_khk h
    obtain ⟨b, x, rfl, hb, hx⟩ := args2_khk h'
    exact ⟨a, b, x, rfl, ha, hb, hx⟩

end Args

/-! ## `strictHook` at each code -/

section Coll
open KCore.Det _root_.KK _root_.KK.Kit _root_.KK.Facts Terms HooksS
open _root_.KK.Kit (ite_pos ite_neg)

/-- At arguments whose literals have a kore.k form, `strictHook` is `hookOp`. -/
theorem coll_of_khk {d : Semantics} {f : Sym} {o : Int} {vs : List GroundTerm} {r : T}
    (hk : silentKey f = false) (hl : ∀ v ∈ vs, litsV v = true)
    (hop : Eval c₀ 473 [.dv 3 (.int o), embTs (encTs vs)] (some (emb r)))
    (hr : r = encR (hook f vs).join) :
    Eval (K₀ sig) 508 [.dv 3 (.int o), embTs (encTs vs)] (some (emb (encR ((d₀ d).hookRes f vs).join))) :=
  scalar_of_khs hk (fun _ => hop) (by
    rw [strictT_of_khs (fun h => by rw [hasBotF_encTs_khs hl] at h; cases h), hr])

/-- `lookup` (code 40), at sorted arguments whose literals have a kore.k form. -/
theorem hooks_coll_lookup {d : Semantics} (vs : List GroundTerm) (hs : SortedArgs_khs (d₀ d) mapLookup vs)
    (hl : ∀ v ∈ vs, litsV v = true) :
    Eval (K₀ sig) 508 [.dv 3 (.int 40), embTs (encTs vs)] (some (emb (encR ((d₀ d).hookRes mapLookup vs).join))) := by
  obtain ⟨m, a, rfl, hm, ha⟩ := args2_khk (sortedArgs_sig_khk (ss := [Srt.map, Srt.kitem]) (r := Srt.kitem)
    (by decide +kernel) hs)
  have la := hl a (by simp)
  by_cases hmap : ∃ s es, m = .map s es
  · obtain ⟨s, es, rfl⟩ := hmap
    obtain ⟨-, hks, hk⟩ := mapOK_khk hm (hl _ (by simp))
    have h := hookOp_lookup_khk s (sortK (encKvs es)) (enc a)
    rw [valueOrF_map_khk hks hk ha la] at h
    exact coll_of_khk (by decide) hl h (by
      rw [hook_mapLookup_khk]
      show (findK a es).elim T.bot enc = encR (findK a es)
      cases findK a es <;> rfl)
  · refine coll_of_khk (by decide) hl (hookOp_fails_khk (cl := opLookup) rfl (.intro fun σ _ hm' => ?_)) ?_
    · rcases hm' with _ | ⟨-, _ | ⟨h1, -⟩⟩
      obtain ⟨t, ts', e₁, h2, -⟩ := pv_cons_khs h1
      cases e₁
      obtain ⟨k, n, es, he, hk, -⟩ := pv_co_khk h2
      obtain rfl := pv_map_khk hk
      exact (hmap (enc_co_map_khk he)).elim
    · rw [hook_mapLookup_khk]
      cases m <;> first | rfl | exact absurd ⟨_, _, rfl⟩ hmap

/-- `lookupOrDefault` (code 41), at sorted arguments whose literals have a kore.k form. -/
theorem hooks_coll_lookupOr {d : Semantics} (vs : List GroundTerm)
    (hs : SortedArgs_khs (d₀ d) mapLookupOrDefault vs) (hl : ∀ v ∈ vs, litsV v = true) :
    Eval (K₀ sig) 508 [.dv 3 (.int 41), embTs (encTs vs)]
      (some (emb (encR ((d₀ d).hookRes mapLookupOrDefault vs).join))) := by
  obtain ⟨m, a, v, rfl, hm, ha, -⟩ := args3_khk (sortedArgs_sig_khk (ss := [Srt.map, Srt.kitem, Srt.kitem])
    (r := Srt.kitem) (by decide +kernel) hs)
  have la := hl a (by simp)
  by_cases hmap : ∃ s es, m = .map s es
  · obtain ⟨s, es, rfl⟩ := hmap
    obtain ⟨-, hks, hk⟩ := mapOK_khk hm (hl _ (by simp))
    have h := hookOp_lookupOr_khk s (sortK (encKvs es)) (enc a) (enc v)
    rw [valueOrF_map_khk hks hk ha la] at h
    exact coll_of_khk (by decide) hl h (by
      rw [hook_mapLookupOr_khk]
      show (findK a es).elim (enc v) enc = enc ((findK a es).getD v)
      cases findK a es <;> rfl)
  · refine coll_of_khk (by decide) hl (hookOp_fails_khk (cl := opLookupOr) rfl (.intro fun σ _ hm' => ?_)) ?_
    · rcases hm' with _ | ⟨-, _ | ⟨h1, -⟩⟩
      obtain ⟨t, ts', e₁, h2, -⟩ := pv_cons_khs h1
      cases e₁
      obtain ⟨k, n, es, he, hk, -⟩ := pv_co_khk h2
      obtain rfl := pv_map_khk hk
      exact (hmap (enc_co_map_khk he)).elim
    · rw [hook_mapLookupOr_khk]
      cases m <;> first | rfl | exact absurd ⟨_, _, rfl⟩ hmap

/-- `update` (code 42), at sorted arguments whose literals have a kore.k form. -/
theorem hooks_coll_update {d : Semantics} (vs : List GroundTerm) (hs : SortedArgs_khs (d₀ d) mapUpdate vs)
    (hl : ∀ v ∈ vs, litsV v = true) :
    Eval (K₀ sig) 508 [.dv 3 (.int 42), embTs (encTs vs)] (some (emb (encR ((d₀ d).hookRes mapUpdate vs).join))) := by
  obtain ⟨m, a, v, rfl, hm, ha, -⟩ := args3_khk (sortedArgs_sig_khk (ss := [Srt.map, Srt.kitem, Srt.kitem])
    (r := Srt.map) (by decide +kernel) hs)
  have la := hl a (by simp)
  by_cases hmap : ∃ s es, m = .map s es
  · obtain ⟨s, es, rfl⟩ := hmap
    obtain ⟨rfl, hks, hk⟩ := mapOK_khk hm (hl _ (by simp))
    have h := hookOp_update_khk Srt.map (sortK (encKvs es)) (enc a) (enc v) (putEF_map_khk hks hk ha la v)
    exact coll_of_khk (by decide) hl h (by rw [hook_mapUpdate_khk]; rfl)
  · refine coll_of_khk (by decide) hl (hookOp_fails_khk (cl := opUpdate) rfl (.intro fun σ _ hm' => ?_)) ?_
    · rcases hm' with _ | ⟨-, _ | ⟨h1, -⟩⟩
      obtain ⟨t, ts', e₁, h2, -⟩ := pv_cons_khs h1
      cases e₁
      obtain ⟨k, n, es, he, hk, -⟩ := pv_co_khk h2
      obtain rfl := pv_map_khk (pv_as_khk hk)
      exact (hmap (enc_co_map_khk he)).elim
    · rw [hook_mapUpdate_khk]
      cases m <;> first | rfl | exact absurd ⟨_, _, rfl⟩ hmap

/-- `remove` (code 43), at sorted arguments whose literals have a kore.k form. -/
theorem hooks_coll_remove {d : Semantics} (vs : List GroundTerm) (hs : SortedArgs_khs (d₀ d) mapRemove vs)
    (hl : ∀ v ∈ vs, litsV v = true) :
    Eval (K₀ sig) 508 [.dv 3 (.int 43), embTs (encTs vs)] (some (emb (encR ((d₀ d).hookRes mapRemove vs).join))) := by
  obtain ⟨m, a, rfl, hm, ha⟩ := args2_khk (sortedArgs_sig_khk (ss := [Srt.map, Srt.kitem]) (r := Srt.map)
    (by decide +kernel) hs)
  have la := hl a (by simp)
  by_cases hmap : ∃ s es, m = .map s es
  · obtain ⟨s, es, rfl⟩ := hmap
    obtain ⟨rfl, hks, hk⟩ := mapOK_khk hm (hl _ (by simp))
    have h := hookOp_remove_khk Srt.map (sortK (encKvs es)) (enc a) (delEF_map_khk hks hk ha la)
    exact coll_of_khk (by decide) hl h (by rw [hook_mapRemove_khk]; rfl)
  · refine coll_of_khk (by decide) hl (hookOp_fails_khk (cl := opRemove) rfl (.intro fun σ _ hm' => ?_)) ?_
    · rcases hm' with _ | ⟨-, _ | ⟨h1, -⟩⟩
      obtain ⟨t, ts', e₁, h2, -⟩ := pv_cons_khs h1
      cases e₁
      obtain ⟨k, n, es, he, hk, -⟩ := pv_co_khk h2
      obtain rfl := pv_map_khk (pv_as_khk hk)
      exact (hmap (enc_co_map_khk he)).elim
    · rw [hook_mapRemove_khk]
      cases m <;> first | rfl | exact absurd ⟨_, _, rfl⟩ hmap

/-- `in_keys` (code 44), at sorted arguments whose literals have a kore.k form. -/
theorem hooks_coll_inKeys {d : Semantics} (vs : List GroundTerm) (hs : SortedArgs_khs (d₀ d) mapInKeys vs)
    (hl : ∀ v ∈ vs, litsV v = true) :
    Eval (K₀ sig) 508 [.dv 3 (.int 44), embTs (encTs vs)] (some (emb (encR ((d₀ d).hookRes mapInKeys vs).join))) := by
  obtain ⟨a, m, rfl, ha, hm⟩ := args2_khk (sortedArgs_sig_khk (ss := [Srt.kitem, Srt.map]) (r := Srt.bool)
    (by decide +kernel) hs)
  have la := hl a (by simp)
  by_cases hmap : ∃ s es, m = .map s es
  · obtain ⟨s, es, rfl⟩ := hmap
    obtain ⟨-, hks, hk⟩ := mapOK_khk hm (hl _ (by simp))
    have h := hookOp_inKeys_khk s (sortK (encKvs es)) (enc a) (hasKeyF_map_khk hks hk ha la)
    exact coll_of_khk (by decide) hl h (by rw [hook_mapInKeys_khk]; rfl)
  · refine coll_of_khk (by decide) hl (hookOp_fails_khk (cl := opInKeys) rfl (.intro fun σ _ hm' => ?_)) ?_
    · rcases hm' with _ | ⟨-, _ | ⟨h1, -⟩⟩
      obtain ⟨t, ts', e₁, -, h3⟩ := pv_cons_khs h1
      cases e₁
      obtain ⟨u, ts'', e₂, h4, -⟩ := pv_cons_khs h3
      cases e₂
      obtain ⟨k, n, es, he, hk, -⟩ := pv_co_khk h4
      obtain rfl := pv_map_khk hk
      exact (hmap (enc_co_map_khk he)).elim
    · rw [hook_mapInKeys_khk]
      cases m <;> first | rfl | exact absurd ⟨_, _, rfl⟩ hmap

theorem length_sortK_khk (L : List T) : (sortK L).length = L.length := (sortK_perm L).length_eq

/-- A list holding `bot` is no single `co` term. -/
theorem sizeT_bot_khk {k : Kind} {ts : List T} (h : hasBotF ts = true) : sizeT_khk k ts = .bot := by
  unfold sizeT_khk
  split
  · simp [hasBotF] at h
  · rfl

/-- A term that is no `co` term of kind `k` has no size. -/
theorem sizeT_enc_other_khk {k : Kind} {t : T} (h : ∀ n es, t ≠ .co k n es) : sizeT_khk k [t] = .bot := by
  cases t with
  | co k' n es =>
    show (if k' = k then T.iv (lenF es) else .bot) = .bot
    rw [ite_neg fun hk => h n es (by rw [hk])]
  | _ => rfl

theorem enc_dv_ne_co_khk (s : Srt) (l : Lit) (k : Kind) (n : Int) (es : List T) : enc (.dv s l) ≠ .co k n es := by
  rcases enc_dv_cases_kkc s l with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, _, h⟩ | h <;> rw [h] <;> intro h' <;> cases h'

/-- A list of two terms or more has no size. -/
theorem sizeT_long_khk {k : Kind} {a b : T} {l : List T} : sizeT_khk k (a :: b :: l) = .bot := by
  cases a <;> rfl

/-- `size` of a map (code 45), at every argument list. -/
theorem hooks_coll_sizeMap {d : Semantics} (vs : List GroundTerm) :
    Eval (K₀ sig) 508 [.dv 3 (.int 45), embTs (encTs vs)] (some (emb (encR ((d₀ d).hookRes mapSize vs).join))) :=
  scalar_of_khs (by decide) (fun _ => hookOp_sizeMap_khk _) (by
    rw [strictT_of_khs sizeT_bot_khk, hook_mapSize_khk, Option.join_some]
    match vs with
    | [v] =>
      show sizeT_khk .map [enc v] = _
      cases v with
      | map s m =>
        show (if Kind.map = Kind.map then T.iv (lenF (sortK (encKvs m))) else .bot) = enc (int m.length)
        rw [ite_pos rfl, lenF, length_sortK_khk, encKvs_eq_map, List.length_map]; rfl
      | dv s l => exact sizeT_enc_other_khk (enc_dv_ne_co_khk s l .map)
      | ctor f vs => rfl
      | inj a b w => rfl
      | set s A => rfl
      | list s A => rfl
    | [] => rfl
    | a :: b :: l =>
      show sizeT_khk _ (enc a :: enc b :: encTs l) = _
      rw [sizeT_long_khk]
      cases a <;> rfl)

/-- `size` of a set (code 51), at every argument list. -/
theorem hooks_coll_sizeSet {d : Semantics} (vs : List GroundTerm) :
    Eval (K₀ sig) 508 [.dv 3 (.int 51), embTs (encTs vs)] (some (emb (encR ((d₀ d).hookRes setSize vs).join))) :=
  scalar_of_khs (by decide) (fun _ => hookOp_sizeSet_khk _) (by
    rw [strictT_of_khs sizeT_bot_khk, hook_setSize_khk, Option.join_some]
    match vs with
    | [v] =>
      show sizeT_khk .set [enc v] = _
      cases v with
      | set s A =>
        show (if Kind.set = Kind.set then T.iv (lenF (sortK (encEls A))) else .bot) = enc (int A.length)
        rw [ite_pos rfl, lenF, length_sortK_khk, encEls_eq_map, List.length_map]; rfl
      | dv s l => exact sizeT_enc_other_khk (enc_dv_ne_co_khk s l .set)
      | ctor f vs => rfl
      | inj a b w => rfl
      | map s m => rfl
      | list s A => rfl
    | [] => rfl
    | a :: b :: l =>
      show sizeT_khk _ (enc a :: enc b :: encTs l) = _
      rw [sizeT_long_khk]
      cases a <;> rfl)

/-- `size` of a list (code 60), at every argument list. -/
theorem hooks_coll_sizeList {d : Semantics} (vs : List GroundTerm) :
    Eval (K₀ sig) 508 [.dv 3 (.int 60), embTs (encTs vs)] (some (emb (encR ((d₀ d).hookRes listSize vs).join))) :=
  scalar_of_khs (by decide) (fun _ => hookOp_sizeList_khk _) (by
    rw [strictT_of_khs sizeT_bot_khk, hook_listSize_khk, Option.join_some]
    match vs with
    | [v] =>
      show sizeT_khk .list [enc v] = _
      cases v with
      | list s A =>
        show (if Kind.list = Kind.list then T.iv (lenF (encEls A)) else .bot) = enc (int A.length)
        rw [ite_pos rfl, lenF, encEls_eq_map, List.length_map]; rfl
      | dv s l => exact sizeT_enc_other_khk (enc_dv_ne_co_khk s l .list)
      | ctor f vs => rfl
      | inj a b w => rfl
      | map s m => rfl
      | set s A => rfl
    | [] => rfl
    | a :: b :: l =>
      show sizeT_khk _ (enc a :: enc b :: encTs l) = _
      rw [sizeT_long_khk]
      cases a <;> rfl)

/-- Set membership (code 50), at sorted arguments whose literals have a kore.k form. -/
theorem hooks_coll_setIn {d : Semantics} (vs : List GroundTerm) (hs : SortedArgs_khs (d₀ d) setIn vs)
    (hl : ∀ v ∈ vs, litsV v = true) :
    Eval (K₀ sig) 508 [.dv 3 (.int 50), embTs (encTs vs)] (some (emb (encR ((d₀ d).hookRes setIn vs).join))) := by
  obtain ⟨x, A, rfl, hx, hA⟩ := args2_khk (sortedArgs_sig_khk (ss := [Srt.kitem, Srt.set]) (r := Srt.bool)
    (by decide +kernel) hs)
  have lx := hl x (by simp)
  by_cases hset : ∃ s B, A = .set s B
  · obtain ⟨s, B, rfl⟩ := hset
    obtain ⟨-, hp, hk⟩ := setOK_khk hA (hl _ (by simp))
    have h := hookOp_setIn_khk s (sortK (encEls B)) (enc x) (hasKeyF_set_khk hp hk hx lx)
    exact coll_of_khk (by decide) hl h (by rw [hook_setIn_khk]; rfl)
  · refine coll_of_khk (by decide) hl (hookOp_fails_khk (cl := opSetIn) rfl (.intro fun σ _ hm' => ?_)) ?_
    · rcases hm' with _ | ⟨-, _ | ⟨h1, -⟩⟩
      obtain ⟨t, ts', e₁, -, h3⟩ := pv_cons_khs h1
      cases e₁
      obtain ⟨u, ts'', e₂, h4, -⟩ := pv_cons_khs h3
      cases e₂
      obtain ⟨k, n, es, he, hk, -⟩ := pv_co_khk h4
      obtain rfl := pv_set_khk hk
      exact (hset (enc_co_set_khk he)).elim
    · rw [hook_setIn_khk]
      cases A <;> first | rfl | exact absurd ⟨_, _, rfl⟩ hset

/-- Set union (code 52), at sorted arguments whose literals have a kore.k form. -/
theorem hooks_coll_union {d : Semantics} (vs : List GroundTerm) (hs : SortedArgs_khs (d₀ d) setUnion vs)
    (hl : ∀ v ∈ vs, litsV v = true) :
    Eval (K₀ sig) 508 [.dv 3 (.int 52), embTs (encTs vs)] (some (emb (encR ((d₀ d).hookRes setUnion vs).join))) := by
  obtain ⟨A, B, rfl, hA, hB⟩ := args2_khk (sortedArgs_sig_khk (ss := [Srt.set, Srt.set]) (r := Srt.set)
    (by decide +kernel) hs)
  by_cases hset : (∃ s A', A = .set s A') ∧ ∃ s B', B = .set s B'
  · obtain ⟨⟨s, A', rfl⟩, ⟨s', B', rfl⟩⟩ := hset
    obtain ⟨rfl, hpA, hkA⟩ := setOK_khk hA (hl _ (by simp))
    obtain ⟨-, hpB, hkB⟩ := setOK_khk hB (hl _ (by simp))
    have h := hookOp_union_khk Srt.set s' (sortK (encEls A')) (sortK (encEls B'))
      (unionF_set_enc_khk hpA hkA hpB hkB)
    exact coll_of_khk (by decide) hl h (by rw [hook_setUnion_khk]; rfl)
  · refine coll_of_khk (by decide) hl (hookOp_fails_khk (cl := opUnion) rfl (.intro fun σ _ hm' => ?_)) ?_
    · rcases hm' with _ | ⟨-, _ | ⟨h1, -⟩⟩
      obtain ⟨t, ts', e₁, h2, h3⟩ := pv_cons_khs h1
      cases e₁
      obtain ⟨u, ts'', e₂, h4, -⟩ := pv_cons_khs h3
      cases e₂
      obtain ⟨k, n, es, he, hk, -⟩ := pv_co_khk h2
      obtain rfl := pv_set_khk (pv_as_khk hk)
      obtain ⟨k', n', es', he', hk', -⟩ := pv_co_khk h4
      obtain rfl := pv_set_khk (pv_as_khk hk')
      exact (hset ⟨enc_co_set_khk he, enc_co_set_khk he'⟩).elim
    · rw [hook_setUnion_khk]
      cases A <;> cases B <;> first | rfl | exact absurd ⟨⟨_, _, rfl⟩, ⟨_, _, rfl⟩⟩ hset

end Coll

/-! ## Every collection code -/

section Uniform
open KCore.Det _root_.KK

/-- The codes of `hookCodes` this module covers: the collections'. -/
def collCodes_khk : List (Sym × Int) := hookCodes.filter fun p => 40 ≤ p.2 && p.2 < 70

theorem collCodes_eq_khk : collCodes_khk =
    [(mapLookup, 40), (mapLookupOrDefault, 41), (mapUpdate, 42), (mapRemove, 43), (mapInKeys, 44),
     (mapSize, 45), (setIn, 50), (setSize, 51), (setUnion, 52), (listSize, 60)] := by decide +kernel

/-- At a pair of `collCodes_khk`, `strictHook` at the encoded arguments evaluates at `K₀ sig` to the
encoding of KCore's result. -/
theorem hooks_coll_mem_khk {d : Semantics} {f : Sym} {o : Int} (hfo : (f, o) ∈ collCodes_khk) (vs : List GroundTerm)
    (hs : SortedArgs_khs (d₀ d) f vs) (hl : ∀ v ∈ vs, litsV v = true) :
    Eval (K₀ sig) 508 [.dv 3 (.int o), embTs (encTs vs)] (some (emb (encR ((d₀ d).hookRes f vs).join))) := by
  rw [collCodes_eq_khk] at hfo
  simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hfo
  rcases hfo with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact hooks_coll_lookup vs hs hl
  · exact hooks_coll_lookupOr vs hs hl
  · exact hooks_coll_update vs hs hl
  · exact hooks_coll_remove vs hs hl
  · exact hooks_coll_inKeys vs hs hl
  · exact hooks_coll_sizeMap vs
  · exact hooks_coll_setIn vs hs hl
  · exact hooks_coll_sizeSet vs
  · exact hooks_coll_union vs hs hl
  · exact hooks_coll_sizeList vs

/-- **The collection hook lemma.** At the code `o` (`opOf`) of an interpreted symbol `f` of Map, Set
or List (`40 ≤ o < 70`), `strictHook` at the encoded arguments evaluates at `K₀ sig` to the encoding
of KCore's result, for every semantics `d`, at arguments sorted at `f`'s argument sorts whose
literals have a kore.k form. -/
theorem hooks_coll {d : Semantics} {f : Sym} {o : Int} (hfo : opOf f = some o) (ho : 40 ≤ o ∧ o < 70)
    (vs : List GroundTerm) (hs : SortedArgs_khs (d₀ d) f vs) (hl : ∀ v ∈ vs, litsV v = true) :
    Eval (K₀ sig) 508 [.dv 3 (.int o), embTs (encTs vs)] (some (emb (encR ((d₀ d).hookRes f vs).join))) :=
  hooks_coll_mem_khk (List.mem_filter.mpr ⟨opOf_mem_khs hfo, by simp [ho.1, ho.2]⟩) vs hs hl

end Uniform

/-! ## Instances -/

section Instances
open _root_.KK _root_.KK.Kit

/-- An Int as a `KItem`. -/
abbrev ik_khk (x : Int) : GroundTerm := .inj Srt.int Srt.kitem (int x)

/-- The map `1 |-> 2`. -/
abbrev m12_khk : GroundTerm := .map Srt.map [(ik_khk 1, ik_khk 2)]

/-- `(1 |-> 2) [1]` is `2`. -/
example : Eval (K₀ sig) 508 [.dv 3 (.int 40), embTs (encTs [m12_khk, ik_khk 1])] (some (emb (enc (ik_khk 2)))) :=
  hooks_coll_lookup (d := RefKk.defn.sem) _ ⟨⟨mapLookup, [Srt.map, Srt.kitem], Srt.kitem⟩, by decide +kernel,
    by decide +kernel⟩ (by decide)

/-- `(1 |-> 2) [3]` has no value on either side. -/
example : Eval (K₀ sig) 508 [.dv 3 (.int 40), embTs (encTs [m12_khk, ik_khk 3])] (some (emb .bot)) :=
  hooks_coll_lookup (d := RefKk.defn.sem) _ ⟨⟨mapLookup, [Srt.map, Srt.kitem], Srt.kitem⟩, by decide +kernel,
    by decide +kernel⟩ (by decide)

/-- `(1 |-> 2) [1 <- 5]` is `1 |-> 5`, through the uniform statement. -/
example : Eval (K₀ sig) 508 [.dv 3 (.int 42), embTs (encTs [m12_khk, ik_khk 1, ik_khk 5])]
    (some (emb (enc (.map Srt.map [(ik_khk 1, ik_khk 5)])))) :=
  hooks_coll (d := RefKk.defn.sem) (f := mapUpdate) rfl (by decide) _
    ⟨⟨mapUpdate, [Srt.map, Srt.kitem, Srt.kitem], Srt.map⟩, by decide +kernel, by decide +kernel⟩ (by decide)

/-- `(1 |-> 2) [1 <- undef]` is the empty map. -/
example : Eval (K₀ sig) 508 [.dv 3 (.int 43), embTs (encTs [m12_khk, ik_khk 1])]
    (some (emb (enc (.map Srt.map [])))) :=
  hooks_coll_remove (d := RefKk.defn.sem) _ ⟨⟨mapRemove, [Srt.map, Srt.kitem], Srt.map⟩, by decide +kernel,
    by decide +kernel⟩ (by decide)

/-- `3 in_keys (1 |-> 2)` is `false`. -/
example : Eval (K₀ sig) 508 [.dv 3 (.int 44), embTs (encTs [ik_khk 3, m12_khk])] (some (emb (.bv false))) :=
  hooks_coll_inKeys (d := RefKk.defn.sem) _ ⟨⟨mapInKeys, [Srt.kitem, Srt.map], Srt.bool⟩, by decide +kernel,
    by decide +kernel⟩ (by decide)

/-- `SetItem(1) |Set SetItem(2)` holds 1 and 2, and `2 in` it. -/
example : Eval (K₀ sig) 508 [.dv 3 (.int 52), embTs (encTs [.set Srt.set [ik_khk 1], .set Srt.set [ik_khk 2]])]
    (some (emb (enc (.set Srt.set [ik_khk 1, ik_khk 2])))) :=
  hooks_coll_union (d := RefKk.defn.sem) _ ⟨⟨setUnion, [Srt.set, Srt.set], Srt.set⟩, by decide +kernel,
    by decide +kernel⟩ (by decide)

example : Eval (K₀ sig) 508 [.dv 3 (.int 50), embTs (encTs [ik_khk 2, .set Srt.set [ik_khk 1, ik_khk 2]])]
    (some (emb (.bv true))) :=
  hooks_coll_setIn (d := RefKk.defn.sem) _ ⟨⟨setIn, [Srt.kitem, Srt.set], Srt.bool⟩, by decide +kernel,
    by decide +kernel⟩ (by decide)

/-- The sizes: of a map, of a set, of a list, and of a term that is no collection. -/
example : Eval (K₀ sig) 508 [.dv 3 (.int 45), embTs (encTs [m12_khk])] (some (emb (.iv 1))) :=
  hooks_coll_sizeMap (d := RefKk.defn.sem) _

example : Eval (K₀ sig) 508 [.dv 3 (.int 51), embTs (encTs [.set Srt.set [ik_khk 1, ik_khk 2]])]
    (some (emb (.iv 2))) :=
  hooks_coll_sizeSet (d := RefKk.defn.sem) _

example : Eval (K₀ sig) 508 [.dv 3 (.int 60), embTs (encTs [.list Srt.list [ik_khk 1, ik_khk 1, ik_khk 2]])]
    (some (emb (.iv 3))) :=
  hooks_coll_sizeList (d := RefKk.defn.sem) _

example : Eval (K₀ sig) 508 [.dv 3 (.int 60), embTs (encTs [int 4])] (some (emb .bot)) :=
  hooks_coll_sizeList (d := RefKk.defn.sem) _

end Instances

/-! ## Checks -/

#check @hooks_coll
#check @hooks_coll_lookup
#check @hooks_coll_lookupOr
#check @hooks_coll_update
#check @hooks_coll_remove
#check @hooks_coll_inKeys
#check @hooks_coll_sizeMap
#check @hooks_coll_setIn
#check @hooks_coll_sizeSet
#check @hooks_coll_union
#check @hooks_coll_sizeList

open Lean in
#eval show CoreM Unit from do
  for n in [``hooks_coll_lookup, ``hooks_coll_lookupOr, ``hooks_coll_update, ``hooks_coll_remove,
      ``hooks_coll_inKeys, ``hooks_coll_sizeMap, ``hooks_coll_setIn, ``hooks_coll_sizeSet, ``hooks_coll_union,
      ``hooks_coll_sizeList, ``hooks_coll_mem_khk, ``hooks_coll, ``sortedK_eq_khk, ``putEF_ok_khk, ``delEF_ok_khk,
      ``unionF_set_khk, ``valueOrF_map_khk, ``putEF_map_khk, ``delEF_map_khk, ``unionF_set_enc_khk] do
    let axs ← collectAxioms n
    unless axs.all ([``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "{n}: axioms {axs}"

end KCore.KK
