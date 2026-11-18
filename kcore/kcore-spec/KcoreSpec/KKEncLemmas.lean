import KcoreSpec.KKEncDef
import KcoreSpec.SetLaws

/-!
# What `encDef` writes

The ensures of an encoded clause or rule is its ensures, encoded: `encTerm` writes `en` at the top
of no term, so `Cl.ens` and `Rl.ens` find exactly the `en` that `encRhs` writes for an ensures.

`enc` writes `bot` only at a literal `kore.k` has no form for (`enc_ne_bot`, over `litsV`); under
`encodable c` no value of `c` at a sort other than `Float` has one (`litsV_of_sorted`); on such
values sorted in one semantics `enc` is injective (`enc_inj`), so on the configurations of `d₀ d`
under `encDef d = some E` (`enc_injective`). Under `encodable d` every term of `d`'s rules and
clauses has a `kore.k` form, so `encT` never writes `bot` for one (`encTerm_of_encodable`).
-/

set_option autoImplicit false

namespace KCore.KK
open GroundTerm

/-- `encTerm` writes no `en` at the top of a term. -/
theorem encTermWith_ne_en (d : Semantics) (lit : Srt → Lit → Option T)
    (hlit : ∀ s l a b, lit s l ≠ some (.en a b)) (t : Term) (a b : T) :
    encTermWith d lit t ≠ some (.en a b) := by
  cases t with
  | var i => simp [encTermWith]
  | dv s l => simpa [encTermWith] using hlit s l a b
  | inj x y t => simp only [encTermWith]; cases encTermWith d lit t <;> simp
  | as t i => simp only [encTermWith]; cases encTermWith d lit t <;> simp
  | app f ts =>
    simp only [encTermWith, readApp]
    split
    · cases encTermsWith d lit ts <;> simp
    · split
      · cases (collSymOf d f).bind _ <;> simp
      · split
        · split
          · cases encTermsWith d lit ts <;> simp
          · cases encTermsWith d lit ts <;> simp [derivedHook] <;> split <;> simp
        · split
          · simp
          · split
            · cases encTermsWith d lit ts <;> simp
            · simp

theorem encLit_ne_en (s : Srt) (l : Lit) (a b : T) : encLit s l ≠ some (.en a b) := by
  unfold encLit encLitWith; split <;> simp

theorem encT_ne_en (d : Semantics) (t : Term) (a b : T) : encT d t ≠ .en a b := by
  unfold encT encTerm
  cases h : encTermWith d encLit t with
  | none => simp
  | some p => simp only [Option.getD_some]; rintro rfl; exact encTermWith_ne_en d encLit encLit_ne_en t a b h

/-- The ensures of an encoded clause is its ensures, encoded. -/
theorem encCl_ens (d : Semantics) (cl : Clause) : (encCl d cl).ens = cl.ens.map (encT d) := by
  unfold encCl encRhs
  cases h : cl.ens with
  | some e => rfl
  | none =>
    simp only [Option.map_none]
    unfold Cl.ens
    split
    · rename_i r e' heq; simp at heq; exact absurd heq.2.2.2.2 (encT_ne_en d cl.rhs r e')
    · rfl

theorem encRl_ens (d : Semantics) (r : Rule) : (encRl d r).ens = r.ens.map (encT d) := by
  unfold encRl encRhs
  cases h : r.ens with
  | some e => rfl
  | none =>
    simp only [Option.map_none]
    unfold Rl.ens
    split
    · rename_i x e' heq; simp at heq; exact absurd heq.2.2.2.2 (encT_ne_en d r.rhs x e')
    · rfl

/-! ## Induction over values, with the members of a list -/

/-- Induction over values, a list's and a map's members given at once. -/
theorem gtInd_kel (P : GroundTerm → Prop)
    (hctor : ∀ f vs, (∀ v ∈ vs, P v) → P (.ctor f vs))
    (hinj : ∀ a b t, P t → P (.inj a b t))
    (hdv : ∀ s l, P (.dv s l))
    (hmap : ∀ s es, (∀ e ∈ es, P e.1 ∧ P e.2) → P (.map s es))
    (hset : ∀ s es, (∀ v ∈ es, P v) → P (.set s es))
    (hlist : ∀ s es, (∀ v ∈ es, P v) → P (.list s es)) (v : GroundTerm) : P v :=
  GroundTerm.rec (motive_1 := P) (motive_2 := fun vs => ∀ v ∈ vs, P v)
    (motive_3 := fun es => ∀ e ∈ es, P e.1 ∧ P e.2) (motive_4 := fun e => P e.1 ∧ P e.2)
    hctor hinj hdv hmap hset hlist
    (fun _ h => nomatch h)
    (fun _ _ hx hxs y hy => match List.mem_cons.mp hy with
      | .inl h => h ▸ hx
      | .inr h => hxs y h)
    (fun _ h => nomatch h)
    (fun _ _ he hes y hy => match List.mem_cons.mp hy with
      | .inl h => h ▸ he
      | .inr h => hes y h)
    (fun _ _ hk hv => ⟨hk, hv⟩) v

/-! ## `enc` on lists, and `sortK` -/

theorem encTs_eq_map : ∀ vs : List GroundTerm, encTs vs = vs.map enc
  | [] => by simp [encTs]
  | v :: vs => by simp [encTs, encTs_eq_map vs]

theorem encEls_eq_map : ∀ vs : List GroundTerm, encEls vs = vs.map fun v => .el (enc v)
  | [] => by simp [encEls]
  | v :: vs => by simp [encEls, encEls_eq_map vs]

theorem encKvs_eq_map : ∀ es : List (GroundTerm × GroundTerm),
    encKvs es = es.map fun e => .kv (enc e.1) (enc e.2)
  | [] => by simp [encKvs]
  | (k, v) :: es => by simp [encKvs, encKv, encKvs_eq_map es]

theorem mem_insK {x e : T} : ∀ {fs : List T}, x ∈ insK e fs ↔ x = e ∨ x ∈ fs
  | [] => by simp [insK]
  | f :: fs => by
    unfold insK
    split
    · simp
    · simp only [List.mem_cons, mem_insK (fs := fs)]
      constructor
      · rintro (h | h | h)
        · exact .inr (.inl h)
        · exact .inl h
        · exact .inr (.inr h)
      · rintro (h | h | h)
        · exact .inr (.inl h)
        · exact .inl h
        · exact .inr (.inr h)

theorem mem_foldl_insK {x : T} : ∀ {L acc : List T},
    x ∈ L.foldl (fun acc e => insK e acc) acc ↔ x ∈ acc ∨ x ∈ L
  | [], acc => by simp
  | e :: L, acc => by
    simp only [List.foldl_cons, mem_foldl_insK (L := L), mem_insK, List.mem_cons]
    constructor
    · rintro ((h | h) | h)
      · exact .inr (.inl h)
      · exact .inl h
      · exact .inr (.inr h)
    · rintro (h | h | h)
      · exact .inl (.inr h)
      · exact .inl (.inl h)
      · exact .inr h

/-- `sortK` keeps every element and adds none. -/
theorem mem_sortK {x : T} {L : List T} : x ∈ sortK L ↔ x ∈ L := by
  unfold sortK; simp [mem_foldl_insK]

/-! ## Values whose literals `kore.k` has, and terms without `bot` -/

mutual
/-- Every literal inside the value has a `kore.k` form (`encLit`): the value-level `litsIn`. -/
def litsV : GroundTerm → Bool
  | .ctor _ vs => litsVL vs
  | .inj _ _ t => litsV t
  | .dv s l => (encLit s l).isSome
  | .map _ es => litsVE es
  | .set _ es => litsVL es
  | .list _ es => litsVL es
  termination_by structural v => v
def litsVL : List GroundTerm → Bool
  | [] => true
  | v :: vs => litsV v && litsVL vs
  termination_by structural vs => vs
def litsVE : List (GroundTerm × GroundTerm) → Bool
  | [] => true
  | e :: es => litsVP e && litsVE es
  termination_by structural es => es
def litsVP : GroundTerm × GroundTerm → Bool
  | (k, v) => litsV k && litsV v
  termination_by structural e => e
end

theorem litsVL_iff : ∀ {vs : List GroundTerm}, litsVL vs = true ↔ ∀ v ∈ vs, litsV v = true
  | [] => by simp [litsVL]
  | v :: vs => by simp [litsVL, litsVL_iff (vs := vs)]

theorem litsVE_iff : ∀ {es : List (GroundTerm × GroundTerm)},
    litsVE es = true ↔ ∀ e ∈ es, litsV e.1 = true ∧ litsV e.2 = true
  | [] => by simp [litsVE]
  | (k, v) :: es => by
    rw [litsVE, litsVP, Bool.and_eq_true, Bool.and_eq_true, litsVE_iff, List.forall_mem_cons]

mutual
/-- `bot` nowhere inside the term. -/
def NoBot : T → Prop
  | .bot => False
  | .ap _ as => NoBotL as
  | .hk _ as => NoBotL as
  | .cb _ _ ps => NoBotL ps
  | .co _ _ es => NoBotL es
  | .ij _ _ t => NoBot t
  | .as t _ => NoBot t
  | .el t => NoBot t
  | .kv a v => NoBot a ∧ NoBot v
  | .en t e => NoBot t ∧ NoBot e
  | .iv _ | .bv _ | .tk _ _ | .vr _ => True
  termination_by structural t => t
def NoBotL : List T → Prop
  | [] => True
  | t :: ts => NoBot t ∧ NoBotL ts
  termination_by structural ts => ts
end

theorem noBotL_iff : ∀ {ts : List T}, NoBotL ts ↔ ∀ t ∈ ts, NoBot t
  | [] => by simp [NoBotL]
  | t :: ts => by simp [NoBotL, noBotL_iff (ts := ts)]

/-- The literals `kore.k` has: an Int at `Int`, a Bool at `Bool`, a token at its sort. -/
theorem encLit_some {s : Srt} {l : Lit} {t : T} (h : encLit s l = some t) :
    (∃ i, l = .int i ∧ s = Srt.int ∧ t = .iv i) ∨ (∃ b, l = .bool b ∧ s = Srt.bool ∧ t = .bv b) ∨
      (∃ x, l = .tok x ∧ t = .tk s x) := by
  unfold encLit encLitWith at h
  split at h
  · cases h; exact .inl ⟨_, rfl, rfl, rfl⟩
  · cases h; exact .inr (.inl ⟨_, rfl, rfl, rfl⟩)
  · cases h; exact .inr (.inr ⟨_, rfl, rfl⟩)
  · cases h

theorem enc_dv_of_encLit {s : Srt} {l : Lit} {t : T} (h : encLit s l = some t) : enc (.dv s l) = t := by
  rcases encLit_some h with ⟨i, rfl, rfl, rfl⟩ | ⟨b, rfl, rfl, rfl⟩ | ⟨x, rfl, rfl⟩
  · rfl
  · rfl
  · simp only [enc]

/-- `enc` writes `bot` at a literal `kore.k` has no form for, and nowhere else. -/
theorem enc_ne_bot {v : GroundTerm} (h : litsV v = true) : NoBot (enc v) := by
  induction v using gtInd_kel with
  | hctor f vs ih =>
    simp only [litsV, litsVL_iff] at h
    simp only [enc, NoBot, noBotL_iff, encTs_eq_map, List.mem_map]
    rintro _ ⟨v, hv, rfl⟩; exact ih v hv (h v hv)
  | hinj a b t ih => simp only [litsV] at h; simp only [enc, NoBot]; exact ih h
  | hdv s l =>
    simp only [litsV, Option.isSome_iff_exists] at h
    obtain ⟨t, ht⟩ := h
    rw [enc_dv_of_encLit ht]
    rcases encLit_some ht with ⟨_, -, -, rfl⟩ | ⟨_, -, -, rfl⟩ | ⟨_, -, rfl⟩ <;> simp [NoBot]
  | hmap s es ih =>
    simp only [litsV, litsVE_iff] at h
    simp only [enc, NoBot, noBotL_iff, mem_sortK, encKvs_eq_map, List.mem_map]
    rintro _ ⟨e, he, rfl⟩; exact ⟨(ih e he).1 (h e he).1, (ih e he).2 (h e he).2⟩
  | hset s es ih =>
    simp only [litsV, litsVL_iff] at h
    simp only [enc, NoBot, noBotL_iff, mem_sortK, encEls_eq_map, List.mem_map]
    rintro _ ⟨v, hv, rfl⟩; exact ih v hv (h v hv)
  | hlist s es ih =>
    simp only [litsV, litsVL_iff] at h
    simp only [enc, NoBot, noBotL_iff, encEls_eq_map, List.mem_map]
    rintro _ ⟨v, hv, rfl⟩; exact ih v hv (h v hv)


/-! ## The sorts of a value's parts -/

theorem sortsOf_mem_kel {c : Semantics} : ∀ {vs : List GroundTerm} {ss : List Srt},
    c.sortsOf vs = some ss → ∀ v ∈ vs, ∃ s ∈ ss, c.sortOf v = some s
  | [], _, _, v, hv => nomatch hv
  | u :: vs, ss, h, v, hv => by
    simp only [Semantics.sortsOf] at h
    split at h
    · rename_i s ss' hu hvs
      cases h
      rcases List.mem_cons.mp hv with rfl | hv
      · exact ⟨s, List.mem_cons_self .., hu⟩
      · obtain ⟨s', hs', h'⟩ := sortsOf_mem_kel hvs v hv
        exact ⟨s', List.mem_cons_of_mem _ hs', h'⟩
    · cases h

theorem entriesOK_mem_kel {c : Semantics} {ks vs : Srt} : ∀ {es : List (GroundTerm × GroundTerm)},
    c.entriesOK ks vs es = true → ∀ e ∈ es, c.sortOf e.1 = some ks ∧ c.sortOf e.2 = some vs
  | [], _, e, he => nomatch he
  | (k, v) :: es, h, e, he => by
    simp only [Semantics.entriesOK, Semantics.entryOK, Bool.and_eq_true, beq_iff_eq] at h
    rcases List.mem_cons.mp he with rfl | he
    · exact h.1
    · exact entriesOK_mem_kel h.2 e he

/-- The three readings of a constructor term's sort, without overloads. -/
theorem sortOf_ctor_kel {c : Semantics} (ho : c.ovls = []) {f : Sym} {vs : List GroundTerm} {s : Srt}
    (h : c.sortOf (.ctor f vs) = some s) :
    (∃ k ∈ c.ctorSigs, c.sortsOf vs = some k.args) ∨ (∃ k ∈ c.params, c.sortsOf vs = some k.sig.args) := by
  have hov : c.lookupOvl f = none := by simp [Semantics.lookupOvl, ho]
  rcases c.sortOf_ctor_iff.mp h with ⟨k, hk, hs, -⟩ | ⟨-, o, ho', -⟩ | ⟨-, -, k, hk, hs, -, -⟩
  · rw [lookupSig_eq] at hk; exact .inl ⟨k, List.mem_of_find?_eq_some hk, hs⟩
  · rw [hov] at ho'; cases ho'
  · exact .inr ⟨k, (c.lookupOpen_spec hk).1, hs⟩

theorem sortOf_inj_kel {c : Semantics} {a b : Srt} {t : GroundTerm} {s : Srt}
    (h : c.sortOf (.inj a b t) = some s) :
    (a, b) ∈ c.subsorts ∧ t.isInj = false ∧ c.sortOf t = some a ∧ s = b := by
  simp only [Semantics.sortOf] at h
  split at h
  · rename_i hc
    simp only [Bool.and_eq_true, List.contains_iff_mem, Bool.not_eq_true', beq_iff_eq] at hc
    cases h; exact ⟨hc.1.1, hc.1.2, hc.2, rfl⟩
  · cases h

theorem sortOf_dv_kel {c : Semantics} {s' : Srt} {l : Lit} {s : Srt} (h : c.sortOf (.dv s' l) = some s) :
    dvOK c.lib s' l = true ∧ s = s' := by
  simp only [Semantics.sortOf] at h
  split at h
  · rename_i hc; cases h; exact ⟨hc, rfl⟩
  · cases h

/-- A map value's collection, keys strictly increasing (a range map's maximal intervals are too),
and its entries' sorts. -/
theorem sortOf_map_kel {c : Semantics} {s' : Srt} {es : List (GroundTerm × GroundTerm)} {s : Srt}
    (h : c.sortOf (.map s' es) = some s) :
    ∃ k vs, k ∈ c.allColls ∧ k.val = some vs ∧ keysSorted es = true ∧ c.entriesOK k.key vs es = true := by
  obtain ⟨k, vs, hk, hv, hks, he, -⟩ := c.sortOf_map_inv h
  refine ⟨k, vs, List.mem_of_find?_eq_some hk, hv, ?_, he⟩
  revert hks; cases k.kind
  · exact id
  · intro h; cases h
  · intro h; cases h
  · exact keysSorted_of_rangesOK

theorem sortOf_set_kel {c : Semantics} {s' : Srt} {es : List GroundTerm} {s : Srt}
    (h : c.sortOf (.set s' es) = some s) :
    ∃ k ss, k ∈ c.allColls ∧ elemsSorted es = true ∧ c.sortsOf es = some ss ∧ ∀ x ∈ ss, x = k.key := by
  simp only [Semantics.sortOf] at h
  split at h
  · rename_i k ss hk hss
    split at h
    · rename_i hc
      simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at hc
      exact ⟨k, ss, List.mem_of_find?_eq_some hk, hc.1.2, hss, hc.2⟩
    · cases h
  · cases h

theorem sortOf_list_kel {c : Semantics} {s' : Srt} {es : List GroundTerm} {s : Srt}
    (h : c.sortOf (.list s' es) = some s) :
    ∃ k ss, k ∈ c.allColls ∧ c.sortsOf es = some ss ∧ ∀ x ∈ ss, x = k.key := by
  simp only [Semantics.sortOf] at h
  split at h
  · rename_i k ss hk hss
    split at h
    · rename_i hc
      simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at hc
      exact ⟨k, ss, List.mem_of_find?_eq_some hk, hss, hc.2⟩
    · cases h
  · cases h

/-! ## Under `encodable`, every value at a sort other than `Float` is `litsV` -/

theorem encodable_facts {c : Semantics} (h : encodable c = true) :
    c.ovls = [] ∧ c.lib.carriers = [] ∧ Srt.float ∉ sigSorts c := by
  simp only [encodable, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, -⟩, -⟩, -⟩, h5⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := h
  simp only [ovlsOK, List.isEmpty_iff] at h1
  simp only [litsOK, Bool.and_eq_true, List.isEmpty_iff, Bool.not_eq_true'] at h5
  refine ⟨h1, h5.1.2, fun hm => ?_⟩
  have := h5.2
  rw [List.contains_eq_any_beq, List.any_eq_false] at this
  exact this _ hm (beq_self_eq_true _)

theorem sigSorts_ctor_kel {c : Semantics} {k : CtorSig} (hk : k ∈ c.ctorSigs) {s : Srt} (hs : s ∈ k.args) :
    s ∈ sigSorts c := by
  simp only [sigSorts, List.mem_append, List.mem_flatMap, List.mem_cons]
  exact .inl (.inl (.inl (.inl ⟨k, hk, .inr hs⟩)))

theorem sigSorts_param_kel {c : Semantics} {k : ParamSig} (hk : k ∈ c.params) {s : Srt}
    (hs : s ∈ k.sig.args) : s ∈ sigSorts c := by
  simp only [sigSorts, List.mem_append, List.mem_flatMap, List.mem_cons]
  exact .inl (.inl (.inr ⟨k, hk, .inr hs⟩))

theorem sigSorts_key_kel {c : Semantics} {k : CollSig} (hk : k ∈ c.allColls) : k.key ∈ sigSorts c := by
  simp only [sigSorts, List.mem_append, List.mem_flatMap, List.mem_cons]
  exact .inl (.inr ⟨k, hk, .inr (.inl rfl)⟩)

theorem sigSorts_val_kel {c : Semantics} {k : CollSig} (hk : k ∈ c.allColls) {v : Srt}
    (hv : k.val = some v) : v ∈ sigSorts c := by
  simp only [sigSorts, List.mem_append, List.mem_flatMap, List.mem_cons]
  exact .inl (.inr ⟨k, hk, .inr (.inr (by simp [hv]))⟩)

theorem sigSorts_sub_kel {c : Semantics} {a b : Srt} (h : (a, b) ∈ c.subsorts) : a ∈ sigSorts c := by
  simp only [sigSorts, List.mem_append, List.mem_flatMap]
  exact .inr ⟨(a, b), h, by simp⟩

/-- Under `encodable c`, a value of `c` at a sort other than `Float` has only literals `kore.k`
has: without carriers a `Float` literal is a value of `Float` only, and every part of a value
(a constructor's or an open generator's argument, an injection's source, a collection's key or
value) has a sort that `sigSorts c` names, which `Float` is not. -/
theorem litsV_of_sorted {c : Semantics} (hc : encodable c = true) {v : GroundTerm} {s : Srt}
    (hv : c.sortOf v = some s) (hs : s ≠ Srt.float) : litsV v = true := by
  obtain ⟨ho, hcar, hf⟩ := encodable_facts hc
  have hne : ∀ {x}, x ∈ sigSorts c → x ≠ Srt.float := fun hx he => hf (he ▸ hx)
  have hL : ∀ {vs : List GroundTerm} {ss : List Srt}, (∀ v ∈ vs, ∀ s, c.sortOf v = some s → s ≠ Srt.float →
      litsV v = true) → c.sortsOf vs = some ss → (∀ x ∈ ss, x ∈ sigSorts c) → litsVL vs = true := by
    intro vs ss ih h hss
    rw [litsVL_iff]; intro v hv
    obtain ⟨s', hs', h'⟩ := sortsOf_mem_kel h v hv
    exact ih v hv s' h' (hne (hss s' hs'))
  induction v using gtInd_kel generalizing s with
  | hctor f vs ih =>
    simp only [litsV]
    rcases sortOf_ctor_kel ho hv with ⟨k, hk, h⟩ | ⟨k, hk, h⟩
    · exact hL ih h fun x hx => sigSorts_ctor_kel hk hx
    · exact hL ih h fun x hx => sigSorts_param_kel hk hx
  | hinj a b t ih =>
    obtain ⟨hab, -, ht, -⟩ := sortOf_inj_kel hv
    exact ih ht (hne (sigSorts_sub_kel hab))
  | hdv s' l =>
    obtain ⟨hd, rfl⟩ := sortOf_dv_kel hv
    rw [dvOK_nil hcar] at hd
    simp only [litsV]
    cases l with
    | int i => simp only [beq_iff_eq] at hd; subst hd; rfl
    | bool b => simp only [beq_iff_eq] at hd; subst hd; rfl
    | tok x => simp [encLit, encLitWith]
    | float p e b => simp only [Bool.and_eq_true, beq_iff_eq] at hd; exact absurd hd.1 hs
  | hmap s' es ih =>
    obtain ⟨k, vs, hk, hvs, -, he⟩ := sortOf_map_kel hv
    simp only [litsV, litsVE_iff]
    intro e hm
    have := entriesOK_mem_kel he e hm
    exact ⟨(ih e hm).1 this.1 (hne (sigSorts_key_kel hk)), (ih e hm).2 this.2 (hne (sigSorts_val_kel hk hvs))⟩
  | hset s' es ih =>
    obtain ⟨k, ss, hk, -, h, hss⟩ := sortOf_set_kel hv
    exact hL ih h fun x hx => hss x hx ▸ sigSorts_key_kel hk
  | hlist s' es ih =>
    obtain ⟨k, ss, hk, h, hss⟩ := sortOf_list_kel hv
    exact hL ih h fun x hx => hss x hx ▸ sigSorts_key_kel hk

/-! ## `enc` is injective on sorted values whose literals `kore.k` has -/

/-- Two lists strictly increasing in an asymmetric relation, with the same members, are equal. -/
theorem eq_of_pairwise_mem_kel {α : Type} {R : α → α → Prop} (hasym : ∀ a b, R a b → ¬ R b a) :
    ∀ {l l' : List α}, l.Pairwise R → l'.Pairwise R → (∀ x, x ∈ l ↔ x ∈ l') → l = l'
  | [], [], _, _, _ => rfl
  | [], b :: _, _, _, h => absurd ((h b).2 (List.mem_cons_self ..)) (by simp)
  | a :: _, [], _, _, h => absurd ((h a).1 (List.mem_cons_self ..)) (by simp)
  | a :: as, b :: bs, hl, hl', h => by
    rw [List.pairwise_cons] at hl hl'
    have hirr : ∀ x, ¬ R x x := fun x r => hasym x x r r
    have hab : a = b := by
      refine Classical.byContradiction fun hne => ?_
      have ha : a ∈ bs := by
        rcases List.mem_cons.mp ((h a).1 (List.mem_cons_self ..)) with h1 | h1
        · exact absurd h1 hne
        · exact h1
      have hb : b ∈ as := by
        rcases List.mem_cons.mp ((h b).2 (List.mem_cons_self ..)) with h1 | h1
        · exact absurd h1.symm hne
        · exact h1
      exact hasym a b (hl.1 b hb) (hl'.1 a ha)
    subst hab
    rw [eq_of_pairwise_mem_kel hasym hl.2 hl'.2 fun x => ⟨fun hx => ?_, fun hx => ?_⟩]
    · rcases List.mem_cons.mp ((h x).1 (List.mem_cons_of_mem _ hx)) with rfl | h'
      · exact absurd (hl.1 _ hx) (hirr _)
      · exact h'
    · rcases List.mem_cons.mp ((h x).2 (List.mem_cons_of_mem _ hx)) with rfl | h'
      · exact absurd (hl'.1 _ hx) (hirr _)
      · exact h'

theorem keysSorted_pairwise_kel : ∀ {es : Entries}, keysSorted es = true →
    es.Pairwise fun a b => GroundTerm.cmp a.1 b.1 = .lt
  | [], _ => .nil
  | (_, _) :: _, h => .cons (keysSorted_lt_all h) (keysSorted_pairwise_kel (keysSorted_cons.mp h).1)

theorem cmp_asymm_kel (a b : GroundTerm) (h : GroundTerm.cmp a b = .lt) : ¬ GroundTerm.cmp b a = .lt := by
  rw [GroundTerm.cmp_swap, h]; decide

/-- The member of an element. -/
def unEl_kel : T → T
  | .el x => x
  | t => t

/-- Lists of values that `enc` maps to one list, where `enc` is injective at each member of the
first. -/
theorem map_enc_inj_kel : ∀ {vs ws : List GroundTerm},
    (∀ v ∈ vs, ∀ w ∈ ws, enc v = enc w → v = w) → vs.map enc = ws.map enc → vs = ws
  | [], [], _, _ => rfl
  | [], _ :: _, _, h => nomatch h
  | _ :: _, [], _, h => nomatch h
  | v :: vs, w :: ws, ih, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    rw [ih v (List.mem_cons_self ..) w (List.mem_cons_self ..) h.1,
      map_enc_inj_kel (fun v hv w hw => ih v (List.mem_cons_of_mem _ hv) w (List.mem_cons_of_mem _ hw)) h.2]

/-- `enc` is injective on the values sorted in one semantics whose literals `kore.k` has. Sorts
are read only for a collection's canonical form (a map's keys and a set's elements strictly
increasing; a range map's keys too), so no condition of `encDef` is needed. -/
theorem enc_inj {c : Semantics} {v w : GroundTerm} {s s' : Srt} (hv : c.sortOf v = some s)
    (hw : c.sortOf w = some s') (lv : litsV v = true) (lw : litsV w = true) (h : enc v = enc w) :
    v = w := by
  -- the members of a list of values sorted in `c` are sorted in `c`
  have hmem : ∀ {vs : List GroundTerm} {ss : List Srt}, c.sortsOf vs = some ss →
      ∀ v ∈ vs, ∃ s, c.sortOf v = some s := fun h v hv =>
    let ⟨s, _, h'⟩ := sortsOf_mem_kel h v hv; ⟨s, h'⟩
  have hctorS : ∀ {f : Sym} {vs : List GroundTerm} {s : Srt}, c.sortOf (.ctor f vs) = some s →
      ∀ v ∈ vs, ∃ s, c.sortOf v = some s := by
    intro f vs s h
    obtain ⟨ss, hss⟩ := c.sortsOf_of_sortOf_ctor h
    exact hmem hss
  have hlistS : ∀ {vs ws : List GroundTerm},
      (∀ v ∈ vs, ∀ {w : GroundTerm} {s s' : Srt}, c.sortOf v = some s → c.sortOf w = some s' →
        litsV v = true → litsV w = true → enc v = enc w → v = w) →
      (∀ v ∈ vs, ∃ s, c.sortOf v = some s) → (∀ w ∈ ws, ∃ s, c.sortOf w = some s) →
      litsVL vs = true → litsVL ws = true → vs.map enc = ws.map enc → vs = ws := by
    intro vs ws ih hvs hws lv lw h
    rw [litsVL_iff] at lv lw
    refine map_enc_inj_kel (fun v hv w hw he => ?_) h
    obtain ⟨s, hs⟩ := hvs v hv
    obtain ⟨s', hs'⟩ := hws w hw
    exact ih v hv hs hs' (lv v hv) (lw w hw) he
  induction v using gtInd_kel generalizing s w s' with
  | hctor f vs ih =>
    cases w with
    | ctor g ws =>
      simp only [enc, T.ap.injEq, encTs_eq_map] at h
      rw [Int.ofNat_inj.mp h.1, hlistS ih (hctorS hv) (hctorS hw) lv lw h.2]
    | dv s'' l =>
      simp only [litsV, Option.isSome_iff_exists] at lw
      obtain ⟨t, ht⟩ := lw
      rw [enc_dv_of_encLit ht] at h
      rcases encLit_some ht with ⟨_, -, -, rfl⟩ | ⟨_, -, -, rfl⟩ | ⟨_, -, rfl⟩ <;> simp [enc] at h
    | _ => simp [enc] at h
  | hinj a b t ih =>
    cases w with
    | inj a' b' t' =>
      simp only [enc, T.ij.injEq] at h
      obtain ⟨-, -, ht, -⟩ := sortOf_inj_kel hv
      obtain ⟨-, -, ht', -⟩ := sortOf_inj_kel hw
      obtain ⟨h1, h2, h3⟩ := h
      rw [Int.ofNat_inj] at h1 h2
      rw [h1, h2, ih ht ht' lv lw h3]
    | dv s'' l =>
      simp only [litsV, Option.isSome_iff_exists] at lw
      obtain ⟨t, ht⟩ := lw
      rw [enc_dv_of_encLit ht] at h
      rcases encLit_some ht with ⟨_, -, -, rfl⟩ | ⟨_, -, -, rfl⟩ | ⟨_, -, rfl⟩ <;> simp [enc] at h
    | _ => simp [enc] at h
  | hdv s₀ l =>
    simp only [litsV, Option.isSome_iff_exists] at lv
    obtain ⟨t, ht⟩ := lv
    rw [enc_dv_of_encLit ht] at h
    cases w with
    | dv s₁ l' =>
      simp only [litsV, Option.isSome_iff_exists] at lw
      obtain ⟨t', ht'⟩ := lw
      rw [enc_dv_of_encLit ht'] at h
      rcases encLit_some ht with ⟨i, rfl, rfl, rfl⟩ | ⟨b, rfl, rfl, rfl⟩ | ⟨x, rfl, rfl⟩ <;>
        rcases encLit_some ht' with ⟨i', rfl, rfl, h'⟩ | ⟨b', rfl, rfl, h'⟩ | ⟨x', rfl, h'⟩ <;>
        (rw [h'] at h; cases h; try rfl)
    | _ => rcases encLit_some ht with ⟨_, -, -, rfl⟩ | ⟨_, -, -, rfl⟩ | ⟨_, -, rfl⟩ <;> simp [enc] at h
  | hmap s₀ es ih =>
    cases w with
    | map s₁ es' =>
      simp only [enc, T.co.injEq, encKvs_eq_map, true_and] at h
      obtain ⟨h1, h2⟩ := h
      rw [Int.ofNat_inj] at h1
      subst h1
      obtain ⟨k, vs, -, -, hks, he⟩ := sortOf_map_kel hv
      obtain ⟨k', vs', -, -, hks', he'⟩ := sortOf_map_kel hw
      rw [litsV, litsVE_iff] at lv lw
      -- an entry of `es` and an entry of `es'` with one encoding are one entry
      have hone : ∀ e ∈ es, ∀ e' ∈ es', enc e.1 = enc e'.1 → enc e.2 = enc e'.2 → e = e' := by
        intro e he₀ e' he₀' h1 h2
        have hs := entriesOK_mem_kel he e he₀
        have hs' := entriesOK_mem_kel he' e' he₀'
        exact Prod.ext ((ih e he₀).1 hs.1 hs'.1 (lv e he₀).1 (lw e' he₀').1 h1)
          ((ih e he₀).2 hs.2 hs'.2 (lv e he₀).2 (lw e' he₀').2 h2)
      have hm : ∀ x, x ∈ es ↔ x ∈ es' := by
        intro x
        constructor
        · intro hx
          have : T.kv (enc x.1) (enc x.2) ∈ sortK (es'.map fun e => .kv (enc e.1) (enc e.2)) := by
            rw [← h2, mem_sortK]; exact List.mem_map.mpr ⟨x, hx, rfl⟩
          rw [mem_sortK, List.mem_map] at this
          obtain ⟨x', hx', hxe⟩ := this
          simp only [T.kv.injEq] at hxe
          rw [hone x hx x' hx' hxe.1.symm hxe.2.symm]; exact hx'
        · intro hx
          have : T.kv (enc x.1) (enc x.2) ∈ sortK (es.map fun e => .kv (enc e.1) (enc e.2)) := by
            rw [h2, mem_sortK]; exact List.mem_map.mpr ⟨x, hx, rfl⟩
          rw [mem_sortK, List.mem_map] at this
          obtain ⟨x', hx', hxe⟩ := this
          simp only [T.kv.injEq] at hxe
          rw [← hone x' hx' x hx hxe.1 hxe.2]; exact hx'
      rw [eq_of_pairwise_mem_kel (fun a b => cmp_asymm_kel a.1 b.1) (keysSorted_pairwise_kel hks)
        (keysSorted_pairwise_kel hks') hm]
    | dv s'' l =>
      simp only [litsV, Option.isSome_iff_exists] at lw
      obtain ⟨t, ht⟩ := lw
      rw [enc_dv_of_encLit ht] at h
      rcases encLit_some ht with ⟨_, -, -, rfl⟩ | ⟨_, -, -, rfl⟩ | ⟨_, -, rfl⟩ <;> simp [enc] at h
    | _ => simp [enc] at h
  | hset s₀ es ih =>
    cases w with
    | set s₁ es' =>
      simp only [enc, T.co.injEq, encEls_eq_map, true_and] at h
      obtain ⟨h1, h2⟩ := h
      rw [Int.ofNat_inj] at h1
      subst h1
      obtain ⟨k, ss, -, hks, hss, -⟩ := sortOf_set_kel hv
      obtain ⟨k', ss', -, hks', hss', -⟩ := sortOf_set_kel hw
      rw [litsV, litsVL_iff] at lv lw
      have hone : ∀ e ∈ es, ∀ e' ∈ es', enc e = enc e' → e = e' := by
        intro e he₀ e' he₀' h1
        obtain ⟨s, -, hs⟩ := sortsOf_mem_kel hss e he₀
        obtain ⟨s', -, hs'⟩ := sortsOf_mem_kel hss' e' he₀'
        exact ih e he₀ hs hs' (lv e he₀) (lw e' he₀') h1
      have hm : ∀ x, x ∈ es ↔ x ∈ es' := by
        intro x
        constructor
        · intro hx
          have : T.el (enc x) ∈ sortK (es'.map fun e => .el (enc e)) := by
            rw [← h2, mem_sortK]; exact List.mem_map.mpr ⟨x, hx, rfl⟩
          rw [mem_sortK, List.mem_map] at this
          obtain ⟨x', hx', hxe⟩ := this
          simp only [T.el.injEq] at hxe
          rw [hone x hx x' hx' hxe.symm]; exact hx'
        · intro hx
          have : T.el (enc x) ∈ sortK (es.map fun e => .el (enc e)) := by
            rw [h2, mem_sortK]; exact List.mem_map.mpr ⟨x, hx, rfl⟩
          rw [mem_sortK, List.mem_map] at this
          obtain ⟨x', hx', hxe⟩ := this
          simp only [T.el.injEq] at hxe
          rw [← hone x' hx' x hx hxe]; exact hx'
      rw [eq_of_pairwise_mem_kel cmp_asymm_kel (elemsSorted_iff.mp hks) (elemsSorted_iff.mp hks') hm]
    | dv s'' l =>
      simp only [litsV, Option.isSome_iff_exists] at lw
      obtain ⟨t, ht⟩ := lw
      rw [enc_dv_of_encLit ht] at h
      rcases encLit_some ht with ⟨_, -, -, rfl⟩ | ⟨_, -, -, rfl⟩ | ⟨_, -, rfl⟩ <;> simp [enc] at h
    | _ => simp [enc] at h
  | hlist s₀ es ih =>
    cases w with
    | list s₁ es' =>
      simp only [enc, T.co.injEq, encEls_eq_map, true_and] at h
      obtain ⟨h1, h2⟩ := h
      rw [Int.ofNat_inj] at h1
      subst h1
      obtain ⟨k, ss, -, hss, -⟩ := sortOf_list_kel hv
      obtain ⟨k', ss', -, hss', -⟩ := sortOf_list_kel hw
      have h3 : es.map enc = es'.map enc := by
        have := congrArg (List.map unEl_kel) h2
        simpa only [List.map_map, Function.comp_def, unEl_kel] using this
      rw [hlistS ih (hmem hss) (hmem hss') lv lw h3]
    | dv s'' l =>
      simp only [litsV, Option.isSome_iff_exists] at lw
      obtain ⟨t, ht⟩ := lw
      rw [enc_dv_of_encLit ht] at h
      rcases encLit_some ht with ⟨_, -, -, rfl⟩ | ⟨_, -, -, rfl⟩ | ⟨_, -, rfl⟩ <;> simp [enc] at h
    | _ => simp [enc] at h

/-- The pinned form: under `encDef d = some E`, two configurations of `d₀ d` with one encoding
are one configuration. -/
theorem enc_injective {d : Semantics} {E : D} (hE : encDef d = some E) {x y : Config (d₀ d)}
    (h : enc x.val = enc y.val) : x = y := by
  have hc : encodable (d₀ d) = true := by
    rw [← encDef_isSome, encDef_withHooks, hE]; rfl
  have htop : topCellSort ≠ Srt.float := by decide
  exact Subtype.ext (enc_inj x.property y.property (litsV_of_sorted hc x.property htop)
    (litsV_of_sorted hc y.property htop) h)

/-! ## Under `encodable`, every term of the definition has a `kore.k` form

`encTermWith`'s result is `some` or `none` by the term's applications alone, except at a literal,
where it reads `lit`: so a term that has a form with every literal accepted (C3) and whose literals
`kore.k` has (C5) has a form. -/

/-- Induction over terms, a list's members given at once. -/
theorem termInd_kel (P : Term → Prop) (hvar : ∀ i, P (.var i))
    (happ : ∀ f ts, (∀ t ∈ ts, P t) → P (.app f ts)) (hinj : ∀ a b t, P t → P (.inj a b t))
    (has : ∀ t i, P t → P (.as t i)) (hdv : ∀ s l, P (.dv s l)) (t : Term) : P t :=
  Term.rec (motive_1 := P) (motive_2 := fun ts => ∀ t ∈ ts, P t) hvar happ hinj has hdv
    (fun _ h => nomatch h)
    (fun _ _ hx hxs y hy => match List.mem_cons.mp hy with
      | .inl h => h ▸ hx
      | .inr h => hxs y h) t

theorem litsInL_iff : ∀ {ts : List Term}, litsIn.litsInL ts = true ↔ ∀ t ∈ ts, litsIn t = true
  | [] => by simp [litsIn.litsInL]
  | t :: ts => by
    rw [litsIn.litsInL, Bool.and_eq_true, litsInL_iff, List.forall_mem_cons]

/-- `derivedHook` is `some` at `=/=Bool` whatever the arguments. -/
theorem derivedHook_isSome_kel (f : Sym) (as as' : List T) :
    (derivedHook f as).isSome = (derivedHook f as').isSome := by
  unfold derivedHook; split <;> rfl

/-- `readApp` is `some` by whether the arguments' forms and the parts are, not by which they are. -/
theorem readApp_isSome_kel {d : Semantics} {f : Sym} {a a' p p' : Option (List T)}
    (h : (readApp d f a p).isSome = true) (ha : a.isSome = true → a'.isSome = true)
    (hp : p.isSome = true → p'.isSome = true) : (readApp d f a' p').isSome = true := by
  unfold readApp at h ⊢
  by_cases hc : d.isCtor f = true
  · rw [ite_eq_left hc, Option.isSome_map] at h ⊢; exact ha h
  rw [ite_eq_right hc] at h ⊢
  cases hcs : collSymOf d f with
  | some x =>
    obtain ⟨k, s, r⟩ := x
    rw [hcs] at h
    simp only [Option.isSome_map] at h ⊢
    exact hp h
  | none =>
    rw [hcs] at h
    simp only at h ⊢
    by_cases hk : isHook f = true
    · rw [ite_eq_left hk] at h ⊢
      cases ho : opOf f with
      | some o => rw [ho] at h; simp only [Option.isSome_map] at h ⊢; exact ha h
      | none =>
        rw [ho] at h
        simp only at h ⊢
        cases a with
        | none => cases h
        | some x =>
          obtain ⟨y, rfl⟩ := Option.isSome_iff_exists.mp (ha rfl)
          simp only [Option.bind_some] at h ⊢
          rw [derivedHook_isSome_kel f y x]; exact h
    · rw [ite_eq_right hk] at h ⊢
      by_cases hpm : d.isParam f = true
      · rw [ite_eq_left hpm] at h; cases h
      · rw [ite_eq_right hpm] at h ⊢
        by_cases hl : (d.lookupFn f).isSome = true
        · rw [ite_eq_left hl, Option.isSome_map] at h ⊢; exact ha h
        · rw [ite_eq_right hl] at h; cases h

theorem bind_isSome_kel {α β : Type} {o : Option α} {g g' : α → Option β}
    (h : (o.bind g).isSome = true) (hg : ∀ x, (g x).isSome = true → (g' x).isSome = true) :
    (o.bind g').isSome = true := by
  cases o with
  | none => cases h
  | some x => exact hg x h

section
variable {d : Semantics} {L : Srt → Lit → Option T}

theorem encTermsWith_isSome_iff : ∀ {ts : List Term},
    (encTermsWith d L ts).isSome = true ↔ ∀ t ∈ ts, (encTermWith d L t).isSome = true
  | [] => by simp [encTermsWith]
  | t :: ts => by
    rw [List.forall_mem_cons, ← encTermsWith_isSome_iff (ts := ts)]
    simp only [encTermsWith]
    cases encTermWith d L t <;> cases encTermsWith d L ts <;> simp

/-- What the induction gives of a term: its form, and its form as a concatenation's argument. -/
def TermOK_kel (d : Semantics) (L : Srt → Lit → Option T) (t : Term) : Prop :=
  ((encTermWith d L t).isSome = true → litsIn t = true → (encTerm d t).isSome = true) ∧
    ∀ k s, (encPartWith d L k s t).isSome = true → litsIn t = true →
      (encPartWith d encLit k s t).isSome = true

theorem encTermsWith_isSome_kel {ts : List Term} (ih : ∀ t ∈ ts, TermOK_kel d L t)
    (h : (encTermsWith d L ts).isSome = true) (hl : litsIn.litsInL ts = true) :
    (encTermsWith d encLit ts).isSome = true := by
  rw [encTermsWith_isSome_iff] at h ⊢
  rw [litsInL_iff] at hl
  exact fun t ht => (ih t ht).1 (h t ht) (hl t ht)

theorem encCollWith_isSome_kel {ts : List Term} (ih : ∀ t ∈ ts, TermOK_kel d L t)
    (hl : litsIn.litsInL ts = true) (k : Kind) (s : Srt) (r : CRole)
    (h : (encCollWith d L k s r ts).isSome = true) : (encCollWith d encLit k s r ts).isSome = true := by
  rw [litsInL_iff] at hl
  rcases ts with _ | ⟨x, _ | ⟨v, _ | ⟨w, rest⟩⟩⟩
  · simpa only [encCollWith] using h
  · simp only [encCollWith] at h ⊢
    by_cases hc : (r == CRole.elem && k != Kind.map) = true
    · rw [ite_eq_left hc, Option.isSome_map] at h ⊢
      exact (ih x (List.mem_cons_self ..)).1 h (hl x (List.mem_cons_self ..))
    · rw [ite_eq_right hc] at h; cases h
  · have ha := ih x (by simp)
    have hv := ih v (by simp)
    have la := hl x (by simp)
    have lv := hl v (by simp)
    simp only [encCollWith] at h ⊢
    by_cases hc : (r == CRole.elem && k == Kind.map) = true
    · rw [ite_eq_left hc] at h ⊢
      cases hx : encTermWith d L x with
      | none => rw [hx] at h; cases h
      | some p =>
        cases hy : encTermWith d L v with
        | none => rw [hx, hy] at h; cases h
        | some q =>
          obtain ⟨p', hp'⟩ := Option.isSome_iff_exists.mp (ha.1 (by rw [hx]; rfl) la)
          obtain ⟨q', hq'⟩ := Option.isSome_iff_exists.mp (hv.1 (by rw [hy]; rfl) lv)
          unfold encTerm at hp' hq'
          rw [hp', hq']; rfl
    · rw [ite_eq_right hc] at h ⊢
      by_cases hc' : (r == CRole.concat) = true
      · rw [ite_eq_left hc'] at h ⊢
        cases hx : encPartWith d L k s x with
        | none => rw [hx] at h; cases h
        | some p =>
          cases hy : encPartWith d L k s v with
          | none => rw [hx, hy] at h; cases h
          | some q =>
            obtain ⟨p', hp'⟩ := Option.isSome_iff_exists.mp (ha.2 k s (by rw [hx]; rfl) la)
            obtain ⟨q', hq'⟩ := Option.isSome_iff_exists.mp (hv.2 k s (by rw [hy]; rfl) lv)
            rw [hp', hq']; rfl
      · rw [ite_eq_right hc'] at h; cases h
  · simp only [encCollWith] at h; cases h

/-- A term that has a form with the literals read by `L`, and whose literals `kore.k` has, has a
form; so does a concatenation's argument read by `encPartWith`. -/
theorem termOK_kel (t : Term) : TermOK_kel d L t := by
  induction t using termInd_kel with
  | hvar i => exact ⟨fun _ _ => rfl, fun _ _ _ _ => rfl⟩
  | hdv s l =>
    refine ⟨fun _ h => ?_, fun k s' _ h => ?_⟩
    · simp only [litsIn] at h; exact h
    · simp only [litsIn] at h
      simp only [encPartWith, Option.isSome_map]
      exact h
  | hinj a b t ih =>
    refine ⟨fun h hl => ?_, fun k s h hl => ?_⟩
    · simp only [encTerm, encTermWith, litsIn, Option.isSome_map] at h hl ⊢
      exact ih.1 h hl
    · simp only [encPartWith, litsIn, Option.isSome_map] at h hl ⊢
      exact ih.1 h hl
  | has t i ih =>
    refine ⟨fun h hl => ?_, fun k s h hl => ?_⟩
    · simp only [encTerm, encTermWith, litsIn, Option.isSome_map] at h hl ⊢
      exact ih.1 h hl
    · simp only [encPartWith, litsIn, Option.isSome_map] at h hl ⊢
      exact ih.1 h hl
  | happ f ts ih =>
    refine ⟨fun h hl => ?_, fun k s h hl => ?_⟩
    · simp only [litsIn] at hl
      simp only [encTerm, encTermWith] at h ⊢
      exact readApp_isSome_kel h (encTermsWith_isSome_kel ih · hl)
        (fun hp => bind_isSome_kel hp fun ⟨k, s, r⟩ h => encCollWith_isSome_kel ih hl k s r h)
    · simp only [litsIn] at hl
      simp only [encPartWith] at h ⊢
      have hgen : ∀ {o : Option (List T)},
          (o.isSome = true → ((collSymOf d f).bind fun (k', s', r) => encCollWith d encLit k' s' r ts).isSome = true) →
          ((readApp d f (encTermsWith d L ts) o).map ([·])).isSome = true →
          ((readApp d f (encTermsWith d encLit ts)
            ((collSymOf d f).bind fun (k', s', r) => encCollWith d encLit k' s' r ts)).map ([·])).isSome = true := by
        intro o ho h
        rw [Option.isSome_map] at h ⊢
        exact readApp_isSome_kel h (encTermsWith_isSome_kel ih · hl) ho
      have hbind : (((collSymOf d f).bind fun (k', s', r) => encCollWith d L k' s' r ts).isSome = true →
          ((collSymOf d f).bind fun (k', s', r) => encCollWith d encLit k' s' r ts).isSome = true) :=
        fun hp => bind_isSome_kel hp fun ⟨k, s, r⟩ h => encCollWith_isSome_kel ih hl k s r h
      cases hct : d.isCtor f with
      | true => simp only [hct] at h ⊢; exact hgen hbind h
      | false =>
        cases hcs : collSymOf d f with
        | none =>
          have h' := h
          simp only [hct, hcs] at h' ⊢
          rw [← hcs] at h' ⊢
          exact hgen hbind h'
        | some x =>
          obtain ⟨k', s', r⟩ := x
          simp only [hct, hcs] at h ⊢
          by_cases hc : (k' == k && s' == s) = true
          · rw [ite_eq_left hc] at h ⊢; exact encCollWith_isSome_kel ih hl _ _ _ h
          · rw [ite_eq_right hc] at h ⊢
            simp only [Option.isSome_map] at h ⊢
            exact readApp_isSome_kel h (encTermsWith_isSome_kel ih · hl) (encCollWith_isSome_kel ih hl _ _ _)

end

/-- Under `encodable d`, every left side, `requires`, right side and ensures of `d` has a
`kore.k` form, so `encT` writes it and not `bot`. -/
theorem encTerm_of_encodable {d : Semantics} (h : encodable d = true) {t : Term}
    (ht : t ∈ lhsTerms d ++ rhsTerms d ++ ensTerms d) : encTerm d t = some (encT d t) := by
  suffices hs : (encTerm d t).isSome = true by
    unfold encT; obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp hs; rw [hp]; rfl
  simp only [encodable, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, h3⟩, -⟩, h5⟩, -⟩, -⟩, -⟩, h9⟩, -⟩ := h
  rw [List.mem_append] at ht
  rcases ht with ht | ht
  · simp only [appsOK, List.all_eq_true] at h3
    simp only [litsOK, Bool.and_eq_true, List.all_eq_true] at h5
    exact (termOK_kel t).1 (h3 t ht) (h5.1.1 t ht)
  · simp only [ensOK, List.all_eq_true, Bool.and_eq_true] at h9
    exact (h9 t ht).1

end KCore.KK
