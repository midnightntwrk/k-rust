/-
  The case of a collection construction of the induction on an evaluation of kore.k
  (User.SpecTerms' `CbStep_kst`), from `execReady` and `encodable`, so that the step cases at `eval`,
  `evalTs`, `ensure` and `strictHook` hold with no hypothesis (`stepCases_terms_c13`).

  An application of a collection symbol `f` of the collection of kind `k` and sort `s` is written
  `cb(k, s, Ps)`, whose parts `Ps` are those `encCollWith` writes, a `Map`'s and a `Set`'s elements
  first (`orderParts`). Its parts are the arguments' forms read as a tree (`CbPart_c13`): an element
  `el(X)`, an entry `kv(A, V)`, the parts of a nested construction of the same collection, or any
  other argument of the concatenation as one term. `ev-col` evaluates the parts by `evalTs` and
  joins them by `colOf` (`eval_cb_inv_kst`).

  KCore evaluates the application by strictness: each argument's result, then `collVal` of the
  values. Along the tree (`cbPart_eval_c13`): a part `bot` is an argument without a value, and the
  whole has none; otherwise the parts hold the items (`PartsIts_khc`) of the value KCore builds, up
  to order, and where two items' keys meet both sides have none. A term argument of the
  concatenation is a value of the collection's sort, which C13 makes a collection value
  (`coll_shape_c13`); an element's arguments are values of the collection's key and value sorts,
  which C13 makes the symbol's argument sorts (`collSig_rhs_c13`). Then `colOf` on the parts in
  `orderParts`' order is the encoding of KCore's result (`colOfF_coll_khc`, `colOfF_overlap_khc`,
  `colOfF_list_items_khc`).
-/
import User.SpecTerms

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option Elab.async false

namespace KCore.KK

open KCore.CExec (content)
open KCore.Faithful (collsOK collSortsOK collSortOK elemArgs valSort)

/-! ## Lists related element by element -/

section Each
variable {α β : Type} {R : α → β → Prop}

theorem Each₂_ksm.append_c13 : ∀ {xs ys : List α} {zs ws : List β}, Each₂_ksm R xs zs →
    Each₂_ksm R ys ws → Each₂_ksm R (xs ++ ys) (zs ++ ws)
  | [], _, [], _, .nil, h => h
  | _ :: _, _, _ :: _, _, .cons h hs, h' => .cons h (Each₂_ksm.append_c13 hs h')

theorem Each₂_ksm.split_c13 : ∀ {xs ys : List α} {zs : List β}, Each₂_ksm R (xs ++ ys) zs →
    ∃ zs₁ zs₂, zs = zs₁ ++ zs₂ ∧ Each₂_ksm R xs zs₁ ∧ Each₂_ksm R ys zs₂
  | [], _, _, h => ⟨[], _, rfl, .nil, h⟩
  | _ :: _, _, _ :: _, .cons h hs => by
    obtain ⟨z₁, z₂, rfl, h1, h2⟩ := Each₂_ksm.split_c13 hs
    exact ⟨_ :: z₁, z₂, rfl, .cons h h1, h2⟩

theorem Each₂_ksm.filter_c13 {P : α → Bool} {Q : β → Bool} (hPQ : ∀ x y, R x y → P x = Q y) :
    ∀ {xs : List α} {ys : List β}, Each₂_ksm R xs ys → Each₂_ksm R (xs.filter P) (ys.filter Q)
  | [], [], .nil => .nil
  | x :: _, y :: _, .cons h hs => by
    cases hp : P x with
    | true =>
      rw [List.filter_cons_of_pos hp, List.filter_cons_of_pos (hPQ x y h ▸ hp)]
      exact .cons h (Each₂_ksm.filter_c13 hPQ hs)
    | false =>
      rw [List.filter_cons_of_neg (by simp [hp]), List.filter_cons_of_neg (by simp [← hPQ x y h, hp])]
      exact Each₂_ksm.filter_c13 hPQ hs

theorem Each₂_ksm.mono_c13 {S : α → β → Prop} (hRS : ∀ x y, R x y → S x y) :
    ∀ {xs : List α} {ys : List β}, Each₂_ksm R xs ys → Each₂_ksm S xs ys
  | [], [], .nil => .nil
  | _ :: _, _ :: _, .cons h hs => .cons (hRS _ _ h) (Each₂_ksm.mono_c13 hRS hs)

/-- Two relations along the same middle list compose. -/
theorem Each₂_ksm.comp_c13 {γ : Type} {S : β → γ → Prop} {U : α → γ → Prop}
    (h : ∀ x y z, R x y → S y z → U x z) :
    ∀ {xs : List α} {ys : List β} {zs : List γ}, Each₂_ksm R xs ys → Each₂_ksm S ys zs →
      Each₂_ksm U xs zs
  | [], [], [], .nil, .nil => .nil
  | _ :: _, _ :: _, _ :: _, .cons h1 hs1, .cons h2 hs2 => .cons (h _ _ _ h1 h2) (Each₂_ksm.comp_c13 h hs1 hs2)

/-- The elements of `xs` that `P` holds of, then the others, related to `ys` element by element:
`xs` itself is related to a permutation of `ys`. -/
theorem Each₂_ksm.unfilter_c13 (P : α → Bool) : ∀ (xs : List α) {ys₁ ys₂ : List β},
    Each₂_ksm R (xs.filter P) ys₁ → Each₂_ksm R (xs.filter (!P ·)) ys₂ →
    ∃ ys₀, Each₂_ksm R xs ys₀ ∧ (ys₁ ++ ys₂).Perm ys₀
  | [], _, _, h1, h2 => by
    cases h1; cases h2; exact ⟨[], .nil, .refl _⟩
  | x :: xs, ys₁, ys₂, h1, h2 => by
    cases hx : P x with
    | true =>
      rw [List.filter_cons_of_pos hx] at h1
      rw [List.filter_cons_of_neg (by simp [hx])] at h2
      cases h1 with
      | cons h hs =>
        obtain ⟨y₀, hy, hp⟩ := Each₂_ksm.unfilter_c13 P xs hs h2
        exact ⟨_ :: y₀, .cons h hy, hp.cons _⟩
    | false =>
      rw [List.filter_cons_of_neg (by simp [hx])] at h1
      rw [List.filter_cons_of_pos (by simp [hx])] at h2
      cases h2 with
      | @cons _ y _ ys hy' hs =>
        obtain ⟨y₀, hy, hp⟩ := Each₂_ksm.unfilter_c13 P xs h1 hs
        exact ⟨y :: y₀, .cons hy' hy, List.perm_middle.trans (hp.cons _)⟩

end Each

/-! ## The forms of a construction's parts, in `orderParts`' order -/

/-- An element or an entry. -/
def isElemF_c13 : EvalForm → Bool
  | .el _ | .kv _ _ => true
  | _ => false

/-- `orderParts` on the forms. -/
def orderPartsF_c13 (k : Kind) (qs : List EvalForm) : List EvalForm :=
  if k == .list then qs else qs.filter isElemF_c13 ++ qs.filter (!isElemF_c13 ·)

theorem Each₂_ksm.order_c13 {β : Type} {R : EvalForm → β → Prop} {Q : β → Bool}
    (hPQ : ∀ x y, R x y → isElemF_c13 x = Q y) (k : Kind) {xs : List EvalForm} {ys : List β}
    (h : Each₂_ksm R xs ys) :
    Each₂_ksm R (orderPartsF_c13 k xs) (if k == .list then ys else ys.filter Q ++ ys.filter (!Q ·)) := by
  unfold orderPartsF_c13
  by_cases hk : (k == .list) = true
  · rw [ite_eq_left hk, ite_eq_left hk]; exact h
  · rw [ite_eq_right hk, ite_eq_right hk]
    exact (h.filter_c13 hPQ).append_c13 (h.filter_c13 (P := (!isElemF_c13 ·)) (Q := (!Q ·))
      fun x y hxy => by rw [hPQ x y hxy])

theorem Each₂_ksm.unorder_c13 {β : Type} {R : EvalForm → β → Prop} (k : Kind) {xs : List EvalForm}
    {ys : List β} (h : Each₂_ksm R (orderPartsF_c13 k xs) ys) :
    ∃ ys₀, Each₂_ksm R xs ys₀ ∧ ys.Perm ys₀ ∧ (k = .list → ys = ys₀) := by
  unfold orderPartsF_c13 at h
  split at h
  · exact ⟨ys, h, .refl _, fun _ => rfl⟩
  · rename_i hk
    obtain ⟨y₁, y₂, rfl, h1, h2⟩ := Each₂_ksm.split_c13 h
    obtain ⟨y₀, hy, hp⟩ := Each₂_ksm.unfilter_c13 isElemF_c13 xs h1 h2
    exact ⟨y₀, hy, hp, fun e => by subst e; simp at hk⟩

theorem orderParts_eq_c13 (k : Kind) (ps : List T) :
    orderParts k ps = if k == .list then ps else ps.filter isElemT ++ ps.filter (!isElemT ·) := rfl

/-! ## `bot` among parts -/

theorem hasBotF_iff_c13 : ∀ {ts : List T}, hasBotF ts = true ↔ T.bot ∈ ts
  | [] => by simp [hasBotF]
  | t :: ts => by
    simp only [hasBotF, Bool.or_eq_true, decide_eq_true_eq, List.mem_cons, hasBotF_iff_c13 (ts := ts)]
    constructor
    · rintro (h | h)
      · exact .inl h.symm
      · exact .inr h
    · rintro (h | h)
      · exact .inl h.symm
      · exact .inr h

theorem hasBotF_perm_c13 {ts us : List T} (h : ts.Perm us) : hasBotF ts = hasBotF us := by
  rw [Bool.eq_iff_iff, hasBotF_iff_c13, hasBotF_iff_c13]
  exact h.mem_iff

theorem hasBotF_append_c13 (ts us : List T) : hasBotF (ts ++ us) = (hasBotF ts || hasBotF us) := by
  induction ts with
  | nil => simp [hasBotF]
  | cons t ts ih => simp only [List.cons_append, hasBotF, ih, Bool.or_assoc]

/-! ## Parts holding items, up to their order -/

section Parts
variable {c : Semantics} {K : CollKind}

theorem PartsIts_khc.uncons_c13 {x : T} {l : List T} {its : List (List GroundTerm)}
    (h : PartsIts_khc c K (x :: l) its) :
    ∃ B rest, its = B ++ rest ∧ PartsIts_khc c K [x] B ∧ PartsIts_khc c K l rest := by
  cases h with
  | elem hit hs => exact ⟨[_], _, rfl, .elem hit .nil, hs⟩
  | coll hc hg hs => exact ⟨_, _, rfl, by simpa using PartsIts_khc.coll hc hg .nil, hs⟩

/-- Permuted parts hold the same items, permuted. -/
theorem PartsIts_khc.perm_c13 {ps ps' : List T} (hp : ps.Perm ps') :
    ∀ {its : List (List GroundTerm)}, PartsIts_khc c K ps its →
      ∃ its', PartsIts_khc c K ps' its' ∧ its'.Perm its := by
  induction hp with
  | nil => exact fun h => ⟨_, h, .refl _⟩
  | cons x _ ih =>
    intro its h
    obtain ⟨B, rest, rfl, hB, hr⟩ := h.uncons_c13
    obtain ⟨r', hr', hp'⟩ := ih hr
    exact ⟨B ++ r', by simpa using hB.append_kcv hr', hp'.append_left B⟩
  | swap x y l =>
    intro its h
    obtain ⟨B, rest, rfl, hB, hr⟩ := h.uncons_c13
    obtain ⟨B', rest', rfl, hB', hr'⟩ := hr.uncons_c13
    refine ⟨B' ++ (B ++ rest'), by simpa using hB'.append_kcv (hB.append_kcv hr'), ?_⟩
    rw [← List.append_assoc, ← List.append_assoc]
    exact List.perm_append_comm.append_right _
  | trans _ _ ih1 ih2 =>
    intro its h
    obtain ⟨i1, h1, p1⟩ := ih1 h
    obtain ⟨i2, h2, p2⟩ := ih2 h1
    exact ⟨i2, h2, p2.trans p1⟩

end Parts

/-! ## C13's consequences -/

section Shapes
variable {d : Semantics}

/-- A collection sort is not `Float`. -/
theorem collSort_ne_float_c13 (hc : encodable d = true) {s : Srt} {Ks : CollSig}
    (hKs : d.collOf s = some Ks) : s ≠ Srt.float := by
  obtain ⟨hmem, rfl⟩ := collOf_parts_kcv hKs
  intro e
  have := Faithful.collSortsOK_mem (encodable_colls_c13 hc).2.1 hmem
  rw [e] at this
  simp [collSortOK] at this

/-- The key sort of a collection is not `Float`, nor the value sort of a map collection. -/
theorem collKey_ne_float_c13 (hc : encodable d = true) {s : Srt} {Ks : CollSig}
    (hKs : d.collOf s = some Ks) : Ks.key ≠ Srt.float ∧ (Ks.kind = .map → valSort Ks ≠ Srt.float) := by
  obtain ⟨hmem, -⟩ := collOf_parts_kcv hKs
  have hf := (encodable_facts hc).2.2
  have hin : ∀ x ∈ Ks.sort :: Ks.key :: Ks.val.toList, x ∈ sigSorts d := fun x hx => by
    unfold sigSorts
    simp only [List.mem_append, List.mem_flatMap]
    exact .inl (.inr ⟨Ks, hmem, hx⟩)
  refine ⟨fun e => hf (e ▸ hin _ (by simp)), fun hk e => ?_⟩
  have hv := Faithful.collsOK_val (encodable_colls_c13 hc).1 hmem hk
  exact hf (e ▸ hin (valSort Ks) (by simp [hv]))

/-- **A value of a collection sort is a collection value** of the collection's kind and of that
sort: not a constructor term (no constructor's result is a collection sort, no overloading symbol,
no open generator), not an injection (no subsort pair ends at a collection sort), not a domain
value (`collSortsOK`). -/
theorem coll_shape_c13 (hr : CExec.execReady d = true) (hc : encodable d = true)
    {s : Srt} {Ks : CollSig} {k : Kind} (hKs : (d₀ d).collOf s = some Ks) (hk : kindOf Ks.kind = some k)
    {w : GroundTerm} (hw : (d₀ d).sortOf w = some s) :
    ∃ its, CExec.content w = some (Ks.kind, s, its) := by
  obtain ⟨-, hcso, hctor, hsub⟩ := encodable_colls_c13 hc
  have hKs' : d.collOf s = some Ks := hKs
  obtain ⟨E, hE⟩ : ∃ E, encDef d = some E :=
    Option.isSome_iff_exists.mp (by rw [encDef_isSome]; exact hc)
  cases w with
  | ctor f ts =>
    exfalso
    obtain ⟨k', hk', -, rfl⟩ :=
      ((d₀ d).sortOf_ctor_of_none (encodable_facts hc).1 (noRaw_kev (d := d) hr hE)).mp hw
    rw [hctor k' (lookupSig_spec hk').1] at hKs'
    cases hKs'
  | inj a b t =>
    exfalso
    obtain ⟨hab, -, -, hsb⟩ := sortOf_inj.mp hw
    have h0 : d.collOf b = none := hsub _ hab
    rw [← hsb, hKs'] at h0
    cases h0
  | dv s' lit =>
    exfalso
    obtain ⟨hmem, hsort⟩ := collOf_parts_kcv hKs'
    have hso := Faithful.collSortsOK_mem hcso hmem
    rw [hsort] at hso
    have hcar : d.lib.carriers.all (·.1 != s) = true := by
      unfold collSortOK at hso; simp only [Bool.and_eq_true] at hso; exact hso.2
    unfold collSortOK at hso
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_true'] at hso
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨hi, hb⟩, hkv⟩, ht⟩, hy⟩, hfl⟩, hstr⟩, hbys⟩, -⟩ := hso
    obtain ⟨hok, hss⟩ := sortOf_dv.mp hw
    rw [← hss] at hok
    have hok' : dvOK d.lib s lit = true := hok
    rw [dvOK_self (Lib.carrier_of_not _ hcar)] at hok'
    cases lit with
    | int i => exact hi (beq_iff_eq.mp hok')
    | bool b => exact hb (beq_iff_eq.mp hok')
    | tok t =>
      simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hok'
      rcases hok' with ((h | h) | h) | ⟨h | h, -⟩
      · exact hkv h
      · exact hstr h
      · rw [ht] at h; cases h
      · exact hbys h
      · rw [hy] at h; cases h
    | float _ _ _ =>
      simp only [Bool.and_eq_true, beq_iff_eq] at hok'; exact hfl hok'.1
  | map s' es =>
    obtain ⟨k', -, hk', hkind, -, -, -, rfl⟩ := sortOf_mapS_fwd hw
    rw [hKs] at hk'; cases hk'
    rcases hkind with h | h
    · exact ⟨es.map fun e => [e.1, e.2], by simp [content, h]⟩
    · rw [h] at hk; cases hk
  | set s' es =>
    obtain ⟨k', hk', hkind, -, -, rfl⟩ := sortOf_setS.mp hw
    rw [hKs] at hk'; cases hk'
    exact ⟨es.map fun e => [e], by simp [content, hkind]⟩
  | list s' es =>
    obtain ⟨k', hk', hkind, -, rfl⟩ := sortOf_listS.mp hw
    rw [hKs] at hk'; cases hk'
    exact ⟨es.map fun e => [e], by simp [content, hkind]⟩

/-- **The signature of a collection symbol among a right side's heads**: the sort `collSymOf`
reads, a collection sort of the symbol's kind, and the collection's argument sorts of the
symbol's role. An interpreted symbol's is its `hookSigs` one; a parameter's is its declaration,
which `collsOK` makes the collection's. -/
theorem collSig_rhs_c13 (hc : encodable d = true) {L : List CtorSig} {f : Sym}
    {k : Kind} {s : Srt} {r : CRole} {sg : CtorSig} (hct : d.isCtor f = false)
    (hcy : collSymOf d f = some (k, s, r)) (hsg : lookupSig ((d₀ d).rhsCtx L).heads f = some sg) :
    sg.result = s ∧ ∃ Ks, (d₀ d).collOf s = some Ks ∧ kindOf Ks.kind = some k ∧
      sg.args = roleArgs_cdp Ks r := by
  have hcs : collsOK d = true := (encodable_colls_c13 hc).1
  obtain ⟨g, s₀, hl, hcase⟩ := collSym_lib_cdp hcy
  rcases hcase with ⟨hh, rfl, rfl⟩ | ⟨hh, kp, hkp, hg, rfl⟩
  · have hlk : lookupSig hookSigs f = some sg := rhs_lookup_hook_kst (c := d₀ d) hct hh hsg
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
    have hci : Faithful.collImpl kp = true := by unfold Faithful.collImpl; rw [hg]; exact hpc
    have hlk : sg = kp.sig := by
      simp only [Semantics.rhsCtx, List.append_assoc] at hsg
      rw [lookupSig_append_of_none (lookupSig_ctor_none_kst (c := d₀ d) hct),
        lookupSig_append_of_none (lookupSig_hookSigs_of_not_isHook hh),
        lookupSig_append_of_some (by rw [(d₀ d).lookupSig_params]; exact congrArg (Option.map (·.sig)) hkp)]
        at hsg
      cases hsg; rfl
    subst hlk
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

/-- An application of a collection symbol evaluates by strictness to `collVal` of the arguments'
values. -/
theorem evalTerm_coll_c13 {σ : Subst} {f : Sym} {k : Kind} {s : Srt} {r : CRole} {ts : List Term}
    {os : List (Option GroundTerm)} (hct : d.isCtor f = false) (hcy : collSymOf d f = some (k, s, r))
    (hos : EvalTerms (d₀ d) σ ts os) :
    EvalTerm (d₀ d) σ (.app f ts) ((allSome os).bind ((d₀ d).collVal f)) := by
  obtain ⟨g, s₀, -, hcase⟩ := collSym_lib_cdp hcy
  rcases hcase with ⟨hh, rfl, -⟩ | ⟨hh, kp, hkp, -, -⟩
  · refine .hook hct hh hos (fun ws hws => ?_) (fun hn => by rw [hn]; rfl)
    simp only [hws, Option.bind_some]
    rw [hookRes_join_kst (d := d) hh ws]
    unfold Semantics.collVal
    rw [ite_eq_left hh, Semantics.hookRes_withHooks_none]
  · have hp : (d₀ d).isParam f = true := by
      unfold Semantics.isParam
      rw [show (d₀ d).lookupParam f = some kp from hkp]; rfl
    refine .param hct hh hp hos ?_
    have hcv : (d₀ d).collVal f = (d₀ d).paramVal f := funext fun vs => by simp [Semantics.collVal, hh]
    rw [hcv]

end Shapes

/-! ## The tree of a construction's parts -/

/-- The forms `eval` is asked for and the parts `encCollWith` writes, of a term read as a part
of a construction of the collection of kind `k` and sort `s`: any term as one part (`leaf`), or
an application of a collection symbol of that collection: the unit no part, the element one
`el` or `kv`, the concatenation the parts of both arguments. -/
inductive CbPart_c13 (d : Semantics) (k : Kind) (s : Srt) : Term → List EvalForm → List T → Prop
  | leaf {a : Term} {p : T} (hp : encTerm d a = some p) : CbPart_c13 d k s a [.term a] [p]
  | unit {f : Sym} (hct : d.isCtor f = false) (hcy : collSymOf d f = some (k, s, .unit)) :
      CbPart_c13 d k s (.app f []) [] []
  | el {f : Sym} {x : Term} {p : T} (hct : d.isCtor f = false)
      (hcy : collSymOf d f = some (k, s, .elem)) (hk : k ≠ .map) (hp : encTerm d x = some p) :
      CbPart_c13 d k s (.app f [x]) [.el x] [.el p]
  | kv {f : Sym} {a v : Term} {p q : T} (hct : d.isCtor f = false)
      (hcy : collSymOf d f = some (k, s, .elem)) (hk : k = .map) (hp : encTerm d a = some p)
      (hq : encTerm d v = some q) : CbPart_c13 d k s (.app f [a, v]) [.kv a v] [.kv p q]
  | concat {f : Sym} {a b : Term} {qa qb : List EvalForm} {pa pb : List T}
      (hct : d.isCtor f = false) (hcy : collSymOf d f = some (k, s, .concat))
      (ha : CbPart_c13 d k s a qa pa) (hb : CbPart_c13 d k s b qb pb) :
      CbPart_c13 d k s (.app f [a, b]) (qa ++ qb) (pa ++ pb)

section Tree
variable {d : Semantics}

theorem encTerms_one_c13 {ts : List Term} {p : T} (h : encTermsWith d encLit ts = some [p]) :
    ∃ x, ts = [x] ∧ encTerm d x = some p := by
  cases ts with
  | nil => cases encTerms_nil_kmf d h
  | cons x ts =>
    obtain ⟨q, qs', hq, hqs, he⟩ := encTerms_cons_kmf d h
    cases he
    cases ts with
    | nil => exact ⟨x, rfl, hq⟩
    | cons y ts =>
      obtain ⟨q₂, qs₂, -, -, he₂⟩ := encTerms_cons_kmf d hqs
      cases he₂

theorem encTerms_two_c13 {ts : List Term} {p q : T} (h : encTermsWith d encLit ts = some [p, q]) :
    ∃ a v, ts = [a, v] ∧ encTerm d a = some p ∧ encTerm d v = some q := by
  cases ts with
  | nil => cases encTerms_nil_kmf d h
  | cons a ts =>
    obtain ⟨p', qs', hp, hqs, he⟩ := encTerms_cons_kmf d h
    cases he
    obtain ⟨v, rfl, hv⟩ := encTerms_one_c13 hqs
    exact ⟨a, v, rfl, hp, hv⟩

/-- `encCollWith`'s parts as a tree. -/
theorem cbPart_of_coll_c13 {k : Kind} {s : Srt} : ∀ (n : Nat) {f : Sym} {r : CRole} {ts : List Term}
    {ps : List T}, sizeOf ts < n → d.isCtor f = false → collSymOf d f = some (k, s, r) →
    encCollWith d encLit k s r ts = some ps → ∃ qs, CbPart_c13 d k s (.app f ts) qs ps
  | 0, _, _, _, _, hn, _, _, _ => absurd hn (Nat.not_lt_zero _)
  | n + 1, f, r, ts, ps, hn, hct, hcy, h => by
    rcases encColl_cases_cdp h with ⟨rfl, rfl, rfl⟩ | ⟨rfl, qs, e, hqs, rfl, hcase⟩ |
      ⟨rfl, a, v, pa, pb, rfl, ha, hb, rfl⟩
    · exact ⟨[], .unit hct hcy⟩
    · rcases hcase with ⟨hk, p, rfl, rfl⟩ | ⟨hk, p, q, rfl, rfl⟩
      · obtain ⟨x, rfl, hx⟩ := encTerms_one_c13 hqs
        exact ⟨_, .el hct hcy hk hx⟩
      · obtain ⟨a, v, rfl, ha, hv⟩ := encTerms_two_c13 hqs
        exact ⟨_, .kv hct hcy hk ha hv⟩
    · have part : ∀ (x : Term) (px : List T), sizeOf x < sizeOf [a, v] →
          encPartWith d encLit k s x = some px → ∃ qx, CbPart_c13 d k s x qx px := by
        intro x px hx h'
        rcases encPart_cases_cdp h' with ⟨g, us, r', rfl, hg, hgy, hus⟩ | ⟨q, hq, rfl⟩
        · refine cbPart_of_coll_c13 n (ts := us) ?_ hg hgy hus
          simp only [Term.app.sizeOf_spec] at hx
          omega
        · exact ⟨_, .leaf hq⟩
      have h1 : sizeOf a < sizeOf [a, v] := List.sizeOf_lt_of_mem (by simp)
      have h2 : sizeOf v < sizeOf [a, v] := List.sizeOf_lt_of_mem (by simp)
      obtain ⟨qa, hqa⟩ := part a pa h1 ha
      obtain ⟨qb, hqb⟩ := part v pb h2 hb
      exact ⟨_, .concat hct hcy hqa hqb⟩

end Tree

/-! ## The forms of the parts, under a substitution -/

section Forms
variable {d : Semantics}

theorem mem_varOccsList_c13 {i : Nat} {a : Term} : ∀ {ts : List Term}, a ∈ ts → i ∈ varOccs a →
    i ∈ varOccsList ts
  | t :: ts, hm, hi => by
    rw [varOccsList, List.mem_append]
    rcases List.mem_cons.mp hm with rfl | hm
    · exact .inl hi
    · exact .inr (mem_varOccsList_c13 hm hi)

theorem varOccs_arg_c13 {i : Nat} {f : Sym} {a : Term} {ts : List Term} (hm : a ∈ ts)
    (hi : i ∈ varOccs a) : i ∈ varOccs (.app f ts) := by
  rw [varOccs]; exact mem_varOccsList_c13 hm hi

/-- The sorts of the arguments of a collection symbol in a right side: its role's argument sorts of
the collection. -/
theorem node_sorts_c13 (hc : encodable d = true) {L : List CtorSig} {vars : List Srt} {f : Sym}
    {k : Kind} {s s₀ : Srt} {r : CRole} {Ks : CollSig} {ts : List Term} (hct : d.isCtor f = false)
    (hcy : collSymOf d f = some (k, s, r)) (hKs : (d₀ d).collOf s = some Ks)
    (hs : sortOfTerm ((d₀ d).rhsCtx L) vars (.app f ts) = some s₀) :
    sortsOfTerms ((d₀ d).rhsCtx L) vars ts = some (roleArgs_cdp Ks r) ∧ s₀ = s := by
  obtain ⟨sg, hsg, hargs, rfl⟩ := sortOfTerm_app.mp hs
  obtain ⟨hres, Ks', hKs', -, hsa⟩ := collSig_rhs_c13 hc hct hcy hsg
  rw [hKs] at hKs'; cases hKs'
  exact ⟨hsa ▸ hargs, hres⟩

theorem sortsOfTerms_one_c13 {x : TermCtx} {vars : List Srt} {a : Term} {s : Srt}
    (h : sortsOfTerms x vars [a] = some [s]) : sortOfTerm x vars a = some s := by
  obtain ⟨s', ss', h1, h2, he⟩ := sortsOfTerms_cons.mp h
  cases he; exact h1

theorem sortsOfTerms_two_c13 {x : TermCtx} {vars : List Srt} {a b : Term} {s t : Srt}
    (h : sortsOfTerms x vars [a, b] = some [s, t]) :
    sortOfTerm x vars a = some s ∧ sortOfTerm x vars b = some t := by
  obtain ⟨s', ss', h1, h2, he⟩ := sortsOfTerms_cons.mp h
  cases he
  exact ⟨h1, sortsOfTerms_one_c13 h2⟩

/-- What a part's form is under `σ`, and whether it is an element: the instance of the part is
the form's instance. -/
def PartIs_c13 (d : Semantics) (σ : Subst) (q : EvalForm) (p : T) : Prop :=
  (∀ p', instF p (bindOfSubst σ) = some p' → q.Is d σ p') ∧ isElemF_c13 q = isElemT p

theorem sortOf_mem_c13 {x : TermCtx} {vars : List Srt} {a : Term} :
    ∀ {ts : List Term} {ss : List Srt}, sortsOfTerms x vars ts = some ss → a ∈ ts →
      ∃ s', sortOfTerm x vars a = some s'
  | t :: ts, ss, h, hm => by
    obtain ⟨s', ss', h1, h2, -⟩ := sortsOfTerms_cons.mp h
    rcases List.mem_cons.mp hm with rfl | hm
    · exact ⟨s', h1⟩
    · exact sortOf_mem_c13 h2 hm

theorem cbPart_is_c13 {σ : Subst} {L : List CtorSig} {vars : List Srt}
    (hL : HeadsOK (d₀ d) L) {k : Kind} {s : Srt}
    {tm : Term} {qs : List EvalForm} {ps : List T} (h : CbPart_c13 d k s tm qs ps) :
    ∀ {s₀ : Srt}, sortOfTerm ((d₀ d).rhsCtx L) vars tm = some s₀ →
    (d₀ d).WellSortedAt vars (varOccs tm) σ →
    (∀ i ∈ varOccs tm, ∀ v, σ.lookup i = some v → litsV v = true) →
    Each₂_ksm (PartIs_c13 d σ) qs ps := by
  have arg : ∀ {f : Sym} {ts : List Term} {a : Term} {s₀ : Srt}, a ∈ ts →
      sortOfTerm ((d₀ d).rhsCtx L) vars (.app f ts) = some s₀ →
      (d₀ d).WellSortedAt vars (varOccs (.app f ts)) σ →
      (∀ i ∈ varOccs (.app f ts), ∀ v, σ.lookup i = some v → litsV v = true) →
      ∃ s', sortOfTerm ((d₀ d).rhsCtx L) vars a = some s' ∧ (d₀ d).WellSortedAt vars (varOccs a) σ ∧
        (∀ i ∈ varOccs a, ∀ v, σ.lookup i = some v → litsV v = true) := by
    intro f ts a s₀ hm hs hw hl
    obtain ⟨sg, -, hargs, -⟩ := sortOfTerm_app.mp hs
    obtain ⟨s', hs'⟩ := sortOf_mem_c13 hargs hm
    exact ⟨s', hs', fun i hi => hw i (varOccs_arg_c13 hm hi), fun i hi => hl i (varOccs_arg_c13 hm hi)⟩
  induction h with
  | @leaf a p hp =>
    intro s₀ hs hw hl
    refine .cons ⟨fun p' hp' => ⟨termOK_of_kst hL hs (fun _ h => h) hw hl, p, hp, hp'⟩, ?_⟩ .nil
    rw [encTerm_notElem_cdp hp]; rfl
  | unit => intros; exact .nil
  | @el f x p hct hcy hkm hp =>
    intro s₀ hs hw hl
    obtain ⟨sx, hsx, hwx, hlx⟩ := arg (List.mem_singleton_self x) hs hw hl
    refine .cons ⟨fun p' hp' => ?_, rfl⟩ .nil
    rw [instF] at hp'
    obtain ⟨p'', h'', rfl⟩ := Option.map_eq_some_iff.mp hp'
    exact ⟨termOK_of_kst hL hsx (fun _ h => h) hwx hlx, p'', ⟨p, hp, h''⟩, rfl⟩
  | @kv f a v p q hct hcy hkm hp hq =>
    intro s₀ hs hw hl
    obtain ⟨sa, hsa, hwa, hla⟩ := arg (List.mem_cons_self ..) hs hw hl
    obtain ⟨sv, hsv, hwv, hlv⟩ := arg (List.mem_cons_of_mem _ (List.mem_singleton_self v)) hs hw hl
    refine .cons ⟨fun p' hp' => ?_, rfl⟩ .nil
    rw [instF] at hp'
    obtain ⟨pa, ha, hp'⟩ := Option.bind_eq_some_iff.mp hp'
    obtain ⟨pv, hv, rfl⟩ := Option.map_eq_some_iff.mp hp'
    exact ⟨termOK_of_kst hL hsa (fun _ h => h) hwa hla, termOK_of_kst hL hsv (fun _ h => h) hwv hlv,
      pa, pv, ⟨p, hp, ha⟩, ⟨q, hq, hv⟩, rfl⟩
  | @concat f a b qa qb pa pb hct hcy ha hb iha ihb =>
    intro s₀ hs hw hl
    obtain ⟨sa, hsa, hwa, hla⟩ := arg (List.mem_cons_self ..) hs hw hl
    obtain ⟨sb, hsb, hwb, hlb⟩ := arg (List.mem_cons_of_mem _ (List.mem_singleton_self b)) hs hw hl
    exact (iha hsa hwa hla).append_c13 (ihb hsb hwb hlb)

theorem instTsF_each_c13 {B : Bind} : ∀ {ps ps' : List T}, instTsF ps B = some ps' →
    Each₂_ksm (fun p p' => instF p B = some p') ps ps'
  | [], ps', h => by rw [instTsF] at h; cases h; exact .nil
  | p :: ps, ps', h => by
    rw [instTsF] at h
    obtain ⟨p', hp, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨ps'', hps, rfl⟩ := Option.map_eq_some_iff.mp h
    exact .cons hp (instTsF_each_c13 hps)

end Forms

/-! ## What KCore gives the tree -/

section Eval
variable {d : Semantics}

/-- The encoding of a value with kore.k literals is no `bot`. -/
theorem enc_ne_bot_c13 : ∀ {w : GroundTerm}, litsV w = true → enc w ≠ .bot
  | .ctor _ _, _ => by simp [enc]
  | .inj _ _ _, _ => by simp [enc]
  | .dv s l, h => by
    simp only [litsV] at h
    obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp h
    rw [enc_dv_of_encLit hp]
    rcases encLit_some hp with ⟨i, -, -, rfl⟩ | ⟨b, -, -, rfl⟩ | ⟨x, -, rfl⟩ <;> simp
  | .map _ _, _ => by simp [enc]
  | .set _ _, _ => by simp [enc]
  | .list _ _, _ => by simp [enc]

theorem mkElV_enc_c13 {w : GroundTerm} (lw : litsV w = true) : mkElV_ksm (enc w) = .el (enc w) := by
  have := enc_ne_bot_c13 lw
  revert this
  cases enc w <;> simp [mkElV_ksm]

theorem mkKvV_enc_c13 {a v : GroundTerm} (la : litsV a = true) (lv : litsV v = true) :
    mkKvV_ksm (enc a) (enc v) = .kv (enc a) (enc v) := by
  unfold mkKvV_ksm
  rw [hasBotF_false_khc (by
    intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    · exact enc_ne_bot_c13 la
    · exact enc_ne_bot_c13 lv)]
  rfl

theorem elemArgs_one_c13 {Ks : CollSig} {k : Kind} (hk : kindOf Ks.kind = some k) (hkm : k ≠ .map) :
    elemArgs Ks = [Ks.key] := by
  rcases kindOf_inv_cdp hk with ⟨h1, rfl⟩ | ⟨h1, -⟩ | ⟨h1, -⟩
  · exact absurd rfl hkm
  · unfold elemArgs; rw [h1]
  · unfold elemArgs; rw [h1]

theorem elemArgs_two_c13 {Ks : CollSig} {k : Kind} (hk : kindOf Ks.kind = some k) (hkm : k = .map) :
    elemArgs Ks = [Ks.key, valSort Ks] ∧ Ks.kind = .map := by
  subst hkm
  rcases kindOf_inv_cdp hk with ⟨h1, -⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · unfold elemArgs; rw [h1]; exact ⟨rfl, rfl⟩
  · cases h2
  · cases h2

/-- **KCore's result on the tree.** A term read as a part of a construction of the collection
`Ks` of sort `s`, sorted at `s`, has a result `o`; where the results `us` of its parts' forms hold
`bot`, `o` is none; otherwise they hold the items `its` (`PartsIts_khc`), and where their keys are
apart (always for a list) `o` is a value of the collection with those items up to order (in order
for a list), and where two keys meet `o` is none. -/
theorem cbPart_eval_c13 (hr : CExec.execReady d = true) (hc : encodable d = true) {σ : Subst}
    {k : Kind} {s : Srt} {Ks : CollSig} (hKs : (d₀ d).collOf s = some Ks) (hk : kindOf Ks.kind = some k)
    {L : List CtorSig} {vars : List Srt} (hL : HeadsOK (d₀ d) L)
    {tm : Term} {qs : List EvalForm} {ps : List T} (h : CbPart_c13 d k s tm qs ps) :
    sortOfTerm ((d₀ d).rhsCtx L) vars tm = some s → (d₀ d).WellSortedAt vars (varOccs tm) σ →
    (∀ i ∈ varOccs tm, ∀ v, σ.lookup i = some v → litsV v = true) →
    ∀ {us : List T}, Each₂_ksm (fun q u => q.Gives d σ u) qs us →
    ∃ o, EvalTerm (d₀ d) σ tm o ∧ (hasBotF us = true → o = none) ∧
      (hasBotF us = false → ∃ its, PartsIts_khc (d₀ d) Ks.kind us its ∧
        ((k = .list ∨ (its.map keyIt_khc).Nodup) →
          ∃ u Y, o = some u ∧ SubCtx_cdp (d₀ d) u Ks k s Y ∧ Y.Perm its ∧ (k = .list → Y = its)) ∧
        (k ≠ .list → ¬ (its.map keyIt_khc).Nodup → o = none)) := by
  have hsc := sortCtx_kst hr hc
  have hcs : collsOK (d₀ d) = true := (encodable_colls_c13 hc).1
  have hsort : Ks.sort = s := (collOf_parts_kcv hKs).2
  have arg : ∀ {f : Sym} {ts : List Term} {a : Term} {s₀ : Srt}, a ∈ ts →
      (d₀ d).WellSortedAt vars (varOccs (.app f ts)) σ →
      (∀ i ∈ varOccs (.app f ts), ∀ v, σ.lookup i = some v → litsV v = true) →
      (d₀ d).WellSortedAt vars (varOccs a) σ ∧
        (∀ i ∈ varOccs a, ∀ v, σ.lookup i = some v → litsV v = true) := by
    intro f ts a s₀ hm hw hl
    exact ⟨fun i hi => hw i (varOccs_arg_c13 hm hi), fun i hi => hl i (varOccs_arg_c13 hm hi)⟩
  induction h with
  | @leaf a p hp =>
    intro hs hw hl us hg
    cases hg with
    | cons h1 h2 =>
    cases h2
    obtain ⟨o, rfl, ho⟩ := h1
    refine ⟨o, ho, ?_⟩
    cases o with
    | none => exact ⟨fun _ => rfl, fun h => by simp [hasBotF, encR] at h⟩
    | some w =>
      have hsw := Faithful.EvalTerm.sorted_at hsc ho hL hw hs rfl
      have lw := litsV_kst hr hc hsw (collSort_ne_float_c13 hc hKs)
      obtain ⟨g, hg⟩ := coll_shape_c13 hr hc hKs hk hsw
      have hx : SubCtx_cdp (d₀ d) w Ks k s g := ⟨hg, hsw, hKs, hk, lw⟩
      refine ⟨fun h => by simp [hasBotF, encR, enc_ne_bot_c13 lw] at h, fun _ => ⟨g, ?_, fun _ =>
        ⟨w, g, rfl, hx, .refl _, fun _ => rfl⟩, fun hkl hn => absurd ?_ hn⟩⟩
      · show PartsIts_khc (d₀ d) Ks.kind [enc w] g
        simpa using PartsIts_khc.coll hg hx.itemOK_kcv (PartsIts_khc.nil (c := d₀ d) (K := Ks.kind))
      · exact (enc_items_khc hk hkl hx.itemOK_kcv hsw lw hg (.refl _)).1
  | @unit f hct hcy =>
    intro hs hw hl us hg
    cases hg
    have hev := evalTerm_coll_c13 (σ := σ) hct hcy EvalTerms.nil
    obtain ⟨hdef, -⟩ := collVal_items_kcv hcs hcy hKs hk (vs := []) sortsOf_nil rfl RoleItems_kcv.unit
    obtain ⟨u, Y, hu, hx, hY, hlY⟩ := hdef (.inr List.nodup_nil)
    refine ⟨_, hev, fun h => by simp [hasBotF] at h, fun _ => ⟨[], .nil, fun _ => ⟨u, Y, ?_, hx, hY, hlY⟩,
      fun _ hn => absurd List.nodup_nil hn⟩⟩
    simpa [allSome] using hu
  | @el f x p hct hcy hkm hp =>
    intro hs hw hl us hg
    cases hg with
    | cons h1 h2 =>
    cases h2
    obtain ⟨ox, rfl, hox⟩ := h1
    obtain ⟨hargs, -⟩ := node_sorts_c13 hc hct hcy hKs hs
    have hel := elemArgs_one_c13 hk hkm
    rw [show roleArgs_cdp Ks .elem = elemArgs Ks from rfl, hel] at hargs
    have hsx := sortsOfTerms_one_c13 hargs
    obtain ⟨hwx, -⟩ := arg (f := f) (s₀ := s) (List.mem_singleton_self x) hw hl
    have hev := evalTerm_coll_c13 hct hcy (.cons hox .nil)
    refine ⟨_, hev, ?_⟩
    cases ox with
    | none => exact ⟨fun _ => by simp [allSome], fun h => by simp [hasBotF, mkElV_ksm, encR] at h⟩
    | some e =>
      have hse := Faithful.EvalTerm.sorted_at hsc hox hL hwx hsx rfl
      have le := litsV_kst hr hc hse (collKey_ne_float_c13 hc hKs).1
      have hit : ItemOK_khc (d₀ d) Ks.kind [e] := by
        rcases kindOf_inv_cdp hk with ⟨h1, rfl⟩ | ⟨h1, -⟩ | ⟨h1, -⟩
        · exact absurd rfl hkm
        · rw [h1]; exact ⟨e, Ks.key, rfl, hse, le⟩
        · rw [h1]; exact ⟨e, rfl⟩
      have hvs : (d₀ d).sortsOf [e] = some (roleArgs_cdp Ks .elem) := by
        rw [show roleArgs_cdp Ks .elem = elemArgs Ks from rfl, hel]
        exact sortsOf_cons.mpr ⟨_, _, hse, sortsOf_nil, rfl⟩
      obtain ⟨hdef, -⟩ := collVal_items_kcv hcs hcy hKs hk hvs (by simp [litsVL, le])
        (RoleItems_kcv.elem [e])
      obtain ⟨u, Y, hu, hx, hY, hlY⟩ := hdef (.inr (by simp))
      refine ⟨fun h => by simp [hasBotF, encR, mkElV_enc_c13 le] at h, fun _ =>
        ⟨[[e]], ?_, fun _ => ⟨u, Y, ?_, hx, hY, hlY⟩, fun _ hn => absurd (by simp) hn⟩⟩
      · show PartsIts_khc (d₀ d) Ks.kind [mkElV_ksm (enc e)] [[e]]
        rw [mkElV_enc_c13 le]
        exact PartsIts_khc.elem (it := [e]) hit .nil
      · simpa [allSome] using hu
  | @kv f a v p q hct hcy hkm hp hq =>
    intro hs hw hl us hg
    cases hg with
    | cons h1 h2 =>
    cases h2
    obtain ⟨oa, ov, rfl, hoa, hov⟩ := h1
    obtain ⟨hargs, -⟩ := node_sorts_c13 hc hct hcy hKs hs
    obtain ⟨hel, hkd⟩ := elemArgs_two_c13 hk hkm
    rw [show roleArgs_cdp Ks .elem = elemArgs Ks from rfl, hel] at hargs
    obtain ⟨hsa, hsv⟩ := sortsOfTerms_two_c13 hargs
    obtain ⟨hwa, -⟩ := arg (f := f) (s₀ := s) (List.mem_cons_self ..) hw hl
    obtain ⟨hwv, -⟩ := arg (f := f) (s₀ := s) (List.mem_cons_of_mem _ (List.mem_singleton_self v)) hw hl
    have hev := evalTerm_coll_c13 hct hcy (.cons hoa (.cons hov .nil))
    refine ⟨_, hev, ?_⟩
    cases oa with
    | none => exact ⟨fun _ => by simp [allSome], fun h => by simp [hasBotF, mkKvV_ksm, encR] at h⟩
    | some ea =>
    cases ov with
    | none => exact ⟨fun _ => by simp [allSome], fun h => by simp [hasBotF, mkKvV_ksm, encR] at h⟩
    | some ev =>
      have hsea := Faithful.EvalTerm.sorted_at hsc hoa hL hwa hsa rfl
      have hsev := Faithful.EvalTerm.sorted_at hsc hov hL hwv hsv rfl
      have lea := litsV_kst hr hc hsea (collKey_ne_float_c13 hc hKs).1
      have lev := litsV_kst hr hc hsev ((collKey_ne_float_c13 hc hKs).2 hkd)
      have hit : ItemOK_khc (d₀ d) Ks.kind [ea, ev] := by
        rw [hkd]; exact ⟨ea, ev, Ks.key, rfl, hsea, lea⟩
      have hvs : (d₀ d).sortsOf [ea, ev] = some (roleArgs_cdp Ks .elem) := by
        rw [show roleArgs_cdp Ks .elem = elemArgs Ks from rfl, hel]
        exact sortsOf_cons.mpr ⟨_, _, hsea, sortsOf_cons.mpr ⟨_, _, hsev, sortsOf_nil, rfl⟩, rfl⟩
      obtain ⟨hdef, -⟩ := collVal_items_kcv hcs hcy hKs hk hvs (by simp [litsVL, lea, lev])
        (RoleItems_kcv.elem [ea, ev])
      obtain ⟨u, Y, hu, hx, hY, hlY⟩ := hdef (.inr (by simp))
      refine ⟨fun h => by simp [hasBotF, encR, mkKvV_enc_c13 lea lev] at h, fun _ =>
        ⟨[[ea, ev]], ?_, fun _ => ⟨u, Y, ?_, hx, hY, hlY⟩, fun _ hn => absurd (by simp) hn⟩⟩
      · show PartsIts_khc (d₀ d) Ks.kind [mkKvV_ksm (enc ea) (enc ev)] [[ea, ev]]
        rw [mkKvV_enc_c13 lea lev]
        exact PartsIts_khc.elem (it := [ea, ev]) hit .nil
      · simpa [allSome] using hu
  | @concat f a b qa qb pa pb hct hcy ha hb iha ihb =>
    intro hs hw hl us hg
    obtain ⟨ua, ub, rfl, hga, hgb⟩ := Each₂_ksm.split_c13 hg
    obtain ⟨hargs, -⟩ := node_sorts_c13 hc hct hcy hKs hs
    rw [show roleArgs_cdp Ks .concat = [Ks.sort, Ks.sort] from rfl, hsort] at hargs
    obtain ⟨hsa, hsb⟩ := sortsOfTerms_two_c13 hargs
    obtain ⟨hwa, hla⟩ := arg (f := f) (s₀ := s) (List.mem_cons_self ..) hw hl
    obtain ⟨hwb, hlb⟩ := arg (f := f) (s₀ := s) (List.mem_cons_of_mem _ (List.mem_singleton_self b)) hw hl
    obtain ⟨oa, hoa, ba, ia⟩ := iha hsa hwa hla hga
    obtain ⟨ob, hob, bb, ib⟩ := ihb hsb hwb hlb hgb
    have hev := evalTerm_coll_c13 hct hcy (.cons hoa (.cons hob .nil))
    refine ⟨_, hev, fun hbot => ?_, fun hnb => ?_⟩
    · rw [hasBotF_append_c13, Bool.or_eq_true] at hbot
      rcases hbot with h | h
      · rw [ba h]; rfl
      · rw [bb h]; cases oa <;> rfl
    · rw [hasBotF_append_c13, Bool.or_eq_false_iff] at hnb
      obtain ⟨itsA, pA, sA, nA⟩ := ia hnb.1
      obtain ⟨itsB, pB, sB, nB⟩ := ib hnb.2
      refine ⟨itsA ++ itsB, pA.append_kcv pB, ?_⟩
      have ndA : ((itsA ++ itsB).map keyIt_khc).Nodup → (itsA.map keyIt_khc).Nodup := fun h => by
        rw [List.map_append] at h; exact h.sublist (List.sublist_append_left ..)
      have ndB : ((itsA ++ itsB).map keyIt_khc).Nodup → (itsB.map keyIt_khc).Nodup := fun h => by
        rw [List.map_append] at h; exact h.sublist (List.sublist_append_right ..)
      by_cases hA : k = .list ∨ (itsA.map keyIt_khc).Nodup
      · obtain ⟨ua', Ya, rfl, hxa, hYa, hla'⟩ := sA hA
        by_cases hB : k = .list ∨ (itsB.map keyIt_khc).Nodup
        · obtain ⟨ub', Yb, rfl, hxb, hYb, hlb'⟩ := sB hB
          have hvs : (d₀ d).sortsOf [ua', ub'] = some (roleArgs_cdp Ks .concat) := by
            rw [show roleArgs_cdp Ks .concat = [Ks.sort, Ks.sort] from rfl, hsort]
            exact sortsOf_cons.mpr ⟨_, _, hxa.sorted, sortsOf_cons.mpr ⟨_, _, hxb.sorted, sortsOf_nil, rfl⟩, rfl⟩
          obtain ⟨hdef, hund⟩ := collVal_items_kcv hcs hcy hKs hk hvs
            (by simp [litsVL, hxa.lits, hxb.lits]) (RoleItems_kcv.concat hxa.cont hxb.cont)
          have hperm : (Ya ++ Yb).Perm (itsA ++ itsB) := hYa.append hYb
          have hnd : ((Ya ++ Yb).map keyIt_khc).Nodup ↔ ((itsA ++ itsB).map keyIt_khc).Nodup :=
            (hperm.map _).nodup_iff
          refine ⟨fun hL' => ?_, fun hkl hn => ?_⟩
          · obtain ⟨u, Y, hu, hx, hY, hlY⟩ := hdef (hL'.imp id hnd.mpr)
            refine ⟨u, Y, ?_, hx, hY.trans hperm, fun hkl => by rw [hlY hkl, hla' hkl, hlb' hkl]⟩
            simpa [allSome] using hu
          · simpa [allSome] using hund hkl fun h => hn (hnd.mp h)
        · obtain ⟨hB1, hB2⟩ := not_or.mp hB
          rw [nB hB1 hB2]
          refine ⟨fun h => ?_, fun _ _ => rfl⟩
          rcases h with h | h
          · exact absurd h hB1
          · exact absurd (ndB h) hB2
      · obtain ⟨hA1, hA2⟩ := not_or.mp hA
        rw [nA hA1 hA2]
        refine ⟨fun h => ?_, fun _ _ => rfl⟩
        rcases h with h | h
        · exact absurd h hA1
        · exact absurd (ndA h) hA2

end Eval

/-! ## The case -/

section Case
open KCore.Det _root_.KK _root_.KK.Kit _root_.KK.Facts EvalV

/-- **The case of a collection construction**: `CbStep_kst` holds with no hypothesis. -/
theorem cbStep_c13 (d : Semantics) (E : D) : CbStep_kst d E := by
  intro hr hE σ f ts t r hb hok hi hct hcs
  have hc : encodable d = true := by rw [← encDef_isSome, hE]; rfl
  obtain ⟨⟨k, s, r₀⟩, hcy⟩ := Option.isSome_iff_exists.mp hcs
  obtain ⟨p, hp, ht⟩ := hi
  rw [encTerm_app_kmf] at hp
  unfold readApp at hp
  rw [ite_eq_right (by simp [hct]), hcy] at hp
  simp only [Option.bind_some] at hp
  obtain ⟨ps, hps, rfl⟩ := Option.map_eq_some_iff.mp hp
  rw [instF] at ht
  obtain ⟨ops, hops, rfl⟩ := Option.map_eq_some_iff.mp ht
  obtain ⟨qs, hcb⟩ := cbPart_of_coll_c13 (sizeOf ts + 1) (Nat.lt_succ_self _) hct hcy hps
  obtain ⟨L, vars, s₀, hL, hs, hw, hl⟩ := hok
  obtain ⟨sg, hsg, -, rfl⟩ := sortOfTerm_app.mp hs
  obtain ⟨hres, Ks, hKs, hk, -⟩ := collSig_rhs_c13 hc hct hcy hsg
  rw [hres] at hs
  -- the parts' forms, in `orderParts`' order, are what `evalTs` is given
  have hrel := cbPart_is_c13 hL hcb hs hw hl
  have hord : Each₂_ksm (PartIs_c13 d σ) (orderPartsF_c13 k qs) (orderParts k ps) :=
    Each₂_ksm.order_c13 (fun _ _ h => h.2) k hrel
  have hIs : Each₂_ksm (fun q t => q.Is d σ t) (orderPartsF_c13 k qs) ops :=
    Each₂_ksm.comp_c13 (fun _ _ _ h1 h2 => h1.1 _ h2) hord (instTsF_each_c13 hops)
  obtain ⟨rs, hrs, hcase⟩ := eval_cb_inv_kst hb
  obtain ⟨us, rfl, hg⟩ := (Spec_evalTs d E _ _).mp hrs.2 σ _ ops rfl hIs
  rcases hcase with ⟨y, hy, hR⟩ | ⟨hn, -⟩
  case inr => cases hn
  cases hy
  have hr' := (colOfF.eval_iff k s us).mp hR.1
  obtain ⟨us₀, hg₀, hperm, hlist⟩ := Each₂_ksm.unorder_c13 k hg
  obtain ⟨o, ho, hbot, hitems⟩ := cbPart_eval_c13 hr hc hKs hk hL hcb hs hw hl hg₀
  refine ⟨o, ?_, ho⟩
  rw [hr']
  suffices h : colOfF k s us = some (encR o) by rw [h]; rfl
  cases hb' : hasBotF us₀ with
  | true =>
    rw [hbot hb']
    show colOfF k s us = some .bot
    unfold colOfF
    rw [hasBotF_perm_c13 hperm, hb', ite_eq_left rfl]
  | false =>
    obtain ⟨its, hits, hdef, hund⟩ := hitems hb'
    obtain ⟨its', hits', hp'⟩ := PartsIts_khc.perm_c13 hperm.symm hits
    by_cases hkl : k = .list
    · subst hkl
      obtain ⟨u, Y, rfl, hx, -, hY⟩ := hdef (.inl rfl)
      have hKl := kindOf_list_cdp hk
      rw [hKl] at hits
      rw [hlist rfl]
      show colOfF .list s us₀ = some (enc u)
      rw [hx.enc_eq, hY rfl, colOfF_list_items_khc s hits]
      rfl
    · by_cases hn : (its.map keyIt_khc).Nodup
      · obtain ⟨u, Y, rfl, hx, hY, -⟩ := hdef (.inr hn)
        show colOfF k s us = some (enc u)
        exact colOfF_coll_khc hk hkl hits' hx.sorted hx.lits hx.cont (hY.trans hp'.symm)
      · rw [hund hkl hn]
        show colOfF k s us = some .bot
        exact colOfF_overlap_khc hk hkl s hits' fun h => hn ((hp'.map _).nodup_iff.mp h)

/-- **The step cases at `eval`, `evalTs`, `ensure` and `strictHook`**, with no hypothesis. -/
theorem stepCases_terms_c13 (d : Semantics) (E : D) :
    StepCase d E 464 ∧ StepCase d E 467 ∧ StepCase d E 463 ∧ StepCase d E 508 :=
  stepCases_terms_kst (cbStep_c13 d E)

end Case

/-! ## Instances -/

/-- kore.k's own definition meets C13: it meets `coreOK`. -/
theorem collFormOK_defn_c13 : collFormOK RefKk.defn.sem = true := collFormOK_of_coreOK RefKk.coreOK_defn

/-! ## Checks -/

#check @coll_shape_c13
#check @collSig_rhs_c13
#check @cbStep_c13
#check @stepCases_terms_c13
#check @collFormOK_defn_c13

open Lean in
#eval show CoreM Unit from do
  for n in [``coll_shape_c13, ``collSig_rhs_c13, ``cbPart_of_coll_c13, ``cbPart_is_c13,
      ``cbPart_eval_c13, ``cbStep_c13, ``stepCases_terms_c13] do
    let axs ← collectAxioms n
    unless axs.all ([``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "{n}: axioms {axs}"

end KCore.KK
