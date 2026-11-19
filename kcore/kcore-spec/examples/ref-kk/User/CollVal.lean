/-
  kore.k's `colOf` against KCore's `collVal`, the value a collection symbol builds from its
  arguments' values.

  A collection symbol `f` of `c` (`collSymOf c f = some (k, s, r)`) at arguments `vs` of its
  argument sorts with kore.k literals builds from the items `its` its role names
  (`RoleItems_kcv`): none for the unit, the one item `vs` for the element, the items of both
  collection values for the concatenation. `collVal_items_kcv`: where those items' keys are apart
  (a map's keys, a set's elements), and always for a list, `collVal f vs` is a value of the
  collection of `s` holding exactly those items (a list's in order); where two keys meet it is
  `none`. For a map the concatenation is `_Map_`, defined exactly where no key of one argument is a
  key of the other (`union_exists`, `union_spec`); for a set `_Set_`, defined exactly where they
  share no element (`concatS`). The unit and the element have one item or none, whose keys are
  apart.

  `colOf_collVal`: on parts that hold the items `its` up to order (in order for a list),
  `colOf(k, s, ps)` is the encoding of `collVal f vs`, `bot` where it is `none`. Its proof is
  User.HelpColl's `colOfF_coll_khc` where the keys are apart, `colOfF_overlap_khc` where they
  meet, `colOfF_list_items_khc` for a list.

  A collection value sorted in `c` with kore.k literals has items that are items of its kind
  (`SubCtx_cdp.itemOK_kcv`, from `SubCtx_cdp.item`), so its encoding is a part holding its items
  (`PartsIts_khc.enc_kcv`); parts concatenate (`PartsIts_khc.append_kcv`).
-/
import User.HelpColl

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option Elab.async false

namespace KCore.KK

open KCore.CExec (content build pairOf oneOf)
open KCore.Faithful (collsOK elemArgs valSort)

/-! ## The parts a collection value is -/

section Parts
variable {c : Semantics}

/-- The items of a collection value sorted in `c` with kore.k literals are items of its kind. -/
theorem SubCtx_cdp.itemOK_kcv {v : GroundTerm} {Ks : CollSig} {k : Kind} {s : Srt}
    {its : List (List GroundTerm)} (hx : SubCtx_cdp c v Ks k s its) :
    ∀ it ∈ its, ItemOK_khc c Ks.kind it := by
  intro it hit
  rcases hx.shape with ⟨es, vs, -, hkd, -, rfl, -, -, he⟩ | ⟨es, -, hkd, -, rfl, -, he⟩ |
    ⟨es, -, hkd, -, rfl, he⟩
  · obtain ⟨e, he', rfl⟩ := List.mem_map.mp hit
    obtain ⟨⟨h1, -⟩, l1, -⟩ := he e he'
    rw [hkd]; exact ⟨e.1, e.2, Ks.key, rfl, h1, l1⟩
  · obtain ⟨e, he', rfl⟩ := List.mem_map.mp hit
    obtain ⟨h1, l1⟩ := he e he'
    rw [hkd]; exact ⟨e, Ks.key, rfl, h1, l1⟩
  · obtain ⟨e, -, rfl⟩ := List.mem_map.mp hit
    rw [hkd]; exact ⟨e, rfl⟩

/-- The encoding of a collection value of the construction's collection is a part holding the
value's items. -/
theorem PartsIts_khc.enc_kcv {w : GroundTerm} {Ks : CollSig} {k : Kind} {s : Srt}
    {g : List (List GroundTerm)} (hx : SubCtx_cdp c w Ks k s g) {ps : List T}
    {its : List (List GroundTerm)} (hs : PartsIts_khc c Ks.kind ps its) :
    PartsIts_khc c Ks.kind (enc w :: ps) (g ++ its) :=
  .coll hx.cont hx.itemOK_kcv hs

/-- Parts concatenate, and so do their items. -/
theorem PartsIts_khc.append_kcv {K : CollKind} {ps qs : List T} {its jts : List (List GroundTerm)}
    (hp : PartsIts_khc c K ps its) (hq : PartsIts_khc c K qs jts) :
    PartsIts_khc c K (ps ++ qs) (its ++ jts) := by
  induction hp with
  | nil => exact hq
  | elem h _ ih => exact .elem h ih
  | coll hc hg _ ih => rw [List.append_assoc]; exact .coll hc hg ih

end Parts

/-! ## The items a collection symbol builds from -/

/-- The items a collection symbol of the collection kind `K`, the sort `s` and the role `r` builds
from its arguments: none for the unit, the one item its arguments are for the element, and for
the concatenation the items of the two collection values of `K` and `s` it is applied to, the
first's before the second's. -/
inductive RoleItems_kcv (K : CollKind) (s : Srt) :
    CRole → List GroundTerm → List (List GroundTerm) → Prop
  | unit : RoleItems_kcv K s .unit [] []
  | elem (it : List GroundTerm) : RoleItems_kcv K s .elem it [it]
  | concat {ua ub : GroundTerm} {ia ib : List (List GroundTerm)} (ha : content ua = some (K, s, ia))
      (hb : content ub = some (K, s, ib)) : RoleItems_kcv K s .concat [ua, ub] (ia ++ ib)

theorem keys_pairs_kcv : ∀ es : List (GroundTerm × GroundTerm),
    (es.map fun e => [e.1, e.2]).map keyIt_khc = es.map Prod.fst
  | [] => rfl
  | e :: es => by simp only [List.map_cons, keys_pairs_kcv es]; rfl

theorem keys_ones_kcv : ∀ es : List GroundTerm, (es.map fun e => [e]).map keyIt_khc = es
  | [] => rfl
  | e :: es => by simp only [List.map_cons, keys_ones_kcv es]; rfl

theorem keys_nodup_kcv {es : List (GroundTerm × GroundTerm)} (h : keysSorted es = true) :
    (es.map Prod.fst).Nodup :=
  List.pairwise_map.mpr ((sorted_pairwise h).imp fun hlt he => by rw [he, GroundTerm.cmp_refl] at hlt; cases hlt)

theorem sortsOf_one_kcv {c : Semantics} {a : Srt} {it : List GroundTerm}
    (h : c.sortsOf it = some [a]) : ∃ e, it = [e] ∧ c.sortOf e = some a := by
  cases it with
  | nil => simp [Semantics.sortsOf] at h
  | cons e es =>
    obtain ⟨s₁, ss, h1, h2, he⟩ := sortsOf_cons.mp h
    simp only [List.cons.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    cases es with
    | nil => exact ⟨e, rfl, h1⟩
    | cons e' es' =>
      obtain ⟨_, _, _, _, he'⟩ := sortsOf_cons.mp h2
      cases he'

theorem sortsOf_two_kcv {c : Semantics} {a b : Srt} {it : List GroundTerm}
    (h : c.sortsOf it = some [a, b]) :
    ∃ x y, it = [x, y] ∧ c.sortOf x = some a ∧ c.sortOf y = some b := by
  cases it with
  | nil => simp [Semantics.sortsOf] at h
  | cons x es =>
    obtain ⟨s₁, ss, h1, h2, he⟩ := sortsOf_cons.mp h
    simp only [List.cons.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    obtain ⟨e, rfl, h3⟩ := sortsOf_one_kcv h2
    exact ⟨x, e, rfl, h1, h3⟩

theorem litsVL_two_kcv {x y : GroundTerm} (h : litsVL [x, y] = true) :
    litsV x = true ∧ litsV y = true := by
  simp only [litsVL, Bool.and_true, Bool.and_eq_true] at h; exact h

theorem litsVL_one_kcv {x : GroundTerm} (h : litsVL [x] = true) : litsV x = true := by
  simp only [litsVL, Bool.and_true] at h; exact h

section Build
variable {c : Semantics} {f : Sym} {k : Kind} {s : Srt} {r : CRole} {Ks : CollSig}

theorem collOf_parts_kcv (hKs : c.collOf s = some Ks) : Ks ∈ c.allColls ∧ Ks.sort = s := by
  unfold Semantics.collOf at hKs
  exact ⟨List.mem_of_find?_eq_some hKs, by simpa using List.find?_some hKs⟩

/-- **The value a collection symbol builds.** At arguments of the symbol's argument sorts with
kore.k literals: where the items' keys are apart, and always for a list, `collVal` is a value of
the collection of `s` whose items are those items (in order for a list); where two keys meet, it
is `none`. -/
theorem collVal_items_kcv (hcs : collsOK c = true) (hcy : collSymOf c f = some (k, s, r))
    (hKs : c.collOf s = some Ks) (hk : kindOf Ks.kind = some k) {vs : List GroundTerm}
    (hvs : c.sortsOf vs = some (roleArgs_cdp Ks r)) (lv : litsVL vs = true)
    {its : List (List GroundTerm)} (hr : RoleItems_kcv Ks.kind s r vs its) :
    ((k = .list ∨ (its.map keyIt_khc).Nodup) →
      ∃ u Y, c.collVal f vs = some u ∧ SubCtx_cdp c u Ks k s Y ∧ Y.Perm its ∧ (k = .list → Y = its)) ∧
    (k ≠ .list → ¬ (its.map keyIt_khc).Nodup → c.collVal f vs = none) := by
  obtain ⟨hmem, hsort⟩ := collOf_parts_kcv hKs
  have hval : Ks.kind = .map → Ks.val = some (valSort Ks) := fun hkd =>
    Faithful.collsOK_val hcs hmem hkd
  cases hr with
  | unit =>
    refine ⟨fun _ => ?_, fun _ hn => absurd List.nodup_nil hn⟩
    rcases kindOf_inv_cdp hk with ⟨hkd, rfl⟩ | ⟨hkd, rfl⟩ | ⟨hkd, rfl⟩
    · have hx : SubCtx_cdp c (.map s []) Ks .map s [] :=
        subCtx_map_cdp hKs hkd (hval hkd) rfl fun e he => nomatch he
      refine ⟨_, [], collVal_unit_cdp hcy hk ?_, ?_, .refl _, fun _ => rfl⟩
      · rw [hkd]; exact hx.sorted
      · rw [hkd]; exact hx
    · have hx : SubCtx_cdp c (.set s []) Ks .set s [] :=
        subCtx_set_cdp hKs hkd rfl fun e he => nomatch he
      refine ⟨_, [], collVal_unit_cdp hcy hk ?_, ?_, .refl _, fun _ => rfl⟩
      · rw [hkd]; exact hx.sorted
      · rw [hkd]; exact hx
    · have hx : SubCtx_cdp c (.list s []) Ks .list s [] :=
        subCtx_list_cdp hKs hkd fun e he => nomatch he
      refine ⟨_, [], collVal_unit_cdp hcy hk ?_, ?_, .refl _, fun _ => rfl⟩
      · rw [hkd]; exact hx.sorted
      · rw [hkd]; exact hx
  | elem _ =>
    refine ⟨fun _ => ?_, fun _ hn => absurd (List.pairwise_singleton _ _) hn⟩
    rcases kindOf_inv_cdp hk with ⟨hkd, rfl⟩ | ⟨hkd, rfl⟩ | ⟨hkd, rfl⟩
    · have h2 : c.sortsOf vs = some [Ks.key, valSort Ks] := by
        rw [hvs]; simp only [roleArgs_cdp, elemArgs, hkd]
      obtain ⟨a, b, rfl, ha, hb⟩ := sortsOf_two_kcv h2
      obtain ⟨la, lb⟩ := litsVL_two_kcv lv
      have hx : SubCtx_cdp c (.map s [(a, b)]) Ks .map s [[a, b]] :=
        subCtx_map_cdp hKs hkd (hval hkd) rfl fun e he => by
          rcases List.mem_singleton.mp he with rfl
          exact ⟨⟨ha, hb⟩, la, lb⟩
      refine ⟨_, [[a, b]], collVal_elem_cdp hcy hk (.inl ⟨rfl, a, b, rfl⟩) ?_, ?_, .refl _, fun _ => rfl⟩
      · rw [hkd]; exact hx.sorted
      · rw [hkd]; exact hx
    · have h1 : c.sortsOf vs = some [Ks.key] := by
        rw [hvs]; simp only [roleArgs_cdp, elemArgs, hkd]
      obtain ⟨e, rfl, he⟩ := sortsOf_one_kcv h1
      have le := litsVL_one_kcv lv
      have hx : SubCtx_cdp c (.set s [e]) Ks .set s [[e]] :=
        subCtx_set_cdp hKs hkd rfl fun x hx => by
          rcases List.mem_singleton.mp hx with rfl
          exact ⟨he, le⟩
      refine ⟨_, [[e]], collVal_elem_cdp hcy hk (.inr ⟨by decide, e, rfl⟩) ?_, ?_, .refl _, fun _ => rfl⟩
      · rw [hkd]; exact hx.sorted
      · rw [hkd]; exact hx
    · have h1 : c.sortsOf vs = some [Ks.key] := by
        rw [hvs]; simp only [roleArgs_cdp, elemArgs, hkd]
      obtain ⟨e, rfl, he⟩ := sortsOf_one_kcv h1
      have le := litsVL_one_kcv lv
      have hx : SubCtx_cdp c (.list s [e]) Ks .list s [[e]] :=
        subCtx_list_cdp hKs hkd fun x hx => by
          rcases List.mem_singleton.mp hx with rfl
          exact ⟨he, le⟩
      refine ⟨_, [[e]], collVal_elem_cdp hcy hk (.inr ⟨by decide, e, rfl⟩) ?_, ?_, .refl _, fun _ => rfl⟩
      · rw [hkd]; exact hx.sorted
      · rw [hkd]; exact hx
  | @concat ua ub ia ib ha hb =>
    have h2 : c.sortsOf [ua, ub] = some [s, s] := by rw [hvs, ← hsort]; rfl
    obtain ⟨hua, hub⟩ := sortsOf_two_cpv h2
    obtain ⟨lua, lub⟩ := litsVL_two_kcv lv
    have hxa : SubCtx_cdp c ua Ks k s ia := ⟨ha, hua, hKs, hk, lua⟩
    have hxb : SubCtx_cdp c ub Ks k s ib := ⟨hb, hub, hKs, hk, lub⟩
    obtain ⟨g, s₀, hl, hv⟩ := collVal_lib_cdp hcy
    have hcases := libCollOf_cases_cdp hl
    simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hcases
    rcases hcases with ⟨-, -, -, ⟨⟩⟩ | ⟨-, -, -, ⟨⟩⟩ | ⟨rfl, rfl, rfl, -⟩ | ⟨-, -, -, ⟨⟩⟩ |
      ⟨-, -, -, ⟨⟩⟩ | ⟨rfl, rfl, rfl, -⟩ | ⟨-, -, -, ⟨⟩⟩ | ⟨-, -, -, ⟨⟩⟩ | ⟨rfl, rfl, rfl, -⟩
    · -- a map: `_Map_`, defined where no key of one is a key of the other
      have hkd := kindOf_map_cdp hk
      obtain ⟨a, va, rfl, -, -, rfl, hva, hka, hea⟩ : ∃ es vs, ua = .map s es ∧ Ks.kind = .map ∧
          Kind.map = .map ∧ ia = es.map (fun e => [e.1, e.2]) ∧ Ks.val = some vs ∧
          keysSorted es = true ∧ ∀ e ∈ es, (c.sortOf e.1 = some Ks.key ∧ c.sortOf e.2 = some vs) ∧
            litsV e.1 = true ∧ litsV e.2 = true := by
        rcases hxa.shape with h | ⟨_, -, h, -⟩ | ⟨_, -, h, -⟩
        · exact h
        · rw [hkd] at h; cases h
        · rw [hkd] at h; cases h
      obtain ⟨b, vb, rfl, -, -, rfl, hvb, hkb, heb⟩ : ∃ es vs, ub = .map s es ∧ Ks.kind = .map ∧
          Kind.map = .map ∧ ib = es.map (fun e => [e.1, e.2]) ∧ Ks.val = some vs ∧
          keysSorted es = true ∧ ∀ e ∈ es, (c.sortOf e.1 = some Ks.key ∧ c.sortOf e.2 = some vs) ∧
            litsV e.1 = true ∧ litsV e.2 = true := by
        rcases hxb.shape with h | ⟨_, -, h, -⟩ | ⟨_, -, h, -⟩
        · exact h
        · rw [hkd] at h; cases h
        · rw [hkd] at h; cases h
      rw [hva] at hvb; cases hvb
      have hkeys : ((a.map fun e => [e.1, e.2]) ++ b.map fun e => [e.1, e.2]).map keyIt_khc =
          a.map Prod.fst ++ b.map Prod.fst := by
        rw [List.map_append, keys_pairs_kcv, keys_pairs_kcv]
      rw [hkeys]
      refine ⟨fun hn => ?_, fun hne hn => ?_⟩
      · have hn : (a.map Prod.fst ++ b.map Prod.fst).Nodup := hn.resolve_left (by decide)
        have hcross : ∀ e ∈ a, ∀ e' ∈ b, GroundTerm.cmp e.1 e'.1 ≠ .eq := fun e he e' he' hc =>
          (List.nodup_append.mp hn).2.2 _ (List.mem_map_of_mem he) _ (List.mem_map_of_mem he')
            (cmp_eq_iff.mp hc)
        obtain ⟨m, hm, hmm⟩ := union_exists (sorted_apart hka) hcross
        have hkm := union_sorted hkb hm
        have hxm : SubCtx_cdp c (.map s m) Ks .map s (m.map fun e => [e.1, e.2]) :=
          subCtx_map_cdp hKs hkd hva hkm fun e he => by
            rcases (hmm e).mp he with h | h
            · exact hea e h
            · exact heb e h
        refine ⟨_, _, hv [.map s a, .map s b] (.map Srt.map m) .map (m.map fun e => [e.1, e.2])
          (by rw [Exec.hook_concat_eq]; simp only [hm]; rfl) rfl hxm.sorted, hxm, ?_, fun h => nomatch h⟩
        rw [← List.map_append]
        exact (CExec.union_perm hka hkb hkm hm).map _
      · cases hcv : c.collVal f [.map s a, .map s b] with
        | none => rfl
        | some u =>
          exfalso
          obtain ⟨K', hK', hbd⟩ := collVal_builds_cpv hcy hcv
          cases kindOf_inj_cpv hK' (show kindOf CollKind.map = some Kind.map from rfl)
          obtain ⟨sa, sb, a', b', s', m, hvs', hm, -⟩ := hbd
          simp only [List.cons.injEq, GroundTerm.map.injEq, and_true] at hvs'
          obtain ⟨⟨-, rfl⟩, -, rfl⟩ := hvs'
          obtain ⟨-, -, -, hcr⟩ := union_spec hm
          refine hn (List.nodup_append.mpr ⟨keys_nodup_kcv hka, keys_nodup_kcv hkb, ?_⟩)
          intro x hx y hy hxy
          obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
          obtain ⟨e', he', rfl⟩ := List.mem_map.mp hy
          exact hcr e he e' he' (cmp_eq_iff.mpr hxy)
    · -- a set: `_Set_`, defined where the two share no element
      have hkd := kindOf_set_cdp hk
      obtain ⟨a, rfl, -, -, rfl, hka, hea⟩ : ∃ es, ua = .set s es ∧ Ks.kind = .set ∧ Kind.set = .set ∧
          ia = es.map (fun e => [e]) ∧ elemsSorted es = true ∧
          ∀ e ∈ es, c.sortOf e = some Ks.key ∧ litsV e = true := by
        rcases hxa.shape with ⟨_, _, -, h, -⟩ | h | ⟨_, -, h, -⟩
        · rw [hkd] at h; cases h
        · exact h
        · rw [hkd] at h; cases h
      obtain ⟨b, rfl, -, -, rfl, hkb, heb⟩ : ∃ es, ub = .set s es ∧ Ks.kind = .set ∧ Kind.set = .set ∧
          ib = es.map (fun e => [e]) ∧ elemsSorted es = true ∧
          ∀ e ∈ es, c.sortOf e = some Ks.key ∧ litsV e = true := by
        rcases hxb.shape with ⟨_, _, -, h, -⟩ | h | ⟨_, -, h, -⟩
        · rw [hkd] at h; cases h
        · exact h
        · rw [hkd] at h; cases h
      have hkeys : ((a.map fun e => [e]) ++ b.map fun e => [e]).map keyIt_khc = a ++ b := by
        rw [List.map_append, keys_ones_kcv, keys_ones_kcv]
      rw [hkeys]
      refine ⟨fun hn => ?_, fun hne hn => ?_⟩
      · have hn : (a ++ b).Nodup := hn.resolve_left (by decide)
        have hdis : a.all (fun x => !memS x b) = true := by
          rw [List.all_eq_true]
          intro x hx
          rw [Bool.not_eq_true', Bool.eq_false_iff, ne_eq, KCore.Set.memS_iff]
          intro hx'
          exact (List.nodup_append.mp hn).2.2 x hx x hx' rfl
        have hcs' : concatS a b = some (unionS a b) := by simp only [concatS, hdis, ↓reduceIte]
        have hkm : elemsSorted (unionS a b) = true := KCore.Set.union_canon hkb
        have hxm : SubCtx_cdp c (.set s (unionS a b)) Ks .set s ((unionS a b).map fun e => [e]) :=
          subCtx_set_cdp hKs hkd hkm fun e he => by
            rcases (KCore.Set.mem_union e a b).mp he with h | h
            · exact hea e h
            · exact heb e h
        refine ⟨_, _, hv [.set s a, .set s b] (.set Srt.set (unionS a b)) .set
          ((unionS a b).map fun e => [e])
          (by rw [Exec.hook_setConcat_eq]; simp only [hcs']; rfl) rfl hxm.sorted, hxm, ?_,
          fun h => nomatch h⟩
        rw [← List.map_append]
        exact (CExec.concatS_perm hka hkb hkm hcs').map _
      · cases hcv : c.collVal f [.set s a, .set s b] with
        | none => rfl
        | some u =>
          exfalso
          obtain ⟨K', hK', hbd⟩ := collVal_builds_cpv hcy hcv
          cases kindOf_inj_cpv hK' (show kindOf CollKind.set = some Kind.set from rfl)
          obtain ⟨sa, sb, a', b', s', m, hvs', hm, -⟩ := hbd
          simp only [List.cons.injEq, GroundTerm.set.injEq, and_true] at hvs'
          obtain ⟨⟨-, rfl⟩, -, rfl⟩ := hvs'
          unfold concatS at hm
          split at hm
          · rename_i hd
            refine hn (List.nodup_append.mpr ⟨CExec.nodup_of_elemsSorted hka,
              CExec.nodup_of_elemsSorted hkb, ?_⟩)
            intro x hx y hy hxy
            subst hxy
            have := List.all_eq_true.mp hd x hx
            rw [Bool.not_eq_true', Bool.eq_false_iff, ne_eq, KCore.Set.memS_iff] at this
            exact this hy
          · cases hm
    · -- a list: always defined, the items in order
      have hkd := kindOf_list_cdp hk
      obtain ⟨a, rfl, -, -, rfl, hea⟩ : ∃ es, ua = .list s es ∧ Ks.kind = .list ∧ Kind.list = .list ∧
          ia = es.map (fun e => [e]) ∧ ∀ e ∈ es, c.sortOf e = some Ks.key ∧ litsV e = true := by
        rcases hxa.shape with ⟨_, _, -, h, -⟩ | ⟨_, -, h, -⟩ | h
        · rw [hkd] at h; cases h
        · rw [hkd] at h; cases h
        · exact h
      obtain ⟨b, rfl, -, -, rfl, heb⟩ : ∃ es, ub = .list s es ∧ Ks.kind = .list ∧ Kind.list = .list ∧
          ib = es.map (fun e => [e]) ∧ ∀ e ∈ es, c.sortOf e = some Ks.key ∧ litsV e = true := by
        rcases hxb.shape with ⟨_, _, -, h, -⟩ | ⟨_, -, h, -⟩ | h
        · rw [hkd] at h; cases h
        · rw [hkd] at h; cases h
        · exact h
      refine ⟨fun _ => ?_, fun h => absurd rfl h⟩
      have hxm : SubCtx_cdp c (.list s (a ++ b)) Ks .list s ((a ++ b).map fun e => [e]) :=
        subCtx_list_cdp hKs hkd fun e he => by
          rcases List.mem_append.mp he with h | h
          · exact hea e h
          · exact heb e h
      have hY : (a ++ b).map (fun e => [e]) = (a.map fun e => [e]) ++ b.map fun e => [e] :=
        List.map_append
      refine ⟨_, _, hv [.list s a, .list s b] (.list Srt.list (a ++ b)) .list
        ((a ++ b).map fun e => [e]) (by rw [Exec.hook_listConcat_eq]) rfl hxm.sorted, hxm, ?_,
        fun _ => hY⟩
      rw [hY]

/-- **`colOf` against `collVal`.** A collection symbol `f` of `c` at arguments `vs` of its
argument sorts with kore.k literals, building from the items `its'` (`RoleItems_kcv`), and parts
`ps` holding the items `its`, which are `its'` up to order (in order for a list): `colOf(k, s,
ps)` is the encoding of what `f` builds, `bot` where it builds nothing. -/
theorem colOf_collVal {c : Semantics} (hcs : collsOK c = true) {f : Sym} {k : Kind} {s : Srt}
    {r : CRole} (hcy : collSymOf c f = some (k, s, r)) {Ks : CollSig} (hKs : c.collOf s = some Ks)
    (hk : kindOf Ks.kind = some k) {vs : List GroundTerm}
    (hvs : c.sortsOf vs = some (roleArgs_cdp Ks r)) (lv : litsVL vs = true)
    {its' : List (List GroundTerm)} (hr : RoleItems_kcv Ks.kind s r vs its') {ps : List T}
    {its : List (List GroundTerm)} (hps : PartsIts_khc c Ks.kind ps its) (hp : its.Perm its')
    (hl : k = .list → its = its') :
    colOfF k s ps = some (encR (c.collVal f vs)) := by
  obtain ⟨hdef, hund⟩ := collVal_items_kcv hcs hcy hKs hk hvs lv hr
  by_cases hkl : k = .list
  · subst hkl
    obtain ⟨u, Y, hu, hx, -, hY⟩ := hdef (.inl rfl)
    have hKl := kindOf_list_cdp hk
    rw [hu, encR, hx.enc_eq, hY rfl, ← hl rfl]
    rw [hKl] at hps
    exact colOfF_list_items_khc s hps
  · have hiff : (its.map keyIt_khc).Nodup ↔ (its'.map keyIt_khc).Nodup := (hp.map _).nodup_iff
    by_cases hn : (its'.map keyIt_khc).Nodup
    · obtain ⟨u, Y, hu, hx, hY, -⟩ := hdef (.inr hn)
      rw [hu, encR]
      exact colOfF_coll_khc hk hkl hps hx.sorted hx.lits hx.cont (hY.trans hp.symm)
    · rw [hund hkl hn, encR]
      exact colOfF_overlap_khc hk hkl s hps fun h => hn (hiff.mp h)

end Build

/-! ## Instances -/

section Instances
open _root_.KK

/-- The Int 1 and 2 as elements of the library's `Set` (of `KItem`). -/
abbrev x1_kcv : GroundTerm := .inj 3 Srt.kitem (.dv 3 (.int 1))
abbrev x2_kcv : GroundTerm := .inj 3 Srt.kitem (.dv 3 (.int 2))

theorem collsOK_c₀_kcv : collsOK c₀ = true := RefKk.core_collsOK

theorem collSym_setConcat_kcv : collSymOf c₀ setConcat = some (.set, Srt.set, .concat) := by
  decide +kernel

theorem collOf_set_kcv : c₀.collOf Srt.set = some (builtinColl .set) := by decide +kernel

theorem sort_x1_kcv : c₀.sortOf x1_kcv = some Srt.kitem := by decide +kernel
theorem sort_x2_kcv : c₀.sortOf x2_kcv = some Srt.kitem := by decide +kernel

theorem sorts_sets_kcv :
    c₀.sortsOf [.set Srt.set [x1_kcv], .set Srt.set [x2_kcv]] = some [Srt.set, Srt.set] := by
  decide +kernel

theorem sorts_sets_dup_kcv :
    c₀.sortsOf [.set Srt.set [x1_kcv], .set Srt.set [x1_kcv]] = some [Srt.set, Srt.set] := by
  decide +kernel

/-- `_Set_` of the sets `{1}` and `{2}` has a value, the set `{1, 2}`. -/
theorem collVal_items_ex_kcv :
    ∃ u Y, c₀.collVal setConcat [.set Srt.set [x1_kcv], .set Srt.set [x2_kcv]] = some u ∧
      SubCtx_cdp c₀ u (builtinColl .set) .set Srt.set Y ∧ Y.Perm [[x1_kcv], [x2_kcv]] :=
  have h := (collVal_items_kcv collsOK_c₀_kcv collSym_setConcat_kcv collOf_set_kcv rfl
    sorts_sets_kcv rfl (.concat rfl rfl)).1 (.inr (by decide +kernel))
  let ⟨u, Y, hu, hx, hY, _⟩ := h
  ⟨u, Y, hu, hx, hY⟩

/-- The parts `{1}` and `2` of a set's construction hold the items `1` and `2`. -/
theorem partsIts_enc_ex_kcv :
    PartsIts_khc c₀ (builtinColl .set).kind [enc (.set Srt.set [x1_kcv]), encIt_cdp [x2_kcv]]
      [[x1_kcv], [x2_kcv]] :=
  PartsIts_khc.enc_kcv (k := .set) (s := Srt.set) (g := [[x1_kcv]]) ⟨rfl, by decide +kernel, collOf_set_kcv, rfl, rfl⟩
    (.elem ⟨x2_kcv, Srt.kitem, rfl, sort_x2_kcv, rfl⟩ .nil)

/-- On the parts `{1}` and `2`, `colOf` is the encoding of `_Set_` of `{1}` and `{2}`. -/
theorem colOf_collVal_ex_kcv :
    colOfF .set Srt.set [enc (.set Srt.set [x1_kcv]), encIt_cdp [x2_kcv]] =
      some (encR (c₀.collVal setConcat [.set Srt.set [x1_kcv], .set Srt.set [x2_kcv]])) :=
  colOf_collVal collsOK_c₀_kcv collSym_setConcat_kcv collOf_set_kcv rfl sorts_sets_kcv rfl
    (.concat rfl rfl) partsIts_enc_ex_kcv (.refl _) fun h => nomatch h

/-- The parts `1` and `1` of a set's construction, appended from two one-part lists. -/
theorem partsIts_dup_ex_kcv :
    PartsIts_khc c₀ (builtinColl .set).kind [encIt_cdp [x1_kcv], encIt_cdp [x1_kcv]]
      [[x1_kcv], [x1_kcv]] :=
  PartsIts_khc.append_kcv (ps := [encIt_cdp [x1_kcv]]) (its := [[x1_kcv]])
    (.elem ⟨x1_kcv, Srt.kitem, rfl, sort_x1_kcv, rfl⟩ .nil)
    (.elem ⟨x1_kcv, Srt.kitem, rfl, sort_x1_kcv, rfl⟩ .nil)

/-- On the parts `1` and `1`, `colOf` is `bot`, the encoding of `_Set_` of `{1}` and `{1}`, which
has no value. -/
theorem colOf_collVal_dup_ex_kcv :
    colOfF .set Srt.set [encIt_cdp [x1_kcv], encIt_cdp [x1_kcv]] =
      some (encR (c₀.collVal setConcat [.set Srt.set [x1_kcv], .set Srt.set [x1_kcv]])) ∧
    c₀.collVal setConcat [.set Srt.set [x1_kcv], .set Srt.set [x1_kcv]] = none :=
  ⟨colOf_collVal collsOK_c₀_kcv collSym_setConcat_kcv collOf_set_kcv rfl sorts_sets_dup_kcv rfl
    (.concat rfl rfl) partsIts_dup_ex_kcv (.refl _) (fun h => nomatch h),
   (collVal_items_kcv collsOK_c₀_kcv collSym_setConcat_kcv collOf_set_kcv rfl sorts_sets_dup_kcv rfl
    (.concat rfl rfl)).2 (by decide) (by decide +kernel)⟩

end Instances

/-! ## Checks -/

#check @SubCtx_cdp.itemOK_kcv
#check @PartsIts_khc.enc_kcv
#check @PartsIts_khc.append_kcv
#check @collVal_items_kcv
#check @colOf_collVal
#check @collVal_items_ex_kcv
#check @colOf_collVal_ex_kcv
#check @colOf_collVal_dup_ex_kcv

open Lean in
#eval show CoreM Unit from do
  for n in [``SubCtx_cdp.itemOK_kcv, ``PartsIts_khc.enc_kcv, ``PartsIts_khc.append_kcv,
      ``keys_pairs_kcv, ``keys_ones_kcv, ``keys_nodup_kcv, ``sortsOf_one_kcv, ``sortsOf_two_kcv,
      ``collVal_items_kcv, ``colOf_collVal, ``collVal_items_ex_kcv, ``partsIts_enc_ex_kcv,
      ``colOf_collVal_ex_kcv, ``partsIts_dup_ex_kcv, ``colOf_collVal_dup_ex_kcv] do
    let axs ← collectAxioms n
    unless axs.all ([``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "{n}: axioms {axs}"

end KCore.KK
