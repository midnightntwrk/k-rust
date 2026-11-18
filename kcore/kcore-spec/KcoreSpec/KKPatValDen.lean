import KcoreSpec.KKDenPatVal
import KcoreSpec.KKMatchTotal

/-!
# `PatVal` as a substitution of `kore.k`'s `match`, collection patterns included

`patVal_denF`: where a pattern `p`, sorted in a left side's context, denotes a value `v` under a
well-sorted `σ` (`PatVal`), under `σ` encoded (`bindOfSubst σ`) the encoding of `p` is the
encoding of `v` (`DenF`). It is the converse of `den_patVal`. `matchF_col_complete` is
`matchF_complete` without `noCb`, from it and `matchF_complete_of_den`: `match` has a value, and
the value holds a substitution that agrees with `σ` and binds every variable of `p`. The
conclusion is membership: a `Map` or `Set` pattern with an element whose key is unbound has
several matches.

A collection pattern is read from `PatVal` itself. The value of an application of a collection
symbol is what the symbol builds from its arguments' values (`CExec.Builds`): no item, the one
item its arguments are, or the items of two collections, a list's in order and a map's or a set's
each once (`builds_concat_cpv`). `collParts_cpv` so gives each part of the pattern, in the
pattern's order, the items of the value it takes (`Takes_cpv`): an element part one item, any
other part a collection value of the pattern's sort, which is the value the part denotes. A part
that is no element is any pattern: a variable, an alias, an application of a function or of a
collection symbol of another collection. `denCol_of_chunks_cpv` puts the parts in `kore.k`'s order
(`DenColF`): a list's parts take stretches in order; a map's or a set's element parts take their
items wherever they stand among the value's elements, and the other part the elements left, which
are the elements of the encoding of the part's own value since both are strictly increasing by
`ckeyF` (`SubCtx_cdp.strict`).

What is read beyond `den_patVal`'s hypotheses: `colPatOK` of the encoded pattern, for one fact,
that a `Map` or `Set` pattern has at most one part that is no element (`DenColF` has no case for
two: `split`, which divides the elements between two such parts, is a `List`'s). The value's
literals have `kore.k` forms (`litsV v`), as in `matchF_col_sound`; the sub-values' follow from
it.
-/

set_option autoImplicit false

namespace KCore.KK

open KCore.Exec (MatchCtxO termSize termSizeList)
open KCore.CExec (content build CanonI pairOf oneOf)
open KCore.Faithful (collsOK collSymsOK elemArgs valSort collImpl)

/-! ## What a collection symbol builds -/

/-- The role of a collection symbol, as `CExec.Builds` names it. -/
def roleOf_cpv : CRole → CExec.Role
  | .unit => .unit
  | .elem => .elem
  | .concat => .concat

theorem lib_hookRole_cpv {g : Sym} {k : Kind} {s₀ : Srt} {r : CRole}
    (h : libCollOf g = some (k, s₀, r)) :
    ∃ K, kindOf K = some k ∧ CExec.hookRole g = some (K, roleOf_cpv r) := by
  have hmem := libCollOf_cases_cdp h
  simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hmem
  rcases hmem with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
  · exact ⟨.map, rfl, by decide⟩
  · exact ⟨.map, rfl, by decide⟩
  · exact ⟨.map, rfl, by decide⟩
  · exact ⟨.set, rfl, by decide⟩
  · exact ⟨.set, rfl, by decide⟩
  · exact ⟨.set, rfl, by decide⟩
  · exact ⟨.list, rfl, by decide⟩
  · exact ⟨.list, rfl, by decide⟩
  · exact ⟨.list, rfl, by decide⟩

theorem kindOf_inj_cpv {K K' : CollKind} {k : Kind} (h : kindOf K = some k)
    (h' : kindOf K' = some k) : K = K' := by
  cases K <;> cases K' <;> simp [kindOf] at h h' <;> first | rfl | (rw [← h] at h'; cases h')

/-- The value of a collection symbol of `c` at its arguments' values is what its role builds. -/
theorem collVal_builds_cpv {c : Semantics} {f : Sym} {k : Kind} {s : Srt} {r : CRole}
    (hcy : collSymOf c f = some (k, s, r)) {ws : List GroundTerm} {u : GroundTerm}
    (hv : c.collVal f ws = some u) :
    ∃ K, kindOf K = some k ∧ CExec.Builds K (roleOf_cpv r) ws u := by
  obtain ⟨g, s₀, hl, hcase⟩ := collSym_lib_cdp hcy
  obtain ⟨K, hK, hr⟩ := lib_hookRole_cpv hl
  obtain ⟨-, -, hsk, hrc⟩ := lib_hook_facts_cdp hl
  refine ⟨K, hK, ?_⟩
  rcases hcase with ⟨hh, rfl, rfl⟩ | ⟨hh, kp, hkp, hg, rfl⟩
  · unfold Semantics.collVal at hv
    simp only [hh, ↓reduceIte] at hv
    exact CExec.builds_of_hook hr (Option.join_eq_some_iff.mp hv)
  · unfold Semantics.collVal at hv
    simp only [hh, Bool.false_eq_true, ↓reduceIte] at hv
    unfold Semantics.paramVal at hv
    rw [hkp] at hv
    dsimp only at hv
    rw [hg] at hv
    dsimp only at hv
    have hw := (Option.filter_eq_some_iff.mp hv).1
    obtain ⟨u', hu, rfl⟩ := Option.map_eq_some_iff.mp hw
    rw [Semantics.libArgs_coll c hrc, Semantics.hookRes_of_notKey hsk] at hu
    have hb := CExec.builds_of_hook hr (Option.join_eq_some_iff.mp hu)
    have hu' : u'.asSort c.lib kp.sig.result = u'.withSort kp.sig.result := by
      cases u' with
      | dv b lit => exact (CExec.builds_not_dv hb).elim
      | _ => rfl
    rw [hu']
    exact CExec.builds_withSort _ hb

/-- A pattern headed by a symbol that is no constructor denotes the symbol's collection value at
its arguments' values. -/
theorem patVal_coll_inv_cpv {c : Semantics} (hov : c.ovls = []) {σ : Subst} {f : Sym}
    {ps : List Term} {u : GroundTerm} (hct : c.isCtor f = false) (h : PatVal c σ (.app f ps) u) :
    ∃ vs, PatVals c σ ps vs ∧ c.collVal f vs = some u := by
  cases h with
  | ctor hk _ => rw [hct] at hk; cases hk
  | hook hp hs hv =>
    refine ⟨_, hs, ?_⟩
    unfold Semantics.collVal
    simp only [isHook_patHook_cdp hp, ↓reduceIte, hv]; rfl
  | coll _ _ hs hv => exact ⟨_, hs, hv⟩
  | ovl _ ho _ _ => rw [c.isOvl_of_none hov] at ho; cases ho

theorem patVals_two_cpv {c : Semantics} {σ : Subst} {a b : Term} : ∀ {vs : List GroundTerm},
    PatVals c σ [a, b] vs → ∃ ua ub, vs = [ua, ub] ∧ PatVal c σ a ua ∧ PatVal c σ b ub
  | _, .cons (v := ua) h (.cons (v := ub) h' .nil) => ⟨ua, ub, rfl, h, h'⟩

theorem sortsOf_two_cpv {c : Semantics} {ua ub : GroundTerm} {s t : Srt}
    (h : c.sortsOf [ua, ub] = some [s, t]) : c.sortOf ua = some s ∧ c.sortOf ub = some t := by
  obtain ⟨s₁, ss₁, h1, h2, he⟩ := sortsOf_cons.mp h
  obtain ⟨s₂, ss₂, h3, h4, he'⟩ := sortsOf_cons.mp h2
  simp only [List.cons.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  simp only [List.cons.injEq] at he'
  obtain ⟨rfl, -⟩ := he'
  exact ⟨h1, h3⟩

theorem sorted_map_cpv {c : Semantics} {s s' : Srt} {es : List (GroundTerm × GroundTerm)}
    (h : c.sortOf (.map s' es) = some s) : s = s' ∧ keysSorted es = true := by
  obtain ⟨hs, es', hes', hmap⟩ := CExec.content_canon (c := c) (w := .map s' es) rfl h
  have : es = es' := CExec.map_inj_of (fun x y (h : [x.1, x.2] = [y.1, y.2]) => by
    simp only [List.cons.injEq, and_true] at h; exact Prod.ext h.1 h.2) hmap
  subst this
  exact ⟨hs, hes'⟩

theorem sorted_set_cpv {c : Semantics} {s s' : Srt} {es : List GroundTerm}
    (h : c.sortOf (.set s' es) = some s) : s = s' ∧ elemsSorted es = true := by
  obtain ⟨hs, es', hes', hmap⟩ := CExec.content_canon (c := c) (w := .set s' es) rfl h
  have : es = es' := CExec.map_inj_of (fun x y (h : [x] = [y]) => by
    simpa using h) hmap
  subst this
  exact ⟨hs, hes'⟩

theorem sorted_list_cpv {c : Semantics} {s s' : Srt} {es : List GroundTerm}
    (h : c.sortOf (.list s' es) = some s) : s = s' :=
  (CExec.content_canon (c := c) (w := .list s' es) rfl h).1

/-- **The items of a concatenation.** What a concatenation symbol builds from two collection
values of the sort `s`, where it is a value of `s`, holds the items of both: a list's in order,
a map's and a set's each once. -/
theorem builds_concat_cpv {c : Semantics} {K : CollKind} {ua ub u : GroundTerm} {s : Srt}
    (hb : CExec.Builds K .concat [ua, ub] u) (ha : c.sortOf ua = some s)
    (hb' : c.sortOf ub = some s) (hu : c.sortOf u = some s) :
    ∃ ia ib iu, content ua = some (K, s, ia) ∧ content ub = some (K, s, ib) ∧
      content u = some (K, s, iu) ∧ iu.Perm (ia ++ ib) ∧ (K = .list → iu = ia ++ ib) := by
  cases K with
  | map =>
    obtain ⟨sa, sb, a, b, s', m, hvs, hm, rfl⟩ := hb
    simp only [List.cons.injEq, and_true] at hvs
    obtain ⟨rfl, rfl⟩ := hvs
    obtain ⟨rfl, hka⟩ := sorted_map_cpv ha
    obtain ⟨rfl, hkb⟩ := sorted_map_cpv hb'
    obtain ⟨rfl, hkm⟩ := sorted_map_cpv hu
    refine ⟨_, _, _, rfl, rfl, rfl, ?_, fun h => nomatch h⟩
    rw [← List.map_append]
    exact (CExec.union_perm hka hkb hkm hm).map _
  | set =>
    obtain ⟨sa, sb, a, b, s', m, hvs, hm, rfl⟩ := hb
    simp only [List.cons.injEq, and_true] at hvs
    obtain ⟨rfl, rfl⟩ := hvs
    obtain ⟨rfl, hka⟩ := sorted_set_cpv ha
    obtain ⟨rfl, hkb⟩ := sorted_set_cpv hb'
    obtain ⟨rfl, hkm⟩ := sorted_set_cpv hu
    refine ⟨_, _, _, rfl, rfl, rfl, ?_, fun h => nomatch h⟩
    rw [← List.map_append]
    exact (CExec.concatS_perm hka hkb hkm hm).map _
  | list =>
    obtain ⟨sa, sb, a, b, s', hvs, rfl⟩ := hb
    simp only [List.cons.injEq, and_true] at hvs
    obtain ⟨rfl, rfl⟩ := hvs
    have h1 := sorted_list_cpv ha
    have h2 := sorted_list_cpv hb'
    have h3 := sorted_list_cpv hu
    subst h1; subst h2; subst h3
    refine ⟨_, _, _, rfl, rfl, rfl, ?_, fun _ => ?_⟩
    · rw [← List.map_append]
    · rw [← List.map_append]
  | rangeMap => exact hb.elim

/-- A collection value whose items' literals `kore.k` has. -/
theorem litsV_of_items_cpv {w : GroundTerm} {K : CollKind} {s : Srt}
    {its : List (List GroundTerm)} (hc : content w = some (K, s, its))
    (h : ∀ it ∈ its, litsVL it = true) : litsV w = true := by
  cases w with
  | ctor f vs => simp only [content] at hc; cases hc
  | inj a b u => simp only [content] at hc; cases hc
  | dv s' l => simp only [content] at hc; cases hc
  | map s' es =>
    simp only [content, Option.some.injEq, Prod.mk.injEq] at hc
    obtain ⟨-, -, rfl⟩ := hc
    simp only [litsV, litsVE_iff]
    intro e he
    have := h [e.1, e.2] (List.mem_map.mpr ⟨e, he, rfl⟩)
    simpa [litsVL] using this
  | set s' es =>
    simp only [content, Option.some.injEq, Prod.mk.injEq] at hc
    obtain ⟨-, -, rfl⟩ := hc
    simp only [litsV, litsVL_iff]
    intro e he
    have := h [e] (List.mem_map.mpr ⟨e, he, rfl⟩)
    simpa [litsVL] using this
  | list s' es =>
    simp only [content, Option.some.injEq, Prod.mk.injEq] at hc
    obtain ⟨-, -, rfl⟩ := hc
    simp only [litsV, litsVL_iff]
    intro e he
    have := h [e] (List.mem_map.mpr ⟨e, he, rfl⟩)
    simpa [litsVL] using this

/-- A collection value of a kind of `kore.k`, sorted at a collection sort of that kind. -/
theorem subCtx_content_cpv {c : Semantics} {v : GroundTerm} {K : CollKind} {s₁ s : Srt}
    {its : List (List GroundTerm)} {Ks : CollSig} {k : Kind}
    (hc : content v = some (K, s₁, its)) (hKk : kindOf K = some k) (hv : c.sortOf v = some s)
    (lv : litsV v = true) (hK : c.collOf s = some Ks) (hkd : kindOf Ks.kind = some k) :
    SubCtx_cdp c v Ks k s its := by
  obtain ⟨rfl, -⟩ := CExec.content_canon (c := c) hc hv
  have := kindOf_inj_cpv hKk hkd
  subst this
  exact ⟨hc, hv, hK, hkd, lv⟩

/-! ## The parts of a collection pattern, in `kore.k`'s order -/

/-- What a part takes of the items of a collection value: an element part one item, which it is;
any other part the items of a collection value of the pattern's sort, which it is. -/
def Takes_cpv (S : List (Int × Int)) (B : Bind) (c : Semantics) (Ks : CollSig) (k : Kind) (s : Srt)
    (p : T) (g : List (List GroundTerm)) : Prop :=
  if isElemT p = true then ∃ it, g = [it] ∧ DenF S B p (encIt_cdp it)
  else ∃ w, SubCtx_cdp c w Ks k s g ∧ DenF S B p (enc w)

theorem ordK_ne_list_cpv {k : Kind} (hk : k ≠ .list) (L : List T) : ordK_cdp k L = sortK L := by
  cases k with
  | list => exact absurd rfl hk
  | _ => rfl

/-- The parts of a `List` pattern take the items in order. -/
theorem denCol_list_cpv {S : List (Int × Int)} {B : Bind} {c : Semantics} {Ks : CollSig}
    {s : Srt} : ∀ (ch : List (T × List (List GroundTerm))),
    (∀ x ∈ ch, Takes_cpv S B c Ks .list s x.1 x.2) →
    DenColF S B .list (s : Int) (ch.map (·.1)) ((ch.flatMap (·.2)).map encIt_cdp)
  | [], _ => .done
  | [(p, g)], h => by
    have hp := h (p, g) (by simp)
    unfold Takes_cpv at hp
    split at hp
    · rename_i he
      obtain ⟨it, rfl, hd⟩ := hp
      exact .head he hd .done
    · rename_i he
      obtain ⟨w, hw, hd⟩ := hp
      rw [hw.enc_eq] at hd
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.map_cons, List.map_nil]
      exact .frame (by simpa using he) hd
  | (p, g) :: y :: ch, h => by
    have ih := denCol_list_cpv (y :: ch) (fun x hx => h x (List.mem_cons_of_mem _ hx))
    have hp := h (p, g) (by simp)
    unfold Takes_cpv at hp
    rw [List.map_cons, List.flatMap_cons, List.map_append]
    split at hp
    · rename_i he
      obtain ⟨it, rfl, hd⟩ := hp
      exact .head he hd ih
    · rename_i he
      obtain ⟨w, hw, hd⟩ := hp
      rw [hw.enc_eq] at hd
      exact .split (by simpa using he) hd ih

/-- The element parts of a `Map` or `Set` pattern take elements wherever they stand; what follows
them takes the elements left, in their order. -/
theorem denCol_pick_cpv {S : List (Int × Int)} {B : Bind} {k : Kind} {s : Int} (hk : k ≠ .list)
    {tail R : List T} : ∀ (els picked L : List T), DensF S B els picked →
    (∀ p ∈ els, isElemT p = true) → L.Perm (picked ++ R) →
    (∀ L', L'.Perm R → L'.Sublist L → DenColF S B k s tail L') →
    DenColF S B k s (els ++ tail) L
  | [], picked, L, hd, _, hperm, ht => by
    cases hd
    exact ht L hperm (List.Sublist.refl _)
  | p :: els, picked, L, hd, he, hperm, ht => by
    cases hd with
    | cons h hs =>
      rename_i e pk
      have hmem : e ∈ L := hperm.symm.subset (by simp)
      obtain ⟨l, r, rfl⟩ := List.append_of_mem hmem
      have hperm' : (l ++ r).Perm (pk ++ R) := by
        have : (e :: (l ++ r)).Perm (e :: (pk ++ R)) := List.perm_middle.symm.trans hperm
        exact this.cons_inv
      exact .choose (he p (by simp)) hk h
        (denCol_pick_cpv hk els pk (l ++ r) hs (fun q hq => he q (List.mem_cons_of_mem _ hq)) hperm'
          fun L' h1 h2 => ht L' h1
            (h2.trans (List.Sublist.append (List.Sublist.refl l) (List.sublist_cons_self e r))))

/-- The element parts with the items they take, and the items the other parts take. -/
theorem chunks_pick_cpv {S : List (Int × Int)} {B : Bind} {c : Semantics} {Ks : CollSig}
    {k : Kind} {s : Srt} : ∀ (ch : List (T × List (List GroundTerm))),
    (∀ x ∈ ch, Takes_cpv S B c Ks k s x.1 x.2) →
    ∃ picked, DensF S B ((ch.map (·.1)).filter isElemT) picked ∧
      ((ch.flatMap (·.2)).map encIt_cdp).Perm
        (picked ++ ((ch.filter fun x => !isElemT x.1).flatMap (·.2)).map encIt_cdp)
  | [], _ => ⟨[], .nil, by simp⟩
  | (p, g) :: ch, h => by
    obtain ⟨picked, hd, hperm⟩ := chunks_pick_cpv ch fun x hx => h x (List.mem_cons_of_mem _ hx)
    have hp := h (p, g) (by simp)
    unfold Takes_cpv at hp
    cases hel : isElemT p with
    | true =>
      simp only [hel, ↓reduceIte] at hp
      obtain ⟨it, rfl, hde⟩ := hp
      refine ⟨encIt_cdp it :: picked, ?_, ?_⟩
      · rw [List.map_cons, List.filter_cons_of_pos (by simpa using hel)]
        exact .cons hde hd
      · rw [List.filter_cons_of_neg (by simp [hel])]
        simpa using hperm.cons (encIt_cdp it)
    | false =>
      simp only [hel, Bool.false_eq_true, ↓reduceIte] at hp
      refine ⟨picked, ?_, ?_⟩
      · rw [List.map_cons, List.filter_cons_of_neg (by simp [hel])]
        exact hd
      · rw [List.filter_cons_of_pos (by simp [hel]), List.flatMap_cons, List.flatMap_cons,
          List.map_append, List.map_append]
        refine (hperm.append_left (g.map encIt_cdp)).trans ?_
        rw [← List.append_assoc, ← List.append_assoc]
        exact List.Perm.append_right _ List.perm_append_comm

/-- The parts of a `Map` or `Set` pattern with at most one part that is no element, the elements
first, take the elements of the value's encoding. -/
theorem denCol_coll_cpv {c : Semantics} {v : GroundTerm} {Ks : CollSig} {k : Kind} {s : Srt}
    {its : List (List GroundTerm)} (hx : SubCtx_cdp c v Ks k s its) (hk : k ≠ .list)
    {S : List (Int × Int)} {B : Bind} {ch : List (T × List (List GroundTerm))}
    (hT : ∀ x ∈ ch, Takes_cpv S B c Ks k s x.1 x.2) (hperm : its.Perm (ch.flatMap (·.2)))
    (hone : ((ch.map (·.1)).filter (!isElemT ·)).length ≤ 1) :
    DenColF S B k (s : Int) ((ch.map (·.1)).filter isElemT ++ (ch.map (·.1)).filter (!isElemT ·))
      (sortK (its.map encIt_cdp)) := by
  obtain ⟨picked, hd, hp⟩ := chunks_pick_cpv ch hT
  have hfm : (ch.map (·.1)).filter (!isElemT ·) = (ch.filter fun x => !isElemT x.1).map (·.1) := by
    rw [List.filter_map]; rfl
  have hFm : ∀ x ∈ ch.filter (fun x => !isElemT x.1), x ∈ ch ∧ isElemT x.1 = false := fun x hx' => by
    have := List.mem_filter.mp hx'
    exact ⟨this.1, by simpa using this.2⟩
  rw [hfm] at hone ⊢
  refine denCol_pick_cpv hk _ picked _ hd (fun p hp' => (List.mem_filter.mp hp').2)
    ((sortK_perm _).trans ((hperm.map encIt_cdp).trans hp)) ?_
  intro L' h1 h2
  generalize ch.filter (fun x => !isElemT x.1) = F at hone hFm h1 ⊢
  match F, hone, hFm, h1 with
  | [], _, _, h1 =>
    have : L' = [] := by simpa using h1
    subst this
    exact .done
  | [(f, g)], _, hFm, h1 =>
    obtain ⟨hmem, hf⟩ := hFm (f, g) (by simp)
    have ht := hT (f, g) hmem
    unfold Takes_cpv at ht
    simp only [hf, Bool.false_eq_true, ↓reduceIte] at ht
    obtain ⟨w, hw, hdw⟩ := ht
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil] at h1
    have hL : L' = sortK (g.map encIt_cdp) :=
      perm_pairwise_eq_cdp (fun _ _ => ckeyF_asym_cdp) ((hx.strict hk).sublist h2) (hw.strict hk)
        (h1.trans (sortK_perm _).symm)
    rw [hw.enc_eq, ordK_ne_list_cpv hk, ← hL] at hdw
    exact .frame hf hdw
  | _ :: _ :: _, hone, _, _ => simp at hone

theorem mem_orderParts_of_cpv {k : Kind} {ps : List T} {p : T} (h : p ∈ ps) : p ∈ orderParts k ps := by
  unfold orderParts
  split
  · exact h
  · rw [List.mem_append, List.mem_filter, List.mem_filter]
    cases hp : isElemT p with
    | true => exact .inl ⟨h, rfl⟩
    | false => exact .inr ⟨h, rfl⟩

theorem orderParts_ne_list_cpv {k : Kind} (hk : k ≠ .list) (ps : List T) :
    orderParts k ps = ps.filter isElemT ++ ps.filter (!isElemT ·) := by
  unfold orderParts
  have hb : (k == Kind.list) = false := by simpa using hk
  simp only [hb, Bool.false_eq_true, ↓reduceIte]

theorem orderParts_others_cpv {k : Kind} (hk : k ≠ .list) (ps : List T) :
    (orderParts k ps).filter (!isElemT ·) = ps.filter (!isElemT ·) := by
  rw [orderParts_ne_list_cpv hk, List.filter_append]
  have h1 : (ps.filter isElemT).filter (!isElemT ·) = [] := by
    rw [List.filter_eq_nil_iff]
    intro x hx
    simp [(List.mem_filter.mp hx).2]
  have h2 : (ps.filter (!isElemT ·)).filter (!isElemT ·) = ps.filter (!isElemT ·) := by
    rw [List.filter_filter]; simp
  rw [h1, h2, List.nil_append]

/-- **The parts of a collection pattern take the elements of the value's encoding.** Where each
part of a collection pattern, in the pattern's order, takes items of a collection value and
together they take every item, in order for a list and each once for a map or a set with at most
one part that is no element: the parts, in `kore.k`'s order, take the elements of the value's
encoding. -/
theorem denCol_of_chunks_cpv {c : Semantics} {v : GroundTerm} {Ks : CollSig} {k : Kind} {s : Srt}
    {its : List (List GroundTerm)} (hx : SubCtx_cdp c v Ks k s its) {S : List (Int × Int)}
    {B : Bind} {ch : List (T × List (List GroundTerm))} {parts : List T}
    (hch : ch.map (·.1) = parts) (hT : ∀ x ∈ ch, Takes_cpv S B c Ks k s x.1 x.2)
    (hperm : its.Perm (ch.flatMap (·.2))) (hlist : k = .list → its = ch.flatMap (·.2))
    (hone : k ≠ .list → (parts.filter (!isElemT ·)).length ≤ 1) :
    DenColF S B k (s : Int) (orderParts k parts) (ordK_cdp k (its.map encIt_cdp)) := by
  subst hch
  by_cases hk : k = .list
  · subst hk
    have hop : orderParts .list (ch.map (·.1)) = ch.map (·.1) := by simp [orderParts]
    rw [hop, hlist rfl]
    exact denCol_list_cpv ch hT
  · rw [orderParts_ne_list_cpv hk, ordK_ne_list_cpv hk]
    exact denCol_coll_cpv hx hk hT hperm (hone hk)

theorem colPatsOKL_iff_cpv : ∀ {ps : List T}, colPatsOKL ps = true ↔ ∀ p ∈ ps, colPatOK p = true
  | [] => by simp [colPatsOKL]
  | p :: ps => by simp [colPatsOKL, colPatsOKL_iff_cpv (ps := ps)]

/-! ## A pattern that denotes a value, as a substitution of `match` -/

section
variable {c : Semantics} (hmc : MatchCtxO c) (hov : c.ovls = []) (hcs : collsOK c = true)
  {vars : List Srt} {σ : Subst} (hσ : c.WellSorted vars σ)
include hmc hov hcs hσ
set_option linter.unusedSectionVars false

mutual
/-- **A pattern that denotes a value states the match.** Where the pattern `p`, sorted in a left
side's context, denotes `v` under a well-sorted `σ`, and a `Map` or `Set` pattern in it has at
most one part that is no element (`colPatOK`): under `σ` encoded, the encoding of `p` is the
encoding of `v`. A collection pattern included, whatever its parts that are no elements. -/
theorem patVal_denF : ∀ (p : Term) {q : T} {s : Srt} {v : GroundTerm},
    encTerm c p = some q → colPatOK q = true → sortOfTerm c.patCtxNF vars p = some s →
    litsV v = true → PatVal c σ p v → DenF (subsF c) (bindOfSubst σ) q (enc v)
  | .var i, q, s, v, hq, _, _, _, h => by
    rw [encTerm_var_kmf] at hq; cases hq
    cases h with
    | var hi => exact .vr (lookF_bindOfSubst_of hi)
  | .dv s' l, q, s, v, hq, _, _, _, h => by
    rw [encTerm_dv_kmf] at hq
    cases h with
    | dv =>
      rw [enc_dv_of_encLit hq]
      rcases encLit_some hq with ⟨i, -, -, rfl⟩ | ⟨b, -, -, rfl⟩ | ⟨x, -, rfl⟩
      · exact .iv i
      · exact .bv b
      · exact .tk _ x
  | .inj a b p, q, s, v, hq, hcp, hp, lv, h => by
    rw [encTerm_inj_kmf] at hq
    obtain ⟨q', hq', rfl⟩ := Option.map_eq_some_iff.mp hq
    obtain ⟨hab, hp', rfl⟩ := sortOfTerm_inj.mp hp
    have hcp' : colPatOK q' = true := by simpa [colPatOK] using hcp
    cases h with
    | inj h =>
      rename_i w
      have hw : c.sortOf w = some a := Det.patVal_sortedAll hmc hσ h hp'
      cases hi : w.isInj with
      | false =>
        rw [Det.injNormal_of_not_inj hi] at lv ⊢
        have lw : litsV w = true := by simpa [litsV] using lv
        rw [enc_inj_form_kmf]
        exact .ijSame (patVal_denF p hq' hcp' hp' lw h)
      | true =>
        cases w with
        | inj a' x u =>
          obtain ⟨ha', -, -, rfl⟩ := sortOf_inj_kel hw
          have hne : a' ≠ a := fun h => hmc.irrefl a (h ▸ ha')
          have hne' : (a : Int) ≠ (a' : Int) := fun h => hne (Int.natCast_inj.mp h).symm
          have hle : leqF (a' : Int) (a : Int) (subsF c) = true := by
            rw [leqF_subsF hmc.trans]; simp [ha']
          have lw : litsV (.inj a' a u) = true := by
            have : litsV (GroundTerm.inj a' s u) = true := lv
            simpa [litsV] using this
          have ih := patVal_denF p hq' hcp' hp' lw h
          rw [enc_inj_form_kmf] at ih
          show DenF (subsF c) (bindOfSubst σ) (.ij a s q') (enc (.inj a' s u))
          rw [enc_inj_form_kmf]
          exact .ijSub hne' hle ih
        | _ => cases hi
  | .as p i, q, s, v, hq, hcp, hp, lv, h => by
    rw [encTerm_as_kmf] at hq
    obtain ⟨q', hq', rfl⟩ := Option.map_eq_some_iff.mp hq
    obtain ⟨-, hp'⟩ := Exec.sortOfTerm_as hp
    have hcp' : colPatOK q' = true := by simpa [colPatOK] using hcp
    cases h with
    | as h hi => exact .as (patVal_denF p hq' hcp' hp' lv h) (lookF_bindOfSubst_of hi)
  | .app f ps, q, s, v, hq, hcp, hp, lv, h => by
    rw [encTerm_app_kmf] at hq
    by_cases hct : c.isCtor f = true
    · rw [readApp_ctor_kmf hct] at hq
      obtain ⟨qs, hqs, rfl⟩ := Option.map_eq_some_iff.mp hq
      obtain ⟨sg, -, hps, -⟩ := sortOfTerm_app.mp hp
      cases h with
      | ctor hc hs =>
        rw [enc_ctor_kmf]
        exact .ap (patVals_densF ps hqs (by simpa [colPatOK] using hcp) hps
          (by simpa [litsV] using lv) hs)
      | hook hp' _ _ => rw [hmc.patHooks f (List.contains_iff_mem.mp hp')] at hct; cases hct
      | coll hc _ _ _ => rw [hc] at hct; cases hct
      | ovl hc _ _ _ => rw [hc] at hct; cases hct
    · have hct' : c.isCtor f = false := by simpa using hct
      have hsome : (collSymOf c f).isSome = true := by
        cases h with
        | ctor hc _ => exact absurd hc hct
        | hook hp' _ _ => exact collSymOf_pat_kmf (.inl hp')
        | coll _ hp' _ _ => exact collSymOf_pat_kmf (.inr hp')
        | ovl _ ho _ _ => rw [c.isOvl_of_none hov] at ho; cases ho
      obtain ⟨⟨k, s', r⟩, hcy⟩ := Option.isSome_iff_exists.mp hsome
      simp only [readApp, hct', Bool.false_eq_true, ite_false, hcy] at hq
      obtain ⟨parts, hparts, rfl⟩ := Option.map_eq_some_iff.mp hq
      have hparts' : encCollWith c encLit k s' r ps = some parts := hparts
      obtain ⟨sg, hsg, -, hs⟩ := sortOfTerm_app.mp hp
      obtain ⟨hres, Ks, hK, hkd, -⟩ := collSig_cdp hmc hcs hct' hcy hsg
      have hss : s = s' := hs.trans hres
      subst hss
      obtain ⟨vs, -, hval⟩ := patVal_coll_inv_cpv hov hct' h
      obtain ⟨K, hKk, hbd⟩ := collVal_builds_cpv hcy hval
      obtain ⟨s₁, its, hcont⟩ := CExec.builds_content hbd
      have hv : c.sortOf v = some s := Det.patVal_sortedAll hmc hσ h hp
      have hx := subCtx_content_cpv hcont hKk hv lv hK hkd
      rw [colPatOK] at hcp
      simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at hcp
      have hcps : colPatsOKL parts = true :=
        colPatsOKL_iff_cpv.mpr fun p hp' => colPatsOKL_iff_cpv.mp hcp.2 p (mem_orderParts_of_cpv hp')
      have hone : k ≠ .list → (parts.filter (!isElemT ·)).length ≤ 1 := fun hk => by
        rw [← orderParts_others_cpv hk]
        exact (hcp.1.resolve_left hk).1
      obtain ⟨ch, h1, h2, h3, h4⟩ := collParts_cpv ps hct' hcy hparts' hcps hp hx h
      rw [hx.enc_eq]
      exact .cb (denCol_of_chunks_cpv hx h1 h2 h3 h4 hone)
  termination_by p => 3 * termSize p
  decreasing_by all_goals (first | omega | (simp only [termSize]; omega))
/-- The same of a list of patterns and a list of values. -/
theorem patVals_densF : ∀ (ps : List Term) {qs : List T} {ss : List Srt} {vs : List GroundTerm},
    encTermsWith c encLit ps = some qs → colPatsOKL qs = true →
    sortsOfTerms c.patCtxNF vars ps = some ss → litsVL vs = true → PatVals c σ ps vs →
    DensF (subsF c) (bindOfSubst σ) qs (encTs vs)
  | [], qs, ss, vs, hq, _, _, _, h => by
    cases encTerms_nil_kmf c hq
    cases h with
    | nil => rw [encTs]; exact .nil
  | p :: ps, qs, ss, vs, hq, hcp, hp, lv, h => by
    obtain ⟨q, qs', hq1, hq2, rfl⟩ := encTerms_cons_kmf c hq
    obtain ⟨s, ss', hp1, hp2, rfl⟩ := sortsOfTerms_cons.mp hp
    have hpos := Exec.termSize_pos p
    simp only [colPatsOKL, Bool.and_eq_true] at hcp
    cases h with
    | cons h hs =>
      simp only [litsVL, Bool.and_eq_true] at lv
      rw [encTs_cons_kmf]
      exact .cons (patVal_denF p hq1 hcp.1 hp1 lv.1 h) (patVals_densF ps hq2 hcp.2 hp2 lv.2 hs)
  termination_by ps => 3 * termSizeList ps + 1
  decreasing_by all_goals (first | omega | (simp only [termSizeList]; omega))
/-- The parts of a collection symbol's application, in the pattern's order, with the items each
takes of the collection value the application denotes. -/
theorem collParts_cpv : ∀ (ts : List Term) {f : Sym} {k : Kind} {s : Srt} {r : CRole}
    {parts : List T} {u : GroundTerm} {Ks : CollSig} {its : List (List GroundTerm)},
    c.isCtor f = false → collSymOf c f = some (k, s, r) →
    encCollWith c encLit k s r ts = some parts → colPatsOKL parts = true →
    sortOfTerm c.patCtxNF vars (.app f ts) = some s → SubCtx_cdp c u Ks k s its →
    PatVal c σ (.app f ts) u →
    ∃ ch : List (T × List (List GroundTerm)), ch.map (·.1) = parts ∧
      (∀ x ∈ ch, Takes_cpv (subsF c) (bindOfSubst σ) c Ks k s x.1 x.2) ∧
      its.Perm (ch.flatMap (·.2)) ∧ (k = .list → its = ch.flatMap (·.2))
  | ts, f, k, s, r, parts, u, Ks, its, hct, hcy, henc, hcp, hp, hx, h => by
    obtain ⟨sg, hsg, hargs, -⟩ := sortOfTerm_app.mp hp
    obtain ⟨-, Ks', hK', -, hsargs⟩ := collSig_cdp hmc hcs hct hcy hsg
    rw [hx.coll] at hK'; cases hK'
    rw [hsargs] at hargs
    obtain ⟨vs, hvs, hval⟩ := patVal_coll_inv_cpv hov hct h
    obtain ⟨K, hKk, hbd⟩ := collVal_builds_cpv hcy hval
    have hKK := kindOf_inj_cpv hKk hx.kind
    subst hKK
    have hsv := Det.patVals_sortedAll hmc hσ hvs hargs
    rcases encColl_cases_cdp henc with ⟨rfl, hts, rfl⟩ | ⟨rfl, qs, e, hqs, rfl, hsh⟩ |
      ⟨rfl, a, b, pa, pb, hts, hpa, hpb, rfl⟩
    · obtain ⟨-, s₁, hc1⟩ := hbd
      rw [hx.cont] at hc1
      simp only [Option.some.injEq, Prod.mk.injEq, true_and] at hc1
      obtain ⟨-, rfl⟩ := hc1
      exact ⟨[], rfl, (by intro x hx'; cases hx'), List.Perm.refl _, fun _ => rfl⟩
    · obtain ⟨s₁, hc1⟩ := hbd
      rw [hx.cont] at hc1
      simp only [Option.some.injEq, Prod.mk.injEq, true_and] at hc1
      obtain ⟨-, rfl⟩ := hc1
      obtain ⟨hits, lits, hform⟩ := hx.item (it := vs) (by simp)
      have hcq : colPatsOKL qs = true := by
        rcases hsh with ⟨-, p, rfl, rfl⟩ | ⟨-, p, q, rfl, rfl⟩ <;>
          simpa [colPatsOKL, colPatOK] using hcp
      have hds := patVals_densF ts hqs hcq hargs lits hvs
      have hel : isElemT e = true := by
        rcases hsh with ⟨-, p, -, rfl⟩ | ⟨-, p, q, -, rfl⟩ <;> rfl
      refine ⟨[(e, [vs])], rfl, fun x hx' => ?_, by simp, fun _ => by simp⟩
      simp only [List.mem_singleton] at hx'
      subst hx'
      unfold Takes_cpv
      simp only [hel, ↓reduceIte]
      refine ⟨vs, rfl, ?_⟩
      rcases hsh with ⟨hkm, p, rfl, rfl⟩ | ⟨hkm, p, q, rfl, rfl⟩
      · rcases hform with ⟨hk', -⟩ | ⟨-, x, rfl⟩
        · exact absurd hk' hkm
        · rw [encTs_cons_kmf, encTs] at hds
          cases hds with
          | cons hd _ => exact .el hd
      · rcases hform with ⟨-, x, y, rfl⟩ | ⟨hk', -⟩
        · rw [encTs_cons_kmf, encTs_cons_kmf, encTs] at hds
          cases hds with
          | cons hd1 hd' =>
            cases hd' with
            | cons hd2 _ => exact .kv hd1 hd2
        · exact absurd hkm hk'
    · have hsort := collOf_sort_cdp hx.coll
      have hsz : termSizeList ts = termSize a + termSize b := by rw [hts]; simp [termSizeList]
      have hpa' := Exec.termSize_pos a
      have hpb' := Exec.termSize_pos b
      rw [hts] at hargs hvs
      obtain ⟨hsa, hsb⟩ := Det.sortsOfTerms_two hargs
      rw [hsort] at hsa hsb
      obtain ⟨ua, ub, rfl, hva, hvb⟩ := patVals_two_cpv hvs
      obtain ⟨hua, hub⟩ := sortsOf_two_cpv hsv
      rw [hsort] at hua hub
      obtain ⟨ia, ib, iu, hca, hcb, hcu, hperm, hlist⟩ := builds_concat_cpv hbd hua hub hx.sorted
      rw [hx.cont] at hcu
      simp only [Option.some.injEq, Prod.mk.injEq, true_and] at hcu
      subst hcu
      have lia : ∀ it ∈ ia, litsVL it = true := fun it hit =>
        (hx.item (hperm.symm.subset (List.mem_append_left _ hit))).2.1
      have lib : ∀ it ∈ ib, litsVL it = true := fun it hit =>
        (hx.item (hperm.symm.subset (List.mem_append_right _ hit))).2.1
      have hxa := subCtx_content_cpv hca hx.kind hua (litsV_of_items_cpv hca lia) hx.coll hx.kind
      have hxb := subCtx_content_cpv hcb hx.kind hub (litsV_of_items_cpv hcb lib) hx.coll hx.kind
      have hcpa : colPatsOKL pa = true := colPatsOKL_iff_cpv.mpr fun p hp' =>
        colPatsOKL_iff_cpv.mp hcp p (List.mem_append_left _ hp')
      have hcpb : colPatsOKL pb = true := colPatsOKL_iff_cpv.mpr fun p hp' =>
        colPatsOKL_iff_cpv.mp hcp p (List.mem_append_right _ hp')
      obtain ⟨cha, a1, a2, a3, a4⟩ := partParts_cpv a hpa hcpa hsa hxa hva
      obtain ⟨chb, b1, b2, b3, b4⟩ := partParts_cpv b hpb hcpb hsb hxb hvb
      refine ⟨cha ++ chb, by rw [List.map_append, a1, b1], fun x hx' => ?_, ?_, fun hk => ?_⟩
      · rcases List.mem_append.mp hx' with h' | h'
        · exact a2 x h'
        · exact b2 x h'
      · rw [List.flatMap_append]
        exact hperm.trans (a3.append b3)
      · rw [List.flatMap_append, ← a4 hk, ← b4 hk]
        exact hlist (kindOf_list_cdp (hk ▸ hx.kind))
  termination_by ts => 3 * termSizeList ts + 2
  decreasing_by all_goals (omega)
/-- The same of an argument of a concatenation: the parts of a nested construction of the same
collection, or the argument as one part, which takes every item of the value it denotes. -/
theorem partParts_cpv : ∀ (a : Term) {k : Kind} {s : Srt} {parts : List T} {u : GroundTerm}
    {Ks : CollSig} {its : List (List GroundTerm)},
    encPartWith c encLit k s a = some parts → colPatsOKL parts = true →
    sortOfTerm c.patCtxNF vars a = some s → SubCtx_cdp c u Ks k s its → PatVal c σ a u →
    ∃ ch : List (T × List (List GroundTerm)), ch.map (·.1) = parts ∧
      (∀ x ∈ ch, Takes_cpv (subsF c) (bindOfSubst σ) c Ks k s x.1 x.2) ∧
      its.Perm (ch.flatMap (·.2)) ∧ (k = .list → its = ch.flatMap (·.2))
  | a, k, s, parts, u, Ks, its, henc, hcp, hp, hx, h => by
    rcases encPart_cases_cdp henc with ⟨f, ts, r, ha, hct, hcy, hc⟩ | ⟨q, hq, rfl⟩
    · have hsz : termSize a = termSizeList ts + 1 := by rw [ha]; simp [termSize]
      rw [ha] at hp h
      exact collParts_cpv ts hct hcy hc hcp hp hx h
    · have hd := patVal_denF a hq (by simpa [colPatsOKL] using hcp) hp hx.lits h
      refine ⟨[(q, its)], rfl, fun x hx' => ?_, by simp, fun _ => by simp⟩
      simp only [List.mem_singleton] at hx'
      subst hx'
      unfold Takes_cpv
      simp only [encTerm_notElem_cdp hq, Bool.false_eq_true, ↓reduceIte]
      exact ⟨u, hx, hd⟩
  termination_by a => 3 * termSize a + 1
  decreasing_by all_goals (omega)
end

/-- **`matchF` is complete, collection patterns included.** `matchF_complete` without `noCb`:
where the pattern `p` denotes `v` under a well-sorted `σ`, a `Map` or `Set` pattern in it has at
most one part that is no element, and `B` agrees with `σ`, `match` at the encodings has a value,
and the value holds a substitution that extends `B`, agrees with `σ` and binds every variable of
`p`. The value may hold other substitutions: an element pattern whose key `B` does not bind
matches every element. -/
theorem matchF_col_complete {p : Term} {q : T} {s : Srt} {v : GroundTerm} {B : Bind}
    (hq : encTerm c p = some q) (hcp : colPatOK q = true)
    (hp : sortOfTerm c.patCtxNF vars p = some s) (lv : litsV v = true) (h : PatVal c σ p v)
    (hB : BindAgree B σ) :
    ∃ M, matchF (subsF c) q (enc v) B = some M ∧ ∃ B' ∈ M, BindAgree B' σ ∧ BindExt B B' ∧
      ∀ i ∈ varOccs p, (lookF (i : Int) B').isSome = true :=
  matchF_complete_of_den hov hq hp (Det.patVal_sortedAll hmc hσ h hp)
    (patVal_denF hmc hov hcs hσ p hq hcp hp lv h) hB

end

end KCore.KK
