/-
  KCore, checked layer: the candidates of CollExec.lean reach every match, so `cmatch` lists, up to
  the clause's or rule's variables, every well-sorted match (`cmatch_complete`).

  1. **What a collection pattern symbol builds** (`roleVal`): a symbol with a `role` (K, r) denotes,
     at its arguments' values vs, what the library's symbol of kind K and role r builds (`Builds`:
     the empty collection, the one item vs, or the concatenation of two collections of kind K), of
     the library's or a parameter's sort.
  2. **The decomposition** (`collDecomp`): the value of a flattened collection pattern of kind K is
     made of what its parts take (`Takes`: an element its arguments' values, one item; a frame its
     variable's collection's items): for a list in order, for a map or a set up to order (`Comb`).
     Up to order is where the sorts are read: the values of well-sorted patterns are canonical
     (`Det.patVal_sortedAll`), so a defined `_Map_` or `_Set_` holds its arguments' items each once
     (`union_perm`, `concatS_perm`).
  3. **The candidates' completeness** (`cmatchP_complete`, with `cmatchL_complete`,
     `pickAll_complete`, `matchSeq_complete`): from any σ below a well-sorted τ under which a ready,
     well-sorted pattern denotes the value, the candidates include a substitution below τ, above σ,
     binding the pattern's variables. A map's or a set's elements choose their items (each chosen
     item is in the list, `perm_eraseIdx`), and the rest is the frame's collection: the items left
     are a sublist of the value's canonical items with the frame's items up to order, so they are
     the frame's items (`canonI_perm`), and `build` gives back the frame's value (`build_content`).
     A list's frame takes the items before those of the elements after it (one item each,
     `flat_len`). At an injection pattern `inj{a,b}(p)`, the value p denotes has sort a, so it is
     not an injection into another sort than a: one of the candidates' two tries is it.
  4. `cmatch_complete`: the substitution found agrees with τ on the variables (all bound), so it
     is well sorted and passes the check (`patEval_complete`, `patEval_congr`).
-/
import KcoreSpec.CollExecComplete
import KcoreSpec.Collections

set_option autoImplicit false

namespace KCore.CExec

open KCore Exec GroundTerm

variable {c : Semantics}

/-! ## What a collection pattern symbol builds -/

/-- The library's collection symbol of each kind and role. -/
def roleSym : CollKind → Role → Sym
  | .map, .unit => mapUnit
  | .map, .elem => mapElem
  | .map, .concat => mapConcat
  | .set, .unit => setUnit
  | .set, .elem => setElem
  | .set, .concat => setConcat
  | .list, .unit => listUnit
  | .list, .elem => listElem
  | .list, .concat => listConcat
  | .rangeMap, .unit => rmUnit
  | .rangeMap, .elem => rmElem
  | .rangeMap, .concat => rmConcat

theorem hookRole_sym {g : Sym} {K : CollKind} {r : Role} (h : hookRole g = some (K, r)) :
    g = roleSym K r := by
  unfold hookRole at h
  repeat' (first
    | (split at h; rename_i hg; simp only [Option.some.injEq, Prod.mk.injEq] at h;
       obtain ⟨rfl, rfl⟩ := h; exact beq_iff_eq.mp hg)
    | (split at h))
  all_goals cases h

/-- What the symbol of kind K and role r builds from the values vs: the empty collection, the
collection of the one item vs, or the concatenation of two collections of kind K (`_Map_` and
`_Set_` defined only where they share no key or member). The result's sort is left open: a
parameter's value takes its declared sort (`GroundTerm.withSort`). -/
def Builds : CollKind → Role → List GroundTerm → GroundTerm → Prop
  | K, .unit, vs, u => vs = [] ∧ ∃ s, content u = some (K, s, [])
  | K, .elem, vs, u => ∃ s, content u = some (K, s, [vs])
  | .map, .concat, vs, u => ∃ sa sb a b s m, vs = [.map sa a, .map sb b] ∧ union a b = some m ∧
      u = .map s m
  | .set, .concat, vs, u => ∃ sa sb a b s m, vs = [.set sa a, .set sb b] ∧ concatS a b = some m ∧
      u = .set s m
  | .list, .concat, vs, u => ∃ sa sb a b s, vs = [.list sa a, .list sb b] ∧ u = .list s (a ++ b)
  | .rangeMap, .concat, _, _ => False

theorem content_withSort {u : GroundTerm} {K : CollKind} {s : Srt} {its : List (List GroundTerm)}
    (s' : Srt) (h : content u = some (K, s, its)) : content (u.withSort s') = some (K, s', its) := by
  cases u with
  | map s0 es =>
    simp only [content, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h; rfl
  | set s0 es =>
    simp only [content, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h; rfl
  | list s0 es =>
    simp only [content, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h; rfl
  | _ => simp [content] at h

/-- What a collection's symbol builds is no literal. -/
theorem builds_not_dv {K : CollKind} {r : Role} {vs : List GroundTerm} {b : Srt} {lit : Lit}
    (h : Builds K r vs (.dv b lit)) : False := by
  cases r with
  | unit => obtain ⟨-, s, hs⟩ := h; cases hs
  | elem => obtain ⟨s, hs⟩ := h; cases hs
  | concat =>
    cases K with
    | map => obtain ⟨_, _, _, _, _, _, -, -, hu⟩ := h; cases hu
    | set => obtain ⟨_, _, _, _, _, _, -, -, hu⟩ := h; cases hu
    | list => obtain ⟨_, _, _, _, _, -, hu⟩ := h; cases hu
    | rangeMap => exact h

theorem builds_withSort {K : CollKind} {r : Role} {vs : List GroundTerm} {u : GroundTerm} (s' : Srt)
    (h : Builds K r vs u) : Builds K r vs (u.withSort s') := by
  cases r with
  | unit => obtain ⟨h1, s, h2⟩ := h; exact ⟨h1, s', content_withSort s' h2⟩
  | elem => obtain ⟨s, h2⟩ := h; exact ⟨s', content_withSort s' h2⟩
  | concat =>
    cases K with
    | map => obtain ⟨sa, sb, a, b, s, m, h1, h2, rfl⟩ := h; exact ⟨sa, sb, a, b, s', m, h1, h2, rfl⟩
    | set => obtain ⟨sa, sb, a, b, s, m, h1, h2, rfl⟩ := h; exact ⟨sa, sb, a, b, s', m, h1, h2, rfl⟩
    | list => obtain ⟨sa, sb, a, b, s, h1, rfl⟩ := h; exact ⟨sa, sb, a, b, s', h1, rfl⟩
    | rangeMap => exact h.elim

theorem builds_content {K : CollKind} {r : Role} {vs : List GroundTerm} {u : GroundTerm}
    (h : Builds K r vs u) : ∃ s its, content u = some (K, s, its) := by
  cases r with
  | unit => obtain ⟨_, s, h2⟩ := h; exact ⟨s, _, h2⟩
  | elem => obtain ⟨s, h2⟩ := h; exact ⟨s, _, h2⟩
  | concat =>
    cases K with
    | map => obtain ⟨_, _, _, _, s, m, _, _, rfl⟩ := h; exact ⟨s, _, rfl⟩
    | set => obtain ⟨_, _, _, _, s, m, _, _, rfl⟩ := h; exact ⟨s, _, rfl⟩
    | list => obtain ⟨_, _, _, _, s, _, rfl⟩ := h; exact ⟨s, _, rfl⟩
    | rangeMap => exact h.elim

/-- The library's collection symbols build what `Builds` says. -/
theorem builds_of_hook {g : Sym} {K : CollKind} {r : Role} {vs : List GroundTerm} {u : GroundTerm}
    (hr : hookRole g = some (K, r)) (hv : hook g vs = some (some u)) : Builds K r vs u := by
  have hg := hookRole_sym hr
  subst hg
  cases K <;> cases r <;> dsimp only [roleSym] at hv
  · obtain ⟨rfl, rfl⟩ := hook_unit_inv hv; exact ⟨rfl, _, rfl⟩
  · obtain ⟨k, w, rfl, rfl⟩ := hook_elem_inv hv; exact ⟨_, rfl⟩
  · obtain ⟨s, t, a, b, m, rfl, hm, rfl⟩ := hook_concat_inv hv; exact ⟨s, t, a, b, _, m, rfl, hm, rfl⟩
  · rw [hook_setUnit_eq] at hv
    split at hv
    · cases hv; exact ⟨rfl, _, rfl⟩
    · cases hv
  · rw [hook_setElem_eq] at hv
    split at hv
    · cases hv; exact ⟨_, rfl⟩
    · cases hv
  · rw [hook_setConcat_eq] at hv
    split at hv
    · obtain ⟨m, hm, rfl⟩ := Option.map_eq_some_iff.mp (Option.some.inj hv)
      exact ⟨_, _, _, _, _, m, rfl, hm, rfl⟩
    · cases hv
  · rw [hook_listUnit_eq] at hv
    split at hv
    · cases hv; exact ⟨rfl, _, rfl⟩
    · cases hv
  · rw [hook_listElem_eq] at hv
    split at hv
    · cases hv; exact ⟨_, rfl⟩
    · cases hv
  · rw [hook_listConcat_eq] at hv
    split at hv
    · cases hv; exact ⟨_, _, _, _, _, rfl, rfl⟩
    · cases hv
  -- RANGEMAP's symbols have no collection role
  all_goals exact absurd hr (by decide)

/-- A map pattern symbol's pattern denotes its hook's value at its arguments' values. -/
theorem hookPat_invO (hc : MatchCtxO c) {τ : Subst} {f : Sym} {ps : List Term} {v : GroundTerm}
    (hf : patternHooks.contains f = true) (h : PatVal c τ (.app f ps) v) :
    ∃ vs, PatVals c τ ps vs ∧ hook f vs = some (some v) := by
  generalize ht : Term.app f ps = t at h
  cases h with
  | ctor hk _ =>
    cases ht
    rw [hc.patHooks f (List.contains_iff_mem.mp hf)] at hk; cases hk
  | hook _ hs hv => cases ht; exact ⟨_, hs, hv⟩
  | coll _ hp _ _ => cases ht; rw [Semantics.isCollPat_of_hook c hf] at hp; cases hp
  | ovl _ ho _ _ => cases ht; rw [c.isOvl_of_patternHook hf] at ho; cases ho
  | _ => cases ht

/-- A symbol with a role is no overloading symbol. -/
theorem isOvl_of_role {g : Sym} {K : CollKind} {r : Role} (hr : role c g = some (K, r)) :
    c.isOvl g = false := by
  unfold role at hr
  by_cases hct : c.isCtor g = true
  · rw [if_pos hct] at hr; cases hr
  rw [if_neg hct] at hr
  by_cases hph : patternHooks.contains g = true
  · exact c.isOvl_of_patternHook hph
  rw [if_neg hph] at hr
  by_cases hcp : c.isCollPat g = true
  · exact c.isOvl_of_collPat hcp
  · rw [if_neg hcp] at hr; cases hr

/-- **The overloading symbol's candidate arguments are its arguments**: where f's normal form at
arguments of its sorts that no function overload covers is v, `ovlArgs c f v` reads them back
(`OvlLaws.norm_decomp_ovlF`). -/
theorem ovlArgs_complete (H : OvlLaws.OvlHyp c) {f : Sym} {o : OvlSig} (ho : c.lookupOvl f = some o)
    {vs : List GroundTerm} (hvs : c.sortsOf vs = some o.sig.args) (hnf : c.fnCover f vs = none) :
    ovlArgs c f (c.norm f vs) = some vs := by
  obtain ⟨-, hn, -, -, hks, -⟩ := OvlLaws.ovl_facts_ovlF H.fnFacts ho
  obtain ⟨h, us, hkh, -, -, -, hne, hv, -⟩ :=
    OvlLaws.norm_decomp_ovlF H H.fnFacts _ o.sig hks (OvlLaws.ovlRank_le _) vs hvs (by rw [hn]; exact hnf)
  rw [hn] at hne
  have hraw : rawHead (lift h.result o.sig.result (.ctor h.name us)) = some (h.name, us) := by
    unfold lift; split <;> simp [rawHead, injNormal]
  rw [hne]
  unfold ovlArgs
  rw [ho, hraw]
  unfold OvlLaws.KnownSig at hkh
  simp only [hkh, Option.map_some, hv]

/-- A symbol with a role denotes, at its arguments' values, what its role builds. -/
theorem roleVal (hc : MatchCtxO c) {σ : Subst} {g : Sym} {ps : List Term} {v : GroundTerm}
    {K : CollKind} {r : Role} (hr : role c g = some (K, r)) (hp : PatVal c σ (.app g ps) v) :
    ∃ vs, PatVals c σ ps vs ∧ Builds K r vs v := by
  unfold role at hr
  by_cases hct : c.isCtor g = true
  · rw [if_pos hct] at hr; cases hr
  rw [if_neg hct] at hr
  have hct' : c.isCtor g = false := by simpa using hct
  by_cases hph : patternHooks.contains g = true
  · rw [if_pos hph] at hr
    obtain ⟨vs, hs, hv⟩ := hookPat_invO hc hph hp
    exact ⟨vs, hs, builds_of_hook hr hv⟩
  rw [if_neg hph] at hr
  by_cases hcp : c.isCollPat g = true
  · rw [if_pos hcp] at hr
    obtain ⟨vs, hs, hv⟩ : ∃ vs, PatVals c σ ps vs ∧ c.collVal g vs = some v := by
      generalize ht : Term.app g ps = t at hp
      cases hp with
      | ctor hk _ => cases ht; exact absurd hk hct
      | hook hp' _ _ => cases ht; exact absurd hp' hph
      | coll _ _ hs hv => cases ht; exact ⟨_, hs, hv⟩
      | ovl _ ho _ _ => cases ht; rw [c.isOvl_of_collPat hcp] at ho; cases ho
      | _ => cases ht
    refine ⟨vs, hs, ?_⟩
    unfold Semantics.collVal at hv
    by_cases hh : isHook g = true
    · rw [if_pos hh] at hr hv
      exact builds_of_hook hr (Option.join_eq_some_iff.mp hv)
    · rw [if_neg hh] at hr hv
      unfold Semantics.paramVal at hv
      cases hk : c.lookupParam g with
      | none => rw [hk] at hr; cases hr
      | some k =>
        rw [hk] at hr hv
        dsimp only at hr hv
        cases hi : k.impl with
        | none => rw [hi] at hr; cases hr
        | some h =>
          rw [hi] at hr hv
          simp only [Option.bind_some] at hr
          have hw := (Option.filter_eq_some_iff.mp hv).1
          obtain ⟨u, hu, rfl⟩ := Option.map_eq_some_iff.mp hw
          have hsh : silentKey h = false := by
            have hr' := hr
            rw [hookRole_sym hr] at hr' ⊢; rcases K with _ | _ | _ | _ <;> rcases r with _ | _ | _ <;>
              first | exact silentKey_of_mem rfl | decide | exact absurd hr' (by decide)
          have hrc : Semantics.rawArgHooks.contains h = true := by
            rw [hookRole_sym hr]; rcases K with _ | _ | _ | _ <;> rcases r with _ | _ | _ <;> decide
          rw [Semantics.libArgs_coll c hrc, Semantics.hookRes_of_notKey hsh] at hu
          have hb := builds_of_hook hr (Option.join_eq_some_iff.mp hu)
          have hu' : u.asSort c.lib k.sig.result = u.withSort k.sig.result := by
            cases u with
            | dv b lit => exact (builds_not_dv hb).elim
            | _ => rfl
          rw [hu']
          exact builds_withSort _ hb
  · rw [if_neg hcp] at hr; cases hr

/-! ## Canonical items -/

/-- The items of a collection value are in canonical order: a map's keys and a set's elements
strictly increasing (a list's in any order). -/
def CanonI : CollKind → List (List GroundTerm) → Prop
  | .map, its => ∃ es, keysSorted es = true ∧ its = es.map fun e => [e.1, e.2]
  | .set, its => ∃ es, elemsSorted es = true ∧ its = es.map fun e => [e]
  | .list, _ => True
  | .rangeMap, _ => False

/-- A collection value of some sort has that collection's sort and canonical items. -/
theorem content_canon {w : GroundTerm} {K : CollKind} {s t : Srt} {its : List (List GroundTerm)}
    (h : content w = some (K, s, its)) (hs : c.sortOf w = some t) : t = s ∧ CanonI K its := by
  cases w with
  | map s0 es =>
    simp only [content, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    obtain ⟨_, _, _, _, h1, _, rfl⟩ := c.sortOf_map_inv hs
    exact ⟨rfl, es, (mapKeys_sorted h1).2, rfl⟩
  | set s0 es =>
    simp only [content, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    simp only [Semantics.sortOf] at hs
    split at hs
    · split at hs
      · rename_i hcond
        simp only [Bool.and_eq_true] at hcond
        cases hs
        exact ⟨rfl, es, hcond.1.2, rfl⟩
      · cases hs
    · cases hs
  | list s0 es =>
    simp only [content, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    simp only [Semantics.sortOf] at hs
    split at hs
    · split at hs
      · cases hs; exact ⟨rfl, trivial⟩
      · cases hs
    · cases hs
  | _ => simp [content] at h

theorem canonI_sublist {K : CollKind} {a b : List (List GroundTerm)} (ha : CanonI K a)
    (hs : b.Sublist a) : CanonI K b := by
  cases K with
  | map =>
    obtain ⟨es, hes, rfl⟩ := ha
    obtain ⟨es', hs', rfl⟩ := List.sublist_map_iff.mp hs
    exact ⟨es', sorted_sublist hs' hes, rfl⟩
  | set =>
    obtain ⟨es, hes, rfl⟩ := ha
    obtain ⟨es', hs', rfl⟩ := List.sublist_map_iff.mp hs
    exact ⟨es', elemsSorted_iff.mpr ((elemsSorted_iff.mp hes).sublist hs'), rfl⟩
  | list => trivial
  | rangeMap => exact ha.elim

/-- Two canonical item lists of a map or a set with the same items are equal. -/
theorem canonI_perm {K : CollKind} {a b : List (List GroundTerm)} (hK : K ≠ .list)
    (ha : CanonI K a) (hb : CanonI K b) (hp : a.Perm b) : a = b := by
  cases K with
  | map =>
    obtain ⟨ea, hea, rfl⟩ := ha
    obtain ⟨eb, heb, rfl⟩ := hb
    have hm : ∀ e, e ∈ ea ↔ e ∈ eb := fun e => by
      have := hp.mem_iff (a := [e.1, e.2])
      simp only [List.mem_map, List.cons.injEq, and_true] at this
      constructor
      · intro he
        obtain ⟨e', he', h1, h2⟩ := this.mp ⟨e, he, rfl, rfl⟩
        rwa [show e = e' from Prod.ext h1.symm h2.symm]
      · intro he
        obtain ⟨e', he', h1, h2⟩ := this.mpr ⟨e, he, rfl, rfl⟩
        rwa [show e = e' from Prod.ext h1.symm h2.symm]
    rw [entries_canon hea heb hm]
  | set =>
    obtain ⟨ea, hea, rfl⟩ := ha
    obtain ⟨eb, heb, rfl⟩ := hb
    have hm : ∀ e, e ∈ ea ↔ e ∈ eb := fun e => by
      have := hp.mem_iff (a := [e])
      simp only [List.mem_map, List.cons.injEq, and_true, exists_eq_right] at this
      exact this
    rw [KCore.Set.ext hea heb hm]
  | list => exact absurd rfl hK
  | rangeMap => exact ha.elim

theorem nodup_of_keysSorted {es : Entries} (h : keysSorted es = true) : es.Nodup :=
  (sorted_pairwise h).imp fun hlt he => by rw [he, cmp_refl] at hlt; cases hlt

theorem nodup_of_elemsSorted {es : List GroundTerm} (h : elemsSorted es = true) : es.Nodup :=
  (elemsSorted_iff.mp h).imp fun hlt he => by rw [he, cmp_refl] at hlt; cases hlt

/-- A defined `_Map_` of canonical maps holds their entries, each once. -/
theorem union_perm {a b m : Entries} (ha : keysSorted a = true) (hb : keysSorted b = true)
    (hm : keysSorted m = true) (hu : union a b = some m) : m.Perm (a ++ b) := by
  obtain ⟨hmem, -, -, hcross⟩ := union_spec hu
  refine (List.perm_ext_iff_of_nodup (nodup_of_keysSorted hm) ?_).mpr fun e => by
    rw [hmem, List.mem_append]
  refine List.nodup_append.mpr ⟨nodup_of_keysSorted ha, nodup_of_keysSorted hb, fun x hx y hy he => ?_⟩
  subst he
  exact hcross x hx x hy (cmp_refl _)

/-- A defined `_Set_` of canonical sets holds their members, each once. -/
theorem concatS_perm {a b m : List GroundTerm} (ha : elemsSorted a = true) (hb : elemsSorted b = true)
    (hm : elemsSorted m = true) (hu : concatS a b = some m) : m.Perm (a ++ b) := by
  unfold concatS at hu
  split at hu
  · rename_i hd
    cases hu
    refine (List.perm_ext_iff_of_nodup (nodup_of_elemsSorted hm) ?_).mpr fun e => by
      rw [KCore.Set.mem_union, List.mem_append]
    refine List.nodup_append.mpr ⟨nodup_of_elemsSorted ha, nodup_of_elemsSorted hb, fun x hx y hy he => ?_⟩
    subst he
    have := List.all_eq_true.mp hd x hx
    rw [Bool.not_eq_true', Bool.eq_false_iff, ne_eq, KCore.Set.memS_iff] at this
    exact this hy
  · cases hu

/-- How the items of a value relate to the parts' items: a list's are them in order, a map's or a
set's the same up to order. -/
def Comb : CollKind → List (List GroundTerm) → List (List GroundTerm) → Prop
  | .list, a, b => a = b
  | _, a, b => a.Perm b

theorem comb_refl (K : CollKind) (a : List (List GroundTerm)) : Comb K a a := by
  cases K
  · exact List.Perm.refl a
  · exact List.Perm.refl a
  · rfl
  · exact List.Perm.refl a

theorem comb_perm {K : CollKind} {a b : List (List GroundTerm)} (h : Comb K a b) : a.Perm b := by
  cases K
  · exact h
  · exact h
  · rw [show a = b from h]
  · exact h

theorem comb_append {K : CollKind} {a b a' b' : List (List GroundTerm)} (ha : Comb K a a')
    (hb : Comb K b b') : Comb K (a ++ b) (a' ++ b') := by
  cases K
  · exact List.Perm.append ha hb
  · exact List.Perm.append ha hb
  · show a ++ b = a' ++ b'
    rw [show a = a' from ha, show b = b' from hb]
  · exact List.Perm.append ha hb

theorem comb_trans {K : CollKind} {a b d : List (List GroundTerm)} (h1 : Comb K a b) (h2 : Comb K b d) :
    Comb K a d := by
  cases K
  · exact List.Perm.trans h1 h2
  · exact List.Perm.trans h1 h2
  · show a = d
    rw [show a = b from h1, show b = d from h2]
  · exact List.Perm.trans h1 h2

theorem map_inj_of {α β : Type} {f : α → β} (hf : ∀ x y, f x = f y → x = y) :
    ∀ {a b : List α}, a.map f = b.map f → a = b
  | [], [], _ => rfl
  | x :: a, y :: b, h => by
    simp only [List.map_cons, List.cons.injEq] at h; rw [hf x y h.1, map_inj_of hf h.2]
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

/-- The concatenation's items, from the two collections' items. -/
theorem concat_split {K : CollKind} {vs : List GroundTerm} {v : GroundTerm} {s t : Srt}
    {items : List (List GroundTerm)} {ss : List Srt}
    (hb : Builds K .concat vs v) (hv : content v = some (K, s, items)) (hs : c.sortOf v = some t)
    (hvs : c.sortsOf vs = some ss) :
    ∃ a b sa sb ia ib, vs = [a, b] ∧ content a = some (K, sa, ia) ∧ content b = some (K, sb, ib) ∧
      Comb K items (ia ++ ib) := by
  cases K with
  | map =>
    obtain ⟨sa, sb, a, b, s', m, rfl, hu, rfl⟩ := hb
    simp only [content, Option.some.injEq, Prod.mk.injEq] at hv
    obtain ⟨-, -, rfl⟩ := hv
    obtain ⟨ta, _, hta, hrest, -⟩ := sortsOf_cons.mp hvs
    obtain ⟨tb, _, htb, -, -⟩ := sortsOf_cons.mp hrest
    obtain ⟨-, ea, hea, he⟩ := content_canon (K := .map) rfl hta
    obtain ⟨-, eb, heb, he'⟩ := content_canon (K := .map) rfl htb
    obtain ⟨-, em, hem, hm⟩ := content_canon (K := .map) rfl hs
    have hea' := map_inj_of (fun x y (h : [x.1, x.2] = [y.1, y.2]) => by
      simp only [List.cons.injEq, and_true] at h; exact Prod.ext h.1 h.2) he
    have heb' := map_inj_of (fun x y (h : [x.1, x.2] = [y.1, y.2]) => by
      simp only [List.cons.injEq, and_true] at h; exact Prod.ext h.1 h.2) he'
    have hem' := map_inj_of (fun x y (h : [x.1, x.2] = [y.1, y.2]) => by
      simp only [List.cons.injEq, and_true] at h; exact Prod.ext h.1 h.2) hm
    subst hea' heb' hem'
    refine ⟨_, _, sa, sb, _, _, rfl, rfl, rfl, ?_⟩
    rw [← List.map_append]
    exact (union_perm hea heb hem hu).map _
  | set =>
    obtain ⟨sa, sb, a, b, s', m, rfl, hu, rfl⟩ := hb
    simp only [content, Option.some.injEq, Prod.mk.injEq] at hv
    obtain ⟨-, -, rfl⟩ := hv
    obtain ⟨ta, _, hta, hrest, -⟩ := sortsOf_cons.mp hvs
    obtain ⟨tb, _, htb, -, -⟩ := sortsOf_cons.mp hrest
    obtain ⟨-, ea, hea, he⟩ := content_canon (K := .set) rfl hta
    obtain ⟨-, eb, heb, he'⟩ := content_canon (K := .set) rfl htb
    obtain ⟨-, em, hem, hm⟩ := content_canon (K := .set) rfl hs
    have hea' := map_inj_of (fun x y (h : [x] = [y]) => by
      simpa using h) he
    have heb' := map_inj_of (fun x y (h : [x] = [y]) => by
      simpa using h) he'
    have hem' := map_inj_of (fun x y (h : [x] = [y]) => by
      simpa using h) hm
    subst hea' heb' hem'
    refine ⟨_, _, sa, sb, _, _, rfl, rfl, rfl, ?_⟩
    rw [← List.map_append]
    exact (concatS_perm hea heb hem hu).map _
  | list =>
    obtain ⟨sa, sb, a, b, s', rfl, rfl⟩ := hb
    simp only [content, Option.some.injEq, Prod.mk.injEq] at hv
    obtain ⟨-, -, rfl⟩ := hv
    exact ⟨_, _, sa, sb, _, _, rfl, rfl, rfl, List.map_append⟩
  | rangeMap => exact hb.elim

/-! ## Flattening -/

theorem hasOther_append : ∀ (a b : List Part),
    Part.hasOther (a ++ b) = (Part.hasOther a || Part.hasOther b)
  | [], _ => by simp [Part.hasOther]
  | .elem _ :: a, b => by simp only [List.cons_append, Part.hasOther]; exact hasOther_append a b
  | .frame _ :: a, b => by simp only [List.cons_append, Part.hasOther]; exact hasOther_append a b
  | .other _ :: _, _ => by simp [Part.hasOther]

theorem frames_append : ∀ (a b : List Part), Part.frames (a ++ b) = Part.frames a ++ Part.frames b
  | [], _ => rfl
  | .elem _ :: a, b => by simp only [List.cons_append, Part.frames]; exact frames_append a b
  | .frame _ :: a, b => by simp only [List.cons_append, Part.frames, frames_append a b]
  | .other _ :: a, b => by simp only [List.cons_append, Part.frames]; exact frames_append a b

theorem elems_append : ∀ (a b : List Part), Part.elems (a ++ b) = Part.elems a ++ Part.elems b
  | [], _ => rfl
  | .elem _ :: a, b => by simp only [List.cons_append, Part.elems, elems_append a b]
  | .frame _ :: a, b => by simp only [List.cons_append, Part.elems]; exact elems_append a b
  | .other _ :: a, b => by simp only [List.cons_append, Part.elems]; exact elems_append a b

/-- The size of the parts: an element its arguments' and one, a frame one. -/
def partsSize : List Part → Nat
  | [] => 0
  | .elem qs :: ps => termSizeList qs + 1 + partsSize ps
  | .frame _ :: ps => 1 + partsSize ps
  | .other q :: ps => termSize q + partsSize ps

theorem partsSize_append : ∀ (a b : List Part), partsSize (a ++ b) = partsSize a + partsSize b
  | [], _ => by simp [partsSize]
  | .elem _ :: a, b => by simp only [List.cons_append, partsSize, partsSize_append a b]; omega
  | .frame _ :: a, b => by simp only [List.cons_append, partsSize, partsSize_append a b]; omega
  | .other _ :: a, b => by simp only [List.cons_append, partsSize, partsSize_append a b]; omega

theorem flatten_size (K : CollKind) : ∀ (N : Nat) (p : Term) {parts : List Part},
    flatten c K N p = some parts → partsSize parts ≤ termSize p
  | 0, _, _, h => by simp [flatten] at h
  | N + 1, .var j, _, h => by
    simp only [flatten, Option.some.injEq] at h; subst h; simp [partsSize, termSize]
  | N + 1, .dv _ _, _, h => by
    simp only [flatten, Option.some.injEq] at h; subst h; simp [partsSize]
  | N + 1, .inj _ _ _, _, h => by
    simp only [flatten, Option.some.injEq] at h; subst h; simp [partsSize]
  | N + 1, .as _ _, _, h => by
    simp only [flatten, Option.some.injEq] at h; subst h; simp [partsSize]
  | N + 1, .app g ps, parts, h => by
    simp only [flatten] at h
    split at h
    · split at h
      · split at h
        · cases h; simp [partsSize]
        · cases h; simp [partsSize, termSize]
        · rename_i a b _
          simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
            Option.some.injEq] at h
          obtain ⟨pa, ha, pb, hb, rfl⟩ := h
          have h1 := flatten_size K N a ha
          have h2 := flatten_size K N b hb
          simp only [partsSize_append, termSize, termSizeList]
          omega
        · cases h
      · cases h; simp [partsSize]
    · cases h; simp [partsSize]

/-- Every variable of a flattened pattern is a frame or in an element's arguments. -/
theorem flatten_vars (K : CollKind) : ∀ (N : Nat) (p : Term) {parts : List Part},
    flatten c K N p = some parts → Part.hasOther parts = false →
    ∀ i ∈ varOccs p, i ∈ Part.frames parts ∨ ∃ qs ∈ Part.elems parts, i ∈ varOccsList qs
  | 0, _, _, h, _ => by simp [flatten] at h
  | N + 1, .var j, _, h, _ => by
    simp only [flatten, Option.some.injEq] at h; subst h
    intro i hi; simp only [varOccs, List.mem_singleton] at hi; subst hi
    exact .inl (by simp [Part.frames])
  | N + 1, .dv _ _, _, h, ho => by
    simp only [flatten, Option.some.injEq] at h; subst h; simp [Part.hasOther] at ho
  | N + 1, .inj _ _ _, _, h, ho => by
    simp only [flatten, Option.some.injEq] at h; subst h; simp [Part.hasOther] at ho
  | N + 1, .as _ _, _, h, ho => by
    simp only [flatten, Option.some.injEq] at h; subst h; simp [Part.hasOther] at ho
  | N + 1, .app g ps, parts, h, ho => by
    simp only [flatten] at h
    split at h
    · split at h
      · split at h
        · cases h; intro i hi; simp [varOccs, varOccsList] at hi
        · cases h; intro i hi
          exact .inr ⟨ps, by simp [Part.elems], by simpa [varOccs] using hi⟩
        · rename_i a b _
          simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
            Option.some.injEq] at h
          obtain ⟨pa, ha, pb, hb, rfl⟩ := h
          rw [hasOther_append, Bool.or_eq_false_iff] at ho
          intro i hi
          simp only [varOccs, varOccsList, List.append_nil, List.mem_append] at hi
          rw [frames_append, elems_append]
          rcases hi with hi | hi
          · rcases flatten_vars K N a ha ho.1 i hi with h1 | ⟨qs, hq, hi'⟩
            · exact .inl (List.mem_append_left _ h1)
            · exact .inr ⟨qs, List.mem_append_left _ hq, hi'⟩
          · rcases flatten_vars K N b hb ho.2 i hi with h1 | ⟨qs, hq, hi'⟩
            · exact .inl (List.mem_append_right _ h1)
            · exact .inr ⟨qs, List.mem_append_right _ hq, hi'⟩
        · cases h
      · cases h; simp [Part.hasOther] at ho
    · cases h; simp [Part.hasOther] at ho

/-! ## Splitting a collection pattern's value among its parts -/

/-- What a part takes of a collection value under τ: an element one item, its arguments' values; a
frame the items of its variable's collection. -/
def Takes (c : Semantics) (τ : Subst) (vars : List Srt) (K : CollKind) :
    Part × List (List GroundTerm) → Prop
  | (.elem qs, its) => ∃ it, its = [it] ∧ PatVals c τ qs it ∧
      ∃ ss, sortsOfTerms c.patCtxNF vars qs = some ss
  | (.frame j, its) => ∃ w s, τ.lookup j = some w ∧ content w = some (K, s, its)
  | (.other _, _) => False

/-- **The decomposition**: the value of a flattened collection pattern of kind K is made of what its
parts take: for a list, in order; for a map or a set, up to order. -/
theorem collDecomp (hc : MatchCtxO c) {τ : Subst} {vars : List Srt} (hτ : c.WellSorted vars τ)
    (K : CollKind) : ∀ (N : Nat) (p : Term) {parts : List Part} {v : GroundTerm} {sp s : Srt}
    {items : List (List GroundTerm)},
    flatten c K N p = some parts → Part.hasOther parts = false → PatVal c τ p v →
    sortOfTerm c.patCtxNF vars p = some sp → content v = some (K, s, items) →
    ∃ ch : List (Part × List (List GroundTerm)), ch.map (·.1) = parts ∧
      (∀ x ∈ ch, Takes c τ vars K x) ∧ Comb K items (ch.flatMap (·.2))
  | 0, _, _, _, _, _, _, h, _, _, _, _ => by simp [flatten] at h
  | N + 1, .var j, parts, v, sp, s, items, h, _, hp, _, hv => by
    simp only [flatten, Option.some.injEq] at h
    subst h
    refine ⟨[(.frame j, items)], rfl, fun x hx => ?_, by simpa using comb_refl K items⟩
    rw [List.mem_singleton.mp hx]
    exact ⟨v, s, PatVal.var_inv hp, hv⟩
  | N + 1, .dv _ _, _, _, _, _, _, h, ho, _, _, _ => by
    simp only [flatten, Option.some.injEq] at h; subst h; simp [Part.hasOther] at ho
  | N + 1, .inj _ _ _, _, _, _, _, _, h, ho, _, _, _ => by
    simp only [flatten, Option.some.injEq] at h; subst h; simp [Part.hasOther] at ho
  | N + 1, .as _ _, _, _, _, _, _, h, ho, _, _, _ => by
    simp only [flatten, Option.some.injEq] at h; subst h; simp [Part.hasOther] at ho
  | N + 1, .app g ps, parts, v, sp, s, items, h, ho, hp, ht, hv => by
    simp only [flatten] at h
    split at h
    · rename_i K' r hr
      split at h
      · rename_i hK
        have hK : K = K' := (beq_iff_eq.mp hK).symm
        subst hK
        obtain ⟨vs, hvs, hb⟩ := roleVal hc hr hp
        obtain ⟨k, -, hargs, rfl⟩ := sortOfTerm_app.mp ht
        split at h
        · cases h
          obtain ⟨-, s', hv'⟩ := hb
          rw [hv] at hv'
          simp only [Option.some.injEq, Prod.mk.injEq] at hv'
          obtain ⟨-, -, rfl⟩ := hv'
          exact ⟨[], rfl, fun x hx => by simp at hx, by simpa using comb_refl K []⟩
        · cases h
          obtain ⟨s', hv'⟩ := hb
          rw [hv] at hv'
          simp only [Option.some.injEq, Prod.mk.injEq] at hv'
          obtain ⟨-, -, rfl⟩ := hv'
          refine ⟨[(.elem ps, [vs])], rfl, fun x hx => ?_, by simpa using comb_refl K [vs]⟩
          rw [List.mem_singleton.mp hx]
          exact ⟨vs, rfl, hvs, _, hargs⟩
        · rename_i a b
          simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
            Option.some.injEq] at h
          obtain ⟨pa, ha, pb, hpb, rfl⟩ := h
          rw [hasOther_append, Bool.or_eq_false_iff] at ho
          have hsv := Det.patVal_sortedAllO hc hτ hp ht
          have hss := Det.patVals_sortedAllO hc hτ hvs hargs
          obtain ⟨va, vb, sa, sb, ia, ib, rfl, hca, hcb, hcomb⟩ := concat_split hb hv hsv hss
          obtain ⟨_, _, he0, hpa, hps⟩ := PatVals.cons_inv hvs
          simp only [List.cons.injEq] at he0
          obtain ⟨rfl, rfl⟩ := he0
          obtain ⟨_, _, he, hpb', -⟩ := PatVals.cons_inv hps
          simp only [List.cons.injEq] at he
          obtain ⟨rfl, -⟩ := he
          obtain ⟨ta, _, hta, hrest, -⟩ := sortsOfTerms_cons.mp hargs
          obtain ⟨tb, _, htb, -, -⟩ := sortsOfTerms_cons.mp hrest
          obtain ⟨cha, hma, hta', hca'⟩ := collDecomp hc hτ K N a ha ho.1 hpa hta hca
          obtain ⟨chb, hmb, htb', hcb'⟩ := collDecomp hc hτ K N b hpb ho.2 hpb' htb hcb
          refine ⟨cha ++ chb, by rw [List.map_append, hma, hmb], fun x hx => ?_, ?_⟩
          · rcases List.mem_append.mp hx with hx | hx
            · exact hta' x hx
            · exact htb' x hx
          · rw [List.flatMap_append]
            exact comb_trans hcomb (comb_append hca' hcb')
        · cases h
      · cases h; simp [Part.hasOther] at ho
    · cases h; simp [Part.hasOther] at ho

/-! ## The candidates' completeness -/

/-- A collection rebuilt from its own items and sort is itself. -/
theorem build_content {w : GroundTerm} {K : CollKind} {s : Srt} {its : List (List GroundTerm)}
    (h : content w = some (K, s, its)) : build K s its = w := by
  cases w with
  | map s0 es =>
    simp only [content, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    simp only [build, List.filterMap_map]
    congr 1
    induction es with
    | nil => rfl
    | cons e es ih => simp [pairOf, ih]
  | set s0 es =>
    simp only [content, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    simp only [build, List.filterMap_map]
    congr 1
    induction es with
    | nil => rfl
    | cons e es ih => simp [oneOf, ih]
  | list s0 es =>
    simp only [content, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    simp only [build, List.filterMap_map]
    congr 1
    induction es with
    | nil => rfl
    | cons e es ih => simp [oneOf, ih]
  | _ => simp [content] at h

theorem perm_eraseIdx {α : Type} {l : List α} {j : Nat} (hj : j < l.length) :
    l.Perm (l[j] :: l.eraseIdx j) := by
  rw [List.eraseIdx_eq_take_drop_succ]
  have hl : l = l.take j ++ l[j] :: l.drop (j + 1) := by
    rw [List.getElem_cons_drop, List.take_append_drop]
  conv => lhs; rw [hl]
  exact List.perm_middle

/-- The fuel `pickAll` needs: each element its arguments' (`cmatchL`'s) and two. -/
def pickFuel : List (List Term) → Nat
  | [] => 1
  | qs :: E => 8 * termSizeList qs + 2 + pickFuel E

/-- The fuel `matchSeq` needs: an element as in `pickFuel`, a frame one. -/
def seqFuel : List Part → Nat
  | [] => 1
  | .elem qs :: ps => 8 * termSizeList qs + 2 + seqFuel ps
  | .frame _ :: ps => 1 + seqFuel ps
  | .other _ :: ps => 1 + seqFuel ps

theorem pickFuel_le : ∀ (ps : List Part), pickFuel (Part.elems ps) ≤ seqFuel ps
  | [] => by simp [pickFuel, seqFuel, Part.elems]
  | .elem _ :: ps => by simp only [Part.elems, pickFuel, seqFuel]; have := pickFuel_le ps; omega
  | .frame _ :: ps => by simp only [Part.elems, seqFuel]; have := pickFuel_le ps; omega
  | .other _ :: ps => by simp only [Part.elems, seqFuel]; have := pickFuel_le ps; omega

theorem seqFuel_bound : ∀ (ps : List Part), seqFuel ps + 6 * ps.length ≤ 8 * partsSize ps + 1
  | [] => by simp [seqFuel, partsSize]
  | .elem _ :: ps => by
    simp only [seqFuel, partsSize, List.length_cons]; have := seqFuel_bound ps; omega
  | .frame _ :: ps => by
    simp only [seqFuel, partsSize, List.length_cons]; have := seqFuel_bound ps; omega
  | .other q :: ps => by
    simp only [seqFuel, partsSize, List.length_cons]
    have := seqFuel_bound ps; have := termSize_pos q; omega

theorem pickFuel_pos : ∀ (E : List (List Term)), 1 ≤ pickFuel E
  | [] => Nat.le_refl _
  | _ :: E => by simp only [pickFuel]; omega

theorem seqFuel_pos : ∀ (ps : List Part), 1 ≤ seqFuel ps
  | [] => Nat.le_refl _
  | .elem _ :: _ => by simp only [seqFuel]; omega
  | .frame _ :: _ => by simp only [seqFuel]; omega
  | .other _ :: _ => by simp only [seqFuel]; omega

/-- Parts without a frame take one item each. -/
theorem flat_len {τ : Subst} {vars : List Srt} {K : CollKind} :
    ∀ (ch : List (Part × List (List GroundTerm))), (∀ x ∈ ch, Takes c τ vars K x) →
    Part.frames (ch.map (·.1)) = [] → (ch.flatMap (·.2)).length = Part.countElems (ch.map (·.1))
  | [], _, _ => rfl
  | (.elem qs, its) :: ch, ht, hf => by
    obtain ⟨it, rfl, -⟩ := ht _ (List.mem_cons_self ..)
    have := flat_len ch (fun x hx => ht x (List.mem_cons_of_mem _ hx)) (by simpa [Part.frames] using hf)
    simp only [List.flatMap_cons, List.length_append, List.map_cons,
      Part.countElems, Part.elems, List.length_cons, List.length_nil] at this ⊢
    omega
  | (.frame _, _) :: _, _, hf => by simp [Part.frames] at hf
  | (.other _, _) :: _, ht, _ => (ht _ (List.mem_cons_self ..)).elim

/-- The parts' items, as the elements' items in order and the frames' items. -/
theorem split_chunks {τ : Subst} {vars : List Srt} {K : CollKind} :
    ∀ (ch : List (Part × List (List GroundTerm))), (∀ x ∈ ch, Takes c τ vars K x) →
    ∃ (EP : List (List Term × List GroundTerm)) (Fr : List (Nat × List (List GroundTerm))),
      EP.map (·.1) = Part.elems (ch.map (·.1)) ∧
      (∀ x ∈ EP, PatVals c τ x.1 x.2 ∧ ∃ ss, sortsOfTerms c.patCtxNF vars x.1 = some ss) ∧
      Fr.map (·.1) = Part.frames (ch.map (·.1)) ∧
      (∀ x ∈ Fr, ∃ w s, τ.lookup x.1 = some w ∧ content w = some (K, s, x.2)) ∧
      (ch.flatMap (·.2)).Perm (EP.map (·.2) ++ Fr.flatMap (·.2))
  | [], _ => ⟨[], [], rfl, by simp, rfl, by simp, by simp⟩
  | (.elem qs, its) :: ch, ht => by
    obtain ⟨it, rfl, hpv, hss⟩ := ht _ (List.mem_cons_self ..)
    obtain ⟨EP, Fr, h1, h2, h3, h4, h5⟩ := split_chunks ch (fun x hx => ht x (List.mem_cons_of_mem _ hx))
    refine ⟨(qs, it) :: EP, Fr, by simp [h1, Part.elems], fun x hx => ?_, by simp [h3, Part.frames],
      h4, ?_⟩
    · rcases List.mem_cons.mp hx with rfl | hx
      · exact ⟨hpv, hss⟩
      · exact h2 x hx
    · simp only [List.flatMap_cons, List.map_cons, List.cons_append]
      exact h5.cons it
  | (.frame j, its) :: ch, ht => by
    obtain ⟨w, s, hl, hw⟩ := ht _ (List.mem_cons_self ..)
    obtain ⟨EP, Fr, h1, h2, h3, h4, h5⟩ := split_chunks ch (fun x hx => ht x (List.mem_cons_of_mem _ hx))
    refine ⟨EP, (j, its) :: Fr, by simp [h1, Part.elems], h2, by simp [h3, Part.frames],
      fun x hx => ?_, ?_⟩
    · rcases List.mem_cons.mp hx with rfl | hx
      · exact ⟨w, s, hl, hw⟩
      · exact h4 x hx
    · simp only [List.flatMap_cons]
      refine (h5.append_left its).trans ?_
      rw [← List.append_assoc, ← List.append_assoc]
      exact List.perm_append_comm.append_right _
  | (.other _, _) :: _, ht => (ht _ (List.mem_cons_self ..)).elim

/-- The candidates of a map or a set pattern: the elements choose items, the frame takes the rest. -/
def pickBranch (c : Semantics) (vars : List Srt) (n : Nat) (σ : Subst) (K : CollKind)
    (parts : List Part) (items : List (List GroundTerm)) : List Subst :=
  match Part.frames parts with
  | [] => (pickAll c vars n σ (Part.elems parts) items).filterMap fun (σ', rest) =>
      if rest.isEmpty then some σ' else none
  | [j] => match vars[j]? with
    | some s => (pickAll c vars n σ (Part.elems parts) items).flatMap fun (σ', rest) =>
        (bindVar σ' j (build K s rest)).toList
    | none => []
  | _ => []

theorem cmatchP_coll {vars : List Srt} {n : Nat} {σ : Subst} {f : Sym} {ps : List Term}
    {v : GroundTerm} {K : CollKind} {r : Role} {sv : Srt} {items : List (List GroundTerm)}
    {parts : List Part} (hct : c.isCtor f = false) (hr : role c f = some (K, r))
    (hv : content v = some (K, sv, items))
    (hfl : flatten c K (termSize (.app f ps)) (.app f ps) = some parts)
    (hno : Part.hasOther parts = false) :
    cmatchP c vars (n + 1) σ (.app f ps) v =
      if K = .list then matchSeq c vars n σ parts items else pickBranch c vars n σ K parts items := by
  simp only [cmatchP, hct, isOvl_of_role hr, Bool.false_eq_true, ↓reduceIte, hr, hv, beq_self_eq_true, hfl, hno]
  cases K <;> rfl

theorem matchSeq_elem {vars : List Srt} (n : Nat) (σ : Subst) (qs : List Term) (ps : List Part)
    (it : List GroundTerm) (its : List (List GroundTerm)) :
    matchSeq c vars (n + 1) σ (.elem qs :: ps) (it :: its) =
      (cmatchL c vars n σ qs it).flatMap fun σ1 => matchSeq c vars n σ1 ps its := by
  rw [matchSeq]

theorem matchSeq_frame {vars : List Srt} (n : Nat) (σ : Subst) (j : Nat) (ps : List Part)
    (its : List (List GroundTerm)) (s : Srt) (hs : vars[j]? = some s) :
    matchSeq c vars (n + 1) σ (.frame j :: ps) its =
      (bindVar σ j (build .list s (its.take (its.length - Part.countElems ps)))).toList.flatMap
        fun σ1 => matchSeq c vars n σ1 ps (its.drop (its.length - Part.countElems ps)) := by
  rw [matchSeq]; simp only [hs]

/-- What the candidates read of an element: its arguments denote the item, are well sorted, and are
ready. -/
def ElemOK (c : Semantics) (τ : Subst) (vars : List Srt) (x : List Term × List GroundTerm) : Prop :=
  PatVals c τ x.1 x.2 ∧ (∃ ss, sortsOfTerms c.patCtxNF vars x.1 = some ss) ∧
    ∀ q ∈ x.1, ∃ m, readyP c vars m q = true

mutual
  /-- **The candidates reach every match**: from any σ below a well-sorted τ under which a ready,
  well-sorted pattern denotes the value, with enough fuel, the candidates include a substitution
  below τ, above σ, binding every variable of the pattern. -/
  theorem cmatchP_complete (hc : MatchCtxO c) {τ : Subst} {vars : List Srt}
      (hτ : c.WellSorted vars τ) : ∀ (n m : Nat) {σ : Subst} {p : Term} {v : GroundTerm} {s : Srt},
      8 * termSize p ≤ n → readyP c vars m p = true → PatVal c τ p v →
      sortOfTerm c.patCtxNF vars p = some s → Ext σ τ →
      ∃ σ' ∈ cmatchP c vars n σ p v, Ext σ' τ ∧ Ext σ σ' ∧ Binds σ' (varOccs p)
    | 0, _, _, p, _, _, hn, _, _, _, _ => by have := termSize_pos p; omega
    | n + 1, _, σ, .var i, v, _, _, _, hp, _, hx => by
      obtain ⟨σ', hb, hx', hx'', hl⟩ := bindVar_complete hx (PatVal.var_inv hp)
      refine ⟨σ', by simp [cmatchP, hb], hx', hx'', fun j hj => ?_⟩
      simp only [varOccs, List.mem_singleton] at hj
      exact ⟨v, hj ▸ hl⟩
    | n + 1, _, σ, .dv s l, v, _, _, _, hp, _, hx => by
      cases hp
      exact ⟨σ, by simp [cmatchP], hx, Ext.refl _, fun j hj => by simp [varOccs] at hj⟩
    | n + 1, m, σ, .inj a b p, v, s, hn, hr, hp, ht, hx => by
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := by
        cases m with
        | zero => simp [readyP] at hr
        | succ m' => exact ⟨m', rfl⟩
      simp only [readyP] at hr
      obtain ⟨-, ht', rfl⟩ := sortOfTerm_inj.mp ht
      have hn' : 8 * termSize p ≤ n := by simp [termSize] at hn; omega
      cases hp with
      | inj hw =>
        rename_i w
        obtain ⟨σ', hm, hx', hx'', hb⟩ := cmatchP_complete hc hτ n m' hn' hr hw ht' hx
        have hsw := Det.patVal_sortedAllO hc hτ hw ht'
        refine ⟨σ', ?_, hx', hx'', by simpa [varOccs] using hb⟩
        cases w with
        | inj a' y u =>
          obtain ⟨-, -, -, rfl⟩ := sortOf_inj.mp hsw
          simp only [cmatchP, injNormal, beq_self_eq_true, ↓reduceIte]
          split <;> simp [hm]
        | ctor _ _ => simp [cmatchP, injNormal, hm]
        | dv _ _ => simp [cmatchP, injNormal, hm]
        | map _ _ => simp [cmatchP, injNormal, hm]
        | set _ _ => simp [cmatchP, injNormal, hm]
        | list _ _ => simp [cmatchP, injNormal, hm]
    | n + 1, m, σ, .as p i, v, s, hn, hr, hp, ht, hx => by
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := by
        cases m with
        | zero => simp [readyP] at hr
        | succ m' => exact ⟨m', rfl⟩
      simp only [readyP] at hr
      obtain ⟨hp', hi⟩ := PatVal.as_inv hp
      have hn' : 8 * termSize p ≤ n := by simp [termSize] at hn; omega
      obtain ⟨σ1, hm, hx1, hx1', hb1⟩ := cmatchP_complete hc hτ n m' hn' hr hp' (sortOfTerm_as ht).2 hx
      obtain ⟨σ', hbv, hx', hx'', hl⟩ := bindVar_complete hx1 hi
      refine ⟨σ', ?_, hx', hx1'.trans hx'', fun j hj => ?_⟩
      · simp only [cmatchP, List.mem_filterMap]
        exact ⟨σ1, hm, hbv⟩
      · simp only [varOccs, List.mem_append, List.mem_singleton] at hj
        rcases hj with hj | rfl
        · exact Binds.mono hx'' hb1 j hj
        · exact ⟨v, hl⟩
    | n + 1, m, σ, .app f ps, v, s, hn, hr, hp, ht, hx => by
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := by
        cases m with
        | zero => simp [readyP] at hr
        | succ m' => exact ⟨m', rfl⟩
      by_cases hct : c.isCtor f = true
      · -- a constructor
        simp only [readyP, hct, ↓reduceIte, List.all_eq_true] at hr
        have hph : patternHooks.contains f = false := by
          cases h : patternHooks.contains f with
          | false => rfl
          | true => rw [hc.patHooks f (List.contains_iff_mem.mp h)] at hct; cases hct
        obtain ⟨-, vs, rfl, hs⟩ := PatVal.app_inv hph hp hct
        obtain ⟨k, -, hargs, rfl⟩ := sortOfTerm_app.mp ht
        have hn' : 8 * termSizeList ps + 1 ≤ n := by simp [termSize] at hn; omega
        obtain ⟨σ', hm, hx', hx'', hb⟩ :=
          cmatchL_complete hc hτ n hn' (fun q hq => ⟨m', hr q hq⟩) hs hargs hx
        exact ⟨σ', by simp [cmatchP, hct, hm], hx', hx'', by simpa [varOccs] using hb⟩
      · -- a collection pattern
        have hct' : c.isCtor f = false := by simpa using hct
        simp only [readyP, hct', Bool.false_eq_true, ↓reduceIte] at hr
        split at hr
        · rename_i K r hrole
          split at hr
          · rename_i parts hfl
            simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hr
            obtain ⟨⟨⟨hno, hfr1⟩, hfrv⟩, hel⟩ := hr
            obtain ⟨vs, hvs, hb⟩ := roleVal hc hrole hp
            obtain ⟨sv, items, hcv⟩ := builds_content hb
            obtain ⟨ch, hmap, htk, hcomb⟩ := collDecomp hc hτ K _ _ hfl hno hp ht hcv
            have hsz := flatten_size K _ _ hfl
            have hvars := flatten_vars K _ _ hfl hno
            have hsv := Det.patVal_sortedAllO hc hτ hp ht
            have hfuel : seqFuel parts ≤ n := by
              have h1 := seqFuel_bound parts
              have h2 := termSize_pos (.app f ps)
              rcases hpe : parts with _ | ⟨x, xs⟩
              · simp only [seqFuel]; omega
              · rw [hpe] at h1 hsz
                simp only [List.length_cons] at h1
                omega
            have hel' : ∀ qs ∈ Part.elems parts, ∀ q ∈ qs, ∃ m, readyP c vars m q = true :=
              fun qs hq q hqs => ⟨m', List.all_eq_true.mp (List.all_eq_true.mp hel qs hq) q hqs⟩
            rw [cmatchP_coll hct' hrole hcv hfl hno]
            by_cases hKl : K = .list
            · subst hKl
              rw [if_pos rfl]
              have hit : items = ch.flatMap (·.2) := hcomb
              subst hit hmap
              obtain ⟨σ', hm, hx', hx'', hbf, hbe⟩ :=
                matchSeq_complete hc hτ n hfuel htk hel' hfr1 hfrv hx
              exact ⟨σ', hm, hx', hx'', fun i hi => by
                rcases hvars i hi with h1 | ⟨qs, hq, hi'⟩
                · exact hbf i h1
                · exact hbe qs hq i hi'⟩
            · rw [if_neg hKl]
              obtain ⟨EP, Fr, hEP, hEPok, hFr, hFrok, hperm⟩ := split_chunks ch htk
              rw [hmap] at hEP hFr
              have hperm' : items.Perm (EP.map (·.2) ++ Fr.flatMap (·.2)) :=
                (comb_perm hcomb).trans hperm
              have hpf : pickFuel (EP.map (·.1)) ≤ n := by
                rw [hEP]; exact Nat.le_trans (pickFuel_le parts) hfuel
              have hEPok' : ∀ x ∈ EP, ElemOK c τ vars x := fun x hx =>
                ⟨(hEPok x hx).1, (hEPok x hx).2,
                  hel' x.1 (by rw [← hEP]; exact List.mem_map_of_mem hx)⟩
              obtain ⟨σ1, rest, hpa, hx1, hx1', hb1, hsub, hrp⟩ :=
                pickAll_complete hc hτ n hpf hEPok' hperm' hx
              rw [hEP] at hpa
              have hbE : ∀ qs ∈ Part.elems parts, Binds σ1 (varOccsList qs) := fun qs hq => by
                rw [← hEP] at hq
                obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hq
                exact hb1 x hx
              unfold pickBranch
              rcases hfrs : Part.frames parts with _ | ⟨j, _ | ⟨j', fs⟩⟩
              · -- no frame: the elements take every item
                rw [hfrs] at hFr
                have hFr0 : Fr = [] := List.map_eq_nil_iff.mp hFr
                subst hFr0
                have hr0 : rest = [] := (by simpa using hrp : rest.Perm []).eq_nil
                subst hr0
                refine ⟨σ1, List.mem_filterMap.mpr ⟨(σ1, []), hpa, by simp⟩, hx1, hx1', fun i hi => ?_⟩
                rcases hvars i hi with h1 | ⟨qs, hq, hi'⟩
                · rw [hfrs] at h1; cases h1
                · exact hbE qs hq i hi'
              · -- one frame: it takes the rest
                rw [hfrs] at hFr hfrv
                obtain ⟨⟨j0, its⟩, rfl, hj0⟩ : ∃ x, Fr = [x] ∧ x.1 = j := by
                  match Fr, hFr with
                  | [x], h => exact ⟨x, rfl, by simpa using h⟩
                simp only at hj0
                subst hj0
                obtain ⟨w, sw, hlw, hcw⟩ := hFrok _ (List.mem_singleton_self _)
                simp only [List.all_cons, List.all_nil, Bool.and_true, Option.isSome_iff_exists] at hfrv
                obtain ⟨s0, hs0⟩ := hfrv
                obtain ⟨w', hlw', hsw'⟩ := hτ j0 s0 hs0
                rw [hlw] at hlw'
                cases hlw'
                obtain ⟨rfl, hcanw⟩ := content_canon hcw hsw'
                obtain ⟨-, hcanv⟩ := content_canon hcv hsv
                have hrp' : rest.Perm its := by simpa using hrp
                have hre : rest = its :=
                  canonI_perm hKl (canonI_sublist hcanv hsub) hcanw hrp'
                subst hre
                obtain ⟨σ', hbv, hx', hx'', hl'⟩ := bindVar_complete hx1 hlw
                refine ⟨σ', ?_, hx', hx1'.trans hx'', fun i hi => ?_⟩
                · simp only [hs0]
                  exact List.mem_flatMap.mpr ⟨(σ1, rest), hpa, by simp [build_content hcw, hbv]⟩
                · rcases hvars i hi with h1 | ⟨qs, hq, hi'⟩
                  · rw [hfrs] at h1
                    rw [List.mem_singleton.mp h1]
                    exact ⟨w, hl'⟩
                  · exact Binds.mono hx'' (hbE qs hq) i hi'
              · rw [hfrs] at hfr1; simp at hfr1
          · cases hr
        · -- an overloading symbol: its arguments are read off the value
          simp only [Bool.and_eq_true, List.all_eq_true] at hr
          obtain ⟨ho, hr⟩ := hr
          obtain ⟨vs, hs, hv⟩ : ∃ vs, PatVals c τ ps vs ∧ c.norm f vs = v := by
            generalize ht' : Term.app f ps = t at hp
            cases hp with
            | ctor hk _ => cases ht'; rw [hk] at hct'; cases hct'
            | hook hp' _ _ => cases ht'; rw [c.isOvl_of_patternHook hp'] at ho; cases ho
            | coll _ hcp _ _ => cases ht'; rw [c.isOvl_of_collPat hcp] at ho; cases ho
            | ovl _ _ hs hv => cases ht'; exact ⟨_, hs, hv⟩
            | _ => cases ht'
          obtain ⟨k, hk', hargs, rfl⟩ := sortOfTerm_app.mp ht
          obtain ⟨o, hlo, rfl⟩ := Det.patCtxNF_ovl_lookup ho hk'
          have hoa : ovlArgs c f v = some vs := by
            rw [← hv]; exact ovlArgs_complete hc.ovlHyp hlo (Det.patVals_sortedAllO hc hτ hs hargs)
              (OvlLaws.fnCover_none_of_not_fnOvl (patCtxNF_lookup.mp hk').2 _)
          have hn' : 8 * termSizeList ps + 1 ≤ n := by simp [termSize] at hn; omega
          obtain ⟨σ', hm, hx', hx'', hb⟩ :=
            cmatchL_complete hc hτ n hn' (fun q hq => ⟨m', hr q hq⟩) hs hargs hx
          exact ⟨σ', by simp [cmatchP, hct', ho, hoa, hm], hx', hx'', by simpa [varOccs] using hb⟩
  theorem cmatchL_complete (hc : MatchCtxO c) {τ : Subst} {vars : List Srt}
      (hτ : c.WellSorted vars τ) : ∀ (n : Nat) {σ : Subst} {ps : List Term} {vs : List GroundTerm}
      {ss : List Srt}, 8 * termSizeList ps + 1 ≤ n → (∀ q ∈ ps, ∃ m, readyP c vars m q = true) →
      PatVals c τ ps vs → sortsOfTerms c.patCtxNF vars ps = some ss → Ext σ τ →
      ∃ σ' ∈ cmatchL c vars n σ ps vs, Ext σ' τ ∧ Ext σ σ' ∧ Binds σ' (varOccsList ps)
    | 0, _, _, _, _, hn, _, _, _, _ => by omega
    | n + 1, σ, [], vs, _, _, _, hp, _, hx => by
      rw [PatVals.nil_inv hp]
      exact ⟨σ, by simp [cmatchL], hx, Ext.refl _, fun j hj => by simp [varOccsList] at hj⟩
    | n + 1, σ, p :: ps, vs, ss, hn, hr, hp, ht, hx => by
      obtain ⟨v, vs', rfl, hp1, hps⟩ := PatVals.cons_inv hp
      obtain ⟨s, ss', h1, h2, rfl⟩ := sortsOfTerms_cons.mp ht
      have hsz := termSize_pos p
      have hn1 : 8 * termSize p ≤ n := by simp [termSizeList] at hn; omega
      have hn2 : 8 * termSizeList ps + 1 ≤ n := by simp [termSizeList] at hn; omega
      obtain ⟨m, hm⟩ := hr p (List.mem_cons_self ..)
      obtain ⟨σ1, hm1, hx1, hx1', hb1⟩ := cmatchP_complete hc hτ n m hn1 hm hp1 h1 hx
      obtain ⟨σ', hm2, hx', hx'', hb2⟩ :=
        cmatchL_complete hc hτ n hn2 (fun q hq => hr q (List.mem_cons_of_mem _ hq)) hps h2 hx1
      refine ⟨σ', ?_, hx', hx1'.trans hx'', fun j hj => ?_⟩
      · simp only [cmatchL, List.mem_flatMap]
        exact ⟨σ1, hm1, hm2⟩
      · simp only [varOccsList, List.mem_append] at hj
        rcases hj with hj | hj
        · exact Binds.mono hx'' hb1 j hj
        · exact hb2 j hj
  theorem pickAll_complete (hc : MatchCtxO c) {τ : Subst} {vars : List Srt}
      (hτ : c.WellSorted vars τ) : ∀ (n : Nat) {σ : Subst} {EP : List (List Term × List GroundTerm)}
      {items R : List (List GroundTerm)},
      pickFuel (EP.map (·.1)) ≤ n → (∀ x ∈ EP, ElemOK c τ vars x) →
      items.Perm (EP.map (·.2) ++ R) → Ext σ τ →
      ∃ σ' rest, (σ', rest) ∈ pickAll c vars n σ (EP.map (·.1)) items ∧ Ext σ' τ ∧ Ext σ σ' ∧
        (∀ x ∈ EP, Binds σ' (varOccsList x.1)) ∧ rest.Sublist items ∧ rest.Perm R
    | 0, _, EP, _, _, hn, _, _, _ => by have := pickFuel_pos (EP.map (·.1)); omega
    | n + 1, σ, [], items, R, _, _, hperm, hx =>
      ⟨σ, items, by simp [pickAll], hx, Ext.refl _, by simp, List.Sublist.refl _, by simpa using hperm⟩
    | n + 1, σ, (qs, it) :: EP, items, R, hn, hok, hperm, hx => by
      have hit : it ∈ items := hperm.mem_iff.mpr (List.mem_append_left _ (List.mem_cons_self ..))
      obtain ⟨j, hj, hjx⟩ := List.getElem_of_mem hit
      have hpj := perm_eraseIdx hj
      rw [hjx] at hpj
      have hperm' : (items.eraseIdx j).Perm (EP.map (·.2) ++ R) := by
        have := hpj.symm.trans hperm
        simp only [List.map_cons, List.cons_append] at this
        exact this.cons_inv
      obtain ⟨hpv, ⟨ss, hss⟩, hrd⟩ := hok (qs, it) (List.mem_cons_self ..)
      simp only [List.map_cons, pickFuel] at hn
      have hn1 : 8 * termSizeList qs + 1 ≤ n := by omega
      have hn2 : pickFuel (EP.map (·.1)) ≤ n := by omega
      obtain ⟨σ1, hm1, hx1, hx1', hb1⟩ := cmatchL_complete hc hτ n hn1 hrd hpv hss hx
      obtain ⟨σ', rest, hpa, hx', hx'', hb', hsub, hrp⟩ :=
        pickAll_complete hc hτ n hn2 (fun x hx => hok x (List.mem_cons_of_mem _ hx)) hperm' hx1
      refine ⟨σ', rest, ?_, hx', hx1'.trans hx'', fun x hx => ?_,
        hsub.trans (List.eraseIdx_sublist _ _), hrp⟩
      · simp only [List.map_cons, pickAll, List.mem_flatMap, List.mem_range]
        refine ⟨j, hj, ?_⟩
        rw [List.getElem?_eq_getElem hj, hjx]
        exact List.mem_flatMap.mpr ⟨σ1, hm1, hpa⟩
      · rcases List.mem_cons.mp hx with rfl | hx
        · exact Binds.mono hx'' hb1
        · exact hb' x hx
  theorem matchSeq_complete (hc : MatchCtxO c) {τ : Subst} {vars : List Srt}
      (hτ : c.WellSorted vars τ) : ∀ (n : Nat) {σ : Subst} {ch : List (Part × List (List GroundTerm))},
      seqFuel (ch.map (·.1)) ≤ n → (∀ x ∈ ch, Takes c τ vars .list x) →
      (∀ qs ∈ Part.elems (ch.map (·.1)), ∀ q ∈ qs, ∃ m, readyP c vars m q = true) →
      (Part.frames (ch.map (·.1))).length ≤ 1 →
      (Part.frames (ch.map (·.1))).all (fun j => (vars[j]?).isSome) = true → Ext σ τ →
      ∃ σ' ∈ matchSeq c vars n σ (ch.map (·.1)) (ch.flatMap (·.2)), Ext σ' τ ∧ Ext σ σ' ∧
        (∀ j ∈ Part.frames (ch.map (·.1)), ∃ w, σ'.lookup j = some w) ∧
        (∀ qs ∈ Part.elems (ch.map (·.1)), Binds σ' (varOccsList qs))
    | 0, _, ch, hn, _, _, _, _, _ => by have := seqFuel_pos (ch.map (·.1)); omega
    | n + 1, σ, [], _, _, _, _, _, hx =>
      ⟨σ, by simp only [List.map_nil, List.flatMap_nil]; exact List.mem_singleton.mpr rfl, hx,
        Ext.refl _, by simp [Part.frames], by simp [Part.elems]⟩
    | n + 1, σ, (.elem qs, its) :: ch, hn, htk, hrd, hfr1, hfrv, hx => by
      obtain ⟨it, rfl, hpv, ss, hss⟩ := htk _ (List.mem_cons_self ..)
      simp only [List.map_cons, seqFuel] at hn
      simp only [List.map_cons, Part.frames] at hfr1 hfrv
      have hn1 : 8 * termSizeList qs + 1 ≤ n := by omega
      have hn2 : seqFuel (ch.map (·.1)) ≤ n := by omega
      have hrd1 : ∀ q ∈ qs, ∃ m, readyP c vars m q = true :=
        hrd qs (by simp only [List.map_cons, Part.elems]; exact List.mem_cons_self ..)
      have hrd2 : ∀ qs' ∈ Part.elems (ch.map (·.1)), ∀ q ∈ qs', ∃ m, readyP c vars m q = true :=
        fun qs' hq => hrd qs' (by
          simp only [List.map_cons, Part.elems]; exact List.mem_cons_of_mem _ hq)
      obtain ⟨σ1, hm1, hx1, hx1', hb1⟩ := cmatchL_complete hc hτ n hn1 hrd1 hpv hss hx
      obtain ⟨σ', hm, hx', hx'', hbf, hbe⟩ :=
        matchSeq_complete hc hτ n hn2 (fun x hx => htk x (List.mem_cons_of_mem _ hx)) hrd2 hfr1
          hfrv hx1
      refine ⟨σ', ?_, hx', hx1'.trans hx'', fun j hj => hbf j (by
        simp only [List.map_cons, Part.frames] at hj; exact hj), fun qs' hq => ?_⟩
      · simp only [List.map_cons, List.flatMap_cons, List.singleton_append]
        rw [matchSeq_elem]
        exact List.mem_flatMap.mpr ⟨σ1, hm1, hm⟩
      · simp only [List.map_cons, Part.elems, List.mem_cons] at hq
        rcases hq with rfl | hq
        · exact Binds.mono hx'' hb1
        · exact hbe qs' hq
    | n + 1, σ, (.frame j, its) :: ch, hn, htk, hrd, hfr1, hfrv, hx => by
      obtain ⟨w, sw, hlw, hcw⟩ := htk _ (List.mem_cons_self ..)
      simp only [List.map_cons, seqFuel] at hn
      simp only [List.map_cons, Part.frames, List.length_cons, List.all_cons, Bool.and_eq_true,
        Option.isSome_iff_exists] at hfr1 hfrv
      have hfr0 : Part.frames (ch.map (·.1)) = [] := List.length_eq_zero_iff.mp (by omega)
      obtain ⟨⟨s0, hs0⟩, -⟩ := hfrv
      obtain ⟨w', hlw', hsw'⟩ := hτ j s0 hs0
      rw [hlw] at hlw'
      cases hlw'
      obtain ⟨rfl, -⟩ := content_canon hcw hsw'
      have hlen := flat_len ch (fun x hx => htk x (List.mem_cons_of_mem _ hx)) hfr0
      have hk : (its ++ ch.flatMap (·.2)).length - Part.countElems (ch.map (·.1)) = its.length := by
        rw [List.length_append, hlen]; omega
      obtain ⟨σ1, hbv, hx1, hx1', hl1⟩ := bindVar_complete hx hlw
      have hrd2 : ∀ qs' ∈ Part.elems (ch.map (·.1)), ∀ q ∈ qs', ∃ m, readyP c vars m q = true :=
        fun qs' hq => hrd qs' (by simp only [List.map_cons, Part.elems]; exact hq)
      obtain ⟨σ', hm, hx', hx'', hbf, hbe⟩ :=
        matchSeq_complete hc hτ n (by omega) (fun x hx => htk x (List.mem_cons_of_mem _ hx)) hrd2
          (by rw [hfr0]; simp) (by rw [hfr0]; rfl) hx1
      refine ⟨σ', ?_, hx', hx1'.trans hx'', fun j' hj' => ?_, fun qs hq => ?_⟩
      · simp only [List.map_cons, List.flatMap_cons]
        rw [matchSeq_frame _ _ _ _ _ _ hs0, hk, List.take_left' rfl, List.drop_left' rfl,
          build_content hcw, hbv]
        exact List.mem_flatMap.mpr ⟨σ1, by simp, hm⟩
      · simp only [List.map_cons, Part.frames, hfr0, List.mem_singleton] at hj'
        subst hj'
        exact ⟨w, hx'' _ _ hl1⟩
      · exact hbe qs (by simp only [List.map_cons, Part.elems] at hq; exact hq)
    | n + 1, _, (.other _, _) :: _, _, htk, _, _, _, _ => (htk _ (List.mem_cons_self ..)).elim
end

/-- **The matcher is complete**: every well-sorted τ under which ready, well-sorted patterns that
bind every variable denote the values agrees, on the variables, with a substitution `cmatch`
lists. -/
theorem cmatch_complete (hc : MatchCtxO c) {vars : List Srt} {τ : Subst} {ps : List Term}
    {vs : List GroundTerm} {ss : List Srt} (hτ : c.WellSorted vars τ) (hpv : PatVals c τ ps vs)
    (hr : readyL c vars ps = true) (hb : binds vars.length (varOccsList ps) = true)
    (hss : sortsOfTerms c.patCtxNF vars ps = some ss) :
    ∃ σ₀ ∈ cmatch c vars ps vs, ∀ i < vars.length, σ₀.lookup i = τ.lookup i := by
  unfold readyL at hr
  obtain ⟨σ', hm, hx', -, hb'⟩ := cmatchL_complete hc hτ (cfuel ps) (σ := [])
    (by unfold cfuel; omega) (fun q hq => ⟨_, List.all_eq_true.mp hr q hq⟩) hpv hss
    (fun _ _ h => by simp at h)
  have hcov : ∀ i < vars.length, i ∈ varOccsList ps := fun i hi => by
    unfold binds at hb
    exact List.contains_iff_mem.mp (List.all_eq_true.mp hb i (List.mem_range.mpr hi))
  have hag : ∀ i ∈ varOccsList ps, σ'.lookup i = τ.lookup i := fun i hi => by
    obtain ⟨w, hw⟩ := hb' i hi
    rw [hw, hx' i w hw]
  refine ⟨σ', ?_, fun i hi => hag i (hcov i hi)⟩
  unfold cmatch
  refine List.mem_filter.mpr ⟨hm, ?_⟩
  rw [wellSorted_iff.mpr (wellSorted_of_below hτ hx' hb' hcov), patEvals_congr ps hag,
    patEvals_complete hc hpv]
  simp [sameL_iff]

end KCore.CExec
