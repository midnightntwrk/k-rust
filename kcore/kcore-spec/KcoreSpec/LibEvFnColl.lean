/-
  KCore, checked layer: the equations of SET and LIST in the function form (`LibEv.FnEqn`) over
  interpreted hooked symbols, entailed at values in every semantics meeting `coreOK` whose Set and
  List values are collections (`shapesOK`), for every interpretation: none reaches a silent point.

  Each is stated once, over the registry's names: `X_ev` takes any axiom declaration of a text
  whose pattern is `X.patR`. The line numbers are those of domains.md in K 7.1.337.
  - `fnSetUnion` (749): `S1 |Set S2 => S1 (S2 -Set S1)`. The right side has a value at every two
    sets: `S1` and `S2 -Set S1` share no member.
  - `fnPushList` (955): `pushList(K, L1) => ListItem(K) L1`.

  Neither has an injection. The values of the collection symbols at collections are stated here
  (`fhv_setConcat`, `fhv_mapConcat`, …) for the collection laws too.
-/
import KcoreSpec.LibEvFnLib
import KcoreSpec.ModelColls

set_option autoImplicit false

namespace KCore

namespace LibEv

open ML Faithful

section
variable {c : Semantics}

/-- Off the keys of `silentTable`, Γ's value is `hook`'s. -/
theorem fq_hv_notKey {f : Sym} (h : silentKey f = false) (vs : List GroundTerm) : c.hv f vs = (hook f vs).join := by
  unfold Semantics.hv; rw [Semantics.hookRes_of_notKey h]

theorem fhv_setUnit : c.hv setUnit [] = some (.set Srt.set []) := hv_of_value rfl
theorem fhv_setUnion (s t : Srt) (a b : List GroundTerm) :
    c.hv setUnion [.set s a, .set t b] = some (.set Srt.set (unionS a b)) := hv_of_value rfl
theorem fhv_setDifference (s t : Srt) (a b : List GroundTerm) :
    c.hv setDifference [.set s a, .set t b] = some (.set Srt.set (a.filter (!memS · b))) := hv_of_value rfl
theorem fhv_setConcat (s t : Srt) (a b : List GroundTerm) :
    c.hv setConcat [.set s a, .set t b] = (concatS a b).map (.set Srt.set) := by
  rw [fq_hv_notKey (by decide +kernel), hook_setConcat]; rfl
theorem fhv_mapUnit : c.hv mapUnit [] = some (.map Srt.map []) := hv_of_value rfl
theorem fhv_mapConcat (s t : Srt) (a b : Entries) :
    c.hv mapConcat [.map s a, .map t b] = (union a b).map (.map Srt.map) := by
  rw [fq_hv_notKey (by decide +kernel), hook_mapConcat]; rfl
theorem fhv_listUnit : c.hv listUnit [] = some (.list Srt.list []) := hv_of_value rfl
theorem fhv_listElem (k : GroundTerm) : c.hv listElem [k] = some (.list Srt.list [k]) := hv_of_value rfl
theorem fhv_listPush (s : Srt) (k : GroundTerm) (a : List GroundTerm) :
    c.hv listPush [k, .list s a] = some (.list Srt.list (k :: a)) := hv_of_value rfl
theorem fhv_listConcat (s t : Srt) (a b : List GroundTerm) :
    c.hv listConcat [.list s a, .list t b] = some (.list Srt.list (a ++ b)) := hv_of_value rfl

end

section
variable {c : Semantics} (hs : c.shapesOK = true) {vars : Vars} {σ : Subst}
  (hσ : ∀ i p, vars[i]? = some p → ∃ v, σ.lookup i = some v ∧ c.sortOf v = some p.2)
include hs hσ

/-- A substitution of values of the variables' sorts gives a Set variable a set, its elements in
order. -/
theorem fq_set_at (i : Nat) {n : String} (hi : vars[i]? = some (n, Srt.set)) :
    ∃ es, σ.lookup i = some (.set Srt.set es) ∧ Set.Canon es := by
  obtain ⟨v, hv, hsv⟩ := hσ i _ hi
  obtain ⟨es, rfl⟩ := shape_set hs hsv
  exact ⟨es, hv, Set.canon_of_sortOf hsv⟩

/-- A substitution of values of the variables' sorts gives a Map variable a map, its keys in
order. -/
theorem fq_map_at (i : Nat) {n : String} (hi : vars[i]? = some (n, Srt.map)) :
    ∃ es, σ.lookup i = some (.map Srt.map es) ∧ Map.Canon es := by
  obtain ⟨v, hv, hsv⟩ := hσ i _ hi
  obtain ⟨es, rfl⟩ := shape_map hs hsv
  exact ⟨es, hv, Map.canon_of_sortOf hsv⟩

/-- A substitution of values of the variables' sorts gives a List variable a list. -/
theorem fq_list_at (i : Nat) {n : String} (hi : vars[i]? = some (n, Srt.list)) :
    ∃ es, σ.lookup i = some (.list Srt.list es) := by
  obtain ⟨v, hv, hsv⟩ := hσ i _ hi
  obtain ⟨es, rfl⟩ := shape_list hs hsv
  exact ⟨es, hv⟩

end

/-! ## 749: `S1 |Set S2 => S1 (S2 -Set S1)` -/

/-- `_Set_` of a set and the members of a second that are not the first's is their union. -/
theorem fq_concat_diff (a : List GroundTerm) {b : List GroundTerm} (hb : Set.Canon b) :
    concatS a (b.filter (!memS · a)) = some (unionS a b) :=
  Model.concatS_of (Set.filter_canon hb _) (Set.union_canon hb)
    (fun x hx hx' => ((Set.mem_diff x b a).mp hx').2 hx)
    (fun x => by
      rw [Set.mem_union, Set.mem_diff]
      by_cases hx : x ∈ a
      · simp [hx]
      · simp [hx])

def fnSetUnion : FnEqn :=
  ⟨[("VarS1", Srt.set), ("VarS2", Srt.set)], setUnion, [(Srt.set, .var 0, none), (Srt.set, .var 1, none)], Srt.set,
    none, .app setConcat [.var 0, .app setDifference [.var 1, .var 0]]⟩

theorem fnSetUnion_holds {c : Semantics} (hs : c.shapesOK = true) : fnSetUnion.Holds c := by
  intro σ hσ _ hm
  obtain ⟨a, ha, -⟩ := fq_set_at hs hσ 0 (n := "VarS1") rfl
  obtain ⟨b, hb, hcb⟩ := fq_set_at hs hσ 1 (n := "VarS2") rfl
  obtain ⟨h2, -, h3, -⟩ := hm
  rw [fq_val_var] at h2 h3
  have h2' : σ.lookup 2 = some (.set Srt.set a) := h2.symm.trans ha
  have h3' : σ.lookup 3 = some (.set Srt.set b) := h3.symm.trans hb
  fq_eval [fnSetUnion, h2', h3', ha, hb, fhv_setUnion, fhv_setDifference, fhv_setConcat, fq_concat_diff a hcb]

theorem fnSetUnion_ev {c : Semantics} (h : c.coreOK = true) (hs : c.shapesOK = true) (ad : KoreAML.AxiomDecl)
    (hp : ad.ax.pattern = fnSetUnion.patR) (hsv : ad.ax.sortVars = [KoreAML.Rv]) :
    EntailsAtValues c ad (KoreAML.trAxiom [] [] ad).pat :=
  FnEqn.entailed_reg h fnSetUnion (by decide) (by rfl) (fnSetUnion_holds hs) ad hp hsv

/-! ## 955: `pushList(K, L1) => ListItem(K) L1` -/

def fnPushList : FnEqn :=
  ⟨[("VarK", Srt.kitem), ("VarL1", Srt.list)], listPush, [(Srt.kitem, .var 0, none), (Srt.list, .var 1, none)],
    Srt.list, none, .app listConcat [.app listElem [.var 0], .var 1]⟩

theorem fnPushList_holds {c : Semantics} (hs : c.shapesOK = true) : fnPushList.Holds c := by
  intro σ hσ _ hm
  obtain ⟨k, hk, -⟩ := hσ 0 ("VarK", Srt.kitem) rfl
  obtain ⟨l, hl⟩ := fq_list_at hs hσ 1 (n := "VarL1") rfl
  obtain ⟨h2, -, h3, -⟩ := hm
  rw [fq_val_var] at h2 h3
  have h2' : σ.lookup 2 = some k := h2.symm.trans hk
  have h3' : σ.lookup 3 = some (.list Srt.list l) := h3.symm.trans hl
  fq_eval [fnPushList, h2', h3', hk, hl, fhv_listPush, fhv_listElem, fhv_listConcat, List.singleton_append]

theorem fnPushList_ev {c : Semantics} (h : c.coreOK = true) (hs : c.shapesOK = true) (ad : KoreAML.AxiomDecl)
    (hp : ad.ax.pattern = fnPushList.patR) (hsv : ad.ax.sortVars = [KoreAML.Rv]) :
    EntailsAtValues c ad (KoreAML.trAxiom [] [] ad).pat :=
  FnEqn.entailed_reg h fnPushList (by decide) (by rfl) (fnPushList_holds hs) ad hp hsv

end LibEv

end KCore
