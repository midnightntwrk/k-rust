/-
  KCore, checked layer: lemmas of the builtin library's MAP-KORE-SYMBOLIC and SET-KORE-SYMBOLIC
  modules (the `simplification` rules of domains.md 405 to 460 and 817 to 892 in K 7.1.337) whose
  sides are terms over element variables (`LibEv.Eqn`), entailed at values in every semantics
  meeting `coreOK` whose Map and Set values are collections (`shapesOK`), for every
  interpretation: none of them reaches a silent point.

  A map is the partial function `Map.find`, a set its membership (KcoreSpec/Collections.lean); a
  Map or Set variable at a value holds a canonical one (`fq_map_at`, `fq_set_at`). `_Map_` of a
  binding and a map has a value exactly where the map does not have the binding's key, and the
  sides below agree there and both have none elsewhere.

  Each is stated once, over the registry's names: `X_ev` takes any axiom declaration of a text
  whose pattern is `X.patR`. A rule written with `_` has the variable `_Gen0` in the text; a
  `comm` rule is the two sentences of its two argument orders.
  - `msUpdConcat` (417): `(K |-> _ M:Map) [ K <- V ] => (K |-> V M)`.
  - `msUpdFresh` (418): `M:Map [ K <- V ] => (K |-> V M) requires notBool (K in_keys(M))`.
  - `msUpdUpd` (419): `M:Map [ K <- _ ] [ K <- V ] => M [ K <- V ]`.
  - `msRemFresh` (426): `M:Map [ K <- undef ] => M requires notBool (K in_keys(M))`.
  - `msLookupUpd` (434): `(_MAP:Map [ K <- V1 ]) [ K ] => V1`.
  - `msLookupDefUpd` (439): `(_MAP:Map [ K <- V1 ]) [ K ] orDefault _ => V1`.
  - `msLookupDefUnit` (441): `.Map [ _ ] orDefault D => D`.
  - `msInKeysRem` (444): `K in_keys(_M [ K <- undef ]) => false`.
  - `msInKeysUpd` (445): `K in_keys(_M [ K <- _ ]) => true`.
  - `ssDiffUnit` (835): `S -Set .Set => S`; `ssUnitDiff` (836): `.Set -Set _ => .Set`.
  - `ssUnionUnit`, `ssUnitUnion` (854, `comm`): `S |Set .Set => S`, `.Set |Set S => S`.
  - `ssUnionSelf` (855): `S |Set S => S`.
  - `ssInterUnit`, `ssUnitInter` (864, `comm`): `intersectSet(_, .Set) => .Set` and the flip.
  - `ssInterSelf` (865): `intersectSet(S, S) => S`.
  - `ssInUnit` (876): `_E in .Set => false`.

  With an `ensures` (`LibEv.EqnE`, `EqnE.entailed`: the left side is the right side where the
  `ensures` is `true`, and has no value elsewhere; here it is `notBool (X in S)` or
  `notBool (K in_keys(M))`, exactly where the left side's `_Set_` or `_Map_` has a value):
  - `msRemConcat` (425), `msLookupConcat` (432), `msLookupDefConcat` (437);
  - `ssItemDiffConcat` (837), `ssDiffConcat` (839), `ssConcatDiff` (841), `ssConcatDiffItem` (843),
    `ssItemUnionConcat`, `ssConcatUnionItem` (857, `comm`), `ssItemInterConcat`,
    `ssConcatInterItem` (867, `comm`), `ssInterConcat2` (871), `ssInConcat` (877), `ssInUnionL`
    (886), `ssInUnionR` (888).

  Over a set variable (`LibEv.SvEqn`), entailed at set values: `msInKeysUnitSv` (449, 450),
  `{false #Equals @Key in_keys(.Map)} => #Ceil(@Key)` and the flip.

  Not stated here: the lemmas whose `requires` applies `=/=K` or `==K` to two KItem variables
  (422, 429, 433, 435, 438, 440, 446, 447), whose terms `kseq(K, dotk())` `LibEv.Term`'s
  translation does not write; 451 and 452 (`#Not` over set variables, which `LibEv.SvPred` has
  not); 411 and 830 (`#Ceil` of `Map:lookup` and of `_Set_` over set variables).
-/
import KcoreSpec.LibEvFnColl
import KcoreSpec.LibEvBool
import KcoreSpec.LibEvCeil

set_option autoImplicit false

namespace KCore

namespace LibEv

open ML Faithful

/-! ## The values of the map and set symbols -/

section
variable {c : Semantics}

theorem csHv_mapElem (k v : GroundTerm) : c.hv mapElem [k, v] = some (.map Srt.map [(k, v)]) := hv_of_value rfl
theorem csHv_mapUpdate (s : Srt) (m : Entries) (k v : GroundTerm) :
    c.hv mapUpdate [.map s m, k, v] = some (.map Srt.map (insertE k v m)) := hv_of_value rfl
theorem csHv_mapRemove (s : Srt) (m : Entries) (k : GroundTerm) :
    c.hv mapRemove [.map s m, k] = some (.map Srt.map (eraseK k m)) := hv_of_value rfl
theorem csHv_mapLookup (s : Srt) (m : Entries) (k : GroundTerm) :
    c.hv mapLookup [.map s m, k] = Map.find m k := by
  rw [fq_hv_notKey (by decide +kernel), hook_mapLookup]; rfl
theorem csHv_mapLookupOrDefault (s : Srt) (m : Entries) (k d : GroundTerm) :
    c.hv mapLookupOrDefault [.map s m, k, d] = some ((Map.find m k).getD d) := hv_of_value rfl
theorem csHv_mapInKeys (s : Srt) (m : Entries) (k : GroundTerm) :
    c.hv mapInKeys [k, .map s m] = some (bool (hasKey k m)) := hv_of_value rfl
theorem csHv_setIn (t : Srt) (s : List GroundTerm) (k : GroundTerm) :
    c.hv setIn [k, .set t s] = some (bool (memS k s)) := hv_of_value rfl
theorem csHv_setIntersect (s t : Srt) (a b : List GroundTerm) :
    c.hv setIntersect [.set s a, .set t b] = some (.set Srt.set (a.filter (memS · b))) := hv_of_value rfl
theorem csHv_boolNot (b : Bool) : c.hv boolNot [bool b] = some (bool !b) := hv_of_value rfl

end

/-! ## Facts of the collections -/

/-- Updating a key twice is updating it once, to the second value. -/
theorem cs_insertE_insertE (k v v0 : GroundTerm) : ∀ m : Entries, insertE k v (insertE k v0 m) = insertE k v m
  | [] => by simp [insertE, GroundTerm.cmp_refl]
  | (k', v') :: es => by
    simp only [insertE]
    cases hc : GroundTerm.cmp k k' with
    | lt => simp [insertE, GroundTerm.cmp_refl]
    | eq => simp [insertE, GroundTerm.cmp_refl]
    | gt => simp only [insertE, hc, cs_insertE_insertE k v v0 es]

/-- `_Map_` of a binding and a map: the map with the binding added where its key is fresh. -/
theorem cs_union_single (k v : GroundTerm) (m : Entries) :
    union [(k, v)] m = if hasKey k m then none else some (insertE k v m) := by
  simp only [union, Option.bind_some, addNew]

/-- Removing a key the map does not have leaves it. -/
theorem cs_eraseK_fresh (k : GroundTerm) : ∀ {m : Entries}, hasKey k m = false → eraseK k m = m
  | [], _ => rfl
  | (k', v') :: es, h => by
    simp only [hasKey, List.any_cons, Bool.or_eq_false_iff] at h
    simp only [eraseK, h.1, Bool.false_eq_true, ite_false]
    rw [cs_eraseK_fresh k (m := es) h.2]

theorem cs_memS_nil (k : GroundTerm) : memS k [] = false := rfl

/-- The union of a set with itself, or with the empty set on either side, is the set. -/
theorem cs_unionS_nil {a : List GroundTerm} (ha : Set.Canon a) : unionS a [] = a :=
  Set.ext (Set.union_canon (by rfl)) ha fun x => by rw [Set.mem_union]; simp

theorem cs_unionS_self {a : List GroundTerm} (ha : Set.Canon a) : unionS a a = a :=
  Set.ext (Set.union_canon ha) ha fun x => by rw [Set.mem_union, or_self]

theorem cs_filter_memS_self (a : List GroundTerm) : a.filter (memS · a) = a :=
  List.filter_eq_self.mpr fun x hx => (Set.memS_iff x a).mpr hx

theorem cs_filter_not_memS_nil (a : List GroundTerm) : a.filter (!memS · []) = a :=
  List.filter_eq_self.mpr fun _ _ => rfl

theorem cs_filter_memS_nil (a : List GroundTerm) : a.filter (memS · []) = [] :=
  List.filter_eq_nil_iff.mpr fun _ _ => by simp [cs_memS_nil]

local syntax "cs_eval" "[" Lean.Parser.Tactic.simpLemma,* "]" (Lean.Parser.Tactic.location)? : tactic

macro_rules
  | `(tactic| cs_eval [$ls,*] $[$loc]?) => `(tactic|
    simp only [val, valList, allSome, Option.bind_some, Option.map_some, boolT, dv_bool, csHv_mapElem,
      csHv_mapUpdate, csHv_mapRemove, csHv_mapLookup, csHv_mapLookupOrDefault, csHv_mapInKeys, csHv_setIn,
      csHv_setIntersect, csHv_boolNot, fhv_mapConcat, fhv_mapUnit, fhv_setUnit, fhv_setUnion, fhv_setDifference,
      $ls,*] $[$loc]?)

/-! ## 417: `(K |-> _ M:Map) [ K <- V ] => (K |-> V M)` -/

def msUpdConcat : Eqn :=
  ⟨[("VarK", Srt.kitem), ("Var'Unds'Gen0", Srt.kitem), ("VarM", Srt.map), ("VarV", Srt.kitem)], Srt.map, none,
    .app mapUpdate [.app mapConcat [.app mapElem [.var 0, .var 1], .var 2], .var 0, .var 3],
    .app mapConcat [.app mapElem [.var 0, .var 3], .var 2]⟩

theorem msUpdConcat_holds {c : Semantics} (hs : c.shapesOK = true) : msUpdConcat.Holds c := by
  intro σ hσ hreq
  obtain ⟨k, hk, -⟩ := hσ 0 ("VarK", Srt.kitem) rfl
  obtain ⟨v0, hv0, -⟩ := hσ 1 ("Var'Unds'Gen0", Srt.kitem) rfl
  obtain ⟨m, hm, -⟩ := fq_map_at hs hσ 2 (n := "VarM") rfl
  obtain ⟨v, hv, -⟩ := hσ 3 ("VarV", Srt.kitem) rfl
  simp only [msUpdConcat]
  cs_eval [hk, hv0, hm, hv, cs_union_single]
  cases hkm : hasKey k m <;> simp [csHv_mapUpdate, cs_insertE_insertE]

theorem msUpdConcat_ev {c : Semantics} (h : c.coreOK = true) (hs : c.shapesOK = true) (ad : KoreAML.AxiomDecl)
    (hp : ad.ax.pattern = msUpdConcat.patR) (hsv : ad.ax.sortVars = [KoreAML.Rv]) :
    EntailsAtValues c ad (KoreAML.trAxiom [] [] ad).pat :=
  Eqn.entailed_reg h msUpdConcat (by decide) (by rfl) (msUpdConcat_holds hs) ad hp hsv

/-! ## 418: `M:Map [ K <- V ] => (K |-> V M) requires notBool (K in_keys(M))` -/

def msUpdFresh : Eqn :=
  ⟨[("VarK", Srt.kitem), ("VarM", Srt.map), ("VarV", Srt.kitem)], Srt.map,
    some (.app boolNot [.app mapInKeys [.var 0, .var 1]]),
    .app mapUpdate [.var 1, .var 0, .var 2], .app mapConcat [.app mapElem [.var 0, .var 2], .var 1]⟩

theorem msUpdFresh_holds {c : Semantics} (hs : c.shapesOK = true) : msUpdFresh.Holds c := by
  intro σ hσ hreq
  obtain ⟨k, hk, -⟩ := hσ 0 ("VarK", Srt.kitem) rfl
  obtain ⟨m, hm, -⟩ := fq_map_at hs hσ 1 (n := "VarM") rfl
  obtain ⟨v, hv, -⟩ := hσ 2 ("VarV", Srt.kitem) rfl
  have hq := hreq _ rfl
  simp only [msUpdFresh] at hq ⊢
  cs_eval [hk, hm, hv, cs_union_single] at hq ⊢
  cases hkm : hasKey k m
  · simp
  · simp [hkm, bool] at hq

theorem msUpdFresh_ev {c : Semantics} (h : c.coreOK = true) (hs : c.shapesOK = true) (ad : KoreAML.AxiomDecl)
    (hp : ad.ax.pattern = msUpdFresh.patR) (hsv : ad.ax.sortVars = [KoreAML.Rv]) :
    EntailsAtValues c ad (KoreAML.trAxiom [] [] ad).pat :=
  Eqn.entailed_reg h msUpdFresh (by decide) (by rfl) (msUpdFresh_holds hs) ad hp hsv

/-! ## 419: `M:Map [ K <- _ ] [ K <- V ] => M [ K <- V ]` -/

def msUpdUpd : Eqn :=
  ⟨[("VarM", Srt.map), ("VarK", Srt.kitem), ("Var'Unds'Gen0", Srt.kitem), ("VarV", Srt.kitem)], Srt.map, none,
    .app mapUpdate [.app mapUpdate [.var 0, .var 1, .var 2], .var 1, .var 3], .app mapUpdate [.var 0, .var 1, .var 3]⟩

theorem msUpdUpd_holds {c : Semantics} (hs : c.shapesOK = true) : msUpdUpd.Holds c := by
  intro σ hσ _
  obtain ⟨m, hm, -⟩ := fq_map_at hs hσ 0 (n := "VarM") rfl
  obtain ⟨k, hk, -⟩ := hσ 1 ("VarK", Srt.kitem) rfl
  obtain ⟨v0, hv0, -⟩ := hσ 2 ("Var'Unds'Gen0", Srt.kitem) rfl
  obtain ⟨v, hv, -⟩ := hσ 3 ("VarV", Srt.kitem) rfl
  simp only [msUpdUpd]
  cs_eval [hk, hv0, hm, hv, cs_insertE_insertE]

theorem msUpdUpd_ev {c : Semantics} (h : c.coreOK = true) (hs : c.shapesOK = true) (ad : KoreAML.AxiomDecl)
    (hp : ad.ax.pattern = msUpdUpd.patR) (hsv : ad.ax.sortVars = [KoreAML.Rv]) :
    EntailsAtValues c ad (KoreAML.trAxiom [] [] ad).pat :=
  Eqn.entailed_reg h msUpdUpd (by decide) (by rfl) (msUpdUpd_holds hs) ad hp hsv

/-! ## 426: `M:Map [ K <- undef ] => M requires notBool (K in_keys(M))` -/

def msRemFresh : Eqn :=
  ⟨[("VarK", Srt.kitem), ("VarM", Srt.map)], Srt.map, some (.app boolNot [.app mapInKeys [.var 0, .var 1]]),
    .app mapRemove [.var 1, .var 0], .var 1⟩

theorem msRemFresh_holds {c : Semantics} (hs : c.shapesOK = true) : msRemFresh.Holds c := by
  intro σ hσ hreq
  obtain ⟨k, hk, -⟩ := hσ 0 ("VarK", Srt.kitem) rfl
  obtain ⟨m, hm, -⟩ := fq_map_at hs hσ 1 (n := "VarM") rfl
  have hq := hreq _ rfl
  simp only [msRemFresh] at hq ⊢
  cs_eval [hk, hm] at hq ⊢
  cases hkm : hasKey k m
  · rw [cs_eraseK_fresh k hkm]
  · simp [hkm, bool] at hq

theorem msRemFresh_ev {c : Semantics} (h : c.coreOK = true) (hs : c.shapesOK = true) (ad : KoreAML.AxiomDecl)
    (hp : ad.ax.pattern = msRemFresh.patR) (hsv : ad.ax.sortVars = [KoreAML.Rv]) :
    EntailsAtValues c ad (KoreAML.trAxiom [] [] ad).pat :=
  Eqn.entailed_reg h msRemFresh (by decide) (by rfl) (msRemFresh_holds hs) ad hp hsv

/-! ## 434: `(_MAP:Map [ K <- V1 ]) [ K ] => V1` -/

def msLookupUpd : Eqn :=
  ⟨[("Var'Unds'MAP", Srt.map), ("VarK", Srt.kitem), ("VarV1", Srt.kitem)], Srt.kitem, none,
    .app mapLookup [.app mapUpdate [.var 0, .var 1, .var 2], .var 1], .var 2⟩

theorem msLookupUpd_holds {c : Semantics} (hs : c.shapesOK = true) : msLookupUpd.Holds c := by
  intro σ hσ _
  obtain ⟨m, hm, -⟩ := fq_map_at hs hσ 0 (n := "Var'Unds'MAP") rfl
  obtain ⟨k, hk, -⟩ := hσ 1 ("VarK", Srt.kitem) rfl
  obtain ⟨v, hv, -⟩ := hσ 2 ("VarV1", Srt.kitem) rfl
  simp only [msLookupUpd]
  cs_eval [hk, hm, hv, Map.find_insert_self]

theorem msLookupUpd_ev {c : Semantics} (h : c.coreOK = true) (hs : c.shapesOK = true) (ad : KoreAML.AxiomDecl)
    (hp : ad.ax.pattern = msLookupUpd.patR) (hsv : ad.ax.sortVars = [KoreAML.Rv]) :
    EntailsAtValues c ad (KoreAML.trAxiom [] [] ad).pat :=
  Eqn.entailed_reg h msLookupUpd (by decide) (by rfl) (msLookupUpd_holds hs) ad hp hsv

/-! ## 439: `(_MAP:Map [ K <- V1 ]) [ K ] orDefault _ => V1` -/

def msLookupDefUpd : Eqn :=
  ⟨[("Var'Unds'MAP", Srt.map), ("VarK", Srt.kitem), ("VarV1", Srt.kitem), ("Var'Unds'Gen0", Srt.kitem)], Srt.kitem,
    none, .app mapLookupOrDefault [.app mapUpdate [.var 0, .var 1, .var 2], .var 1, .var 3], .var 2⟩

theorem msLookupDefUpd_holds {c : Semantics} (hs : c.shapesOK = true) : msLookupDefUpd.Holds c := by
  intro σ hσ _
  obtain ⟨m, hm, -⟩ := fq_map_at hs hσ 0 (n := "Var'Unds'MAP") rfl
  obtain ⟨k, hk, -⟩ := hσ 1 ("VarK", Srt.kitem) rfl
  obtain ⟨v, hv, -⟩ := hσ 2 ("VarV1", Srt.kitem) rfl
  obtain ⟨d, hd, -⟩ := hσ 3 ("Var'Unds'Gen0", Srt.kitem) rfl
  simp only [msLookupDefUpd]
  cs_eval [hk, hm, hv, hd, Map.find_insert_self, Option.getD_some]

theorem msLookupDefUpd_ev {c : Semantics} (h : c.coreOK = true) (hs : c.shapesOK = true) (ad : KoreAML.AxiomDecl)
    (hp : ad.ax.pattern = msLookupDefUpd.patR) (hsv : ad.ax.sortVars = [KoreAML.Rv]) :
    EntailsAtValues c ad (KoreAML.trAxiom [] [] ad).pat :=
  Eqn.entailed_reg h msLookupDefUpd (by decide) (by rfl) (msLookupDefUpd_holds hs) ad hp hsv

/-! ## 441: `.Map [ _ ] orDefault D => D` -/

def msLookupDefUnit : Eqn :=
  ⟨[("Var'Unds'Gen0", Srt.kitem), ("VarD", Srt.kitem)], Srt.kitem, none,
    .app mapLookupOrDefault [.app mapUnit [], .var 0, .var 1], .var 1⟩

theorem msLookupDefUnit_holds {c : Semantics} : msLookupDefUnit.Holds c := by
  intro σ hσ _
  obtain ⟨k, hk, -⟩ := hσ 0 ("Var'Unds'Gen0", Srt.kitem) rfl
  obtain ⟨d, hd, -⟩ := hσ 1 ("VarD", Srt.kitem) rfl
  simp only [msLookupDefUnit]
  cs_eval [hk, hd, Map.find_nil, Option.getD_none]

theorem msLookupDefUnit_ev {c : Semantics} (h : c.coreOK = true) (ad : KoreAML.AxiomDecl)
    (hp : ad.ax.pattern = msLookupDefUnit.patR) (hsv : ad.ax.sortVars = [KoreAML.Rv]) :
    EntailsAtValues c ad (KoreAML.trAxiom [] [] ad).pat :=
  Eqn.entailed_reg h msLookupDefUnit (by decide) (by rfl) msLookupDefUnit_holds ad hp hsv

/-! ## 444: `K in_keys(_M [ K <- undef ]) => false` -/

def msInKeysRem : Eqn :=
  ⟨[("VarK", Srt.kitem), ("Var'Unds'M", Srt.map)], Srt.bool, none,
    .app mapInKeys [.var 0, .app mapRemove [.var 1, .var 0]], boolT false⟩

theorem msInKeysRem_holds {c : Semantics} (hs : c.shapesOK = true) : msInKeysRem.Holds c := by
  intro σ hσ _
  obtain ⟨k, hk, -⟩ := hσ 0 ("VarK", Srt.kitem) rfl
  obtain ⟨m, hm, hcm⟩ := fq_map_at hs hσ 1 (n := "Var'Unds'M") rfl
  simp only [msInKeysRem]
  cs_eval [hk, hm, Map.hasKey_eq, Map.find_erase_self k hcm]
  rfl

theorem msInKeysRem_ev {c : Semantics} (h : c.coreOK = true) (hs : c.shapesOK = true) (ad : KoreAML.AxiomDecl)
    (hp : ad.ax.pattern = msInKeysRem.patR) (hsv : ad.ax.sortVars = [KoreAML.Rv]) :
    EntailsAtValues c ad (KoreAML.trAxiom [] [] ad).pat :=
  Eqn.entailed_reg h msInKeysRem (by decide) (by rfl) (msInKeysRem_holds hs) ad hp hsv

/-! ## 445: `K in_keys(_M [ K <- _ ]) => true` -/

def msInKeysUpd : Eqn :=
  ⟨[("VarK", Srt.kitem), ("Var'Unds'M", Srt.map), ("Var'Unds'Gen0", Srt.kitem)], Srt.bool, none,
    .app mapInKeys [.var 0, .app mapUpdate [.var 1, .var 0, .var 2]], boolT true⟩

theorem msInKeysUpd_holds {c : Semantics} (hs : c.shapesOK = true) : msInKeysUpd.Holds c := by
  intro σ hσ _
  obtain ⟨k, hk, -⟩ := hσ 0 ("VarK", Srt.kitem) rfl
  obtain ⟨m, hm, -⟩ := fq_map_at hs hσ 1 (n := "Var'Unds'M") rfl
  obtain ⟨v, hv, -⟩ := hσ 2 ("Var'Unds'Gen0", Srt.kitem) rfl
  simp only [msInKeysUpd]
  cs_eval [hk, hm, hv, Map.hasKey_eq, Map.find_insert_self]
  rfl

theorem msInKeysUpd_ev {c : Semantics} (h : c.coreOK = true) (hs : c.shapesOK = true) (ad : KoreAML.AxiomDecl)
    (hp : ad.ax.pattern = msInKeysUpd.patR) (hsv : ad.ax.sortVars = [KoreAML.Rv]) :
    EntailsAtValues c ad (KoreAML.trAxiom [] [] ad).pat :=
  Eqn.entailed_reg h msInKeysUpd (by decide) (by rfl) (msInKeysUpd_holds hs) ad hp hsv

/-! ## 835, 836: `S -Set .Set => S`, `.Set -Set _ => .Set` -/

def ssDiffUnit : Eqn :=
  ⟨[("VarS", Srt.set)], Srt.set, none, .app setDifference [.var 0, .app setUnit []], .var 0⟩

theorem ssDiffUnit_holds {c : Semantics} (hs : c.shapesOK = true) : ssDiffUnit.Holds c := by
  intro σ hσ _
  obtain ⟨a, ha, -⟩ := fq_set_at hs hσ 0 (n := "VarS") rfl
  simp only [ssDiffUnit]
  cs_eval [ha, cs_filter_not_memS_nil]

theorem ssDiffUnit_ev {c : Semantics} (h : c.coreOK = true) (hs : c.shapesOK = true) (ad : KoreAML.AxiomDecl)
    (hp : ad.ax.pattern = ssDiffUnit.patR) (hsv : ad.ax.sortVars = [KoreAML.Rv]) :
    EntailsAtValues c ad (KoreAML.trAxiom [] [] ad).pat :=
  Eqn.entailed_reg h ssDiffUnit (by decide) (by rfl) (ssDiffUnit_holds hs) ad hp hsv

def ssUnitDiff : Eqn :=
  ⟨[("Var'Unds'Gen0", Srt.set)], Srt.set, none, .app setDifference [.app setUnit [], .var 0], .app setUnit []⟩

theorem ssUnitDiff_holds {c : Semantics} (hs : c.shapesOK = true) : ssUnitDiff.Holds c := by
  intro σ hσ _
  obtain ⟨a, ha, -⟩ := fq_set_at hs hσ 0 (n := "Var'Unds'Gen0") rfl
  simp only [ssUnitDiff]
  cs_eval [ha, List.filter_nil]

theorem ssUnitDiff_ev {c : Semantics} (h : c.coreOK = true) (hs : c.shapesOK = true) (ad : KoreAML.AxiomDecl)
    (hp : ad.ax.pattern = ssUnitDiff.patR) (hsv : ad.ax.sortVars = [KoreAML.Rv]) :
    EntailsAtValues c ad (KoreAML.trAxiom [] [] ad).pat :=
  Eqn.entailed_reg h ssUnitDiff (by decide) (by rfl) (ssUnitDiff_holds hs) ad hp hsv

/-! ## 854 (`comm`), 855: `S |Set .Set => S`, `.Set |Set S => S`, `S |Set S => S` -/

def ssUnionUnit : Eqn :=
  ⟨[("VarS", Srt.set)], Srt.set, none, .app setUnion [.var 0, .app setUnit []], .var 0⟩

theorem ssUnionUnit_holds {c : Semantics} (hs : c.shapesOK = true) : ssUnionUnit.Holds c := by
  intro σ hσ _
  obtain ⟨a, ha, hca⟩ := fq_set_at hs hσ 0 (n := "VarS") rfl
  simp only [ssUnionUnit]
  cs_eval [ha, cs_unionS_nil hca]

theorem ssUnionUnit_ev {c : Semantics} (h : c.coreOK = true) (hs : c.shapesOK = true) (ad : KoreAML.AxiomDecl)
    (hp : ad.ax.pattern = ssUnionUnit.patR) (hsv : ad.ax.sortVars = [KoreAML.Rv]) :
    EntailsAtValues c ad (KoreAML.trAxiom [] [] ad).pat :=
  Eqn.entailed_reg h ssUnionUnit (by decide) (by rfl) (ssUnionUnit_holds hs) ad hp hsv

def ssUnitUnion : Eqn :=
  ⟨[("VarS", Srt.set)], Srt.set, none, .app setUnion [.app setUnit [], .var 0], .var 0⟩

theorem ssUnitUnion_holds {c : Semantics} (hs : c.shapesOK = true) : ssUnitUnion.Holds c := by
  intro σ hσ _
  obtain ⟨a, ha, -⟩ := fq_set_at hs hσ 0 (n := "VarS") rfl
  simp only [ssUnitUnion]
  cs_eval [ha]
  rfl

theorem ssUnitUnion_ev {c : Semantics} (h : c.coreOK = true) (hs : c.shapesOK = true) (ad : KoreAML.AxiomDecl)
    (hp : ad.ax.pattern = ssUnitUnion.patR) (hsv : ad.ax.sortVars = [KoreAML.Rv]) :
    EntailsAtValues c ad (KoreAML.trAxiom [] [] ad).pat :=
  Eqn.entailed_reg h ssUnitUnion (by decide) (by rfl) (ssUnitUnion_holds hs) ad hp hsv

def ssUnionSelf : Eqn :=
  ⟨[("VarS", Srt.set)], Srt.set, none, .app setUnion [.var 0, .var 0], .var 0⟩

theorem ssUnionSelf_holds {c : Semantics} (hs : c.shapesOK = true) : ssUnionSelf.Holds c := by
  intro σ hσ _
  obtain ⟨a, ha, hca⟩ := fq_set_at hs hσ 0 (n := "VarS") rfl
  simp only [ssUnionSelf]
  cs_eval [ha, cs_unionS_self hca]

theorem ssUnionSelf_ev {c : Semantics} (h : c.coreOK = true) (hs : c.shapesOK = true) (ad : KoreAML.AxiomDecl)
    (hp : ad.ax.pattern = ssUnionSelf.patR) (hsv : ad.ax.sortVars = [KoreAML.Rv]) :
    EntailsAtValues c ad (KoreAML.trAxiom [] [] ad).pat :=
  Eqn.entailed_reg h ssUnionSelf (by decide) (by rfl) (ssUnionSelf_holds hs) ad hp hsv

/-! ## 864 (`comm`), 865: `intersectSet(_, .Set) => .Set`, the flip, `intersectSet(S, S) => S` -/

def ssInterUnit : Eqn :=
  ⟨[("Var'Unds'Gen0", Srt.set)], Srt.set, none, .app setIntersect [.var 0, .app setUnit []], .app setUnit []⟩

theorem ssInterUnit_holds {c : Semantics} (hs : c.shapesOK = true) : ssInterUnit.Holds c := by
  intro σ hσ _
  obtain ⟨a, ha, -⟩ := fq_set_at hs hσ 0 (n := "Var'Unds'Gen0") rfl
  simp only [ssInterUnit]
  cs_eval [ha, cs_filter_memS_nil]

theorem ssInterUnit_ev {c : Semantics} (h : c.coreOK = true) (hs : c.shapesOK = true) (ad : KoreAML.AxiomDecl)
    (hp : ad.ax.pattern = ssInterUnit.patR) (hsv : ad.ax.sortVars = [KoreAML.Rv]) :
    EntailsAtValues c ad (KoreAML.trAxiom [] [] ad).pat :=
  Eqn.entailed_reg h ssInterUnit (by decide) (by rfl) (ssInterUnit_holds hs) ad hp hsv

def ssUnitInter : Eqn :=
  ⟨[("Var'Unds'Gen0", Srt.set)], Srt.set, none, .app setIntersect [.app setUnit [], .var 0], .app setUnit []⟩

theorem ssUnitInter_holds {c : Semantics} (hs : c.shapesOK = true) : ssUnitInter.Holds c := by
  intro σ hσ _
  obtain ⟨a, ha, -⟩ := fq_set_at hs hσ 0 (n := "Var'Unds'Gen0") rfl
  simp only [ssUnitInter]
  cs_eval [ha, List.filter_nil]

theorem ssUnitInter_ev {c : Semantics} (h : c.coreOK = true) (hs : c.shapesOK = true) (ad : KoreAML.AxiomDecl)
    (hp : ad.ax.pattern = ssUnitInter.patR) (hsv : ad.ax.sortVars = [KoreAML.Rv]) :
    EntailsAtValues c ad (KoreAML.trAxiom [] [] ad).pat :=
  Eqn.entailed_reg h ssUnitInter (by decide) (by rfl) (ssUnitInter_holds hs) ad hp hsv

def ssInterSelf : Eqn :=
  ⟨[("VarS", Srt.set)], Srt.set, none, .app setIntersect [.var 0, .var 0], .var 0⟩

theorem ssInterSelf_holds {c : Semantics} (hs : c.shapesOK = true) : ssInterSelf.Holds c := by
  intro σ hσ _
  obtain ⟨a, ha, -⟩ := fq_set_at hs hσ 0 (n := "VarS") rfl
  simp only [ssInterSelf]
  cs_eval [ha, cs_filter_memS_self]

theorem ssInterSelf_ev {c : Semantics} (h : c.coreOK = true) (hs : c.shapesOK = true) (ad : KoreAML.AxiomDecl)
    (hp : ad.ax.pattern = ssInterSelf.patR) (hsv : ad.ax.sortVars = [KoreAML.Rv]) :
    EntailsAtValues c ad (KoreAML.trAxiom [] [] ad).pat :=
  Eqn.entailed_reg h ssInterSelf (by decide) (by rfl) (ssInterSelf_holds hs) ad hp hsv

/-! ## 876: `_E in .Set => false` -/

def ssInUnit : Eqn :=
  ⟨[("Var'Unds'E", Srt.kitem)], Srt.bool, none, .app setIn [.var 0, .app setUnit []], boolT false⟩

theorem ssInUnit_holds {c : Semantics} : ssInUnit.Holds c := by
  intro σ hσ _
  obtain ⟨k, hk, -⟩ := hσ 0 ("Var'Unds'E", Srt.kitem) rfl
  simp only [ssInUnit]
  cs_eval [hk, cs_memS_nil]

theorem ssInUnit_ev {c : Semantics} (h : c.coreOK = true) (ad : KoreAML.AxiomDecl)
    (hp : ad.ax.pattern = ssInUnit.patR) (hsv : ad.ax.sortVars = [KoreAML.Rv]) :
    EntailsAtValues c ad (KoreAML.trAxiom [] [] ad).pat :=
  Eqn.entailed_reg h ssInUnit (by decide) (by rfl) ssInUnit_holds ad hp hsv

/-! ## An equation with an `ensures`

kompile writes `lhs => rhs ensures ens` (no `requires`) as
`\implies{R}(\top{R}(), \equals{s, R}(lhs, \and{s}(rhs, \equals{SortBool, s}(ens, \dv{SortBool}("true")))))`:
the left side is the right side where `ens` is `true`, and has no value elsewhere. -/

/-- A library equation `lhs => rhs ensures ens` over the variables `vars`, its sides of the sort
`s`. -/
structure EqnE where
  vars : Vars
  s : Srt
  lhs : Term
  rhs : Term
  ens : Term

namespace EqnE

/-- The pattern of the equation's axiom over the sort variable `R`. -/
def pattern (c : Semantics) (E : EqnE) : Kore.Pattern :=
  .implies KoreAML.R (.top KoreAML.R)
    (.equals (srtOf c E.s) KoreAML.R (kore c E.vars E.lhs)
      (.and (srtOf c E.s) [kore c E.vars E.rhs,
        .equals (srtOf c Srt.bool) (srtOf c E.s) (kore c E.vars E.ens) (.dv (srtOf c Srt.bool) "true")]))

/-- The equation is over registry sorts, its sides are terms of the sort `s` and its `ensures` a
term of the sort Bool. -/
def typed (c : Semantics) (E : EqnE) : Bool :=
  decide (E.s < nRegSorts) && E.vars.all (fun p => decide (p.2 < nRegSorts)) &&
  srt? c E.vars E.lhs == some E.s && srt? c E.vars E.rhs == some E.s && srt? c E.vars E.ens == some Srt.bool

/-- At every substitution of values of the variables' sorts, the left side has the right side's
value where the `ensures` has the value `true`, and none elsewhere. -/
def Holds (c : Semantics) (E : EqnE) : Prop :=
  ∀ σ : Subst, (∀ i p, E.vars[i]? = some p → ∃ v, σ.lookup i = some v ∧ c.sortOf v = some p.2) →
    val c σ E.lhs = if val c σ E.ens = some (bool true) then val c σ E.rhs else none

/-- `pattern` with the registry's names. -/
def patR (E : EqnE) : Kore.Pattern :=
  .implies KoreAML.R (.top KoreAML.R)
    (.equals (regSrtK E.s) KoreAML.R (koreR E.vars E.lhs)
      (.and (regSrtK E.s) [koreR E.vars E.rhs,
        .equals (regSrtK Srt.bool) (regSrtK E.s) (koreR E.vars E.ens) (.dv (regSrtK Srt.bool) "true")]))

/-- The equation is over the registry's symbols and sorts, and each of its variables is free in
its pattern. -/
def regular (E : EqnE) : Bool :=
  decide (E.s < nRegSorts) && E.vars.all (fun p => decide (p.2 < nRegSorts)) &&
  reg E.lhs && reg E.rhs && reg E.ens &&
  E.vars.all (fun p => (KoreAML.freeOf [] E.patR).contains (.evar p.1 (regSrtK p.2)))

theorem pattern_reg (c : Semantics) {E : EqnE} (hr : E.regular = true) : E.pattern c = E.patR := by
  simp only [regular, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hr
  obtain ⟨⟨⟨⟨⟨hs, hv⟩, hl⟩, hrr⟩, he⟩, -⟩ := hr
  unfold pattern patR
  rw [kore_reg c hv _ hl, kore_reg c hv _ hrr, kore_reg c hv _ he, srtOf_reg c hs,
    srtOf_reg c (by decide : Srt.bool < nRegSorts)]

end EqnE

/-- **A library equation with an `ensures` that holds of the values is entailed at values.** For
a semantics meeting `coreOK` and an equation `E` whose left side has the right side's value
where its `ensures` is `true` and none elsewhere (`EqnE.Holds`): the translation of any axiom
declaration whose pattern is `E`'s, over the one sort variable `R` and with each variable of `E`
free in it, holds in every model of `Γ c` at every valuation that sends the axiom's free element
variables to values. -/
theorem EqnE.entailed {c : Semantics} (h : c.coreOK = true) (E : EqnE) (ht : E.typed c = true)
    (hE : E.Holds c) (ad : KoreAML.AxiomDecl) (hp : ad.ax.pattern = E.pattern c)
    (hsv : ad.ax.sortVars = [KoreAML.Rv])
    (hfv : ∀ i, i < E.vars.length → vkey c E.vars i ∈ KoreAML.freeOf [] ad.ax.pattern) :
    EntailsAtValues c ad (KoreAML.trAxiom [] [] ad).pat := by
  intro M _ I hI e hat m
  haveI : OvlOK c := ovlOK_of_core h
  have hD := defOK hI
  have hc := sat_sigItem hI (sig_ceilDef (c := c))
  simp only [EqnE.typed, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, beq_iff_eq] at ht
  obtain ⟨⟨⟨⟨hsR, hvR⟩, htl⟩, htr⟩, hte⟩ := ht
  have hnum : ∀ {s : Srt}, s < nRegSorts → s < nRegSorts + c.sortNames.length :=
    fun hs => Nat.lt_of_lt_of_le hs (Nat.le_add_right _ _)
  obtain ⟨σ, hσ, hag⟩ := fq_subst h hI E.vars hvR ad.ax hfv e hat
  unfold KoreAML.trAxiom
  dsimp only
  generalize htb : KoreAML.tableOf ad.ax.sortVars ad.ax.pattern = t at hag ⊢
  rw [interpret_impl]
  intro hgd
  have hR : KoreAML.IsSort I (e.evalEvar (t.ev (.sortVar "R"))) :=
    (KoreAML.interp_guard_sortVar hD).mp (conjList_mem hgd _ (List.mem_map.mpr ⟨.sortVar "R",
      List.mem_eraseDups.mpr (List.mem_append_left _ (by rw [hsv]; exact List.mem_singleton.mpr rfl)), rfl⟩))
  have hDV := fun (u : Term) (s : Srt) (hu : srt? c E.vars u = some s) =>
    den_val (tbl := t) (e := e) h hI hσ hag u hu
  obtain ⟨τ, hτsort, hτ⟩ := srt_den hI (hnum hsR)
  obtain ⟨τb, hτbsort, hτb⟩ := srt_den hI (hnum (show Srt.bool < nRegSorts by decide))
  have hdist : (distinctSorts c).contains Srt.bool = true := by
    refine List.elem_eq_true_of_mem ?_
    unfold distinctSorts
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_cons_of_mem _ (List.mem_cons_self ..)))))
  have hRv : ∀ b, (KoreAML.trSort t KoreAML.R).interpret I e b ↔ b = e.evalEvar (t.ev (.sortVar "R")) :=
    fun b => by rw [trSort_R, KoreAML.interp_evar]
  have hT : c.sortOf (bool true) = some Srt.bool := rmS_sortOf_bool c true
  obtain ⟨hT1, hT2⟩ := elemOf_spec hI hT e
  have hinh : KoreAML.Inh I τb (elemOf c I (bool true)) := by
    refine (KoreAML.interp_inhOf_of (fun a' => ?_)).mp hT2
    have := hτb t e a'
    rwa [trSort_srtOf_twoT] at this
  -- `\dv{SortBool}("true")` denotes the element of `true`
  have hdvT : ∀ a, (KoreAML.tr ⟨t, []⟩ (.dv (srtOf c Srt.bool) "true")).interpret I e a ↔
      (den c (bool true)).interpret I e a := by
    intro a
    unfold den KoreAML.den bool
    rw [GroundTerm.kore]
    unfold srtOf
    rw [KoreAML.tr_dv, KoreAML.tr_dv]
    rfl
  -- the `ensures` predicate holds exactly where `ens` has the value `true`
  have hensP : (∀ a, KoreAML.Inh I τb a → ((KoreAML.tr ⟨t, []⟩ (kore c E.vars E.ens)).interpret I e a ↔
      (KoreAML.tr ⟨t, []⟩ (.dv (srtOf c Srt.bool) "true")).interpret I e a)) ↔
      val c σ E.ens = some (bool true) := by
    constructor
    · intro hq
      have hq1 := (hq _ hinh).mpr ((hdvT _).mpr ((hT1 _).mpr rfl))
      rw [(hDV E.ens _ hte).1] at hq1
      cases hvq : val c σ E.ens with
      | none => rw [hvq] at hq1; exact hq1.elim
      | some w =>
        rw [hvq] at hq1
        have hw := (hDV E.ens _ hte).2 w hvq
        by_cases hne : w = bool true
        · rw [hne]
        · exact absurd ⟨hq1, (hT1 _).mpr rfl⟩ (dom_apart hI hdist hw hT hne e _)
    · intro hv a _
      rw [(hDV E.ens _ hte).1, hv, hdvT]
      rfl
  rw [hp]
  unfold EqnE.pattern
  simp only [KoreAML.sortOf]
  rw [KoreAML.interp_equal hD]
  intro a
  rw [KoreAML.tr, KoreAML.interp_sImp]
  constructor
  · exact fun h' => h'.1
  · intro ha
    refine ⟨ha, fun _ => ?_⟩
    have heq := hE σ hσ
    rw [KoreAML.tr, KoreAML.interp_sEquals hD hc (hτ t e) hRv hτsort hR]
    refine ⟨(KoreAML.interp_inhOf_of hRv).mp ha, fun b hb => ?_⟩
    rw [(hDV E.lhs _ htl).1 b, heq, KoreAML.tr]
    show _ ↔ (KoreAML.sAnd (KoreAML.tr ⟨t, []⟩ (kore c E.vars E.rhs))
      (KoreAML.tr ⟨t, []⟩ (.equals (srtOf c Srt.bool) (srtOf c E.s) (kore c E.vars E.ens)
        (.dv (srtOf c Srt.bool) "true")))).interpret I e b
    rw [KoreAML.interp_sAnd, KoreAML.tr, KoreAML.interp_sEquals hD hc (hτb t e) (hτ t e) hτbsort hτsort,
      hensP]
    have hr := (hDV E.rhs _ htr).1 b
    by_cases hv : val c σ E.ens = some (bool true)
    · rw [if_pos hv]
      exact ⟨fun h' => ⟨hr.mpr h', hb, hv⟩, fun h' => hr.mp h'.1⟩
    · rw [if_neg hv]
      exact ⟨fun h' => h'.elim, fun h' => absurd h'.2.2 hv⟩

/-- `EqnE.entailed` for an equation over the registry's names. -/
theorem EqnE.entailed_reg {c : Semantics} (h : c.coreOK = true) (E : EqnE) (hr : E.regular = true)
    (ht : E.typed c = true) (hE : E.Holds c) (ad : KoreAML.AxiomDecl) (hp : ad.ax.pattern = E.patR)
    (hsv : ad.ax.sortVars = [KoreAML.Rv]) : EntailsAtValues c ad (KoreAML.trAxiom [] [] ad).pat := by
  refine EqnE.entailed h E ht hE ad (hp.trans (EqnE.pattern_reg c hr).symm) hsv (fun i hi => ?_)
  have hr' := hr
  simp only [EqnE.regular, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hr'
  obtain ⟨⟨⟨⟨⟨-, hv⟩, -⟩, -⟩, -⟩, hf⟩ := hr'
  have hmem : E.vars.getD i ("", 0) ∈ E.vars := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
    exact List.getElem_mem hi
  have := hf _ hmem
  rw [hp]
  unfold vkey
  rw [srtOf_reg c (hv _ hmem)]
  exact List.mem_of_elem_eq_true this

/-! ## Facts for the equations with an `ensures` -/

section
variable {c : Semantics}

theorem csHv_setElem (k : GroundTerm) : c.hv setElem [k] = some (.set Srt.set [k]) := hv_of_value rfl

end

/-- Removing a fresh key just added gives the map back. -/
theorem cs_eraseK_insertE (k v : GroundTerm) : ∀ {m : Entries}, hasKey k m = false → eraseK k (insertE k v m) = m
  | [], _ => by simp [insertE, eraseK, GroundTerm.cmp_refl]
  | (k', v') :: es, h => by
    simp only [hasKey, List.any_cons, Bool.or_eq_false_iff] at h
    simp only [insertE]
    cases hc : GroundTerm.cmp k k' with
    | lt => simp [eraseK, GroundTerm.cmp_refl]
    | eq => rw [hc] at h; simp at h
    | gt =>
      have : (GroundTerm.cmp k k' == .eq) = false := by rw [hc]; rfl
      simp only [eraseK, this, Bool.false_eq_true, ite_false]
      rw [cs_eraseK_insertE k v (m := es) h.2]

theorem cs_canon_single (x : GroundTerm) : Set.Canon [x] := rfl

theorem cs_mem_single {x y : GroundTerm} : y ∈ [x] ↔ y = x := List.mem_singleton

/-- `_Set_` of a set and one element: their union where the element is not a member. -/
theorem cs_concatS_single (a : List GroundTerm) (x : GroundTerm) :
    concatS a [x] = if memS x a then none else some (unionS a [x]) := by
  have : a.all (fun y => !memS y [x]) = !memS x a := by
    rw [Bool.eq_iff_iff, List.all_eq_true, Bool.not_eq_true', Bool.eq_false_iff, ne_eq, Set.memS_iff]
    constructor
    · intro h hx
      have := h x hx
      rw [Bool.not_eq_true', Bool.eq_false_iff, ne_eq, Set.memS_iff] at this
      exact this (List.mem_singleton_self x)
    · intro h y hy
      rw [Bool.not_eq_true', Bool.eq_false_iff, ne_eq, Set.memS_iff, List.mem_singleton]
      rintro rfl
      exact h hy
  unfold concatS
  rw [this]
  cases memS x a <;> rfl

/-- `_Set_` of one element and a set. -/
theorem cs_concatS_single_left (a : List GroundTerm) (x : GroundTerm) :
    concatS [x] a = if memS x a then none else some (unionS [x] a) := by
  unfold concatS
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  cases memS x a <;> rfl

theorem cs_memS_union_single (a : List GroundTerm) (x : GroundTerm) : memS x (unionS a [x]) = true :=
  (Set.memS_iff _ _).mpr ((Set.mem_union _ _ _).mpr (Or.inr (List.mem_singleton_self x)))

theorem cs_memS_single_union (a : List GroundTerm) (x : GroundTerm) : memS x (unionS [x] a) = true :=
  (Set.memS_iff _ _).mpr ((Set.mem_union _ _ _).mpr (Or.inl (List.mem_singleton_self x)))

theorem cs_memS_union_left {a b : List GroundTerm} {x : GroundTerm} (h : memS x a = true) :
    memS x (unionS a b) = true :=
  (Set.memS_iff _ _).mpr ((Set.mem_union _ _ _).mpr (Or.inl ((Set.memS_iff _ _).mp h)))

theorem cs_memS_union_right {a b : List GroundTerm} {x : GroundTerm} (h : memS x b = true) :
    memS x (unionS a b) = true :=
  (Set.memS_iff _ _).mpr ((Set.mem_union _ _ _).mpr (Or.inr ((Set.memS_iff _ _).mp h)))

theorem cs_not_mem {x : GroundTerm} {a : List GroundTerm} (h : memS x a = false) : x ∉ a := by
  rw [← Set.memS_iff, h]; exact Bool.false_ne_true

/-- The set equations' sides, characterised by membership. -/
theorem cs_ext {a b : List GroundTerm} (ha : Set.Canon a) (hb : Set.Canon b) (h : ∀ y, y ∈ a ↔ y ∈ b) :
    GroundTerm.set Srt.set a = .set Srt.set b := by rw [Set.ext ha hb h]

/-! ## 425: `(K |-> _ M:Map) [ K <- undef ] => M ensures notBool (K in_keys(M))` -/

def msRemConcat : EqnE :=
  ⟨[("VarK", Srt.kitem), ("Var'Unds'Gen0", Srt.kitem), ("VarM", Srt.map)], Srt.map,
    .app mapRemove [.app mapConcat [.app mapElem [.var 0, .var 1], .var 2], .var 0], .var 2,
    .app boolNot [.app mapInKeys [.var 0, .var 2]]⟩

theorem msRemConcat_holds {c : Semantics} (hs : c.shapesOK = true) : msRemConcat.Holds c := by
  intro σ hσ
  obtain ⟨k, hk, -⟩ := hσ 0 ("VarK", Srt.kitem) rfl
  obtain ⟨v0, hv0, -⟩ := hσ 1 ("Var'Unds'Gen0", Srt.kitem) rfl
  obtain ⟨m, hm, -⟩ := fq_map_at hs hσ 2 (n := "VarM") rfl
  simp only [msRemConcat]
  cs_eval [hk, hv0, hm, cs_union_single]
  cases hkm : hasKey k m
  · simp [csHv_mapRemove, cs_eraseK_insertE k v0 hkm, bool]
  · simp [bool]

theorem msRemConcat_ev {c : Semantics} (h : c.coreOK = true) (hs : c.shapesOK = true) (ad : KoreAML.AxiomDecl)
    (hp : ad.ax.pattern = msRemConcat.patR) (hsv : ad.ax.sortVars = [KoreAML.Rv]) :
    EntailsAtValues c ad (KoreAML.trAxiom [] [] ad).pat :=
  EqnE.entailed_reg h msRemConcat (by decide) (by rfl) (msRemConcat_holds hs) ad hp hsv

/-! ## 432: `(K |-> V M:Map) [ K ] => V ensures notBool (K in_keys(M))` -/

def msLookupConcat : EqnE :=
  ⟨[("VarK", Srt.kitem), ("VarV", Srt.kitem), ("VarM", Srt.map)], Srt.kitem,
    .app mapLookup [.app mapConcat [.app mapElem [.var 0, .var 1], .var 2], .var 0], .var 1,
    .app boolNot [.app mapInKeys [.var 0, .var 2]]⟩

theorem msLookupConcat_holds {c : Semantics} (hs : c.shapesOK = true) : msLookupConcat.Holds c := by
  intro σ hσ
  obtain ⟨k, hk, -⟩ := hσ 0 ("VarK", Srt.kitem) rfl
  obtain ⟨v, hv, -⟩ := hσ 1 ("VarV", Srt.kitem) rfl
  obtain ⟨m, hm, -⟩ := fq_map_at hs hσ 2 (n := "VarM") rfl
  simp only [msLookupConcat]
  cs_eval [hk, hv, hm, cs_union_single]
  cases hkm : hasKey k m
  · simp [csHv_mapLookup, Map.find_insert_self, bool]
  · simp [bool]

theorem msLookupConcat_ev {c : Semantics} (h : c.coreOK = true) (hs : c.shapesOK = true) (ad : KoreAML.AxiomDecl)
    (hp : ad.ax.pattern = msLookupConcat.patR) (hsv : ad.ax.sortVars = [KoreAML.Rv]) :
    EntailsAtValues c ad (KoreAML.trAxiom [] [] ad).pat :=
  EqnE.entailed_reg h msLookupConcat (by decide) (by rfl) (msLookupConcat_holds hs) ad hp hsv

/-! ## 437: `(K |-> V M:Map) [ K ] orDefault _ => V ensures notBool (K in_keys(M))` -/

def msLookupDefConcat : EqnE :=
  ⟨[("VarK", Srt.kitem), ("VarV", Srt.kitem), ("VarM", Srt.map), ("Var'Unds'Gen0", Srt.kitem)], Srt.kitem,
    .app mapLookupOrDefault [.app mapConcat [.app mapElem [.var 0, .var 1], .var 2], .var 0, .var 3], .var 1,
    .app boolNot [.app mapInKeys [.var 0, .var 2]]⟩

theorem msLookupDefConcat_holds {c : Semantics} (hs : c.shapesOK = true) : msLookupDefConcat.Holds c := by
  intro σ hσ
  obtain ⟨k, hk, -⟩ := hσ 0 ("VarK", Srt.kitem) rfl
  obtain ⟨v, hv, -⟩ := hσ 1 ("VarV", Srt.kitem) rfl
  obtain ⟨m, hm, -⟩ := fq_map_at hs hσ 2 (n := "VarM") rfl
  obtain ⟨d, hd, -⟩ := hσ 3 ("Var'Unds'Gen0", Srt.kitem) rfl
  simp only [msLookupDefConcat]
  cs_eval [hk, hv, hm, hd, cs_union_single]
  cases hkm : hasKey k m
  · simp [csHv_mapLookupOrDefault, Map.find_insert_self, bool]
  · simp [bool]

theorem msLookupDefConcat_ev {c : Semantics} (h : c.coreOK = true) (hs : c.shapesOK = true)
    (ad : KoreAML.AxiomDecl) (hp : ad.ax.pattern = msLookupDefConcat.patR) (hsv : ad.ax.sortVars = [KoreAML.Rv]) :
    EntailsAtValues c ad (KoreAML.trAxiom [] [] ad).pat :=
  EqnE.entailed_reg h msLookupDefConcat (by decide) (by rfl) (msLookupDefConcat_holds hs) ad hp hsv

/-! ## The SET equations with `ensures notBool (X in S)`

Each left side applies `_Set_` to `S` and `SetItem(X)`, which has a value exactly where `X` is no
member of `S`, the `ensures`. -/

/-- 837: `SetItem(X) -Set (S SetItem(X)) => .Set ensures notBool (X in S)`. -/
def ssItemDiffConcat : EqnE :=
  ⟨[("VarS", Srt.set), ("VarX", Srt.kitem)], Srt.set,
    .app setDifference [.app setElem [.var 1], .app setConcat [.var 0, .app setElem [.var 1]]], .app setUnit [],
    .app boolNot [.app setIn [.var 1, .var 0]]⟩

theorem ssItemDiffConcat_holds {c : Semantics} (hs : c.shapesOK = true) : ssItemDiffConcat.Holds c := by
  intro σ hσ
  obtain ⟨a, ha, hca⟩ := fq_set_at hs hσ 0 (n := "VarS") rfl
  obtain ⟨x, hx, -⟩ := hσ 1 ("VarX", Srt.kitem) rfl
  simp only [ssItemDiffConcat]
  cs_eval [ha, hx, csHv_setElem, fhv_setConcat, cs_concatS_single, cs_concatS_single_left]
  cases hxa : memS x a
  · simp [fhv_setDifference, cs_memS_union_single, bool]
  · simp [bool]

theorem ssItemDiffConcat_ev {c : Semantics} (h : c.coreOK = true) (hs : c.shapesOK = true) (ad : KoreAML.AxiomDecl)
    (hp : ad.ax.pattern = ssItemDiffConcat.patR) (hsv : ad.ax.sortVars = [KoreAML.Rv]) :
    EntailsAtValues c ad (KoreAML.trAxiom [] [] ad).pat :=
  EqnE.entailed_reg h ssItemDiffConcat (by decide) (by rfl) (ssItemDiffConcat_holds hs) ad hp hsv

/-- 839: `S -Set (S SetItem(X)) => .Set ensures notBool (X in S)`. -/
def ssDiffConcat : EqnE :=
  ⟨[("VarS", Srt.set), ("VarX", Srt.kitem)], Srt.set,
    .app setDifference [.var 0, .app setConcat [.var 0, .app setElem [.var 1]]], .app setUnit [],
    .app boolNot [.app setIn [.var 1, .var 0]]⟩

theorem ssDiffConcat_holds {c : Semantics} (hs : c.shapesOK = true) : ssDiffConcat.Holds c := by
  intro σ hσ
  obtain ⟨a, ha, hca⟩ := fq_set_at hs hσ 0 (n := "VarS") rfl
  obtain ⟨x, hx, -⟩ := hσ 1 ("VarX", Srt.kitem) rfl
  simp only [ssDiffConcat]
  cs_eval [ha, hx, csHv_setElem, fhv_setConcat, cs_concatS_single, cs_concatS_single_left]
  cases hxa : memS x a
  · have : a.filter (!memS · (unionS a [x])) = [] := List.filter_eq_nil_iff.mpr fun y hy => by
      rw [Bool.not_eq_true', Bool.not_eq_false]
      exact (Set.memS_iff _ _).mpr ((Set.mem_union _ _ _).mpr (Or.inl hy))
    simp [fhv_setDifference, this, bool]
  · simp [bool]

theorem ssDiffConcat_ev {c : Semantics} (h : c.coreOK = true) (hs : c.shapesOK = true) (ad : KoreAML.AxiomDecl)
    (hp : ad.ax.pattern = ssDiffConcat.patR) (hsv : ad.ax.sortVars = [KoreAML.Rv]) :
    EntailsAtValues c ad (KoreAML.trAxiom [] [] ad).pat :=
  EqnE.entailed_reg h ssDiffConcat (by decide) (by rfl) (ssDiffConcat_holds hs) ad hp hsv

/-- 841: `(S SetItem(X)) -Set S => SetItem(X) ensures notBool (X in S)`. -/
def ssConcatDiff : EqnE :=
  ⟨[("VarS", Srt.set), ("VarX", Srt.kitem)], Srt.set,
    .app setDifference [.app setConcat [.var 0, .app setElem [.var 1]], .var 0], .app setElem [.var 1],
    .app boolNot [.app setIn [.var 1, .var 0]]⟩

theorem ssConcatDiff_holds {c : Semantics} (hs : c.shapesOK = true) : ssConcatDiff.Holds c := by
  intro σ hσ
  obtain ⟨a, ha, hca⟩ := fq_set_at hs hσ 0 (n := "VarS") rfl
  obtain ⟨x, hx, -⟩ := hσ 1 ("VarX", Srt.kitem) rfl
  simp only [ssConcatDiff]
  cs_eval [ha, hx, csHv_setElem, fhv_setConcat, cs_concatS_single, cs_concatS_single_left]
  cases hxa : memS x a
  · have hx' := cs_not_mem hxa
    have : GroundTerm.set Srt.set ((unionS a [x]).filter (!memS · a)) = .set Srt.set [x] :=
      cs_ext (Set.filter_canon (Set.union_canon (cs_canon_single x)) _) (cs_canon_single x) fun y => by
        simp only [Set.mem_diff, Set.mem_union, cs_mem_single]
        constructor
        · rintro ⟨h1 | h1, h2⟩; exact absurd h1 h2; exact h1
        · rintro rfl; exact ⟨Or.inr rfl, hx'⟩
    simp [fhv_setDifference, this, bool]
  · simp [bool]

theorem ssConcatDiff_ev {c : Semantics} (h : c.coreOK = true) (hs : c.shapesOK = true) (ad : KoreAML.AxiomDecl)
    (hp : ad.ax.pattern = ssConcatDiff.patR) (hsv : ad.ax.sortVars = [KoreAML.Rv]) :
    EntailsAtValues c ad (KoreAML.trAxiom [] [] ad).pat :=
  EqnE.entailed_reg h ssConcatDiff (by decide) (by rfl) (ssConcatDiff_holds hs) ad hp hsv

/-- 843: `(S SetItem(X)) -Set SetItem(X) => S ensures notBool (X in S)`. -/
def ssConcatDiffItem : EqnE :=
  ⟨[("VarS", Srt.set), ("VarX", Srt.kitem)], Srt.set,
    .app setDifference [.app setConcat [.var 0, .app setElem [.var 1]], .app setElem [.var 1]], .var 0,
    .app boolNot [.app setIn [.var 1, .var 0]]⟩

theorem ssConcatDiffItem_holds {c : Semantics} (hs : c.shapesOK = true) : ssConcatDiffItem.Holds c := by
  intro σ hσ
  obtain ⟨a, ha, hca⟩ := fq_set_at hs hσ 0 (n := "VarS") rfl
  obtain ⟨x, hx, -⟩ := hσ 1 ("VarX", Srt.kitem) rfl
  simp only [ssConcatDiffItem]
  cs_eval [ha, hx, csHv_setElem, fhv_setConcat, cs_concatS_single, cs_concatS_single_left]
  cases hxa : memS x a
  · have hx' := cs_not_mem hxa
    have : GroundTerm.set Srt.set ((unionS a [x]).filter (!memS · [x])) = .set Srt.set a :=
      cs_ext (Set.filter_canon (Set.union_canon (cs_canon_single x)) _) hca fun y => by
        simp only [Set.mem_diff, Set.mem_union, cs_mem_single]
        constructor
        · rintro ⟨h1 | h1, h2⟩; exact h1; exact absurd h1 h2
        · intro hy; exact ⟨Or.inl hy, fun h' => hx' (h' ▸ hy)⟩
    simp [fhv_setDifference, this, bool]
  · simp [bool]

theorem ssConcatDiffItem_ev {c : Semantics} (h : c.coreOK = true) (hs : c.shapesOK = true) (ad : KoreAML.AxiomDecl)
    (hp : ad.ax.pattern = ssConcatDiffItem.patR) (hsv : ad.ax.sortVars = [KoreAML.Rv]) :
    EntailsAtValues c ad (KoreAML.trAxiom [] [] ad).pat :=
  EqnE.entailed_reg h ssConcatDiffItem (by decide) (by rfl) (ssConcatDiffItem_holds hs) ad hp hsv

/-- 857 (`comm`): `SetItem(X) |Set (S SetItem(X)) => S SetItem(X) ensures notBool (X in S)`. -/
def ssItemUnionConcat : EqnE :=
  ⟨[("VarS", Srt.set), ("VarX", Srt.kitem)], Srt.set,
    .app setUnion [.app setElem [.var 1], .app setConcat [.var 0, .app setElem [.var 1]]],
    .app setConcat [.var 0, .app setElem [.var 1]], .app boolNot [.app setIn [.var 1, .var 0]]⟩

theorem ssItemUnionConcat_holds {c : Semantics} (hs : c.shapesOK = true) : ssItemUnionConcat.Holds c := by
  intro σ hσ
  obtain ⟨a, ha, hca⟩ := fq_set_at hs hσ 0 (n := "VarS") rfl
  obtain ⟨x, hx, -⟩ := hσ 1 ("VarX", Srt.kitem) rfl
  simp only [ssItemUnionConcat]
  cs_eval [ha, hx, csHv_setElem, fhv_setConcat, cs_concatS_single, cs_concatS_single_left]
  cases hxa : memS x a
  · have : GroundTerm.set Srt.set (unionS [x] (unionS a [x])) = .set Srt.set (unionS a [x]) :=
      cs_ext (Set.union_canon (Set.union_canon (cs_canon_single x))) (Set.union_canon (cs_canon_single x))
        fun y => by
          simp only [Set.mem_union, cs_mem_single]
          constructor
          · rintro (h1 | h1 | h1); exact Or.inr h1; exact Or.inl h1; exact Or.inr h1
          · rintro (h1 | h1); exact Or.inr (Or.inl h1); exact Or.inl h1
    simp [fhv_setUnion, this, bool]
  · simp [bool]

theorem ssItemUnionConcat_ev {c : Semantics} (h : c.coreOK = true) (hs : c.shapesOK = true)
    (ad : KoreAML.AxiomDecl) (hp : ad.ax.pattern = ssItemUnionConcat.patR) (hsv : ad.ax.sortVars = [KoreAML.Rv]) :
    EntailsAtValues c ad (KoreAML.trAxiom [] [] ad).pat :=
  EqnE.entailed_reg h ssItemUnionConcat (by decide) (by rfl) (ssItemUnionConcat_holds hs) ad hp hsv

/-- 857: `(S SetItem(X)) |Set SetItem(X) => S SetItem(X) ensures notBool (X in S)`. -/
def ssConcatUnionItem : EqnE :=
  ⟨[("VarS", Srt.set), ("VarX", Srt.kitem)], Srt.set,
    .app setUnion [.app setConcat [.var 0, .app setElem [.var 1]], .app setElem [.var 1]],
    .app setConcat [.var 0, .app setElem [.var 1]], .app boolNot [.app setIn [.var 1, .var 0]]⟩

theorem ssConcatUnionItem_holds {c : Semantics} (hs : c.shapesOK = true) : ssConcatUnionItem.Holds c := by
  intro σ hσ
  obtain ⟨a, ha, hca⟩ := fq_set_at hs hσ 0 (n := "VarS") rfl
  obtain ⟨x, hx, -⟩ := hσ 1 ("VarX", Srt.kitem) rfl
  simp only [ssConcatUnionItem]
  cs_eval [ha, hx, csHv_setElem, fhv_setConcat, cs_concatS_single, cs_concatS_single_left]
  cases hxa : memS x a
  · have : GroundTerm.set Srt.set (unionS (unionS a [x]) [x]) = .set Srt.set (unionS a [x]) :=
      cs_ext (Set.union_canon (cs_canon_single x)) (Set.union_canon (cs_canon_single x)) fun y => by
        simp only [Set.mem_union, cs_mem_single]
        constructor
        · rintro ((h1 | h1) | h1); exact Or.inl h1; exact Or.inr h1; exact Or.inr h1
        · rintro (h1 | h1); exact Or.inl (Or.inl h1); exact Or.inr h1
    simp [fhv_setUnion, this, bool]
  · simp [bool]

theorem ssConcatUnionItem_ev {c : Semantics} (h : c.coreOK = true) (hs : c.shapesOK = true)
    (ad : KoreAML.AxiomDecl) (hp : ad.ax.pattern = ssConcatUnionItem.patR) (hsv : ad.ax.sortVars = [KoreAML.Rv]) :
    EntailsAtValues c ad (KoreAML.trAxiom [] [] ad).pat :=
  EqnE.entailed_reg h ssConcatUnionItem (by decide) (by rfl) (ssConcatUnionItem_holds hs) ad hp hsv

/-- 867 (`comm`): `intersectSet(SetItem(X), S SetItem(X)) => SetItem(X) ensures notBool (X in S)`. -/
def ssItemInterConcat : EqnE :=
  ⟨[("VarS", Srt.set), ("VarX", Srt.kitem)], Srt.set,
    .app setIntersect [.app setElem [.var 1], .app setConcat [.var 0, .app setElem [.var 1]]],
    .app setElem [.var 1], .app boolNot [.app setIn [.var 1, .var 0]]⟩

theorem ssItemInterConcat_holds {c : Semantics} (hs : c.shapesOK = true) : ssItemInterConcat.Holds c := by
  intro σ hσ
  obtain ⟨a, ha, hca⟩ := fq_set_at hs hσ 0 (n := "VarS") rfl
  obtain ⟨x, hx, -⟩ := hσ 1 ("VarX", Srt.kitem) rfl
  simp only [ssItemInterConcat]
  cs_eval [ha, hx, csHv_setElem, fhv_setConcat, cs_concatS_single, cs_concatS_single_left]
  cases hxa : memS x a
  · simp [csHv_setIntersect, cs_memS_union_single, bool]
  · simp [bool]

theorem ssItemInterConcat_ev {c : Semantics} (h : c.coreOK = true) (hs : c.shapesOK = true)
    (ad : KoreAML.AxiomDecl) (hp : ad.ax.pattern = ssItemInterConcat.patR) (hsv : ad.ax.sortVars = [KoreAML.Rv]) :
    EntailsAtValues c ad (KoreAML.trAxiom [] [] ad).pat :=
  EqnE.entailed_reg h ssItemInterConcat (by decide) (by rfl) (ssItemInterConcat_holds hs) ad hp hsv

/-- 867: `intersectSet(S SetItem(X), SetItem(X)) => SetItem(X) ensures notBool (X in S)`. -/
def ssConcatInterItem : EqnE :=
  ⟨[("VarS", Srt.set), ("VarX", Srt.kitem)], Srt.set,
    .app setIntersect [.app setConcat [.var 0, .app setElem [.var 1]], .app setElem [.var 1]],
    .app setElem [.var 1], .app boolNot [.app setIn [.var 1, .var 0]]⟩

theorem ssConcatInterItem_holds {c : Semantics} (hs : c.shapesOK = true) : ssConcatInterItem.Holds c := by
  intro σ hσ
  obtain ⟨a, ha, hca⟩ := fq_set_at hs hσ 0 (n := "VarS") rfl
  obtain ⟨x, hx, -⟩ := hσ 1 ("VarX", Srt.kitem) rfl
  simp only [ssConcatInterItem]
  cs_eval [ha, hx, csHv_setElem, fhv_setConcat, cs_concatS_single, cs_concatS_single_left]
  cases hxa : memS x a
  · have : GroundTerm.set Srt.set ((unionS a [x]).filter (memS · [x])) = .set Srt.set [x] :=
      cs_ext (Set.filter_canon (Set.union_canon (cs_canon_single x)) _) (cs_canon_single x) fun y => by
        simp only [Set.mem_inter, Set.mem_union, cs_mem_single]
        constructor
        · rintro ⟨-, h2⟩; exact h2
        · rintro rfl; exact ⟨Or.inr rfl, rfl⟩
    simp [csHv_setIntersect, this, bool]
  · simp [bool]

theorem ssConcatInterItem_ev {c : Semantics} (h : c.coreOK = true) (hs : c.shapesOK = true)
    (ad : KoreAML.AxiomDecl) (hp : ad.ax.pattern = ssConcatInterItem.patR) (hsv : ad.ax.sortVars = [KoreAML.Rv]) :
    EntailsAtValues c ad (KoreAML.trAxiom [] [] ad).pat :=
  EqnE.entailed_reg h ssConcatInterItem (by decide) (by rfl) (ssConcatInterItem_holds hs) ad hp hsv

/-- 877: `E in (S SetItem(E)) => true ensures notBool (E in S)`. -/
def ssInConcat : EqnE :=
  ⟨[("VarS", Srt.set), ("VarE", Srt.kitem)], Srt.bool,
    .app setIn [.var 1, .app setConcat [.var 0, .app setElem [.var 1]]], boolT true,
    .app boolNot [.app setIn [.var 1, .var 0]]⟩

theorem ssInConcat_holds {c : Semantics} (hs : c.shapesOK = true) : ssInConcat.Holds c := by
  intro σ hσ
  obtain ⟨a, ha, hca⟩ := fq_set_at hs hσ 0 (n := "VarS") rfl
  obtain ⟨x, hx, -⟩ := hσ 1 ("VarE", Srt.kitem) rfl
  simp only [ssInConcat]
  cs_eval [ha, hx, csHv_setElem, fhv_setConcat, cs_concatS_single, cs_concatS_single_left]
  cases hxa : memS x a
  · simp [csHv_setIn, cs_memS_union_single, bool]
  · simp [bool]

theorem ssInConcat_ev {c : Semantics} (h : c.coreOK = true) (hs : c.shapesOK = true) (ad : KoreAML.AxiomDecl)
    (hp : ad.ax.pattern = ssInConcat.patR) (hsv : ad.ax.sortVars = [KoreAML.Rv]) :
    EntailsAtValues c ad (KoreAML.trAxiom [] [] ad).pat :=
  EqnE.entailed_reg h ssInConcat (by decide) (by rfl) (ssInConcat_holds hs) ad hp hsv

/-- 871: `intersectSet(S1 SetItem(X), S2 SetItem(X)) => intersectSet(S1, S2) SetItem(X)
ensures notBool (X in S1) andBool notBool (X in S2)`. -/
def ssInterConcat2 : EqnE :=
  ⟨[("VarS1", Srt.set), ("VarX", Srt.kitem), ("VarS2", Srt.set)], Srt.set,
    .app setIntersect [.app setConcat [.var 0, .app setElem [.var 1]], .app setConcat [.var 2, .app setElem [.var 1]]],
    .app setConcat [.app setIntersect [.var 0, .var 2], .app setElem [.var 1]],
    .app boolAnd [.app boolNot [.app setIn [.var 1, .var 0]], .app boolNot [.app setIn [.var 1, .var 2]]]⟩

theorem ssInterConcat2_holds {c : Semantics} (hs : c.shapesOK = true) : ssInterConcat2.Holds c := by
  intro σ hσ
  obtain ⟨a, ha, hca⟩ := fq_set_at hs hσ 0 (n := "VarS1") rfl
  obtain ⟨x, hx, -⟩ := hσ 1 ("VarX", Srt.kitem) rfl
  obtain ⟨b, hb, hcb⟩ := fq_set_at hs hσ 2 (n := "VarS2") rfl
  simp only [ssInterConcat2]
  cs_eval [ha, hx, hb, csHv_setElem, fhv_setConcat, cs_concatS_single, hvb_and]
  have hfx : memS x (a.filter (memS · b)) = (memS x a && memS x b) := by
    rw [Bool.eq_iff_iff, Set.memS_iff, Set.mem_inter, Bool.and_eq_true, Set.memS_iff, Set.memS_iff]
  cases hxa : memS x a
  · cases hxb : memS x b
    · have hxa' := cs_not_mem hxa
      have hxb' := cs_not_mem hxb
      have : GroundTerm.set Srt.set ((unionS a [x]).filter (memS · (unionS b [x]))) =
          .set Srt.set (unionS (a.filter (memS · b)) [x]) :=
        cs_ext (Set.filter_canon (Set.union_canon (cs_canon_single x)) _) (Set.union_canon (cs_canon_single x))
          fun y => by
            simp only [Set.mem_inter, Set.mem_union, cs_mem_single]
            constructor
            · rintro ⟨h1 | h1, h2 | h2⟩
              · exact Or.inl ⟨h1, h2⟩
              · exact Or.inr h2
              · exact Or.inr h1
              · exact Or.inr h1
            · rintro (⟨h1, h2⟩ | h1)
              · exact ⟨Or.inl h1, Or.inl h2⟩
              · exact ⟨Or.inr h1, Or.inr h1⟩
      simp [csHv_setIntersect, hfx, hxa, hxb, this, bool]
    · simp [bool]
  · simp [bool]

theorem ssInterConcat2_ev {c : Semantics} (h : c.coreOK = true) (hs : c.shapesOK = true) (ad : KoreAML.AxiomDecl)
    (hp : ad.ax.pattern = ssInterConcat2.patR) (hsv : ad.ax.sortVars = [KoreAML.Rv]) :
    EntailsAtValues c ad (KoreAML.trAxiom [] [] ad).pat :=
  EqnE.entailed_reg h ssInterConcat2 (by decide) (by rfl) (ssInterConcat2_holds hs) ad hp hsv

/-- 886: `X in ((SetItem(X) S) |Set _) => true ensures notBool (X in S)`. -/
def ssInUnionL : EqnE :=
  ⟨[("VarS", Srt.set), ("VarX", Srt.kitem), ("Var'Unds'Gen0", Srt.set)], Srt.bool,
    .app setIn [.var 1, .app setUnion [.app setConcat [.app setElem [.var 1], .var 0], .var 2]], boolT true,
    .app boolNot [.app setIn [.var 1, .var 0]]⟩

theorem ssInUnionL_holds {c : Semantics} (hs : c.shapesOK = true) : ssInUnionL.Holds c := by
  intro σ hσ
  obtain ⟨a, ha, -⟩ := fq_set_at hs hσ 0 (n := "VarS") rfl
  obtain ⟨x, hx, -⟩ := hσ 1 ("VarX", Srt.kitem) rfl
  obtain ⟨b, hb, -⟩ := fq_set_at hs hσ 2 (n := "Var'Unds'Gen0") rfl
  simp only [ssInUnionL]
  cs_eval [ha, hx, hb, csHv_setElem, fhv_setConcat, cs_concatS_single_left]
  cases hxa : memS x a
  · simp [fhv_setUnion, csHv_setIn, cs_memS_union_left (cs_memS_single_union a x), bool]
  · simp [bool]

theorem ssInUnionL_ev {c : Semantics} (h : c.coreOK = true) (hs : c.shapesOK = true) (ad : KoreAML.AxiomDecl)
    (hp : ad.ax.pattern = ssInUnionL.patR) (hsv : ad.ax.sortVars = [KoreAML.Rv]) :
    EntailsAtValues c ad (KoreAML.trAxiom [] [] ad).pat :=
  EqnE.entailed_reg h ssInUnionL (by decide) (by rfl) (ssInUnionL_holds hs) ad hp hsv

/-- 888: `X in (_ |Set (SetItem(X) S)) => true ensures notBool (X in S)`. -/
def ssInUnionR : EqnE :=
  ⟨[("VarS", Srt.set), ("VarX", Srt.kitem), ("Var'Unds'Gen0", Srt.set)], Srt.bool,
    .app setIn [.var 1, .app setUnion [.var 2, .app setConcat [.app setElem [.var 1], .var 0]]], boolT true,
    .app boolNot [.app setIn [.var 1, .var 0]]⟩

theorem ssInUnionR_holds {c : Semantics} (hs : c.shapesOK = true) : ssInUnionR.Holds c := by
  intro σ hσ
  obtain ⟨a, ha, -⟩ := fq_set_at hs hσ 0 (n := "VarS") rfl
  obtain ⟨x, hx, -⟩ := hσ 1 ("VarX", Srt.kitem) rfl
  obtain ⟨b, hb, -⟩ := fq_set_at hs hσ 2 (n := "Var'Unds'Gen0") rfl
  simp only [ssInUnionR]
  cs_eval [ha, hx, hb, csHv_setElem, fhv_setConcat, cs_concatS_single_left]
  cases hxa : memS x a
  · simp [fhv_setUnion, csHv_setIn, cs_memS_union_right (cs_memS_single_union a x), bool]
  · simp [bool]

theorem ssInUnionR_ev {c : Semantics} (h : c.coreOK = true) (hs : c.shapesOK = true) (ad : KoreAML.AxiomDecl)
    (hp : ad.ax.pattern = ssInUnionR.patR) (hsv : ad.ax.sortVars = [KoreAML.Rv]) :
    EntailsAtValues c ad (KoreAML.trAxiom [] [] ad).pat :=
  EqnE.entailed_reg h ssInUnionR (by decide) (by rfl) (ssInUnionR_holds hs) ad hp hsv

/-! ## 449, 450: `{false #Equals @Key in_keys(.Map)} => #Ceil(@Key)` and the flip

Over a set variable: `@Key in_keys(.Map)` denotes `false` once for each member of `@Key`, so it is
`false` alone exactly where `@Key` is not empty, and nothing where it is. -/

/-- The sentence, `flip` with `false` second. -/
def msInKeysUnitSv (flip : Bool) : SvEqn :=
  let t : Term := .app mapInKeys [.var 0, .app mapUnit []]
  ⟨[("VarKey", Srt.kitem)], if flip then .eq Srt.bool t (boolT false) else .eq Srt.bool (boolT false) t,
    .ceil Srt.kitem (.var 0)⟩

theorem msInKeysUnitSv_apart {c : Semantics} (h : c.coreOK = true) (flip : Bool) :
    (msInKeysUnitSv flip).lhs.Apart c ∧ (msInKeysUnitSv flip).rhs.Apart c := by
  haveI : OvlOK c := ovlOK_of_core h
  cases flip <;> exact ⟨apart_of_distinct bool_distinct, trivial⟩

theorem msInKeysUnitSv_vals {c : Semantics} (ρ : Nat → GroundTerm → Prop) (v : GroundTerm) :
    svVals c ρ (.app mapInKeys [.var 0, .app mapUnit []]) v ↔ (∃ w, ρ 0 w) ∧ v = bool false := by
  simp only [svVals, svValsList]
  constructor
  · rintro ⟨_, ⟨w, _, rfl, hw, u, _, rfl, ⟨_, rfl, hu⟩, rfl⟩, hv⟩
    rw [fhv_mapUnit] at hu
    cases hu
    rw [csHv_mapInKeys] at hv
    cases hv
    exact ⟨⟨w, hw⟩, rfl⟩
  · rintro ⟨⟨w, hw⟩, rfl⟩
    exact ⟨[w, .map Srt.map []], ⟨w, _, rfl, hw, _, [], rfl, ⟨[], rfl, fhv_mapUnit⟩, rfl⟩, csHv_mapInKeys _ _ _⟩

theorem msInKeysUnitSv_holds {c : Semantics} (flip : Bool) : (msInKeysUnitSv flip).Holds c (fun _ => True) := by
  intro ρ _ _
  cases flip
  · simp only [msInKeysUnitSv, Bool.false_eq_true, ite_false, SvPred.Holds, msInKeysUnitSv_vals]
    simp [svVals, boolT, bool]
  · simp only [msInKeysUnitSv, ite_true, SvPred.Holds, msInKeysUnitSv_vals]
    simp [svVals, boolT, bool]

theorem msInKeysUnitSv_ev {c : Semantics} (h : c.coreOK = true) (flip : Bool) (ad : KoreAML.AxiomDecl)
    (hp : ad.ax.pattern = (msInKeysUnitSv flip).patR) (hsv : ad.ax.sortVars = [KoreAML.Rv, Q0v]) :
    EntailsAtSetValues c ad (KoreAML.trAxiom [] [] ad).pat := by
  have hr : (msInKeysUnitSv flip).regular = true := by cases flip <;> decide +kernel
  have ht : (msInKeysUnitSv flip).typed c = true := by cases flip <;> rfl
  exact SvEqn.entailed h _ hr ht (msInKeysUnitSv_apart h flip) (msInKeysUnitSv_holds flip) ad hp hsv

end LibEv

end KCore
