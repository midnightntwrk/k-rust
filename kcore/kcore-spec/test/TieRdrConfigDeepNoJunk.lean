/-
  Part NoJunk of the tie (C14) on `f2-examples/rdr-config-deep.kompile.kore`, test/TieRdrConfigDeep.lean: the sections
  `--split` puts here, in the tie's namespace. A test file imports no test file, so this one
  repeats the literals and the definitions and facts it reads. Written by
  `TIEGEN_PROBE_TIMEOUT=3000 python3 -I test/constructs/tiegen.py rdr-config-deep --split --cons-head
  --wf-parts --sig-chunk-first 13 --account-sorted --heads-literal --heads-codes --chunk 50
  --attrs-blocks 50 --decl-parts --fn-blocks 27 --absent-file --decl-syms-literal --nojunk-eq
  --nojunk-blocks 25`;
  run from the package root: `lake env lean -j1 test/TieRdrConfigDeepNoJunk.lean`
  (193 s, peak 6.4 GiB under a 12 GiB scope with one Lean thread).
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.TieRdrConfigDeep

open KCore ML Faithful KoreAML

kore_term kore from "f2-examples/rdr-config-deep.kompile.kore"
definition_of defn from "f2-examples/rdr-config-deep.kompile.kore"
user_axioms U from "f2-examples/rdr-config-deep.kompile.kore" module "RDR-CONFIG-DEEP"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

/-- `tr s`: the item `Theory.ofDefinition kore` holds for the sentence. -/
noncomputable def trS (ad : AxiomDecl) : Item := trAxiom kore.symbolDecls kore.aliasNames ad

/-! ## No junk -/

/-- `\or{S}(\top{S}(), \bottom{S}())` as an axiom: `⊤ ⇒ (⊤_S ∨ ⊥_S ≡ ⟦S⟧)`. -/
def orTopBot (S : P) : P := conjList [] ⇒ (sOr S (sTop S) (sBot S) ≡ inhOf S)

theorem orTopBot_valid {M : Type} {I : Interpretation KoreAML.Sym M} (hD : DefOK I) {S : P}
    (hS : S.isFreeEvar topVar = false) : I ⊧ᴵ orTopBot S := by
  intro e m
  unfold orTopBot
  rw [interpret_impl]
  intro _
  rw [interp_equal hD]
  intro a
  rw [interp_sOr, interp_sTop hD hS]
  exact ⟨fun h => h.1, fun h => ⟨h, Or.inl h⟩⟩

theorem nj835 : (trS U.ax835).pat = orTopBot (sym (.sort "SortBool")) := by decide +kernel
theorem nj1029 : (trS U.ax1029).pat = orTopBot (sym (.sort "SortInt")) := by decide +kernel
theorem nj1032 : (trS U.ax1032).pat = orTopBot (sym (.sort "SortKConfigVar")) := by decide +kernel

/-- **E for the no-junk sentences of the sorts without generators**: logical truths, entailed by
Γ for every H. -/
theorem nojunk_trivial_entailed (H : HookParams) :
    ∀ ad ∈ [U.ax835, U.ax1029, U.ax1032], Γ (cH H) ⊧ (trS ad).pat := by
  intro ad had M _ I hI
  have hD := defOK hI
  simp only [List.mem_cons, List.not_mem_nil, or_false] at had
  rcases had with rfl | rfl | rfl
  · rw [nj835]; exact orTopBot_valid hD rfl
  · rw [nj1029]; exact orTopBot_valid hD rfl
  · rw [nj1032]; exact orTopBot_valid hD rfl

/-- The text's alias names, written out. -/
def aliasLit : List String := ["weakExistsFinally", "weakAlwaysFinally", "allPathGlobally"]

theorem aliasLit_eq : kore.aliasNames = aliasLit := by decide +kernel

/-- The pattern is a `\or` at the sort `S`. -/
def njIsOr (S : Kore.KSort) : Kore.Pattern → Bool
  | .or S' _ => decide (S' = S)
  | _ => false

/-- The disjuncts of a `\or`. -/
def njOrArgs : Kore.Pattern → List Kore.Pattern
  | .or _ ds => ds
  | _ => []

theorem njOr_eq {S : Kore.KSort} {p : Kore.Pattern} (h : njIsOr S p = true) : p = .or S (njOrArgs p) := by
  cases p <;> simp_all [njIsOr, njOrArgs]

/-- Two disjunctions whose operands translate to the same patterns translate to the same pattern. -/
theorem njTrOrList_eq {c1 c2 : Ctx} {s : P} : ∀ {ds1 ds2 : List Kore.Pattern},
    ds1.map (tr c1) = ds2.map (tr c2) → trOrList c1 s ds1 = trOrList c2 s ds2
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | [_], [_], h => by simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at h; simp [trOrList, h]
  | [_], _ :: _ :: _, h => by simp at h
  | _ :: _ :: _, [_], h => by simp at h
  | p1 :: q1 :: qs1, p2 :: q2 :: qs2, h => by
    rw [List.map_cons, List.map_cons] at h
    obtain ⟨h1, h2⟩ := List.cons.inj h
    have ih := njTrOrList_eq (c1 := c1) (c2 := c2) (s := s) (ds1 := q1 :: qs1) (ds2 := q2 :: qs2) h2
    simp only [trOrList] at ih ⊢
    rw [h1, ih]

/-- **Two `\or` sentences at a sort `N` translate to the same pattern** where neither has a sort
variable or a free variable and their disjuncts translate to the same patterns, each under its own
sentence's table: the guards are none, the sort is `N`'s, and the disjunction is the operands'. The
disjuncts need not be equal: the table makes the variables' names positions. -/
theorem njTrOr_pat {d1 d2 : List SymbolDecl} {al1 al2 : List String} {a1 a2 : AxiomDecl} {N : String}
    {ds1 ds2 : List Kore.Pattern}
    (hsv1 : a1.ax.sortVars = []) (hsv2 : a2.ax.sortVars = [])
    (hp1 : a1.ax.pattern = .or (KoreAML.srt N) ds1) (hp2 : a2.ax.pattern = .or (KoreAML.srt N) ds2)
    (hf1 : freeOfList [] ds1 = []) (hf2 : freeOfList [] ds2 = [])
    (hds : ds1.map (tr ⟨tableOf [] (.or (KoreAML.srt N) ds1), al1⟩) =
      ds2.map (tr ⟨tableOf [] (.or (KoreAML.srt N) ds2), al2⟩)) :
    (trAxiom d1 al1 a1).pat = (trAxiom d2 al2 a2).pat := by
  simp only [trAxiom, hsv1, hsv2, hp1, hp2, List.map_nil, List.nil_append, freeOf, hf1, hf2, sortOf, tr]
  rw [njTrOrList_eq hds]
  simp [trSort, trSortApp, KoreAML.srt]

/-- The no-junk sentences that are Γ's constructor items, each with the sort whose no-junk item
over `Semantics.gens` it is. -/
noncomputable def njEq : List (AxiomDecl × Srt) :=
  [(U.ax836, 57), (U.ax837, 59), (U.ax838, 58), (U.ax839, 60), (U.ax840, 62), (U.ax841, 61),
   (U.ax842, 63), (U.ax843, 65), (U.ax844, 64), (U.ax845, 66), (U.ax846, 68), (U.ax847, 67),
   (U.ax848, 69), (U.ax849, 71), (U.ax850, 70), (U.ax851, 72), (U.ax852, 74), (U.ax853, 73),
   (U.ax854, 75), (U.ax855, 77), (U.ax856, 76), (U.ax857, 78), (U.ax858, 80), (U.ax859, 79),
   (U.ax860, 81), (U.ax861, 83), (U.ax862, 82), (U.ax863, 84), (U.ax864, 86), (U.ax865, 85),
   (U.ax866, 30), (U.ax867, 32), (U.ax868, 31), (U.ax869, 87), (U.ax870, 89), (U.ax871, 88),
   (U.ax872, 90), (U.ax873, 92), (U.ax874, 91), (U.ax875, 93), (U.ax876, 95), (U.ax877, 94),
   (U.ax878, 96), (U.ax879, 98), (U.ax880, 97), (U.ax881, 99), (U.ax882, 101), (U.ax883, 100),
   (U.ax884, 102), (U.ax885, 104), (U.ax886, 103), (U.ax887, 105), (U.ax888, 107), (U.ax889, 106),
   (U.ax890, 108), (U.ax891, 110), (U.ax892, 109), (U.ax893, 111), (U.ax894, 113), (U.ax895, 112),
   (U.ax896, 114), (U.ax897, 116), (U.ax898, 115), (U.ax899, 33), (U.ax900, 35), (U.ax901, 34),
   (U.ax902, 117), (U.ax903, 119), (U.ax904, 118), (U.ax905, 120), (U.ax906, 122), (U.ax907, 121),
   (U.ax908, 123), (U.ax909, 125), (U.ax910, 124), (U.ax911, 126), (U.ax912, 128), (U.ax913, 127),
   (U.ax914, 129), (U.ax915, 131), (U.ax916, 130), (U.ax917, 132), (U.ax918, 134), (U.ax919, 133),
   (U.ax920, 135), (U.ax921, 137), (U.ax922, 136), (U.ax923, 138), (U.ax924, 140), (U.ax925, 139),
   (U.ax926, 141), (U.ax927, 143), (U.ax928, 142), (U.ax929, 144), (U.ax930, 146), (U.ax931, 145),
   (U.ax932, 36), (U.ax933, 38), (U.ax934, 37), (U.ax935, 147), (U.ax936, 149), (U.ax937, 148),
   (U.ax938, 150), (U.ax939, 152), (U.ax940, 151), (U.ax941, 153), (U.ax942, 155), (U.ax943, 154),
   (U.ax944, 156), (U.ax945, 158), (U.ax946, 157), (U.ax947, 159), (U.ax948, 161), (U.ax949, 160),
   (U.ax950, 162), (U.ax951, 164), (U.ax952, 163), (U.ax953, 165), (U.ax954, 167), (U.ax955, 166),
   (U.ax956, 168), (U.ax957, 170), (U.ax958, 169), (U.ax959, 171), (U.ax960, 173), (U.ax961, 172),
   (U.ax962, 174), (U.ax963, 176), (U.ax964, 175), (U.ax965, 39), (U.ax966, 41), (U.ax967, 40),
   (U.ax968, 177), (U.ax969, 179), (U.ax970, 178), (U.ax971, 180), (U.ax972, 182), (U.ax973, 181),
   (U.ax974, 183), (U.ax975, 185), (U.ax976, 184), (U.ax977, 186), (U.ax978, 188), (U.ax979, 187),
   (U.ax980, 189), (U.ax981, 191), (U.ax982, 190), (U.ax983, 192), (U.ax984, 194), (U.ax985, 193),
   (U.ax986, 195), (U.ax987, 197), (U.ax988, 196), (U.ax989, 198), (U.ax990, 200), (U.ax991, 199),
   (U.ax992, 201), (U.ax993, 203), (U.ax994, 202), (U.ax995, 204), (U.ax996, 206), (U.ax997, 205),
   (U.ax998, 42), (U.ax999, 44), (U.ax1000, 43), (U.ax1001, 207), (U.ax1002, 209), (U.ax1003, 208),
   (U.ax1004, 210), (U.ax1005, 212), (U.ax1006, 211), (U.ax1007, 213), (U.ax1008, 215),
   (U.ax1009, 214), (U.ax1010, 216), (U.ax1011, 218), (U.ax1012, 217), (U.ax1013, 45),
   (U.ax1014, 47), (U.ax1015, 46), (U.ax1016, 48), (U.ax1017, 50), (U.ax1018, 49), (U.ax1019, 51),
   (U.ax1020, 53), (U.ax1021, 52), (U.ax1022, 54), (U.ax1023, 56), (U.ax1024, 55), (U.ax1025, 19),
   (U.ax1026, 20), (U.ax1027, 17), (U.ax1028, 18), (U.ax1030, 219), (U.ax1031, 220)]

/-- The sentence `p.1` translates (with the alias names written out) to the no-junk item of the sort
`p.2` over `Semantics.gens`, and `p.2` is a constructor sort with generators. -/
noncomputable def njEqB (p : AxiomDecl × Srt) : Bool :=
  decide ((trAxiom kore.symbolDecls aliasLit p.1).pat =
      (KoreAML.Cons.noJunkItem (c.sortName p.2) ((c.gens p.2).map (Gen.toK c))).pat) &&
    decide (p.2 ∈ consSorts c) && !(c.gens p.2).isEmpty

theorem njEqE_0 : (((njEq).drop 0).take 50).all njEqB = true := by decide +kernel
theorem njEqE_50 : (((njEq).drop 50).take 50).all njEqB = true := by decide +kernel
theorem njEqE_100 : (((njEq).drop 100).take 50).all njEqB = true := by decide +kernel
theorem njEqE_150 : ((njEq).drop 150).all njEqB = true := by decide +kernel
theorem njEq_all : njEq.all njEqB = true :=
  tieAll_whole (l := njEq) (p := njEqB) <|
    tieAll_range (l := njEq) (p := njEqB) (a := 0) (n := 50) njEqE_0 <|
    tieAll_range (l := njEq) (p := njEqB) (a := 50) (n := 50) njEqE_50 <|
    tieAll_range (l := njEq) (p := njEqB) (a := 100) (n := 50) njEqE_100 <|
    njEqE_150

/-- A sentence `njEqB` holds of is Γ's no-junk item of its sort, an item of `consItemsK c`
(`tnjItem_any_of_eq`). -/
theorem njEq_any {l : List (AxiomDecl × Srt)} (h : l.all njEqB = true) :
    ∀ ad ∈ l.map (·.1), (consItemsK c).any (·.pat == (trS ad).pat) = true := by
  intro ad had
  obtain ⟨⟨ad', N⟩, hm, rfl⟩ := List.mem_map.mp had
  have hb := List.all_eq_true.mp h _ hm
  simp only [njEqB, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_eq_eq_not, Bool.not_true] at hb
  obtain ⟨⟨he, hN⟩, hg⟩ := hb
  rw [← aliasLit_eq] at he
  exact tnjItem_any_of_eq hN hg he

/-- **No junk of the sorts with generators**: the translation of each sentence is the pattern of
one of Γ's constructor items, its sort's no-junk item (`njEq_any`). -/
theorem nojunk_items : ∀ ad ∈ [U.ax836, U.ax837, U.ax838, U.ax839, U.ax840, U.ax841, U.ax842, U.ax843, U.ax844, U.ax845,
      U.ax846, U.ax847, U.ax848, U.ax849, U.ax850, U.ax851, U.ax852, U.ax853, U.ax854, U.ax855,
      U.ax856, U.ax857, U.ax858, U.ax859, U.ax860, U.ax861, U.ax862, U.ax863, U.ax864, U.ax865,
      U.ax866, U.ax867, U.ax868, U.ax869, U.ax870, U.ax871, U.ax872, U.ax873, U.ax874, U.ax875,
      U.ax876, U.ax877, U.ax878, U.ax879, U.ax880, U.ax881, U.ax882, U.ax883, U.ax884, U.ax885,
      U.ax886, U.ax887, U.ax888, U.ax889, U.ax890, U.ax891, U.ax892, U.ax893, U.ax894, U.ax895,
      U.ax896, U.ax897, U.ax898, U.ax899, U.ax900, U.ax901, U.ax902, U.ax903, U.ax904, U.ax905,
      U.ax906, U.ax907, U.ax908, U.ax909, U.ax910, U.ax911, U.ax912, U.ax913, U.ax914, U.ax915,
      U.ax916, U.ax917, U.ax918, U.ax919, U.ax920, U.ax921, U.ax922, U.ax923, U.ax924, U.ax925,
      U.ax926, U.ax927, U.ax928, U.ax929, U.ax930, U.ax931, U.ax932, U.ax933, U.ax934, U.ax935,
      U.ax936, U.ax937, U.ax938, U.ax939, U.ax940, U.ax941, U.ax942, U.ax943, U.ax944, U.ax945,
      U.ax946, U.ax947, U.ax948, U.ax949, U.ax950, U.ax951, U.ax952, U.ax953, U.ax954, U.ax955,
      U.ax956, U.ax957, U.ax958, U.ax959, U.ax960, U.ax961, U.ax962, U.ax963, U.ax964, U.ax965,
      U.ax966, U.ax967, U.ax968, U.ax969, U.ax970, U.ax971, U.ax972, U.ax973, U.ax974, U.ax975,
      U.ax976, U.ax977, U.ax978, U.ax979, U.ax980, U.ax981, U.ax982, U.ax983, U.ax984, U.ax985,
      U.ax986, U.ax987, U.ax988, U.ax989, U.ax990, U.ax991, U.ax992, U.ax993, U.ax994, U.ax995,
      U.ax996, U.ax997, U.ax998, U.ax999, U.ax1000, U.ax1001, U.ax1002, U.ax1003, U.ax1004,
      U.ax1005, U.ax1006, U.ax1007, U.ax1008, U.ax1009, U.ax1010, U.ax1011, U.ax1012, U.ax1013,
      U.ax1014, U.ax1015, U.ax1016, U.ax1017, U.ax1018, U.ax1019, U.ax1020, U.ax1021, U.ax1022,
      U.ax1023, U.ax1024, U.ax1025, U.ax1026, U.ax1027, U.ax1028, U.ax1030, U.ax1031],
    (consItemsK c).any (·.pat == (trS ad).pat) = true :=
  njEq_any njEq_all

kernel_rfl consItemsK_withHooks : ∀ (c : Semantics) (H : HookParams), consItemsK (c.withHooks H) = consItemsK c

/-- **E for those**: Γ entails each, for every H. -/
theorem nojunk_items_entailed (H : HookParams) : ∀ ad ∈ [U.ax836, U.ax837, U.ax838, U.ax839, U.ax840, U.ax841, U.ax842, U.ax843, U.ax844, U.ax845,
      U.ax846, U.ax847, U.ax848, U.ax849, U.ax850, U.ax851, U.ax852, U.ax853, U.ax854, U.ax855,
      U.ax856, U.ax857, U.ax858, U.ax859, U.ax860, U.ax861, U.ax862, U.ax863, U.ax864, U.ax865,
      U.ax866, U.ax867, U.ax868, U.ax869, U.ax870, U.ax871, U.ax872, U.ax873, U.ax874, U.ax875,
      U.ax876, U.ax877, U.ax878, U.ax879, U.ax880, U.ax881, U.ax882, U.ax883, U.ax884, U.ax885,
      U.ax886, U.ax887, U.ax888, U.ax889, U.ax890, U.ax891, U.ax892, U.ax893, U.ax894, U.ax895,
      U.ax896, U.ax897, U.ax898, U.ax899, U.ax900, U.ax901, U.ax902, U.ax903, U.ax904, U.ax905,
      U.ax906, U.ax907, U.ax908, U.ax909, U.ax910, U.ax911, U.ax912, U.ax913, U.ax914, U.ax915,
      U.ax916, U.ax917, U.ax918, U.ax919, U.ax920, U.ax921, U.ax922, U.ax923, U.ax924, U.ax925,
      U.ax926, U.ax927, U.ax928, U.ax929, U.ax930, U.ax931, U.ax932, U.ax933, U.ax934, U.ax935,
      U.ax936, U.ax937, U.ax938, U.ax939, U.ax940, U.ax941, U.ax942, U.ax943, U.ax944, U.ax945,
      U.ax946, U.ax947, U.ax948, U.ax949, U.ax950, U.ax951, U.ax952, U.ax953, U.ax954, U.ax955,
      U.ax956, U.ax957, U.ax958, U.ax959, U.ax960, U.ax961, U.ax962, U.ax963, U.ax964, U.ax965,
      U.ax966, U.ax967, U.ax968, U.ax969, U.ax970, U.ax971, U.ax972, U.ax973, U.ax974, U.ax975,
      U.ax976, U.ax977, U.ax978, U.ax979, U.ax980, U.ax981, U.ax982, U.ax983, U.ax984, U.ax985,
      U.ax986, U.ax987, U.ax988, U.ax989, U.ax990, U.ax991, U.ax992, U.ax993, U.ax994, U.ax995,
      U.ax996, U.ax997, U.ax998, U.ax999, U.ax1000, U.ax1001, U.ax1002, U.ax1003, U.ax1004,
      U.ax1005, U.ax1006, U.ax1007, U.ax1008, U.ax1009, U.ax1010, U.ax1011, U.ax1012, U.ax1013,
      U.ax1014, U.ax1015, U.ax1016, U.ax1017, U.ax1018, U.ax1019, U.ax1020, U.ax1021, U.ax1022,
      U.ax1023, U.ax1024, U.ax1025, U.ax1026, U.ax1027, U.ax1028, U.ax1030, U.ax1031],
    Γ (cH H) ⊧ (trS ad).pat := by
  intro ad had M _ I hI
  obtain ⟨it, hit, he⟩ := List.any_eq_true.mp (nojunk_items ad had)
  rw [← of_decide_eq_true he]
  exact sat_cons hI (Or.inl ⟨it, by rw [consItemsK_withHooks]; exact hit, rfl⟩)

/-- KItem's no-junk sentence is the item over KItem's generators in the text's order, the same
generators as `Semantics.gens` lists, in another order. -/
theorem nojunk_kitem_name : c.sortName Srt.kitem = "KItem" := by decide +kernel

/-- KItem's generators in the text's order (`gensInOrder`), written out. -/
def nojunk_kitem_gens : List KoreAML.Gen :=
  [.inj "Bool", .inj "C10Cell", .inj "C10CellFragment", .inj "C10CellOpt", .inj "C11Cell",
   .inj "C11CellFragment", .inj "C11CellOpt", .inj "C12Cell", .inj "C12CellFragment",
   .inj "C12CellOpt", .inj "C13Cell", .inj "C13CellFragment", .inj "C13CellOpt", .inj "C14Cell",
   .inj "C14CellFragment", .inj "C14CellOpt", .inj "C15Cell", .inj "C15CellFragment",
   .inj "C15CellOpt", .inj "C16Cell", .inj "C16CellFragment", .inj "C16CellOpt", .inj "C17Cell",
   .inj "C17CellFragment", .inj "C17CellOpt", .inj "C18Cell", .inj "C18CellFragment",
   .inj "C18CellOpt", .inj "C19Cell", .inj "C19CellFragment", .inj "C19CellOpt", .inj "C1Cell",
   .inj "C1CellFragment", .inj "C1CellOpt", .inj "C20Cell", .inj "C20CellFragment",
   .inj "C20CellOpt", .inj "C21Cell", .inj "C21CellFragment", .inj "C21CellOpt", .inj "C22Cell",
   .inj "C22CellFragment", .inj "C22CellOpt", .inj "C23Cell", .inj "C23CellFragment",
   .inj "C23CellOpt", .inj "C24Cell", .inj "C24CellFragment", .inj "C24CellOpt", .inj "C25Cell",
   .inj "C25CellFragment", .inj "C25CellOpt", .inj "C26Cell", .inj "C26CellFragment",
   .inj "C26CellOpt", .inj "C27Cell", .inj "C27CellFragment", .inj "C27CellOpt", .inj "C28Cell",
   .inj "C28CellFragment", .inj "C28CellOpt", .inj "C29Cell", .inj "C29CellFragment",
   .inj "C29CellOpt", .inj "C2Cell", .inj "C2CellFragment", .inj "C2CellOpt", .inj "C30Cell",
   .inj "C30CellFragment", .inj "C30CellOpt", .inj "C31Cell", .inj "C31CellFragment",
   .inj "C31CellOpt", .inj "C32Cell", .inj "C32CellFragment", .inj "C32CellOpt", .inj "C33Cell",
   .inj "C33CellFragment", .inj "C33CellOpt", .inj "C34Cell", .inj "C34CellFragment",
   .inj "C34CellOpt", .inj "C35Cell", .inj "C35CellFragment", .inj "C35CellOpt", .inj "C36Cell",
   .inj "C36CellFragment", .inj "C36CellOpt", .inj "C37Cell", .inj "C37CellFragment",
   .inj "C37CellOpt", .inj "C38Cell", .inj "C38CellFragment", .inj "C38CellOpt", .inj "C39Cell",
   .inj "C39CellFragment", .inj "C39CellOpt", .inj "C3Cell", .inj "C3CellFragment",
   .inj "C3CellOpt", .inj "C40Cell", .inj "C40CellFragment", .inj "C40CellOpt", .inj "C41Cell",
   .inj "C41CellFragment", .inj "C41CellOpt", .inj "C42Cell", .inj "C42CellFragment",
   .inj "C42CellOpt", .inj "C43Cell", .inj "C43CellFragment", .inj "C43CellOpt", .inj "C44Cell",
   .inj "C44CellFragment", .inj "C44CellOpt", .inj "C45Cell", .inj "C45CellFragment",
   .inj "C45CellOpt", .inj "C46Cell", .inj "C46CellFragment", .inj "C46CellOpt", .inj "C47Cell",
   .inj "C47CellFragment", .inj "C47CellOpt", .inj "C48Cell", .inj "C48CellFragment",
   .inj "C48CellOpt", .inj "C49Cell", .inj "C49CellFragment", .inj "C49CellOpt", .inj "C4Cell",
   .inj "C4CellFragment", .inj "C4CellOpt", .inj "C50Cell", .inj "C50CellFragment",
   .inj "C50CellOpt", .inj "C51Cell", .inj "C51CellFragment", .inj "C51CellOpt", .inj "C52Cell",
   .inj "C52CellFragment", .inj "C52CellOpt", .inj "C53Cell", .inj "C53CellFragment",
   .inj "C53CellOpt", .inj "C54Cell", .inj "C54CellFragment", .inj "C54CellOpt", .inj "C55Cell",
   .inj "C55CellFragment", .inj "C55CellOpt", .inj "C56Cell", .inj "C56CellFragment",
   .inj "C56CellOpt", .inj "C57Cell", .inj "C57CellFragment", .inj "C57CellOpt", .inj "C58Cell",
   .inj "C58CellFragment", .inj "C58CellOpt", .inj "C59Cell", .inj "C59CellFragment",
   .inj "C59CellOpt", .inj "C5Cell", .inj "C5CellFragment", .inj "C5CellOpt", .inj "C60Cell",
   .inj "C60CellFragment", .inj "C60CellOpt", .inj "C61Cell", .inj "C61CellFragment",
   .inj "C61CellOpt", .inj "C62Cell", .inj "C62CellFragment", .inj "C62CellOpt", .inj "C63Cell",
   .inj "C63CellFragment", .inj "C63CellOpt", .inj "C6Cell", .inj "C6CellFragment",
   .inj "C6CellOpt", .inj "C7Cell", .inj "C7CellFragment", .inj "C7CellOpt", .inj "C8Cell",
   .inj "C8CellFragment", .inj "C8CellOpt", .inj "C9Cell", .inj "C9CellFragment", .inj "C9CellOpt",
   .inj "GeneratedCounterCell", .inj "GeneratedCounterCellOpt", .inj "GeneratedTopCell",
   .inj "GeneratedTopCellFragment", .inj "Int", .inj "KCell", .inj "KCellOpt", .inj "KConfigVar",
   .inj "List", .inj "Map", .inj "Set"]
theorem nojunk_kitem_gens_eq : ((gensInOrder c defn.pres Srt.kitem).map (Gen.toK c)) = nojunk_kitem_gens := by decide +kernel

theorem nojunk_kitem_sv : U.ax1033.ax.sortVars = [] := by decide +kernel
theorem nojunk_kitem_or : njIsOr (KoreAML.srt "KItem") U.ax1033.ax.pattern = true := by decide +kernel
theorem nojunk_kitem_free : freeOfList [] (njOrArgs U.ax1033.ax.pattern) = [] := by decide +kernel
theorem nojunk_kitem_ifree : freeOfList [] (KoreAML.noJunkDisjuncts "KItem" [] nojunk_kitem_gens) = [] := by decide +kernel

/-- The tables of the sentence and of the item, written out. -/
def nojunk_kitem_tabT : VarTable :=
  [.evar "Val" (.ctor ⟨⟨"SortBool"⟩⟩ []), .evar "Val" (.ctor ⟨⟨"SortC10Cell"⟩⟩ []),
   .evar "Val" (.ctor ⟨⟨"SortC10CellFragment"⟩⟩ []), .evar "Val" (.ctor ⟨⟨"SortC10CellOpt"⟩⟩ []),
   .evar "Val" (.ctor ⟨⟨"SortC11Cell"⟩⟩ []), .evar "Val" (.ctor ⟨⟨"SortC11CellFragment"⟩⟩ []),
   .evar "Val" (.ctor ⟨⟨"SortC11CellOpt"⟩⟩ []), .evar "Val" (.ctor ⟨⟨"SortC12Cell"⟩⟩ []),
   .evar "Val" (.ctor ⟨⟨"SortC12CellFragment"⟩⟩ []), .evar "Val" (.ctor ⟨⟨"SortC12CellOpt"⟩⟩ []),
   .evar "Val" (.ctor ⟨⟨"SortC13Cell"⟩⟩ []), .evar "Val" (.ctor ⟨⟨"SortC13CellFragment"⟩⟩ []),
   .evar "Val" (.ctor ⟨⟨"SortC13CellOpt"⟩⟩ []), .evar "Val" (.ctor ⟨⟨"SortC14Cell"⟩⟩ []),
   .evar "Val" (.ctor ⟨⟨"SortC14CellFragment"⟩⟩ []), .evar "Val" (.ctor ⟨⟨"SortC14CellOpt"⟩⟩ []),
   .evar "Val" (.ctor ⟨⟨"SortC15Cell"⟩⟩ []), .evar "Val" (.ctor ⟨⟨"SortC15CellFragment"⟩⟩ []),
   .evar "Val" (.ctor ⟨⟨"SortC15CellOpt"⟩⟩ []), .evar "Val" (.ctor ⟨⟨"SortC16Cell"⟩⟩ []),
   .evar "Val" (.ctor ⟨⟨"SortC16CellFragment"⟩⟩ []), .evar "Val" (.ctor ⟨⟨"SortC16CellOpt"⟩⟩ []),
   .evar "Val" (.ctor ⟨⟨"SortC17Cell"⟩⟩ []), .evar "Val" (.ctor ⟨⟨"SortC17CellFragment"⟩⟩ []),
   .evar "Val" (.ctor ⟨⟨"SortC17CellOpt"⟩⟩ []), .evar "Val" (.ctor ⟨⟨"SortC18Cell"⟩⟩ []),
   .evar "Val" (.ctor ⟨⟨"SortC18CellFragment"⟩⟩ []), .evar "Val" (.ctor ⟨⟨"SortC18CellOpt"⟩⟩ []),
   .evar "Val" (.ctor ⟨⟨"SortC19Cell"⟩⟩ []), .evar "Val" (.ctor ⟨⟨"SortC19CellFragment"⟩⟩ []),
   .evar "Val" (.ctor ⟨⟨"SortC19CellOpt"⟩⟩ []), .evar "Val" (.ctor ⟨⟨"SortC1Cell"⟩⟩ []),
   .evar "Val" (.ctor ⟨⟨"SortC1CellFragment"⟩⟩ []), .evar "Val" (.ctor ⟨⟨"SortC1CellOpt"⟩⟩ []),
   .evar "Val" (.ctor ⟨⟨"SortC20Cell"⟩⟩ []), .evar "Val" (.ctor ⟨⟨"SortC20CellFragment"⟩⟩ []),
   .evar "Val" (.ctor ⟨⟨"SortC20CellOpt"⟩⟩ []), .evar "Val" (.ctor ⟨⟨"SortC21Cell"⟩⟩ []),
   .evar "Val" (.ctor ⟨⟨"SortC21CellFragment"⟩⟩ []), .evar "Val" (.ctor ⟨⟨"SortC21CellOpt"⟩⟩ []),
   .evar "Val" (.ctor ⟨⟨"SortC22Cell"⟩⟩ []), .evar "Val" (.ctor ⟨⟨"SortC22CellFragment"⟩⟩ []),
   .evar "Val" (.ctor ⟨⟨"SortC22CellOpt"⟩⟩ []), .evar "Val" (.ctor ⟨⟨"SortC23Cell"⟩⟩ []),
   .evar "Val" (.ctor ⟨⟨"SortC23CellFragment"⟩⟩ []), .evar "Val" (.ctor ⟨⟨"SortC23CellOpt"⟩⟩ []),
   .evar "Val" (.ctor ⟨⟨"SortC24Cell"⟩⟩ []), .evar "Val" (.ctor ⟨⟨"SortC24CellFragment"⟩⟩ []),
   .evar "Val" (.ctor ⟨⟨"SortC24CellOpt"⟩⟩ []), .evar "Val" (.ctor ⟨⟨"SortC25Cell"⟩⟩ []),
   .evar "Val" (.ctor ⟨⟨"SortC25CellFragment"⟩⟩ []), .evar "Val" (.ctor ⟨⟨"SortC25CellOpt"⟩⟩ []),
   .evar "Val" (.ctor ⟨⟨"SortC26Cell"⟩⟩ []), .evar "Val" (.ctor ⟨⟨"SortC26CellFragment"⟩⟩ []),
   .evar "Val" (.ctor ⟨⟨"SortC26CellOpt"⟩⟩ []), .evar "Val" (.ctor ⟨⟨"SortC27Cell"⟩⟩ []),
   .evar "Val" (.ctor ⟨⟨"SortC27CellFragment"⟩⟩ []), .evar "Val" (.ctor ⟨⟨"SortC27CellOpt"⟩⟩ []),
   .evar "Val" (.ctor ⟨⟨"SortC28Cell"⟩⟩ []), .evar "Val" (.ctor ⟨⟨"SortC28CellFragment"⟩⟩ []),
   .evar "Val" (.ctor ⟨⟨"SortC28CellOpt"⟩⟩ []), .evar "Val" (.ctor ⟨⟨"SortC29Cell"⟩⟩ []),
   .evar "Val" (.ctor ⟨⟨"SortC29CellFragment"⟩⟩ []), .evar "Val" (.ctor ⟨⟨"SortC29CellOpt"⟩⟩ []),
   .evar "Val" (.ctor ⟨⟨"SortC2Cell"⟩⟩ []), .evar "Val" (.ctor ⟨⟨"SortC2CellFragment"⟩⟩ []),
   .evar "Val" (.ctor ⟨⟨"SortC2CellOpt"⟩⟩ []), .evar "Val" (.ctor ⟨⟨"SortC30Cell"⟩⟩ []),
   .evar "Val" (.ctor ⟨⟨"SortC30CellFragment"⟩⟩ []), .evar "Val" (.ctor ⟨⟨"SortC30CellOpt"⟩⟩ []),
   .evar "Val" (.ctor ⟨⟨"SortC31Cell"⟩⟩ []), .evar "Val" (.ctor ⟨⟨"SortC31CellFragment"⟩⟩ []),
   .evar "Val" (.ctor ⟨⟨"SortC31CellOpt"⟩⟩ []), .evar "Val" (.ctor ⟨⟨"SortC32Cell"⟩⟩ []),
   .evar "Val" (.ctor ⟨⟨"SortC32CellFragment"⟩⟩ []), .evar "Val" (.ctor ⟨⟨"SortC32CellOpt"⟩⟩ []),
   .evar "Val" (.ctor ⟨⟨"SortC33Cell"⟩⟩ []), .evar "Val" (.ctor ⟨⟨"SortC33CellFragment"⟩⟩ []),
   .evar "Val" (.ctor ⟨⟨"SortC33CellOpt"⟩⟩ []), .evar "Val" (.ctor ⟨⟨"SortC34Cell"⟩⟩ []),
   .evar "Val" (.ctor ⟨⟨"SortC34CellFragment"⟩⟩ []), .evar "Val" (.ctor ⟨⟨"SortC34CellOpt"⟩⟩ []),
   .evar "Val" (.ctor ⟨⟨"SortC35Cell"⟩⟩ []), .evar "Val" (.ctor ⟨⟨"SortC35CellFragment"⟩⟩ []),
   .evar "Val" (.ctor ⟨⟨"SortC35CellOpt"⟩⟩ []), .evar "Val" (.ctor ⟨⟨"SortC36Cell"⟩⟩ []),
   .evar "Val" (.ctor ⟨⟨"SortC36CellFragment"⟩⟩ []), .evar "Val" (.ctor ⟨⟨"SortC36CellOpt"⟩⟩ []),
   .evar "Val" (.ctor ⟨⟨"SortC37Cell"⟩⟩ []), .evar "Val" (.ctor ⟨⟨"SortC37CellFragment"⟩⟩ []),
   .evar "Val" (.ctor ⟨⟨"SortC37CellOpt"⟩⟩ []), .evar "Val" (.ctor ⟨⟨"SortC38Cell"⟩⟩ []),
   .evar "Val" (.ctor ⟨⟨"SortC38CellFragment"⟩⟩ []), .evar "Val" (.ctor ⟨⟨"SortC38CellOpt"⟩⟩ []),
   .evar "Val" (.ctor ⟨⟨"SortC39Cell"⟩⟩ []), .evar "Val" (.ctor ⟨⟨"SortC39CellFragment"⟩⟩ []),
   .evar "Val" (.ctor ⟨⟨"SortC39CellOpt"⟩⟩ []), .evar "Val" (.ctor ⟨⟨"SortC3Cell"⟩⟩ []),
   .evar "Val" (.ctor ⟨⟨"SortC3CellFragment"⟩⟩ []), .evar "Val" (.ctor ⟨⟨"SortC3CellOpt"⟩⟩ []),
   .evar "Val" (.ctor ⟨⟨"SortC40Cell"⟩⟩ []), .evar "Val" (.ctor ⟨⟨"SortC40CellFragment"⟩⟩ []),
   .evar "Val" (.ctor ⟨⟨"SortC40CellOpt"⟩⟩ []), .evar "Val" (.ctor ⟨⟨"SortC41Cell"⟩⟩ []),
   .evar "Val" (.ctor ⟨⟨"SortC41CellFragment"⟩⟩ []), .evar "Val" (.ctor ⟨⟨"SortC41CellOpt"⟩⟩ []),
   .evar "Val" (.ctor ⟨⟨"SortC42Cell"⟩⟩ []), .evar "Val" (.ctor ⟨⟨"SortC42CellFragment"⟩⟩ []),
   .evar "Val" (.ctor ⟨⟨"SortC42CellOpt"⟩⟩ []), .evar "Val" (.ctor ⟨⟨"SortC43Cell"⟩⟩ []),
   .evar "Val" (.ctor ⟨⟨"SortC43CellFragment"⟩⟩ []), .evar "Val" (.ctor ⟨⟨"SortC43CellOpt"⟩⟩ []),
   .evar "Val" (.ctor ⟨⟨"SortC44Cell"⟩⟩ []), .evar "Val" (.ctor ⟨⟨"SortC44CellFragment"⟩⟩ []),
   .evar "Val" (.ctor ⟨⟨"SortC44CellOpt"⟩⟩ []), .evar "Val" (.ctor ⟨⟨"SortC45Cell"⟩⟩ []),
   .evar "Val" (.ctor ⟨⟨"SortC45CellFragment"⟩⟩ []), .evar "Val" (.ctor ⟨⟨"SortC45CellOpt"⟩⟩ []),
   .evar "Val" (.ctor ⟨⟨"SortC46Cell"⟩⟩ []), .evar "Val" (.ctor ⟨⟨"SortC46CellFragment"⟩⟩ []),
   .evar "Val" (.ctor ⟨⟨"SortC46CellOpt"⟩⟩ []), .evar "Val" (.ctor ⟨⟨"SortC47Cell"⟩⟩ []),
   .evar "Val" (.ctor ⟨⟨"SortC47CellFragment"⟩⟩ []), .evar "Val" (.ctor ⟨⟨"SortC47CellOpt"⟩⟩ []),
   .evar "Val" (.ctor ⟨⟨"SortC48Cell"⟩⟩ []), .evar "Val" (.ctor ⟨⟨"SortC48CellFragment"⟩⟩ []),
   .evar "Val" (.ctor ⟨⟨"SortC48CellOpt"⟩⟩ []), .evar "Val" (.ctor ⟨⟨"SortC49Cell"⟩⟩ []),
   .evar "Val" (.ctor ⟨⟨"SortC49CellFragment"⟩⟩ []), .evar "Val" (.ctor ⟨⟨"SortC49CellOpt"⟩⟩ []),
   .evar "Val" (.ctor ⟨⟨"SortC4Cell"⟩⟩ []), .evar "Val" (.ctor ⟨⟨"SortC4CellFragment"⟩⟩ []),
   .evar "Val" (.ctor ⟨⟨"SortC4CellOpt"⟩⟩ []), .evar "Val" (.ctor ⟨⟨"SortC50Cell"⟩⟩ []),
   .evar "Val" (.ctor ⟨⟨"SortC50CellFragment"⟩⟩ []), .evar "Val" (.ctor ⟨⟨"SortC50CellOpt"⟩⟩ []),
   .evar "Val" (.ctor ⟨⟨"SortC51Cell"⟩⟩ []), .evar "Val" (.ctor ⟨⟨"SortC51CellFragment"⟩⟩ []),
   .evar "Val" (.ctor ⟨⟨"SortC51CellOpt"⟩⟩ []), .evar "Val" (.ctor ⟨⟨"SortC52Cell"⟩⟩ []),
   .evar "Val" (.ctor ⟨⟨"SortC52CellFragment"⟩⟩ []), .evar "Val" (.ctor ⟨⟨"SortC52CellOpt"⟩⟩ []),
   .evar "Val" (.ctor ⟨⟨"SortC53Cell"⟩⟩ []), .evar "Val" (.ctor ⟨⟨"SortC53CellFragment"⟩⟩ []),
   .evar "Val" (.ctor ⟨⟨"SortC53CellOpt"⟩⟩ []), .evar "Val" (.ctor ⟨⟨"SortC54Cell"⟩⟩ []),
   .evar "Val" (.ctor ⟨⟨"SortC54CellFragment"⟩⟩ []), .evar "Val" (.ctor ⟨⟨"SortC54CellOpt"⟩⟩ []),
   .evar "Val" (.ctor ⟨⟨"SortC55Cell"⟩⟩ []), .evar "Val" (.ctor ⟨⟨"SortC55CellFragment"⟩⟩ []),
   .evar "Val" (.ctor ⟨⟨"SortC55CellOpt"⟩⟩ []), .evar "Val" (.ctor ⟨⟨"SortC56Cell"⟩⟩ []),
   .evar "Val" (.ctor ⟨⟨"SortC56CellFragment"⟩⟩ []), .evar "Val" (.ctor ⟨⟨"SortC56CellOpt"⟩⟩ []),
   .evar "Val" (.ctor ⟨⟨"SortC57Cell"⟩⟩ []), .evar "Val" (.ctor ⟨⟨"SortC57CellFragment"⟩⟩ []),
   .evar "Val" (.ctor ⟨⟨"SortC57CellOpt"⟩⟩ []), .evar "Val" (.ctor ⟨⟨"SortC58Cell"⟩⟩ []),
   .evar "Val" (.ctor ⟨⟨"SortC58CellFragment"⟩⟩ []), .evar "Val" (.ctor ⟨⟨"SortC58CellOpt"⟩⟩ []),
   .evar "Val" (.ctor ⟨⟨"SortC59Cell"⟩⟩ []), .evar "Val" (.ctor ⟨⟨"SortC59CellFragment"⟩⟩ []),
   .evar "Val" (.ctor ⟨⟨"SortC59CellOpt"⟩⟩ []), .evar "Val" (.ctor ⟨⟨"SortC5Cell"⟩⟩ []),
   .evar "Val" (.ctor ⟨⟨"SortC5CellFragment"⟩⟩ []), .evar "Val" (.ctor ⟨⟨"SortC5CellOpt"⟩⟩ []),
   .evar "Val" (.ctor ⟨⟨"SortC60Cell"⟩⟩ []), .evar "Val" (.ctor ⟨⟨"SortC60CellFragment"⟩⟩ []),
   .evar "Val" (.ctor ⟨⟨"SortC60CellOpt"⟩⟩ []), .evar "Val" (.ctor ⟨⟨"SortC61Cell"⟩⟩ []),
   .evar "Val" (.ctor ⟨⟨"SortC61CellFragment"⟩⟩ []), .evar "Val" (.ctor ⟨⟨"SortC61CellOpt"⟩⟩ []),
   .evar "Val" (.ctor ⟨⟨"SortC62Cell"⟩⟩ []), .evar "Val" (.ctor ⟨⟨"SortC62CellFragment"⟩⟩ []),
   .evar "Val" (.ctor ⟨⟨"SortC62CellOpt"⟩⟩ []), .evar "Val" (.ctor ⟨⟨"SortC63Cell"⟩⟩ []),
   .evar "Val" (.ctor ⟨⟨"SortC63CellFragment"⟩⟩ []), .evar "Val" (.ctor ⟨⟨"SortC63CellOpt"⟩⟩ []),
   .evar "Val" (.ctor ⟨⟨"SortC6Cell"⟩⟩ []), .evar "Val" (.ctor ⟨⟨"SortC6CellFragment"⟩⟩ []),
   .evar "Val" (.ctor ⟨⟨"SortC6CellOpt"⟩⟩ []), .evar "Val" (.ctor ⟨⟨"SortC7Cell"⟩⟩ []),
   .evar "Val" (.ctor ⟨⟨"SortC7CellFragment"⟩⟩ []), .evar "Val" (.ctor ⟨⟨"SortC7CellOpt"⟩⟩ []),
   .evar "Val" (.ctor ⟨⟨"SortC8Cell"⟩⟩ []), .evar "Val" (.ctor ⟨⟨"SortC8CellFragment"⟩⟩ []),
   .evar "Val" (.ctor ⟨⟨"SortC8CellOpt"⟩⟩ []), .evar "Val" (.ctor ⟨⟨"SortC9Cell"⟩⟩ []),
   .evar "Val" (.ctor ⟨⟨"SortC9CellFragment"⟩⟩ []), .evar "Val" (.ctor ⟨⟨"SortC9CellOpt"⟩⟩ []),
   .evar "Val" (.ctor ⟨⟨"SortGeneratedCounterCell"⟩⟩ []),
   .evar "Val" (.ctor ⟨⟨"SortGeneratedCounterCellOpt"⟩⟩ []),
   .evar "Val" (.ctor ⟨⟨"SortGeneratedTopCell"⟩⟩ []),
   .evar "Val" (.ctor ⟨⟨"SortGeneratedTopCellFragment"⟩⟩ []), .evar "Val" (.ctor ⟨⟨"SortInt"⟩⟩ []),
   .evar "Val" (.ctor ⟨⟨"SortKCell"⟩⟩ []), .evar "Val" (.ctor ⟨⟨"SortKCellOpt"⟩⟩ []),
   .evar "Val" (.ctor ⟨⟨"SortKConfigVar"⟩⟩ []), .evar "Val" (.ctor ⟨⟨"SortList"⟩⟩ []),
   .evar "Val" (.ctor ⟨⟨"SortMap"⟩⟩ []), .evar "Val" (.ctor ⟨⟨"SortSet"⟩⟩ [])]
theorem nojunk_kitem_tabT_eq : tableOf [] (.or (KoreAML.srt "KItem") (njOrArgs U.ax1033.ax.pattern)) = nojunk_kitem_tabT := by
  decide +kernel
def nojunk_kitem_tabI : VarTable :=
  [.evar "Val" (.ctor ⟨⟨"SortBool"⟩⟩ []), .evar "ValV2" (.ctor ⟨⟨"SortC10Cell"⟩⟩ []),
   .evar "ValV3" (.ctor ⟨⟨"SortC10CellFragment"⟩⟩ []),
   .evar "ValV4" (.ctor ⟨⟨"SortC10CellOpt"⟩⟩ []), .evar "ValV5" (.ctor ⟨⟨"SortC11Cell"⟩⟩ []),
   .evar "ValV6" (.ctor ⟨⟨"SortC11CellFragment"⟩⟩ []),
   .evar "ValV7" (.ctor ⟨⟨"SortC11CellOpt"⟩⟩ []), .evar "ValV8" (.ctor ⟨⟨"SortC12Cell"⟩⟩ []),
   .evar "ValV9" (.ctor ⟨⟨"SortC12CellFragment"⟩⟩ []),
   .evar "ValV10" (.ctor ⟨⟨"SortC12CellOpt"⟩⟩ []), .evar "ValV11" (.ctor ⟨⟨"SortC13Cell"⟩⟩ []),
   .evar "ValV12" (.ctor ⟨⟨"SortC13CellFragment"⟩⟩ []),
   .evar "ValV13" (.ctor ⟨⟨"SortC13CellOpt"⟩⟩ []), .evar "ValV14" (.ctor ⟨⟨"SortC14Cell"⟩⟩ []),
   .evar "ValV15" (.ctor ⟨⟨"SortC14CellFragment"⟩⟩ []),
   .evar "ValV16" (.ctor ⟨⟨"SortC14CellOpt"⟩⟩ []), .evar "ValV17" (.ctor ⟨⟨"SortC15Cell"⟩⟩ []),
   .evar "ValV18" (.ctor ⟨⟨"SortC15CellFragment"⟩⟩ []),
   .evar "ValV19" (.ctor ⟨⟨"SortC15CellOpt"⟩⟩ []), .evar "ValV20" (.ctor ⟨⟨"SortC16Cell"⟩⟩ []),
   .evar "ValV21" (.ctor ⟨⟨"SortC16CellFragment"⟩⟩ []),
   .evar "ValV22" (.ctor ⟨⟨"SortC16CellOpt"⟩⟩ []), .evar "ValV23" (.ctor ⟨⟨"SortC17Cell"⟩⟩ []),
   .evar "ValV24" (.ctor ⟨⟨"SortC17CellFragment"⟩⟩ []),
   .evar "ValV25" (.ctor ⟨⟨"SortC17CellOpt"⟩⟩ []), .evar "ValV26" (.ctor ⟨⟨"SortC18Cell"⟩⟩ []),
   .evar "ValV27" (.ctor ⟨⟨"SortC18CellFragment"⟩⟩ []),
   .evar "ValV28" (.ctor ⟨⟨"SortC18CellOpt"⟩⟩ []), .evar "ValV29" (.ctor ⟨⟨"SortC19Cell"⟩⟩ []),
   .evar "ValV30" (.ctor ⟨⟨"SortC19CellFragment"⟩⟩ []),
   .evar "ValV31" (.ctor ⟨⟨"SortC19CellOpt"⟩⟩ []), .evar "ValV32" (.ctor ⟨⟨"SortC1Cell"⟩⟩ []),
   .evar "ValV33" (.ctor ⟨⟨"SortC1CellFragment"⟩⟩ []),
   .evar "ValV34" (.ctor ⟨⟨"SortC1CellOpt"⟩⟩ []), .evar "ValV35" (.ctor ⟨⟨"SortC20Cell"⟩⟩ []),
   .evar "ValV36" (.ctor ⟨⟨"SortC20CellFragment"⟩⟩ []),
   .evar "ValV37" (.ctor ⟨⟨"SortC20CellOpt"⟩⟩ []), .evar "ValV38" (.ctor ⟨⟨"SortC21Cell"⟩⟩ []),
   .evar "ValV39" (.ctor ⟨⟨"SortC21CellFragment"⟩⟩ []),
   .evar "ValV40" (.ctor ⟨⟨"SortC21CellOpt"⟩⟩ []), .evar "ValV41" (.ctor ⟨⟨"SortC22Cell"⟩⟩ []),
   .evar "ValV42" (.ctor ⟨⟨"SortC22CellFragment"⟩⟩ []),
   .evar "ValV43" (.ctor ⟨⟨"SortC22CellOpt"⟩⟩ []), .evar "ValV44" (.ctor ⟨⟨"SortC23Cell"⟩⟩ []),
   .evar "ValV45" (.ctor ⟨⟨"SortC23CellFragment"⟩⟩ []),
   .evar "ValV46" (.ctor ⟨⟨"SortC23CellOpt"⟩⟩ []), .evar "ValV47" (.ctor ⟨⟨"SortC24Cell"⟩⟩ []),
   .evar "ValV48" (.ctor ⟨⟨"SortC24CellFragment"⟩⟩ []),
   .evar "ValV49" (.ctor ⟨⟨"SortC24CellOpt"⟩⟩ []), .evar "ValV50" (.ctor ⟨⟨"SortC25Cell"⟩⟩ []),
   .evar "ValV51" (.ctor ⟨⟨"SortC25CellFragment"⟩⟩ []),
   .evar "ValV52" (.ctor ⟨⟨"SortC25CellOpt"⟩⟩ []), .evar "ValV53" (.ctor ⟨⟨"SortC26Cell"⟩⟩ []),
   .evar "ValV54" (.ctor ⟨⟨"SortC26CellFragment"⟩⟩ []),
   .evar "ValV55" (.ctor ⟨⟨"SortC26CellOpt"⟩⟩ []), .evar "ValV56" (.ctor ⟨⟨"SortC27Cell"⟩⟩ []),
   .evar "ValV57" (.ctor ⟨⟨"SortC27CellFragment"⟩⟩ []),
   .evar "ValV58" (.ctor ⟨⟨"SortC27CellOpt"⟩⟩ []), .evar "ValV59" (.ctor ⟨⟨"SortC28Cell"⟩⟩ []),
   .evar "ValV60" (.ctor ⟨⟨"SortC28CellFragment"⟩⟩ []),
   .evar "ValV61" (.ctor ⟨⟨"SortC28CellOpt"⟩⟩ []), .evar "ValV62" (.ctor ⟨⟨"SortC29Cell"⟩⟩ []),
   .evar "ValV63" (.ctor ⟨⟨"SortC29CellFragment"⟩⟩ []),
   .evar "ValV64" (.ctor ⟨⟨"SortC29CellOpt"⟩⟩ []), .evar "ValV65" (.ctor ⟨⟨"SortC2Cell"⟩⟩ []),
   .evar "ValV66" (.ctor ⟨⟨"SortC2CellFragment"⟩⟩ []),
   .evar "ValV67" (.ctor ⟨⟨"SortC2CellOpt"⟩⟩ []), .evar "ValV68" (.ctor ⟨⟨"SortC30Cell"⟩⟩ []),
   .evar "ValV69" (.ctor ⟨⟨"SortC30CellFragment"⟩⟩ []),
   .evar "ValV70" (.ctor ⟨⟨"SortC30CellOpt"⟩⟩ []), .evar "ValV71" (.ctor ⟨⟨"SortC31Cell"⟩⟩ []),
   .evar "ValV72" (.ctor ⟨⟨"SortC31CellFragment"⟩⟩ []),
   .evar "ValV73" (.ctor ⟨⟨"SortC31CellOpt"⟩⟩ []), .evar "ValV74" (.ctor ⟨⟨"SortC32Cell"⟩⟩ []),
   .evar "ValV75" (.ctor ⟨⟨"SortC32CellFragment"⟩⟩ []),
   .evar "ValV76" (.ctor ⟨⟨"SortC32CellOpt"⟩⟩ []), .evar "ValV77" (.ctor ⟨⟨"SortC33Cell"⟩⟩ []),
   .evar "ValV78" (.ctor ⟨⟨"SortC33CellFragment"⟩⟩ []),
   .evar "ValV79" (.ctor ⟨⟨"SortC33CellOpt"⟩⟩ []), .evar "ValV80" (.ctor ⟨⟨"SortC34Cell"⟩⟩ []),
   .evar "ValV81" (.ctor ⟨⟨"SortC34CellFragment"⟩⟩ []),
   .evar "ValV82" (.ctor ⟨⟨"SortC34CellOpt"⟩⟩ []), .evar "ValV83" (.ctor ⟨⟨"SortC35Cell"⟩⟩ []),
   .evar "ValV84" (.ctor ⟨⟨"SortC35CellFragment"⟩⟩ []),
   .evar "ValV85" (.ctor ⟨⟨"SortC35CellOpt"⟩⟩ []), .evar "ValV86" (.ctor ⟨⟨"SortC36Cell"⟩⟩ []),
   .evar "ValV87" (.ctor ⟨⟨"SortC36CellFragment"⟩⟩ []),
   .evar "ValV88" (.ctor ⟨⟨"SortC36CellOpt"⟩⟩ []), .evar "ValV89" (.ctor ⟨⟨"SortC37Cell"⟩⟩ []),
   .evar "ValV90" (.ctor ⟨⟨"SortC37CellFragment"⟩⟩ []),
   .evar "ValV91" (.ctor ⟨⟨"SortC37CellOpt"⟩⟩ []), .evar "ValV92" (.ctor ⟨⟨"SortC38Cell"⟩⟩ []),
   .evar "ValV93" (.ctor ⟨⟨"SortC38CellFragment"⟩⟩ []),
   .evar "ValV94" (.ctor ⟨⟨"SortC38CellOpt"⟩⟩ []), .evar "ValV95" (.ctor ⟨⟨"SortC39Cell"⟩⟩ []),
   .evar "ValV96" (.ctor ⟨⟨"SortC39CellFragment"⟩⟩ []),
   .evar "ValV97" (.ctor ⟨⟨"SortC39CellOpt"⟩⟩ []), .evar "ValV98" (.ctor ⟨⟨"SortC3Cell"⟩⟩ []),
   .evar "ValV99" (.ctor ⟨⟨"SortC3CellFragment"⟩⟩ []),
   .evar "ValV100" (.ctor ⟨⟨"SortC3CellOpt"⟩⟩ []), .evar "ValV101" (.ctor ⟨⟨"SortC40Cell"⟩⟩ []),
   .evar "ValV102" (.ctor ⟨⟨"SortC40CellFragment"⟩⟩ []),
   .evar "ValV103" (.ctor ⟨⟨"SortC40CellOpt"⟩⟩ []), .evar "ValV104" (.ctor ⟨⟨"SortC41Cell"⟩⟩ []),
   .evar "ValV105" (.ctor ⟨⟨"SortC41CellFragment"⟩⟩ []),
   .evar "ValV106" (.ctor ⟨⟨"SortC41CellOpt"⟩⟩ []), .evar "ValV107" (.ctor ⟨⟨"SortC42Cell"⟩⟩ []),
   .evar "ValV108" (.ctor ⟨⟨"SortC42CellFragment"⟩⟩ []),
   .evar "ValV109" (.ctor ⟨⟨"SortC42CellOpt"⟩⟩ []), .evar "ValV110" (.ctor ⟨⟨"SortC43Cell"⟩⟩ []),
   .evar "ValV111" (.ctor ⟨⟨"SortC43CellFragment"⟩⟩ []),
   .evar "ValV112" (.ctor ⟨⟨"SortC43CellOpt"⟩⟩ []), .evar "ValV113" (.ctor ⟨⟨"SortC44Cell"⟩⟩ []),
   .evar "ValV114" (.ctor ⟨⟨"SortC44CellFragment"⟩⟩ []),
   .evar "ValV115" (.ctor ⟨⟨"SortC44CellOpt"⟩⟩ []), .evar "ValV116" (.ctor ⟨⟨"SortC45Cell"⟩⟩ []),
   .evar "ValV117" (.ctor ⟨⟨"SortC45CellFragment"⟩⟩ []),
   .evar "ValV118" (.ctor ⟨⟨"SortC45CellOpt"⟩⟩ []), .evar "ValV119" (.ctor ⟨⟨"SortC46Cell"⟩⟩ []),
   .evar "ValV120" (.ctor ⟨⟨"SortC46CellFragment"⟩⟩ []),
   .evar "ValV121" (.ctor ⟨⟨"SortC46CellOpt"⟩⟩ []), .evar "ValV122" (.ctor ⟨⟨"SortC47Cell"⟩⟩ []),
   .evar "ValV123" (.ctor ⟨⟨"SortC47CellFragment"⟩⟩ []),
   .evar "ValV124" (.ctor ⟨⟨"SortC47CellOpt"⟩⟩ []), .evar "ValV125" (.ctor ⟨⟨"SortC48Cell"⟩⟩ []),
   .evar "ValV126" (.ctor ⟨⟨"SortC48CellFragment"⟩⟩ []),
   .evar "ValV127" (.ctor ⟨⟨"SortC48CellOpt"⟩⟩ []), .evar "ValV128" (.ctor ⟨⟨"SortC49Cell"⟩⟩ []),
   .evar "ValV129" (.ctor ⟨⟨"SortC49CellFragment"⟩⟩ []),
   .evar "ValV130" (.ctor ⟨⟨"SortC49CellOpt"⟩⟩ []), .evar "ValV131" (.ctor ⟨⟨"SortC4Cell"⟩⟩ []),
   .evar "ValV132" (.ctor ⟨⟨"SortC4CellFragment"⟩⟩ []),
   .evar "ValV133" (.ctor ⟨⟨"SortC4CellOpt"⟩⟩ []), .evar "ValV134" (.ctor ⟨⟨"SortC50Cell"⟩⟩ []),
   .evar "ValV135" (.ctor ⟨⟨"SortC50CellFragment"⟩⟩ []),
   .evar "ValV136" (.ctor ⟨⟨"SortC50CellOpt"⟩⟩ []), .evar "ValV137" (.ctor ⟨⟨"SortC51Cell"⟩⟩ []),
   .evar "ValV138" (.ctor ⟨⟨"SortC51CellFragment"⟩⟩ []),
   .evar "ValV139" (.ctor ⟨⟨"SortC51CellOpt"⟩⟩ []), .evar "ValV140" (.ctor ⟨⟨"SortC52Cell"⟩⟩ []),
   .evar "ValV141" (.ctor ⟨⟨"SortC52CellFragment"⟩⟩ []),
   .evar "ValV142" (.ctor ⟨⟨"SortC52CellOpt"⟩⟩ []), .evar "ValV143" (.ctor ⟨⟨"SortC53Cell"⟩⟩ []),
   .evar "ValV144" (.ctor ⟨⟨"SortC53CellFragment"⟩⟩ []),
   .evar "ValV145" (.ctor ⟨⟨"SortC53CellOpt"⟩⟩ []), .evar "ValV146" (.ctor ⟨⟨"SortC54Cell"⟩⟩ []),
   .evar "ValV147" (.ctor ⟨⟨"SortC54CellFragment"⟩⟩ []),
   .evar "ValV148" (.ctor ⟨⟨"SortC54CellOpt"⟩⟩ []), .evar "ValV149" (.ctor ⟨⟨"SortC55Cell"⟩⟩ []),
   .evar "ValV150" (.ctor ⟨⟨"SortC55CellFragment"⟩⟩ []),
   .evar "ValV151" (.ctor ⟨⟨"SortC55CellOpt"⟩⟩ []), .evar "ValV152" (.ctor ⟨⟨"SortC56Cell"⟩⟩ []),
   .evar "ValV153" (.ctor ⟨⟨"SortC56CellFragment"⟩⟩ []),
   .evar "ValV154" (.ctor ⟨⟨"SortC56CellOpt"⟩⟩ []), .evar "ValV155" (.ctor ⟨⟨"SortC57Cell"⟩⟩ []),
   .evar "ValV156" (.ctor ⟨⟨"SortC57CellFragment"⟩⟩ []),
   .evar "ValV157" (.ctor ⟨⟨"SortC57CellOpt"⟩⟩ []), .evar "ValV158" (.ctor ⟨⟨"SortC58Cell"⟩⟩ []),
   .evar "ValV159" (.ctor ⟨⟨"SortC58CellFragment"⟩⟩ []),
   .evar "ValV160" (.ctor ⟨⟨"SortC58CellOpt"⟩⟩ []), .evar "ValV161" (.ctor ⟨⟨"SortC59Cell"⟩⟩ []),
   .evar "ValV162" (.ctor ⟨⟨"SortC59CellFragment"⟩⟩ []),
   .evar "ValV163" (.ctor ⟨⟨"SortC59CellOpt"⟩⟩ []), .evar "ValV164" (.ctor ⟨⟨"SortC5Cell"⟩⟩ []),
   .evar "ValV165" (.ctor ⟨⟨"SortC5CellFragment"⟩⟩ []),
   .evar "ValV166" (.ctor ⟨⟨"SortC5CellOpt"⟩⟩ []), .evar "ValV167" (.ctor ⟨⟨"SortC60Cell"⟩⟩ []),
   .evar "ValV168" (.ctor ⟨⟨"SortC60CellFragment"⟩⟩ []),
   .evar "ValV169" (.ctor ⟨⟨"SortC60CellOpt"⟩⟩ []), .evar "ValV170" (.ctor ⟨⟨"SortC61Cell"⟩⟩ []),
   .evar "ValV171" (.ctor ⟨⟨"SortC61CellFragment"⟩⟩ []),
   .evar "ValV172" (.ctor ⟨⟨"SortC61CellOpt"⟩⟩ []), .evar "ValV173" (.ctor ⟨⟨"SortC62Cell"⟩⟩ []),
   .evar "ValV174" (.ctor ⟨⟨"SortC62CellFragment"⟩⟩ []),
   .evar "ValV175" (.ctor ⟨⟨"SortC62CellOpt"⟩⟩ []), .evar "ValV176" (.ctor ⟨⟨"SortC63Cell"⟩⟩ []),
   .evar "ValV177" (.ctor ⟨⟨"SortC63CellFragment"⟩⟩ []),
   .evar "ValV178" (.ctor ⟨⟨"SortC63CellOpt"⟩⟩ []), .evar "ValV179" (.ctor ⟨⟨"SortC6Cell"⟩⟩ []),
   .evar "ValV180" (.ctor ⟨⟨"SortC6CellFragment"⟩⟩ []),
   .evar "ValV181" (.ctor ⟨⟨"SortC6CellOpt"⟩⟩ []), .evar "ValV182" (.ctor ⟨⟨"SortC7Cell"⟩⟩ []),
   .evar "ValV183" (.ctor ⟨⟨"SortC7CellFragment"⟩⟩ []),
   .evar "ValV184" (.ctor ⟨⟨"SortC7CellOpt"⟩⟩ []), .evar "ValV185" (.ctor ⟨⟨"SortC8Cell"⟩⟩ []),
   .evar "ValV186" (.ctor ⟨⟨"SortC8CellFragment"⟩⟩ []),
   .evar "ValV187" (.ctor ⟨⟨"SortC8CellOpt"⟩⟩ []), .evar "ValV188" (.ctor ⟨⟨"SortC9Cell"⟩⟩ []),
   .evar "ValV189" (.ctor ⟨⟨"SortC9CellFragment"⟩⟩ []),
   .evar "ValV190" (.ctor ⟨⟨"SortC9CellOpt"⟩⟩ []),
   .evar "ValV191" (.ctor ⟨⟨"SortGeneratedCounterCell"⟩⟩ []),
   .evar "ValV192" (.ctor ⟨⟨"SortGeneratedCounterCellOpt"⟩⟩ []),
   .evar "ValV193" (.ctor ⟨⟨"SortGeneratedTopCell"⟩⟩ []),
   .evar "ValV194" (.ctor ⟨⟨"SortGeneratedTopCellFragment"⟩⟩ []),
   .evar "ValV195" (.ctor ⟨⟨"SortInt"⟩⟩ []), .evar "ValV196" (.ctor ⟨⟨"SortKCell"⟩⟩ []),
   .evar "ValV197" (.ctor ⟨⟨"SortKCellOpt"⟩⟩ []), .evar "ValV198" (.ctor ⟨⟨"SortKConfigVar"⟩⟩ []),
   .evar "ValV199" (.ctor ⟨⟨"SortList"⟩⟩ []), .evar "ValV200" (.ctor ⟨⟨"SortMap"⟩⟩ []),
   .evar "ValV201" (.ctor ⟨⟨"SortSet"⟩⟩ [])]
theorem nojunk_kitem_tabI_eq :
    tableOf [] (.or (KoreAML.srt "KItem") (KoreAML.noJunkDisjuncts "KItem" [] nojunk_kitem_gens)) = nojunk_kitem_tabI := by
  decide +kernel

/-- The translations of the sentence's disjuncts, under its table, and of the item's. -/
noncomputable def nojunk_kitem_trT : List P :=
  (njOrArgs U.ax1033.ax.pattern).map (tr ⟨nojunk_kitem_tabT, aliasLit⟩)
noncomputable def nojunk_kitem_trI : List P :=
  (KoreAML.noJunkDisjuncts "KItem" [] nojunk_kitem_gens).map
    (tr ⟨nojunk_kitem_tabI, []⟩)

theorem nojunk_kitem_d0 : (nojunk_kitem_trT.drop 0).take 25 = (nojunk_kitem_trI.drop 0).take 25 := by decide +kernel
theorem nojunk_kitem_d25 : (nojunk_kitem_trT.drop 25).take 25 = (nojunk_kitem_trI.drop 25).take 25 := by decide +kernel
theorem nojunk_kitem_d50 : (nojunk_kitem_trT.drop 50).take 25 = (nojunk_kitem_trI.drop 50).take 25 := by decide +kernel
theorem nojunk_kitem_d75 : (nojunk_kitem_trT.drop 75).take 25 = (nojunk_kitem_trI.drop 75).take 25 := by decide +kernel
theorem nojunk_kitem_d100 : (nojunk_kitem_trT.drop 100).take 25 = (nojunk_kitem_trI.drop 100).take 25 := by decide +kernel
theorem nojunk_kitem_d125 : (nojunk_kitem_trT.drop 125).take 25 = (nojunk_kitem_trI.drop 125).take 25 := by decide +kernel
theorem nojunk_kitem_d150 : (nojunk_kitem_trT.drop 150).take 25 = (nojunk_kitem_trI.drop 150).take 25 := by decide +kernel
theorem nojunk_kitem_d175 : (nojunk_kitem_trT.drop 175).take 25 = (nojunk_kitem_trI.drop 175).take 25 := by decide +kernel
theorem nojunk_kitem_d200 : nojunk_kitem_trT.drop 200 = nojunk_kitem_trI.drop 200 := by decide +kernel
/-- The translations of the disjuncts are the item's, by ranges of 25. -/
theorem nojunk_kitem_ds : nojunk_kitem_trT = nojunk_kitem_trI :=
  tieEq_range (l := nojunk_kitem_trT) (m := nojunk_kitem_trI) (a := 0) (n := 25) nojunk_kitem_d0 <|
    tieEq_range (l := nojunk_kitem_trT) (m := nojunk_kitem_trI) (a := 25) (n := 25) nojunk_kitem_d25 <|
    tieEq_range (l := nojunk_kitem_trT) (m := nojunk_kitem_trI) (a := 50) (n := 25) nojunk_kitem_d50 <|
    tieEq_range (l := nojunk_kitem_trT) (m := nojunk_kitem_trI) (a := 75) (n := 25) nojunk_kitem_d75 <|
    tieEq_range (l := nojunk_kitem_trT) (m := nojunk_kitem_trI) (a := 100) (n := 25) nojunk_kitem_d100 <|
    tieEq_range (l := nojunk_kitem_trT) (m := nojunk_kitem_trI) (a := 125) (n := 25) nojunk_kitem_d125 <|
    tieEq_range (l := nojunk_kitem_trT) (m := nojunk_kitem_trI) (a := 150) (n := 25) nojunk_kitem_d150 <|
    tieEq_range (l := nojunk_kitem_trT) (m := nojunk_kitem_trI) (a := 175) (n := 25) nojunk_kitem_d175 <|
    nojunk_kitem_d200

theorem nojunk_kitem_order : (trS U.ax1033).pat =
    (KoreAML.Cons.noJunkItem (c.sortName Srt.kitem) ((gensInOrder c defn.pres Srt.kitem).map (Gen.toK c))).pat := by
  rw [nojunk_kitem_name, nojunk_kitem_gens_eq]
  exact njTrOr_pat (d2 := []) (al2 := []) (a2 := ⟨0, "kernel", KoreAML.Cons.noJunkAx "KItem" nojunk_kitem_gens⟩)
    nojunk_kitem_sv rfl (njOr_eq nojunk_kitem_or) rfl nojunk_kitem_free nojunk_kitem_ifree (by rw [nojunk_kitem_tabT_eq, nojunk_kitem_tabI_eq, aliasLit_eq]; exact nojunk_kitem_ds)
theorem nojunk_kitem_members :
    ((gensInOrder c defn.pres Srt.kitem).map (Gen.toK c)).isPerm ((c.gens Srt.kitem).map (Gen.toK c)) = true := by
  decide +kernel

/-- **E for KItem's no junk (1033)**, for every H (`noJunkItem_of_subset`). -/
theorem nojunk_kitem_entailed (H : HookParams) : Γ (cH H) ⊧ (trS U.ax1033).pat := by
  intro M _ I hI
  rw [nojunk_kitem_order]
  refine noJunkItem_of_subset (defOK hI) (gs := (c.gens Srt.kitem).map (Gen.toK c))
    (fun g hg => (List.isPerm_iff.mp nojunk_kitem_members).mem_iff.mpr hg) ?_
  exact sat_cons hI (Or.inl ⟨_, noJunkItem_mem (c := cH H) (N := Srt.kitem)
    (show Srt.kitem ∈ consSorts c by decide +kernel) (show (c.gens Srt.kitem).isEmpty = false by decide +kernel), rfl⟩)

end KCore.TieRdrConfigDeep

#check @KCore.TieRdrConfigDeep.nojunk_trivial_entailed
#check @KCore.TieRdrConfigDeep.nojunk_items_entailed
#check @KCore.TieRdrConfigDeep.nojunk_kitem_entailed
#print axioms KCore.TieRdrConfigDeep.nojunk_trivial_entailed
#print axioms KCore.TieRdrConfigDeep.nojunk_items_entailed
#print axioms KCore.TieRdrConfigDeep.nojunk_kitem_entailed
