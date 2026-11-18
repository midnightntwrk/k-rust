/-
  The function equations of kore.k's text as kompile wrote it
  (`examples/ref-kk/RefKk/definition.kore`, user module `KORE`), layer 2 of the tie (C14), on the
  literals `kore` and `defn`. Nothing here reads `Parse.parse` or `emit`. Run from the package
  root: `lake env lean test/TieKkFns.lean`.

  - `fnText`: the account's 302 function-equation sentences (test/TieKk.lean, `classes`), in the
    order of Γ's items (`fnItems`, `TiePair.gammaPats`): the j-th is the equation of the j-th clause,
    found by its head symbol and priority.
  - `fns_same`: at 294 positions (`goodPos`) the item and the sentence's translation are one
    pattern up to one renaming of a free variable (`TiePair.sameB`; equal at 293, renamed at 182,
    `mkEl`'s `[owise]` equation 738), decided by ranges of 20; `fn49_renamed`: at position 49
    (`ensure`'s `[owise]` equation 530) the sentence is the item with two free variables renamed.
  - `fns_entailed` (E): Γ entails the sentence at each of these 295 positions, for every H;
    `fns_from_text` (the converse): the item at each of them is a consequence of its sentence.
  - `fns_positions`: the 295 shown positions and the 7 others are the 302. At the 7 others the
    two are not one pattern up to `sameB`'s renamings (evaluated natively; not stated as a kernel
    decision: `sameB`'s failing search tries every renaming of `renCands` on patterns of up to
    17579 nodes);
    each is the `[owise]` equation of a function (positions 31 `cmp` 503, 109 `hookOp` 564, 133
    `isElem` 628, 166 `match` 709, 172 `matchCol` 724, 185 `mkInj` 739, 225 `tag` 817). Of the
    same size as the item, the first six differ where the exclusion lists the other equations:
    the bound variables' sorts (31, 109, 166, 172) or the disjuncts (133, 225) come in another
    order; 185 differs in the keys of its bound variables. These 7 are tied in
    `test/TieKkOwise.lean`.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.TieKk

open KCore ML Faithful KoreAML

kore_term kore from "examples/ref-kk/RefKk/definition.kore"
definition_of defn from "examples/ref-kk/RefKk/definition.kore"
user_axioms U from "examples/ref-kk/RefKk/definition.kore" module "KORE"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

/-- `tr s`: the item `Theory.ofDefinition kore` holds for the sentence. -/
noncomputable def trS (ad : AxiomDecl) : Item := trAxiom kore.symbolDecls kore.aliasNames ad

/-- The text's function equations, in the order of Γ's items. -/
noncomputable def fnText : List AxiomDecl :=
  [U.ax479, U.ax480, U.ax481, U.ax482, U.ax483, U.ax484, U.ax485, U.ax486, U.ax487, U.ax488, U.ax489,
   U.ax490, U.ax491, U.ax492, U.ax493, U.ax494, U.ax495, U.ax497, U.ax498, U.ax499, U.ax500, U.ax501,
   U.ax502, U.ax504, U.ax505, U.ax506, U.ax507, U.ax508, U.ax509, U.ax510, U.ax511, U.ax503, U.ax512,
   U.ax513, U.ax514, U.ax515, U.ax516, U.ax517, U.ax518, U.ax519, U.ax520, U.ax523, U.ax524, U.ax525,
   U.ax526, U.ax527, U.ax528, U.ax529, U.ax531, U.ax530, U.ax532, U.ax533, U.ax534, U.ax535, U.ax536,
   U.ax537, U.ax538, U.ax539, U.ax540, U.ax541, U.ax542, U.ax543, U.ax544, U.ax545, U.ax546, U.ax547,
   U.ax548, U.ax551, U.ax552, U.ax553, U.ax554, U.ax555, U.ax556, U.ax557, U.ax560, U.ax561, U.ax562,
   U.ax563, U.ax565, U.ax566, U.ax567, U.ax568, U.ax569, U.ax570, U.ax571, U.ax572, U.ax573, U.ax574,
   U.ax575, U.ax576, U.ax577, U.ax578, U.ax579, U.ax580, U.ax581, U.ax582, U.ax583, U.ax584, U.ax585,
   U.ax586, U.ax587, U.ax588, U.ax589, U.ax590, U.ax591, U.ax592, U.ax593, U.ax594, U.ax595, U.ax564,
   U.ax599, U.ax600, U.ax601, U.ax602, U.ax603, U.ax604, U.ax605, U.ax606, U.ax607, U.ax608, U.ax609,
   U.ax610, U.ax611, U.ax612, U.ax613, U.ax614, U.ax615, U.ax616, U.ax617, U.ax618, U.ax619, U.ax629,
   U.ax630, U.ax628, U.ax688, U.ax689, U.ax690, U.ax691, U.ax692, U.ax693, U.ax694, U.ax695, U.ax696,
   U.ax697, U.ax698, U.ax699, U.ax700, U.ax701, U.ax702, U.ax703, U.ax704, U.ax705, U.ax706, U.ax707,
   U.ax708, U.ax710, U.ax711, U.ax712, U.ax713, U.ax714, U.ax715, U.ax716, U.ax717, U.ax718, U.ax719,
   U.ax720, U.ax709, U.ax721, U.ax722, U.ax723, U.ax725, U.ax726, U.ax724, U.ax727, U.ax728, U.ax729,
   U.ax730, U.ax731, U.ax732, U.ax735, U.ax736, U.ax737, U.ax738, U.ax740, U.ax741, U.ax739, U.ax742,
   U.ax743, U.ax744, U.ax745, U.ax746, U.ax747, U.ax750, U.ax751, U.ax752, U.ax753, U.ax754, U.ax755,
   U.ax756, U.ax789, U.ax790, U.ax791, U.ax792, U.ax798, U.ax799, U.ax800, U.ax801, U.ax804, U.ax806,
   U.ax807, U.ax808, U.ax809, U.ax810, U.ax811, U.ax812, U.ax813, U.ax814, U.ax815, U.ax816, U.ax818,
   U.ax819, U.ax820, U.ax821, U.ax822, U.ax823, U.ax817, U.ax824, U.ax825, U.ax826, U.ax827, U.ax828,
   U.ax829, U.ax830, U.ax831, U.ax832, U.ax833, U.ax834, U.ax835, U.ax836, U.ax645, U.ax653, U.ax652,
   U.ax651, U.ax650, U.ax661, U.ax660, U.ax673, U.ax672, U.ax657, U.ax656, U.ax623, U.ax622, U.ax644,
   U.ax643, U.ax632, U.ax631, U.ax679, U.ax678, U.ax640, U.ax639, U.ax642, U.ax641, U.ax647, U.ax646,
   U.ax649, U.ax648, U.ax636, U.ax635, U.ax638, U.ax637, U.ax681, U.ax680, U.ax683, U.ax682, U.ax655,
   U.ax654, U.ax625, U.ax624, U.ax667, U.ax666, U.ax663, U.ax662, U.ax677, U.ax676, U.ax634, U.ax633,
   U.ax659, U.ax658, U.ax669, U.ax668, U.ax671, U.ax670, U.ax685, U.ax684, U.ax665, U.ax664, U.ax627,
   U.ax626, U.ax621, U.ax620, U.ax675, U.ax674]

theorem fnText_length : fnText.length = 302 ∧ (TiePair.gammaPats c).length = 302 := by decide +kernel

/-- The item at position j and the sentence's translation are one pattern up to `sameB`. -/
noncomputable def fnSame (j : Nat) : Bool :=
  match (TiePair.gammaPats c)[j]?, fnText[j]? with
  | some g, some ad => TiePair.sameB g (trS ad).pat
  | _, _ => false

/-- The positions shown by `fnSame`. -/
def goodPos : List Nat :=
  [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25,
    26, 27, 28, 29, 30, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 50, 51, 52, 53,
    54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79,
    80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105,
    106, 107, 108, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132,
    134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159,
    160, 161, 162, 163, 164, 165, 167, 168, 169, 170, 171, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 186, 187, 188,
    189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214,
    215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241,
    242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 256, 257, 258, 259, 260, 261, 262, 263, 264, 265, 266, 267,
    268, 269, 270, 271, 272, 273, 274, 275, 276, 277, 278, 279, 280, 281, 282, 283, 284, 285, 286, 287, 288, 289, 290, 291, 292, 293,
    294, 295, 296, 297, 298, 299, 300, 301]

theorem fns_0 : ((goodPos.drop 0).take 20).all fnSame = true := by decide +kernel
theorem fns_20 : ((goodPos.drop 20).take 20).all fnSame = true := by decide +kernel
theorem fns_40 : ((goodPos.drop 40).take 20).all fnSame = true := by decide +kernel
theorem fns_60 : ((goodPos.drop 60).take 20).all fnSame = true := by decide +kernel
theorem fns_80 : ((goodPos.drop 80).take 20).all fnSame = true := by decide +kernel
theorem fns_100 : ((goodPos.drop 100).take 20).all fnSame = true := by decide +kernel
theorem fns_120 : ((goodPos.drop 120).take 20).all fnSame = true := by decide +kernel
theorem fns_140 : ((goodPos.drop 140).take 20).all fnSame = true := by decide +kernel
theorem fns_160 : ((goodPos.drop 160).take 20).all fnSame = true := by decide +kernel
theorem fns_180 : ((goodPos.drop 180).take 20).all fnSame = true := by decide +kernel
theorem fns_200 : ((goodPos.drop 200).take 20).all fnSame = true := by decide +kernel
theorem fns_220 : ((goodPos.drop 220).take 20).all fnSame = true := by decide +kernel
theorem fns_240 : ((goodPos.drop 240).take 20).all fnSame = true := by decide +kernel
theorem fns_260 : ((goodPos.drop 260).take 20).all fnSame = true := by decide +kernel
theorem fns_280 : (goodPos.drop 280).all fnSame = true := by decide +kernel

theorem fns_same : goodPos.all fnSame = true :=
  tieAll_whole (p := fnSame) <|
    tieAll_range (a := 0) (n := 20) fns_0 <|
    tieAll_range (a := 20) (n := 20) fns_20 <|
    tieAll_range (a := 40) (n := 20) fns_40 <|
    tieAll_range (a := 60) (n := 20) fns_60 <|
    tieAll_range (a := 80) (n := 20) fns_80 <|
    tieAll_range (a := 100) (n := 20) fns_100 <|
    tieAll_range (a := 120) (n := 20) fns_120 <|
    tieAll_range (a := 140) (n := 20) fns_140 <|
    tieAll_range (a := 160) (n := 20) fns_160 <|
    tieAll_range (a := 180) (n := 20) fns_180 <|
    tieAll_range (a := 200) (n := 20) fns_200 <|
    tieAll_range (a := 220) (n := 20) fns_220 <|
    tieAll_range (a := 240) (n := 20) fns_240 <|
    tieAll_range (a := 260) (n := 20) fns_260 <|
    fns_280

/-- Position 49 (`ensure`'s `[owise]` equation, sentence 530): the sentence is the item with its
free variable 5 renamed to 6, then 2 to 5. -/
theorem fn49_renamed : ∃ g ad, (TiePair.gammaPats c)[49]? = some g ∧ fnText[49]? = some ad ∧
    TiePair.renSeq g [(5, 6), (2, 5)] = some (trS ad).pat :=
  ⟨_, _, rfl, rfl, by decide +kernel⟩

/-- The positions the tie shows. -/
def shownPos : List Nat := 49 :: goodPos

/-- At a shown position the item and the sentence are satisfied by the same interpretations. -/
theorem shown_iff {j : Nat} (hj : j ∈ shownPos) : ∃ g ad, (TiePair.gammaPats c)[j]? = some g ∧
    fnText[j]? = some ad ∧ ∀ {M : Type} {I : Interpretation KoreAML.Sym M}, (I ⊧ᴵ (trS ad).pat) ↔ (I ⊧ᴵ g) := by
  rcases List.mem_cons.mp hj with rfl | hj
  · obtain ⟨g, ad, hg, ha, hr⟩ := fn49_renamed
    exact ⟨g, ad, hg, ha, fun {M I} => TiePair.renSeq_iff hr⟩
  · have h := List.all_eq_true.mp fns_same j hj
    unfold fnSame at h
    cases hg : (TiePair.gammaPats c)[j]? with
    | none => rw [hg] at h; cases h
    | some g =>
      cases ha : fnText[j]? with
      | none => rw [hg, ha] at h; cases h
      | some ad =>
        rw [hg, ha] at h
        exact ⟨g, ad, rfl, rfl, fun {M I} => TiePair.sameB_iff h⟩

/-- **E for the shown function equations**: Γ entails the sentence at each shown position, for
every H. -/
theorem fns_entailed (H : HookParams) : ∀ j ∈ shownPos, ∀ ad, fnText[j]? = some ad → Γ (cH H) ⊧ (trS ad).pat := by
  intro j hj ad had M _ I hI
  obtain ⟨g, ad', hg, ha, hiff⟩ := shown_iff hj
  rw [had, Option.some.injEq] at ha
  subst ha
  refine hiff.mpr ?_
  obtain ⟨it, hit, rfl⟩ : ∃ it ∈ fnItems c, it.pat = g := by
    unfold TiePair.gammaPats at hg
    rw [List.getElem?_map] at hg
    cases h : (fnItems c)[j]? with
    | none => rw [h] at hg; cases hg
    | some it => rw [h] at hg; exact ⟨it, List.mem_of_getElem? h, Option.some.inj hg⟩
  exact hI _ (Or.inl (Or.inl (Or.inr (Or.inl ⟨it, by rw [TiePair.fnItems_withHooks]; exact hit, rfl⟩))))

/-- **The converse at the shown positions**: the item at each is a consequence of its sentence,
for every H. -/
theorem fns_from_text (H : HookParams) : ∀ j ∈ shownPos, ∀ it, (fnItems (cH H))[j]? = some it →
    ∃ ad, fnText[j]? = some ad ∧ (itemsPremises [trS ad] ⊧ it.pat) := by
  intro j hj it hit
  rw [TiePair.fnItems_withHooks] at hit
  obtain ⟨g, ad, hg, ha, hiff⟩ := shown_iff hj
  have : g = it.pat := by
    unfold TiePair.gammaPats at hg
    rw [List.getElem?_map, hit] at hg
    exact (Option.some.inj hg).symm
  subst this
  exact ⟨ad, ha, fun {M} _ {I} hI => hiff.mp (hI _ (Or.inl ⟨trS ad, List.mem_singleton_self _, rfl⟩))⟩

/-- The shown and the open positions are all 302. -/
theorem fns_positions : (([31, 109, 133, 166, 172, 185, 225] ++ shownPos).isPerm (List.range 302)) = true := by
  decide +kernel

end KCore.TieKk

#print axioms KCore.TieKk.fns_entailed
#print axioms KCore.TieKk.fns_from_text
