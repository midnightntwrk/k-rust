/-
  Layer 1 of the tie (C14) on kimp's text as kompile wrote it
  (`examples/ref-kimp/RefKimp/definition.kore`, user module `IMP`), on the literals `kore` and `defn`.
  Nothing here reads `Parse.parse` or `emit`. Run from the package root:
  `lake env lean test/TieKimp.lean`.

  - `userAxioms_eq`: the constants `U.axN` are the user module's 901 axioms, in text order.
  - `account`: the class lists partition the 901 sentences; `account_sizes` their counts;
    `account_classes`: the classes are the tie's (`tieClasses`, each with its direction).
  - `account_absent`, `absent_closed`: the no-direction class holds exactly the sentences that
    apply a symbol Γ lacks, so every sentence outside it applies Γ's symbols only.
  - `attrs_agree`: the attributes the translation does not read agree with `defn`.

  Layer 2, the function equations (39 sentences, 838 to 876: `isK`'s equation and, for each
  of the other 19 sort predicates, its plain equation and its `[owise]` one).
  - `fn_shape`: each of the 39 items of `fnItems` is the translation of one text sentence, pattern
    for pattern, in the order `fnText` lists them (one kernel decision); `fnText_mem`, `fns_account`:
    `fnText`'s sentences are the user module's at the indices of the account's function-equation
    class.
  - `fns_entailed` (E): Γ entails each of the 39 sentences, for every H. `fns_from_text` (the
    converse): the j-th item of `fnItems` is a consequence of `fnText[j]`, for every H.

  In files of their own, on the same literals: `sig_origin` (test/TieKimpSig.lean, by ranges of the
  signature's items) and `wf defn = true` (test/TieKimpWf.lean, conjunct by conjunct). One kernel
  decision of either exceeds 12 GiB on this text.

  Layer 2 in files of their own, on the same literals: the 79 rewrite rules (test/TieKimpRules.lean:
  W1, W2 and the converse for `ruleItems`); the constructor and no-junk sentences
  (test/TieKimpCons.lean: `cons_entailed`, `nojunk_entailed`); the declarations
  (test/TieKimpDecls.lean: `decls_entailed`).
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.TieKimp

open KCore ML Faithful KoreAML

kore_term kore from "examples/ref-kimp/RefKimp/definition.kore"
definition_of defn from "examples/ref-kimp/RefKimp/definition.kore"
user_axioms U from "examples/ref-kimp/RefKimp/definition.kore" module "IMP"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

/-- The axioms of the user module, in text order. -/
noncomputable def userAxioms : List AxiomDecl := kore.axiomDecls.filter (·.module == "IMP")

theorem userAxioms_eq : userAxioms = U.all := by kernel_rfl
theorem userAxioms_length : U.all.length = 901 := by decide +kernel

/-- `tr s`: the item `Theory.ofDefinition kore` holds for the sentence. -/
noncomputable def trS (ad : AxiomDecl) : Item := trAxiom kore.symbolDecls kore.aliasNames ad

theorem trS_is_text : (Theory.ofDefinition kore).axioms = kore.axiomDecls.map trS := rfl

/-! ## The account -/

/-- Per class of the tie (`tieClasses`), the indices (`AxiomDecl.index`) of its sentences:
- function equation: the equations of the sort predicates and of the definition's functions;
- rewrite rule: the 79 rules;
- constructor functional, subsort, injectivity, distinctness, no junk: the constructor sentences;
- function functional: the `functional` sentence of a function of the definition;
- hooked functional: the `functional` sentence of a symbol Γ states by its graph;
- collection law: associativity and the two units of `_List_`, `_Map_`, `_Set_`;
- library: an equation or a lemma of the builtin library over symbols Γ has;
- set idempotence: 573;
- set-variable lemma: the definedness lemmas over set variables (671 to 675: `%Int`, `/Int`,
  `<<Int`, `>>Int`, `modInt`; 904: kompile's `#Ceil(@K0 |-> @K1 @Rest)`), refuted at sets of values;
- no direction: a sentence that applies a symbol Γ does not have (633, `ite{Sort}`'s `functional`
  sentence, and 877, 878, `ite{K}`'s equations, among them: a symbol with sort parameters is one
  symbol at each instance, and Γ applies its `ite`, `kIte`, at no sort argument). -/
def classes : List (String × List Nat) :=
  [("function equation", [838, 839, 840, 841, 842, 843, 844, 845, 846, 847, 848, 849, 850, 851, 852, 853, 854, 855, 856, 857, 858,
      859, 860, 861, 862, 863, 864, 865, 866, 867, 868, 869, 870, 871, 872, 873, 874, 875, 876]),
   ("rewrite rule", [700, 701, 702, 703, 704, 705, 706, 707, 708, 709, 710, 711, 712, 713, 714, 715, 716, 717, 718, 719, 720,
      721, 722, 723, 724, 725, 726, 727, 728, 729, 730, 731, 732, 733, 734, 735, 736, 737, 738, 739, 740, 741,
      742, 743, 744, 745, 746, 747, 748, 749, 750, 751, 752, 753, 754, 755, 756, 757, 758, 759, 760, 761, 762,
      763, 764, 765, 766, 767, 768, 769, 770, 771, 772, 773, 774, 775, 776, 777, 778]),
   ("priority equation", []),
   ("constructor functional", [29, 44, 70, 95, 120, 144, 167, 189, 210, 230, 249, 267, 284, 300, 315, 329, 342, 354, 365, 375, 384,
      392, 399, 405, 410, 414, 417, 419, 436, 438, 440, 442, 444, 452, 465, 479, 491, 503, 512, 523, 531, 543,
      548, 557, 562, 577, 596, 600, 606, 637, 638, 646, 650, 653]),
   ("subsort", [4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]),
   ("injectivity", [30, 96, 121, 145, 168, 190, 211, 231, 250, 268, 285, 301, 316, 330, 343, 355, 366, 376, 385, 393, 400,
      406, 411, 415, 418, 420, 437, 439, 441, 443, 445, 453, 466, 480, 492, 504, 513, 524, 532, 544, 549, 558,
      563, 578, 597, 601, 607, 647, 651]),
   ("distinctness", [31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57,
      58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84,
      85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109,
      110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132,
      133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155,
      156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178,
      179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201,
      202, 203, 204, 205, 206, 207, 208, 209, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224,
      225, 226, 227, 228, 229, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247,
      248, 251, 252, 253, 254, 255, 256, 257, 258, 259, 260, 261, 262, 263, 264, 265, 266, 269, 270, 271, 272,
      273, 274, 275, 276, 277, 278, 279, 280, 281, 282, 283, 286, 287, 288, 289, 290, 291, 292, 293, 294, 295,
      296, 297, 298, 299, 302, 303, 304, 305, 306, 307, 308, 309, 310, 311, 312, 313, 314, 317, 318, 319, 320,
      321, 322, 323, 324, 325, 326, 327, 328, 331, 332, 333, 334, 335, 336, 337, 338, 339, 340, 341, 344, 345,
      346, 347, 348, 349, 350, 351, 352, 353, 356, 357, 358, 359, 360, 361, 362, 363, 364, 367, 368, 369, 370,
      371, 372, 373, 374, 377, 378, 379, 380, 381, 382, 383, 386, 387, 388, 389, 390, 391, 394, 395, 396, 397,
      398, 401, 402, 403, 404, 407, 408, 409, 412, 413, 416, 421, 422, 423, 424, 425, 426, 427, 428, 429, 430,
      431, 432, 454, 455, 456, 457, 458, 459, 460, 461, 462, 463, 464, 467, 468, 469, 470, 471, 472, 473, 474,
      475, 476, 481, 482, 483, 484, 485, 486, 487, 488, 489, 493, 494, 495, 496, 497, 498, 499, 500, 505, 506,
      507, 508, 509, 510, 511, 514, 515, 516, 517, 518, 519, 525, 526, 527, 528, 529, 533, 534, 535, 536, 545,
      546, 547, 550, 551, 552, 553, 554, 555, 559, 560, 564, 579, 580, 581, 582, 583, 602, 603, 604, 605, 608,
      609, 610, 648, 649, 652]),
   ("no junk", [655, 656, 657, 658, 659, 660, 661, 662, 663, 664, 665, 666, 667, 668, 669, 670]),
   ("function functional", [613, 614, 615, 616, 617, 618, 619, 620, 621, 622, 623, 624, 625, 626, 627, 628, 629, 630, 631, 632]),
   ("hooked functional", [433, 434, 435, 446, 447, 448, 449, 450, 451, 478, 490, 501, 520, 522, 530, 537, 538, 539,
      540, 541, 542, 556, 561, 568, 576, 584, 585, 586, 587, 588, 589, 590, 591, 593, 595, 598, 599, 612, 634,
      635, 636, 639, 640, 641, 642, 643, 644]),
   ("collection law", [565, 566, 567, 569, 570, 571, 572, 574, 575]),
   ("library", [676, 677, 678, 679, 680, 681, 682, 683, 684, 685, 686, 687, 688, 689, 690, 691, 692, 693,
      694, 695, 696, 697, 698, 699, 779, 781, 782, 783, 784, 785, 786, 787, 788, 789, 790, 791, 792, 793, 794, 795, 796,
      797, 798, 799, 800, 801, 802, 803, 804, 805, 806, 807, 808, 809, 810, 811, 813, 814, 815, 816, 817, 818, 819, 820,
      821, 822, 823, 824, 825, 826, 827, 828, 829, 830, 831, 832, 879, 880, 881, 882, 902, 903]),
   ("set idempotence", [573]),
   ("set-variable lemma", [671, 672, 673, 674, 675, 904]),
   ("function law", []),
   ("open generator law", []),
   ("open generator functional", []),
   ("no direction", [477, 502, 521, 592, 594, 611, 633, 645, 654, 780, 812, 833, 834, 835, 836, 837, 877, 878,
      883, 884, 885, 886, 887, 888, 889, 890, 891, 892, 893, 894, 895, 896, 897, 898, 899, 900, 901])]

/-- The indices of a class. -/
def classOf (n : String) : List Nat := (classes.filter (·.1 == n)).flatMap (·.2)

/-- The sentences' indices are 4 to 904. -/
theorem indices_eq : U.all.map (·.index) = List.range' 4 901 := by decide +kernel

/-- **The account**: the class lists partition the user module's sentences. Their concatenation is
a permutation of the sentences' indices, which are distinct, so each sentence is in one class and
in it once. -/
theorem account : (classes.flatMap (·.2)).isPerm (userAxioms.map (·.index)) = true ∧
    (userAxioms.map (·.index)).Nodup := by
  rw [userAxioms_eq]
  exact ⟨by decide +kernel, by rw [indices_eq]; exact List.nodup_range'⟩

/-- The class sizes. -/
theorem account_sizes : classes.map (fun cl => (cl.1, cl.2.length)) =
    [("function equation", 39), ("rewrite rule", 79), ("priority equation", 0), ("constructor functional",
     54), ("subsort", 25), ("injectivity", 49), ("distinctness", 437), ("no junk", 16), ("function functional", 20), ("hooked functional", 47), ("collection law", 9), ("library", 82), ("set idempotence",
     1), ("set-variable lemma", 6), ("function law", 0), ("open generator law", 0), ("open generator functional", 0), ("no direction", 37)] := by
  decide +kernel

/-- The classes are the tie's (`tieClasses`, which gives each its direction), in its order. -/
theorem account_classes : classes.map (·.1) = tieClasses.map (·.1) := by decide +kernel

/-- The symbol `k` of Γ has no name `iteSort?` reads as an instance of `ite`. -/
noncomputable def plainName (k : CtorSig) : Bool := (iteSort? (c.symName k.name)).isNone

/-- No symbol of Γ has a name `iteSort?` reads as an instance of `ite`, so each is applied at its
name with no sort argument (`gammaHasHead_eq_plain`). In parts of 50 symbols, each one kernel
decision: `iteSort?` reads a name as its characters, and one decision over every name exceeds
12 GiB. -/
theorem noIte₁ : ((kernelSyms c).take 50).all plainName = true := by decide +kernel
theorem noIte₂ : (((kernelSyms c).drop 50).take 50).all plainName = true := by decide +kernel
theorem noIte₃ : ((((kernelSyms c).drop 50).drop 50).take 50).all plainName = true := by decide +kernel
theorem noIte₄ : (((((kernelSyms c).drop 50).drop 50).drop 50).take 50).all plainName = true := by decide +kernel
theorem noIte₅ : (((((kernelSyms c).drop 50).drop 50).drop 50).drop 50).all plainName = true := by decide +kernel
theorem noIte : (kernelSyms c).all plainName = true :=
  all_of_take_drop_heads _ _ 50 noIte₁
    (all_of_take_drop_heads _ _ 50 noIte₂
    (all_of_take_drop_heads _ _ 50 noIte₃
    (all_of_take_drop_heads _ _ 50 noIte₄ noIte₅)))

/-- **A sentence outside the no-direction class applies only symbols Γ has**, each a head with its
sort arguments (`appHeadsOf`) among Γ's (`gammaHeads`), and each sentence of that class applies one
Γ lacks. -/
theorem account_absent : userAxioms.all (fun ad =>
    (classOf "no direction").contains ad.index != (appHeadsOf ad.ax.pattern).all (gammaHasHead c)) = true := by
  rw [userAxioms_eq, gammaHasHead_eq_plain (c := c) noIte]; decide_cheap 100

/-- **The no-direction class is closed**: every sentence outside it applies only symbols Γ has,
so no sentence with a direction applies a symbol Γ lacks. The injection `inj` is no member of
`kernelSyms` (`coreOK` keeps the name from them) and is Γ's all the same: the constructor items
state it for each subsort pair (`gammaHeads`). -/
theorem absent_closed :
    (userAxioms.filter (fun ad => !(classOf "no direction").contains ad.index)).all
      (fun ad => (appHeadsOf ad.ax.pattern).all (gammaHasHead c)) = true :=
  tieAbsent_of_account userAxioms _ _ account_absent

/-! ## The attributes -/

/-- **The attributes of the text agree with `defn`** (`attrsAgree`): constructors, functions,
hooks, collection symbols, priorities. -/
theorem attrs_agree : attrsAgree kore defn = true := by
  rw [attrsAgree, AttrsAgree.ctors, AttrsAgree.fns, AttrsAgree.hooks]; decide_cheap 40

/-! ## Function equations (39 sentences) -/

kernel_rfl fnItems_withHooks : ∀ (c : Semantics) (H : HookParams), fnItems (c.withHooks H) = fnItems c

/-- The axioms of Γ's equations, in `fnItems`'s order. -/
noncomputable def fnAxioms (c : Semantics) : List Kore.Axiom :=
  c.allFns.flatMap fun f => (fnEquationsK c f).filterMap fun
    | .axiom a => some a
    | _ => none

theorem fnItems_eq : fnItems c = (fnAxioms c).map fun a => trAxiom [] [] ⟨0, "kernel", a⟩ := by kernel_rfl

/-- The text sentences of Γ's 39 equations, in `fnItems`'s order (`isK`'s 856 first; of each
other sort predicate the plain equation, then its `[owise]` one). -/
noncomputable def fnText : List AxiomDecl :=
  [U.ax856, U.ax864, U.ax863, U.ax862, U.ax861, U.ax870, U.ax869, U.ax872, U.ax871, U.ax868, U.ax867,
   U.ax839, U.ax838, U.ax855, U.ax854, U.ax853, U.ax852, U.ax849, U.ax848, U.ax851, U.ax850, U.ax858,
   U.ax857, U.ax860, U.ax859, U.ax841, U.ax840, U.ax843, U.ax842, U.ax847, U.ax846, U.ax845, U.ax844,
   U.ax866, U.ax865, U.ax874, U.ax873, U.ax876, U.ax875]

/-- **Γ's equations are the text's sentences' translations, pattern for pattern**: the j-th item
of `fnItems` and the translation of `fnText[j]` (one kernel decision). -/
theorem fn_shape : (fnItems c).map (·.pat) = fnText.map (trS · |>.pat) := by
  rw [fnItems_eq, List.map_map]
  exact (by decide_map_blocks 10 3 :
    ((fnAxioms c).map fun a => (trAxiom [] [] ⟨0, "kernel", a⟩).pat) = fnText.map (trS · |>.pat))

/-- Each member of `fnText` is the sentence of the user module with its index. -/
theorem fnText_mem : fnText = (fnText.map (·.index)).filterMap (fun i => userAxioms.find? (·.index == i)) := by
  rw [userAxioms_eq]; kernel_rfl

/-- **`fnText` is the account's function-equation class**: the same indices, each once. -/
theorem fns_account : (classOf "function equation").isPerm (fnText.map (·.index)) = true := by decide +kernel

/-- **E for the 39 equations**: Γ entails each, for every H. -/
theorem fns_entailed (H : HookParams) : ∀ ad ∈ fnText, Γ (cH H) ⊧ (trS ad).pat := by
  intro ad had M _ I hI
  have hmem : (trS ad).pat ∈ (fnItems c).map (·.pat) := by
    rw [fn_shape]; exact List.mem_map.mpr ⟨ad, had, rfl⟩
  obtain ⟨it, hit, he⟩ := List.mem_map.mp hmem
  exact hI _ (Or.inl (Or.inl (Or.inr (Or.inl ⟨it, by rw [fnItems_withHooks]; exact hit, he⟩))))

/-- **The converse for `fnItems`**: each item is a text sentence's translation, the j-th's
`fnText[j]`. -/
theorem fns_from_text (H : HookParams) :
    ∀ (j : Nat) (it : Item), (fnItems (cH H))[j]? = some it →
      ∃ ad, fnText[j]? = some ad ∧ (itemsPremises [trS ad] ⊧ it.pat) := by
  intro j it hj
  rw [fnItems_withHooks] at hj
  have h1 : ((fnItems c).map (·.pat))[j]? = some it.pat := by rw [List.getElem?_map, hj]; rfl
  rw [fn_shape, List.getElem?_map] at h1
  cases hf : fnText[j]? with
  | none => rw [hf] at h1; cases h1
  | some ad =>
    rw [hf] at h1
    refine ⟨ad, rfl, fun {M} _ {I} hI => ?_⟩
    have he : (trS ad).pat = it.pat := Option.some.inj h1
    exact hI _ (Or.inl ⟨trS ad, List.mem_singleton_self _, he⟩)

end KCore.TieKimp

#print axioms KCore.TieKimp.userAxioms_eq
#print axioms KCore.TieKimp.account
#print axioms KCore.TieKimp.account_classes
#print axioms KCore.TieKimp.account_absent
#print axioms KCore.TieKimp.absent_closed
#print axioms KCore.TieKimp.attrs_agree
#print axioms KCore.TieKimp.fn_shape
#print axioms KCore.TieKimp.fnText_mem
#print axioms KCore.TieKimp.fns_account
#print axioms KCore.TieKimp.fns_entailed
#print axioms KCore.TieKimp.fns_from_text
