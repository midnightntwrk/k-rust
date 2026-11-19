/-
  Part Sig of the tie (C14) on `f2-examples/rdr-config-deep.kompile.kore`, test/TieRdrConfigDeep.lean: the sections
  `--split` puts here, in the tie's namespace. A test file imports no test file, so this one
  repeats the literals and the definitions and facts it reads. Written by
  `TIEGEN_PROBE_TIMEOUT=3000 python3 -I test/constructs/tiegen.py rdr-config-deep --split --cons-head
  --wf-parts --sig-chunk-first 13 --account-sorted --heads-literal --heads-codes --chunk 50
  --attrs-blocks 50 --decl-parts --fn-blocks 27 --absent-file --decl-syms-literal --nojunk-eq
  --nojunk-blocks 25 --sig-positions --fnfun-chunk 34`;
  run from the package root: `lake env lean -j1 test/TieRdrConfigDeepSig.lean`
  (251 s, peak 3.5 GiB under a 12 GiB scope with one Lean thread).
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

/-! ## The declarations: `sig_origin` and `decls_entailed`, by ranges -/

/-- `p` holds from `a` on where it holds on the `n` members from `a` and from `a + n` on. -/
theorem tieAllE_range {α : Type} {l : List α} {p : α → Bool} {a n : Nat}
    (h : ((l.drop a).take n).all p = true) (ht : (l.drop (a + n)).all p = true) :
    (l.drop a).all p = true := by
  rw [← List.take_append_drop n (l.drop a), List.all_append, h, List.drop_drop, ht]; rfl

/-- `p` holds of the whole list where it holds from `0` on. -/
theorem tieAllE_whole {α : Type} {l : List α} {p : α → Bool} (h : (l.drop 0).all p = true) :
    l.all p = true := h

/-- The item of Γ's signature is a declaration's item of the text, or a surplus one. -/
noncomputable def sigFrom (it : Item) : Bool :=
  (Theory.ofDefinition kore).signature.any (·.pat == it.pat) || surplusItem kore it

/-- Next's arity at the configuration sort, which Γ states whatever the text. -/
noncomputable def nextItem : Item := KoreAML.nextArityItem [] (srtOf c topCellSort)

/-- No sentence of the text has a `\rewrites` or a `\next`, so the text's signature states the
arity of next at no sort. -/
theorem text_nextless : kore.axiomDecls.all (fun ad => (nextSortsOf ad.ax.pattern).isEmpty) = true := by
  decide +kernel

/-- The item has an origin in the text, or is next's arity at the configuration sort. -/
noncomputable def sigFromN (it : Item) : Bool := sigFrom it || it.pat == nextItem.pat

/-- Where an item of Γ's signature has its origin: the text's signature item at a position, the
registry sort at a number or the hooked symbol of `hookSigs` at a position whose surplus item it
is, or next's arity. -/
inductive TieSigAt
  | text (j : Nat)
  | regSort (s : Nat)
  | hook (j : Nat)
  | next

/-- The origin of each item of `sigItems c`, in its order. -/
def sigPos : List TieSigAt :=
  [.text 0, .text 1, .text 2, .text 189, .text 143, .text 134, .text 77, .text 118, .text 154,
   .regSort 8, .regSort 9, .regSort 10, .regSort 11, .regSort 12, .regSort 13, .regSort 14,
   .regSort 15, .regSort 16, .text 89, .text 75, .text 95, .text 128, .regSort 21, .regSort 22,
   .regSort 23, .regSort 24, .regSort 25, .regSort 26, .regSort 27, .regSort 28, .regSort 29,
   .text 186, .text 135, .text 204, .text 64, .text 155, .text 180, .text 103, .text 104,
   .text 202, .text 54, .text 79, .text 97, .text 198, .text 28, .text 70, .text 133, .text 106,
   .text 55, .text 131, .text 122, .text 196, .text 178, .text 6, .text 168, .text 132, .text 158,
   .text 49, .text 33, .text 41, .text 17, .text 22, .text 19, .text 145, .text 114, .text 12,
   .text 5, .text 24, .text 94, .text 60, .text 80, .text 83, .text 107, .text 179, .text 169,
   .text 139, .text 184, .text 117, .text 162, .text 9, .text 159, .text 50, .text 130, .text 116,
   .text 192, .text 119, .text 199, .text 172, .text 105, .text 109, .text 201, .text 102,
   .text 125, .text 84, .text 91, .text 113, .text 161, .text 92, .text 127, .text 59, .text 156,
   .text 111, .text 146, .text 23, .text 8, .text 14, .text 69, .text 36, .text 182, .text 126,
   .text 149, .text 29, .text 87, .text 16, .text 44, .text 10, .text 32, .text 21, .text 46,
   .text 90, .text 78, .text 140, .text 123, .text 37, .text 101, .text 183, .text 34, .text 4,
   .text 121, .text 176, .text 200, .text 43, .text 63, .text 152, .text 18, .text 197, .text 148,
   .text 65, .text 74, .text 163, .text 30, .text 93, .text 137, .text 174, .text 31, .text 153,
   .text 195, .text 185, .text 115, .text 81, .text 164, .text 58, .text 3, .text 100, .text 136,
   .text 190, .text 47, .text 40, .text 165, .text 112, .text 142, .text 73, .text 61, .text 129,
   .text 177, .text 120, .text 167, .text 15, .text 181, .text 150, .text 62, .text 72, .text 170,
   .text 76, .text 52, .text 85, .text 194, .text 67, .text 88, .text 68, .text 42, .text 20,
   .text 160, .text 175, .text 96, .text 144, .text 38, .text 157, .text 35, .text 57, .text 71,
   .text 11, .text 45, .text 141, .text 138, .text 7, .text 203, .text 27, .text 13, .text 166,
   .text 188, .text 56, .text 48, .text 110, .text 108, .text 171, .text 147, .text 39, .text 187,
   .text 51, .text 99, .text 98, .text 173, .text 82, .text 124, .text 53, .text 191, .text 26,
   .text 151, .text 66, .text 86, .text 25, .text 410, .text 411, .text 544, .text 545, .text 437,
   .text 857, .text 438, .text 459, .text 868, .text 460, .text 481, .text 879, .text 482,
   .text 503, .text 890, .text 504, .text 525, .text 901, .text 526, .text 535, .text 906,
   .text 536, .text 537, .text 907, .text 538, .text 539, .text 908, .text 540, .text 541,
   .text 909, .text 542, .text 417, .text 847, .text 418, .text 419, .text 848, .text 420,
   .text 421, .text 849, .text 422, .text 423, .text 850, .text 424, .text 425, .text 851,
   .text 426, .text 427, .text 852, .text 428, .text 429, .text 853, .text 430, .text 431,
   .text 854, .text 432, .text 433, .text 855, .text 434, .text 435, .text 856, .text 436,
   .text 439, .text 858, .text 440, .text 441, .text 859, .text 442, .text 443, .text 860,
   .text 444, .text 445, .text 861, .text 446, .text 447, .text 862, .text 448, .text 449,
   .text 863, .text 450, .text 451, .text 864, .text 452, .text 453, .text 865, .text 454,
   .text 455, .text 866, .text 456, .text 457, .text 867, .text 458, .text 461, .text 869,
   .text 462, .text 463, .text 870, .text 464, .text 465, .text 871, .text 466, .text 467,
   .text 872, .text 468, .text 469, .text 873, .text 470, .text 471, .text 874, .text 472,
   .text 473, .text 875, .text 474, .text 475, .text 876, .text 476, .text 477, .text 877,
   .text 478, .text 479, .text 878, .text 480, .text 483, .text 880, .text 484, .text 485,
   .text 881, .text 486, .text 487, .text 882, .text 488, .text 489, .text 883, .text 490,
   .text 491, .text 884, .text 492, .text 493, .text 885, .text 494, .text 495, .text 886,
   .text 496, .text 497, .text 887, .text 498, .text 499, .text 888, .text 500, .text 501,
   .text 889, .text 502, .text 505, .text 891, .text 506, .text 507, .text 892, .text 508,
   .text 509, .text 893, .text 510, .text 511, .text 894, .text 512, .text 513, .text 895,
   .text 514, .text 515, .text 896, .text 516, .text 517, .text 897, .text 518, .text 519,
   .text 898, .text 520, .text 521, .text 899, .text 522, .text 523, .text 900, .text 524,
   .text 527, .text 902, .text 528, .text 529, .text 903, .text 530, .text 531, .text 904,
   .text 532, .text 533, .text 905, .text 534, .text 546, .text 911, .text 543, .text 910,
   .text 836, .text 840, .text 839, .text 842, .text 843, .text 841, .text 641, .text 835,
   .text 833, .text 834, .text 672, .text 674, .text 673, .text 705, .text 707, .text 706,
   .text 738, .text 740, .text 739, .text 771, .text 773, .text 772, .text 804, .text 806,
   .text 805, .text 819, .text 821, .text 820, .text 822, .text 824, .text 823, .text 825,
   .text 827, .text 826, .text 828, .text 830, .text 829, .text 642, .text 644, .text 643,
   .text 645, .text 647, .text 646, .text 648, .text 650, .text 649, .text 651, .text 653,
   .text 652, .text 654, .text 656, .text 655, .text 657, .text 659, .text 658, .text 660,
   .text 662, .text 661, .text 663, .text 665, .text 664, .text 666, .text 668, .text 667,
   .text 669, .text 671, .text 670, .text 675, .text 677, .text 676, .text 678, .text 680,
   .text 679, .text 681, .text 683, .text 682, .text 684, .text 686, .text 685, .text 687,
   .text 689, .text 688, .text 690, .text 692, .text 691, .text 693, .text 695, .text 694,
   .text 696, .text 698, .text 697, .text 699, .text 701, .text 700, .text 702, .text 704,
   .text 703, .text 708, .text 710, .text 709, .text 711, .text 713, .text 712, .text 714,
   .text 716, .text 715, .text 717, .text 719, .text 718, .text 720, .text 722, .text 721,
   .text 723, .text 725, .text 724, .text 726, .text 728, .text 727, .text 729, .text 731,
   .text 730, .text 732, .text 734, .text 733, .text 735, .text 737, .text 736, .text 741,
   .text 743, .text 742, .text 744, .text 746, .text 745, .text 747, .text 749, .text 748,
   .text 750, .text 752, .text 751, .text 753, .text 755, .text 754, .text 756, .text 758,
   .text 757, .text 759, .text 761, .text 760, .text 762, .text 764, .text 763, .text 765,
   .text 767, .text 766, .text 768, .text 770, .text 769, .text 774, .text 776, .text 775,
   .text 777, .text 779, .text 778, .text 780, .text 782, .text 781, .text 783, .text 785,
   .text 784, .text 786, .text 788, .text 787, .text 789, .text 791, .text 790, .text 792,
   .text 794, .text 793, .text 795, .text 797, .text 796, .text 798, .text 800, .text 799,
   .text 801, .text 803, .text 802, .text 807, .text 809, .text 808, .text 810, .text 812,
   .text 811, .text 813, .text 815, .text 814, .text 816, .text 818, .text 817, .text 837,
   .text 838, .text 831, .text 832, .hook 0, .hook 1, .hook 2, .hook 3, .hook 4, .hook 5, .hook 6,
   .hook 7, .hook 8, .hook 9, .hook 10, .hook 11, .hook 12, .hook 13, .hook 14, .hook 15, .hook 16,
   .hook 17, .hook 18, .hook 19, .hook 20, .hook 21, .hook 22, .hook 23, .hook 24, .hook 25,
   .hook 26, .hook 27, .hook 28, .hook 29, .hook 30, .hook 31, .hook 32, .hook 33, .hook 34,
   .text 415, .text 570, .text 565, .text 556, .text 567, .text 554, .text 555, .text 569,
   .text 1119, .text 1115, .text 844, .text 416, .text 560, .text 566, .text 571, .text 640,
   .text 558, .text 559, .text 563, .text 1116, .text 564, .text 414, .text 552, .text 1114,
   .text 547, .text 549, .text 568, .text 1117, .text 550, .text 846, .text 1120, .text 572,
   .hook 67, .hook 68, .hook 69, .hook 70, .hook 71, .hook 72, .hook 73, .hook 74, .hook 75,
   .hook 76, .hook 77, .hook 78, .hook 79, .hook 80, .hook 81, .hook 82, .hook 83, .hook 84,
   .hook 85, .hook 86, .hook 87, .hook 88, .hook 89, .hook 90, .hook 91, .hook 92, .hook 93,
   .hook 94, .hook 95, .hook 96, .hook 97, .hook 98, .hook 99, .hook 100, .hook 101, .hook 102,
   .hook 103, .hook 104, .hook 105, .hook 106, .hook 107, .hook 108, .hook 109, .hook 110,
   .hook 111, .hook 112, .hook 113, .hook 114, .hook 115, .hook 116, .hook 117, .hook 118,
   .hook 119, .hook 120, .hook 121, .hook 122, .hook 123, .hook 124, .hook 125, .hook 126,
   .hook 127, .hook 128, .hook 129, .hook 130, .hook 131, .hook 132, .hook 133, .hook 134,
   .hook 135, .hook 136, .hook 137, .hook 138, .hook 139, .hook 140, .hook 141, .hook 142,
   .hook 143, .hook 144, .text 1123, .text 1124, .next]

theorem sigPos_length : sigPos.length = 770 := rfl

/-- The item is the one its origin names: one comparison, with the text's item at the position or
with the surplus item of the registry sort or the hooked symbol (a disjunct of `surplusItem`). -/
noncomputable def sigFromAt (it : Item) : TieSigAt → Bool
  | .text j => ((Theory.ofDefinition kore).signature[j]?).any (·.pat == it.pat)
  | .regSort s => decide (s < nRegSorts) &&
      (let n := "Sort" ++ regSortNames.getD s ""
       !(kore.sortDecls.any fun sd => sd.name == n && sd.params.isEmpty) &&
         it.pat == (KoreAML.sortConstantItem ⟨n, [], false⟩).pat)
  | .hook j => (hookSigs[j]?).any fun h =>
      let n := regSymNames.getD h.name ""
      !(kore.symbolDecls.any fun sd => sd.name == n && sd.params.isEmpty) &&
        it.pat == (KoreAML.arityItem ⟨n, [], h.args.map regSrtK, regSrtK h.result, false, []⟩).pat
  | .next => it.pat == nextItem.pat

/-- An item with its origin. -/
noncomputable def sigFromAtP (x : Item × TieSigAt) : Bool := sigFromAt x.1 x.2

theorem sigFromAt_sound {it : Item} {p : TieSigAt} (h : sigFromAt it p = true) : sigFromN it = true := by
  have hs : ∀ {it : Item}, surplusItem kore it = true → sigFromN it = true := fun h => by
    simp only [sigFromN, sigFrom, h, Bool.or_true, Bool.true_or]
  cases p with
  | text j =>
    obtain ⟨x, hx, he⟩ := (Option.any_eq_true _ _).mp h
    simp only [sigFromN, sigFrom, Bool.or_eq_true, List.any_eq_true]
    exact Or.inl (Or.inl ⟨x, List.mem_of_getElem? hx, he⟩)
  | regSort s =>
    obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp h
    refine hs ?_
    unfold surplusItem
    exact Bool.or_eq_true_iff.mpr (Or.inl (List.any_eq_true.mpr ⟨s, List.mem_range.mpr (of_decide_eq_true h1), h2⟩))
  | hook j =>
    obtain ⟨x, hx, he⟩ := (Option.any_eq_true _ _).mp h
    refine hs ?_
    unfold surplusItem
    exact Bool.or_eq_true_iff.mpr (Or.inr (List.any_eq_true.mpr ⟨x, List.mem_of_getElem? hx, he⟩))
  | next =>
    simp only [sigFromN, Bool.or_eq_true]
    exact Or.inr h

/-- `sigFromN` holds of each item where `sigFromAtP` holds of each item with its origin. -/
theorem tieSigPos_all {l : List Item} {ps : List TieSigAt} (hl : l.length ≤ ps.length)
    (h : (l.zip ps).all sigFromAtP = true) : l.all sigFromN = true := by
  induction l generalizing ps with
  | nil => rfl
  | cons it l ih =>
    cases ps with
    | nil => exact absurd hl (by simp)
    | cons p ps =>
      simp only [List.zip_cons_cons, List.all_cons, Bool.and_eq_true] at h ⊢
      exact ⟨sigFromAt_sound h.1, ih (by simpa using hl) h.2⟩

theorem sigE_0 : ((((sigItems c).zip sigPos).drop 0).take 13).all sigFromAtP = true := by decide +kernel
theorem sigE_13 : ((((sigItems c).zip sigPos).drop 13).take 13).all sigFromAtP = true := by decide +kernel
theorem sigE_26 : ((((sigItems c).zip sigPos).drop 26).take 13).all sigFromAtP = true := by decide +kernel
theorem sigE_39 : ((((sigItems c).zip sigPos).drop 39).take 13).all sigFromAtP = true := by decide +kernel
theorem sigE_52 : ((((sigItems c).zip sigPos).drop 52).take 13).all sigFromAtP = true := by decide +kernel
theorem sigE_65 : ((((sigItems c).zip sigPos).drop 65).take 13).all sigFromAtP = true := by decide +kernel
theorem sigE_78 : ((((sigItems c).zip sigPos).drop 78).take 13).all sigFromAtP = true := by decide +kernel
theorem sigE_91 : ((((sigItems c).zip sigPos).drop 91).take 13).all sigFromAtP = true := by decide +kernel
theorem sigE_104 : ((((sigItems c).zip sigPos).drop 104).take 13).all sigFromAtP = true := by decide +kernel
theorem sigE_117 : ((((sigItems c).zip sigPos).drop 117).take 13).all sigFromAtP = true := by decide +kernel
theorem sigE_130 : ((((sigItems c).zip sigPos).drop 130).take 13).all sigFromAtP = true := by decide +kernel
theorem sigE_143 : ((((sigItems c).zip sigPos).drop 143).take 13).all sigFromAtP = true := by decide +kernel
theorem sigE_156 : ((((sigItems c).zip sigPos).drop 156).take 13).all sigFromAtP = true := by decide +kernel
theorem sigE_169 : ((((sigItems c).zip sigPos).drop 169).take 13).all sigFromAtP = true := by decide +kernel
theorem sigE_182 : ((((sigItems c).zip sigPos).drop 182).take 13).all sigFromAtP = true := by decide +kernel
theorem sigE_195 : ((((sigItems c).zip sigPos).drop 195).take 13).all sigFromAtP = true := by decide +kernel
theorem sigE_208 : ((((sigItems c).zip sigPos).drop 208).take 13).all sigFromAtP = true := by decide +kernel
theorem sigE_221 : ((((sigItems c).zip sigPos).drop 221).take 13).all sigFromAtP = true := by decide +kernel
theorem sigE_234 : ((((sigItems c).zip sigPos).drop 234).take 13).all sigFromAtP = true := by decide +kernel
theorem sigE_247 : ((((sigItems c).zip sigPos).drop 247).take 13).all sigFromAtP = true := by decide +kernel
theorem sigE_260 : ((((sigItems c).zip sigPos).drop 260).take 13).all sigFromAtP = true := by decide +kernel
theorem sigE_273 : ((((sigItems c).zip sigPos).drop 273).take 13).all sigFromAtP = true := by decide +kernel
theorem sigE_286 : ((((sigItems c).zip sigPos).drop 286).take 13).all sigFromAtP = true := by decide +kernel
theorem sigE_299 : ((((sigItems c).zip sigPos).drop 299).take 13).all sigFromAtP = true := by decide +kernel
theorem sigE_312 : ((((sigItems c).zip sigPos).drop 312).take 13).all sigFromAtP = true := by decide +kernel
theorem sigE_325 : ((((sigItems c).zip sigPos).drop 325).take 13).all sigFromAtP = true := by decide +kernel
theorem sigE_338 : ((((sigItems c).zip sigPos).drop 338).take 13).all sigFromAtP = true := by decide +kernel
theorem sigE_351 : ((((sigItems c).zip sigPos).drop 351).take 13).all sigFromAtP = true := by decide +kernel
theorem sigE_364 : ((((sigItems c).zip sigPos).drop 364).take 13).all sigFromAtP = true := by decide +kernel
theorem sigE_377 : ((((sigItems c).zip sigPos).drop 377).take 13).all sigFromAtP = true := by decide +kernel
theorem sigE_390 : ((((sigItems c).zip sigPos).drop 390).take 13).all sigFromAtP = true := by decide +kernel
theorem sigE_403 : ((((sigItems c).zip sigPos).drop 403).take 13).all sigFromAtP = true := by decide +kernel
theorem sigE_416 : ((((sigItems c).zip sigPos).drop 416).take 13).all sigFromAtP = true := by decide +kernel
theorem sigE_429 : ((((sigItems c).zip sigPos).drop 429).take 13).all sigFromAtP = true := by decide +kernel
theorem sigE_442 : ((((sigItems c).zip sigPos).drop 442).take 13).all sigFromAtP = true := by decide +kernel
theorem sigE_455 : ((((sigItems c).zip sigPos).drop 455).take 13).all sigFromAtP = true := by decide +kernel
theorem sigE_468 : ((((sigItems c).zip sigPos).drop 468).take 13).all sigFromAtP = true := by decide +kernel
theorem sigE_481 : ((((sigItems c).zip sigPos).drop 481).take 13).all sigFromAtP = true := by decide +kernel
theorem sigE_494 : ((((sigItems c).zip sigPos).drop 494).take 13).all sigFromAtP = true := by decide +kernel
theorem sigE_507 : ((((sigItems c).zip sigPos).drop 507).take 13).all sigFromAtP = true := by decide +kernel
theorem sigE_520 : ((((sigItems c).zip sigPos).drop 520).take 13).all sigFromAtP = true := by decide +kernel
theorem sigE_533 : ((((sigItems c).zip sigPos).drop 533).take 13).all sigFromAtP = true := by decide +kernel
theorem sigE_546 : ((((sigItems c).zip sigPos).drop 546).take 13).all sigFromAtP = true := by decide +kernel
theorem sigE_559 : ((((sigItems c).zip sigPos).drop 559).take 13).all sigFromAtP = true := by decide +kernel
theorem sigE_572 : ((((sigItems c).zip sigPos).drop 572).take 13).all sigFromAtP = true := by decide +kernel
theorem sigE_585 : ((((sigItems c).zip sigPos).drop 585).take 13).all sigFromAtP = true := by decide +kernel
theorem sigE_598 : ((((sigItems c).zip sigPos).drop 598).take 13).all sigFromAtP = true := by decide +kernel
theorem sigE_611 : ((((sigItems c).zip sigPos).drop 611).take 13).all sigFromAtP = true := by decide +kernel
theorem sigE_624 : ((((sigItems c).zip sigPos).drop 624).take 13).all sigFromAtP = true := by decide +kernel
theorem sigE_637 : ((((sigItems c).zip sigPos).drop 637).take 13).all sigFromAtP = true := by decide +kernel
theorem sigE_650 : ((((sigItems c).zip sigPos).drop 650).take 13).all sigFromAtP = true := by decide +kernel
theorem sigE_663 : ((((sigItems c).zip sigPos).drop 663).take 13).all sigFromAtP = true := by decide +kernel
theorem sigE_676 : ((((sigItems c).zip sigPos).drop 676).take 13).all sigFromAtP = true := by decide +kernel
theorem sigE_689 : ((((sigItems c).zip sigPos).drop 689).take 13).all sigFromAtP = true := by decide +kernel
theorem sigE_702 : ((((sigItems c).zip sigPos).drop 702).take 13).all sigFromAtP = true := by decide +kernel
theorem sigE_715 : ((((sigItems c).zip sigPos).drop 715).take 13).all sigFromAtP = true := by decide +kernel
theorem sigE_728 : ((((sigItems c).zip sigPos).drop 728).take 13).all sigFromAtP = true := by decide +kernel
theorem sigE_741 : ((((sigItems c).zip sigPos).drop 741).take 13).all sigFromAtP = true := by decide +kernel
theorem sigE_754 : ((((sigItems c).zip sigPos).drop 754).take 13).all sigFromAtP = true := by decide +kernel
theorem sigE_767 : (((sigItems c).zip sigPos).drop 767).all sigFromAtP = true := by decide +kernel

theorem sig_sizes : (sigItems c).length = 770 := by decide +kernel

/-- **Every item of Γ's signature but next's arity has its origin**: the item of a declaration of
the text, or the sort constant of a registry sort or the arity of an interpreted hooked symbol that
the text does not declare at that shape. Next's arity at the configuration sort has none: the
text has no rule (`text_nextless`). -/
theorem sig_origin_but_next : (sigItems c).all (fun it =>
    (Theory.ofDefinition kore).signature.any (·.pat == it.pat) || surplusItem kore it ||
      it.pat == nextItem.pat) = true :=
  tieSigPos_all (Nat.le_of_eq (sig_sizes.trans sigPos_length.symm)) <|
    tieAllE_whole (p := sigFromAtP) <|
    tieAllE_range (a := 0) (n := 13) sigE_0 <|
    tieAllE_range (a := 13) (n := 13) sigE_13 <|
    tieAllE_range (a := 26) (n := 13) sigE_26 <|
    tieAllE_range (a := 39) (n := 13) sigE_39 <|
    tieAllE_range (a := 52) (n := 13) sigE_52 <|
    tieAllE_range (a := 65) (n := 13) sigE_65 <|
    tieAllE_range (a := 78) (n := 13) sigE_78 <|
    tieAllE_range (a := 91) (n := 13) sigE_91 <|
    tieAllE_range (a := 104) (n := 13) sigE_104 <|
    tieAllE_range (a := 117) (n := 13) sigE_117 <|
    tieAllE_range (a := 130) (n := 13) sigE_130 <|
    tieAllE_range (a := 143) (n := 13) sigE_143 <|
    tieAllE_range (a := 156) (n := 13) sigE_156 <|
    tieAllE_range (a := 169) (n := 13) sigE_169 <|
    tieAllE_range (a := 182) (n := 13) sigE_182 <|
    tieAllE_range (a := 195) (n := 13) sigE_195 <|
    tieAllE_range (a := 208) (n := 13) sigE_208 <|
    tieAllE_range (a := 221) (n := 13) sigE_221 <|
    tieAllE_range (a := 234) (n := 13) sigE_234 <|
    tieAllE_range (a := 247) (n := 13) sigE_247 <|
    tieAllE_range (a := 260) (n := 13) sigE_260 <|
    tieAllE_range (a := 273) (n := 13) sigE_273 <|
    tieAllE_range (a := 286) (n := 13) sigE_286 <|
    tieAllE_range (a := 299) (n := 13) sigE_299 <|
    tieAllE_range (a := 312) (n := 13) sigE_312 <|
    tieAllE_range (a := 325) (n := 13) sigE_325 <|
    tieAllE_range (a := 338) (n := 13) sigE_338 <|
    tieAllE_range (a := 351) (n := 13) sigE_351 <|
    tieAllE_range (a := 364) (n := 13) sigE_364 <|
    tieAllE_range (a := 377) (n := 13) sigE_377 <|
    tieAllE_range (a := 390) (n := 13) sigE_390 <|
    tieAllE_range (a := 403) (n := 13) sigE_403 <|
    tieAllE_range (a := 416) (n := 13) sigE_416 <|
    tieAllE_range (a := 429) (n := 13) sigE_429 <|
    tieAllE_range (a := 442) (n := 13) sigE_442 <|
    tieAllE_range (a := 455) (n := 13) sigE_455 <|
    tieAllE_range (a := 468) (n := 13) sigE_468 <|
    tieAllE_range (a := 481) (n := 13) sigE_481 <|
    tieAllE_range (a := 494) (n := 13) sigE_494 <|
    tieAllE_range (a := 507) (n := 13) sigE_507 <|
    tieAllE_range (a := 520) (n := 13) sigE_520 <|
    tieAllE_range (a := 533) (n := 13) sigE_533 <|
    tieAllE_range (a := 546) (n := 13) sigE_546 <|
    tieAllE_range (a := 559) (n := 13) sigE_559 <|
    tieAllE_range (a := 572) (n := 13) sigE_572 <|
    tieAllE_range (a := 585) (n := 13) sigE_585 <|
    tieAllE_range (a := 598) (n := 13) sigE_598 <|
    tieAllE_range (a := 611) (n := 13) sigE_611 <|
    tieAllE_range (a := 624) (n := 13) sigE_624 <|
    tieAllE_range (a := 637) (n := 13) sigE_637 <|
    tieAllE_range (a := 650) (n := 13) sigE_650 <|
    tieAllE_range (a := 663) (n := 13) sigE_663 <|
    tieAllE_range (a := 676) (n := 13) sigE_676 <|
    tieAllE_range (a := 689) (n := 13) sigE_689 <|
    tieAllE_range (a := 702) (n := 13) sigE_702 <|
    tieAllE_range (a := 715) (n := 13) sigE_715 <|
    tieAllE_range (a := 728) (n := 13) sigE_728 <|
    tieAllE_range (a := 741) (n := 13) sigE_741 <|
    tieAllE_range (a := 754) (n := 13) sigE_754 <|
    sigE_767

kernel_rfl sigItems_withHooks : ∀ (c : Semantics) (H : HookParams), sigItems (c.withHooks H) = sigItems c

end KCore.TieRdrConfigDeep

#check @KCore.TieRdrConfigDeep.sig_origin_but_next
#check @KCore.TieRdrConfigDeep.text_nextless
#print axioms KCore.TieRdrConfigDeep.sig_origin_but_next
#print axioms KCore.TieRdrConfigDeep.text_nextless
