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

  Not here, because one kernel decision of each exceeds 12 GiB on this text: `wf defn = true`
  (the generated package checks it by parts, `RefKimp.Wf`) and `sig_origin` (each item of Γ's
  signature is a declaration's item or a `surplusItem`), which holds by native evaluation only.

  The class theorems of layer 2 (what holds of each class's sentences) are not stated here.
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

/-- The axioms of the user module, in text order. -/
noncomputable def userAxioms : List AxiomDecl := kore.axiomDecls.filter (·.module == "IMP")

theorem userAxioms_eq : userAxioms = U.all := by kernel_rfl
theorem userAxioms_length : U.all.length = 901 := by decide +kernel

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
- no direction: a sentence that applies a symbol Γ does not have. -/
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
   ("hooked functional", [433, 434, 435, 446, 447, 448, 449, 450, 451, 478, 490, 501, 520, 522, 530, 537, 538, 539, 540, 541, 542,
      556, 561, 568, 576, 584, 585, 586, 587, 588, 589, 590, 591, 593, 595, 598, 599, 612, 633, 634, 635, 636,
      639, 640, 641, 642, 643, 644]),
   ("collection law", [565, 566, 567, 569, 570, 571, 572, 574, 575]),
   ("library", [671, 672, 675, 676, 677, 678, 679, 680, 681, 682, 683, 684, 685, 686, 687, 688, 689, 690, 691, 692, 693,
      694, 695, 696, 697, 698, 699, 779, 781, 782, 783, 784, 785, 786, 787, 788, 789, 790, 791, 792, 793, 796,
      797, 798, 799, 800, 803, 804, 805, 806, 807, 808, 809, 810, 811, 813, 814, 815, 816, 817, 818, 819, 820,
      821, 822, 823, 824, 825, 826, 827, 828, 829, 830, 832, 877, 878, 879, 880, 881, 882, 902, 904]),
   ("set idempotence", [573]),
   ("no direction", [477, 502, 521, 592, 594, 611, 645, 654, 673, 674, 780, 794, 795, 801, 802, 812, 831, 833, 834, 835, 836,
      837, 883, 884, 885, 886, 887, 888, 889, 890, 891, 892, 893, 894, 895, 896, 897, 898, 899, 900, 901, 903])]

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
     54), ("subsort", 25), ("injectivity", 49), ("distinctness", 437), ("no junk", 16), ("function functional", 20), ("hooked functional", 48), ("collection law", 9), ("library", 82), ("set idempotence",
     1), ("no direction", 42)] := by
  decide +kernel

/-- The classes are the tie's (`tieClasses`, which gives each its direction), in its order. -/
theorem account_classes : classes.map (·.1) = tieClasses.map (·.1) := by decide +kernel

/-- **A sentence outside the no-direction class applies only symbols Γ has** (the injection `inj`
aside, which Γ's constructor items apply), and each sentence of that class applies one Γ lacks. -/
theorem account_absent : userAxioms.all (fun ad =>
    (classOf "no direction").contains ad.index !=
      (symbolsOf ad.ax.pattern).all (fun n => n == "inj" || (kernelSyms c).any (fun k => c.symName k.name == n))) = true := by
  rw [userAxioms_eq]; decide +kernel

/-- **The no-direction class is closed**: every sentence outside it applies only symbols Γ has,
so no sentence with a direction applies a symbol Γ lacks. The injection `inj` is no member of
`kernelSyms` (`coreOK` keeps the name from them) and is Γ's all the same: the constructor items
state it for each subsort pair. -/
theorem absent_closed :
    (userAxioms.filter (fun ad => !(classOf "no direction").contains ad.index)).all
      (fun ad => (symbolsOf ad.ax.pattern).all
        (fun n => n == "inj" || (kernelSyms c).any (fun k => c.symName k.name == n))) = true :=
  tieAbsent_of_account userAxioms _ _ account_absent

/-! ## The attributes -/

/-- **The attributes of the text agree with `defn`** (`attrsAgree`): constructors, functions,
hooks, collection symbols, priorities. -/
theorem attrs_agree : attrsAgree kore defn = true := by decide +kernel

end KCore.TieKimp

#print axioms KCore.TieKimp.userAxioms_eq
#print axioms KCore.TieKimp.account
#print axioms KCore.TieKimp.account_classes
#print axioms KCore.TieKimp.account_absent
#print axioms KCore.TieKimp.absent_closed
#print axioms KCore.TieKimp.attrs_agree
