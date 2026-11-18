/-
  Layer 1 of the tie (C14) on kore.k's text as kompile wrote it
  (`examples/ref-kk/RefKk/definition.kore`, user module `KORE`, 834 sentences), on the literals
  `kore` and `defn`. Nothing here reads `Parse.parse` or `emit`. Run from the package root: `lake env lean test/TieKk.lean`.

  - `userAxioms_eq`: the constants `U.axN` are the user module's 834 axioms, in text order.
  - `account`: the class lists partition the 834 sentences; `account_sizes` their counts;
    `account_classes`: the classes are the tie's (`tieClasses`, each with its direction).
  - `account_absent`, `absent_closed`: the no-direction class holds exactly the sentences that
    apply a symbol Γ lacks, so every sentence outside it applies Γ's symbols only.

  In files of their own, on the same literals: `attrs_agree` (test/TieKkAttrs.lean, by its
  conjuncts), `sig_origin` (test/TieKkSig.lean, by ranges of the signature's items), and the
  classes of layer 2: the function equations (test/TieKkFns.lean), the rules
  (test/TieKkRules.lean), the constructor sentences (test/TieKkCons.lean) and no junk
  (test/TieKkNoJunk.lean).
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

/-- The axioms of the user module, in text order. -/
noncomputable def userAxioms : List AxiomDecl := kore.axiomDecls.filter (·.module == "KORE")

theorem userAxioms_eq : userAxioms = U.all := by kernel_rfl
theorem userAxioms_length : U.all.length = 834 := by decide +kernel

/-- `tr s`: the item `Theory.ofDefinition kore` holds for the sentence. -/
noncomputable def trS (ad : AxiomDecl) : Item := trAxiom kore.symbolDecls kore.aliasNames ad

/-! ## The account -/

/-- Per class of the tie (`tieClasses`), the indices (`AxiomDecl.index`) of its sentences:
- function equation: the equations of the definition's functions and of the sort predicates;
- rewrite rule: the 10 rules;
- constructor functional, subsort, injectivity, distinctness, no junk: the constructor sentences;
- function functional: the `functional` sentence of a function of the definition;
- hooked functional: the `functional` sentence of a symbol Γ states by its graph;
- collection law: associativity and the two units of `_List_`, `_Map_`, `_Set_`;
- library: an equation or a lemma of the builtin library over symbols Γ has;
- set idempotence: the `idem` sentence of `_Set_`;
- set-variable lemma: the definedness lemmas of `%Int`, `/Int`, `>>Int`, `<<Int`, `modInt`
  (domains.md 1392 to 1396) and kompile's `#Ceil(@K0 |-> @K1 @Rest)`, over set variables;
- no direction: a sentence that applies a symbol Γ does not have. -/
def classes : List (String × List Nat) :=
  [("function equation", [479, 480, 481, 482, 483, 484, 485, 486, 487, 488, 489, 490, 491, 492, 493, 494, 495, 497, 498, 499, 500,
      501, 502, 503, 504, 505, 506, 507, 508, 509, 510, 511, 512, 513, 514, 515, 516, 517, 518, 519, 520,
      523, 524, 525, 526, 527, 528, 529, 530, 531, 532, 533, 534, 535, 536, 537, 538, 539, 540, 541, 542,
      543, 544, 545, 546, 547, 548, 551, 552, 553, 554, 555, 556, 557, 560, 561, 562, 563, 564, 565, 566,
      567, 568, 569, 570, 571, 572, 573, 574, 575, 576, 577, 578, 579, 580, 581, 582, 583, 584, 585, 586,
      587, 588, 589, 590, 591, 592, 593, 594, 595, 599, 600, 601, 602, 603, 604, 605, 606, 607, 608, 609,
      610, 611, 612, 613, 614, 615, 616, 617, 618, 619, 620, 621, 622, 623, 624, 625, 626, 627, 628, 629,
      630, 631, 632, 633, 634, 635, 636, 637, 638, 639, 640, 641, 642, 643, 644, 645, 646, 647, 648, 649,
      650, 651, 652, 653, 654, 655, 656, 657, 658, 659, 660, 661, 662, 663, 664, 665, 666, 667, 668, 669,
      670, 671, 672, 673, 674, 675, 676, 677, 678, 679, 680, 681, 682, 683, 684, 685, 688, 689, 690, 691,
      692, 693, 694, 695, 696, 697, 698, 699, 700, 701, 702, 703, 704, 705, 706, 707, 708, 709, 710, 711,
      712, 713, 714, 715, 716, 717, 718, 719, 720, 721, 722, 723, 724, 725, 726, 727, 728, 729, 730, 731,
      732, 735, 736, 737, 738, 739, 740, 741, 742, 743, 744, 745, 746, 747, 750, 751, 752, 753, 754, 755,
      756, 789, 790, 791, 792, 798, 799, 800, 801, 804, 806, 807, 808, 809, 810, 811, 812, 813, 814, 815,
      816, 817, 818, 819, 820, 821, 822, 823, 824, 825, 826, 827, 828, 829, 830, 831, 832, 833, 834, 835,
      836]),
   ("rewrite rule", [408, 409, 410, 411, 412, 413, 414, 415, 416, 417]),
   ("priority equation", []),
   ("constructor functional", [36, 38, 40, 44, 46, 49, 51, 53, 55, 57, 59, 76, 121, 136, 150, 153, 155, 167, 179, 190, 192, 203,
      205, 211, 220, 228, 230, 234, 241, 282, 288, 293, 296, 298, 302, 305, 306, 307, 308, 309, 312, 314,
      323, 325, 329, 333, 335, 338, 339, 342, 346, 348]),
   ("subsort", [4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29,
      30, 31, 32, 33, 34, 35]),
   ("injectivity", [54, 56, 58, 60, 77, 122, 137, 151, 154, 168, 180, 191, 193, 204, 206, 212, 221, 229, 231, 235, 242,
      283, 289, 297, 303, 313, 315, 324, 326, 334, 336, 340, 343, 347, 349]),
   ("distinctness", [37, 39, 41, 45, 47, 50, 52, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 138,
      139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 152, 156, 157, 158, 159, 160, 161, 162, 163,
      164, 165, 166, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 181, 182, 183, 184, 185, 186, 187,
      188, 189, 194, 195, 196, 197, 198, 199, 200, 201, 207, 208, 209, 210, 213, 214, 215, 216, 217, 218,
      219, 222, 223, 224, 225, 226, 227, 232, 236, 237, 238, 239, 240, 243, 244, 245, 246, 284, 285, 286,
      290, 291, 294, 295, 299, 304, 310, 316, 317, 318, 327, 328, 337, 344]),
   ("no junk", [351, 352, 353, 354, 355, 356, 357, 358, 359, 360, 361, 362, 363, 364, 365, 366, 367, 368, 369, 370,
      371, 372, 373, 374, 375, 376, 377, 378]),
   ("function functional", [249, 250, 251, 252, 253, 254, 255, 256, 257, 258, 259, 260, 261, 262, 263, 264, 265, 266, 267, 268,
      269, 270, 271, 272, 273, 274, 275, 276, 277, 278, 279, 280]),
   ("hooked functional", [42, 43, 48, 61, 63, 64, 65, 66, 67, 68, 69, 71, 72, 73, 74, 78, 80, 81, 82, 83, 84, 85, 86, 87, 88,
      89, 90, 91, 92, 93, 94, 95, 99, 107, 108, 109, 110, 111, 112, 113, 114, 115, 117, 119, 120, 202,
      233, 248, 281, 287, 292, 300, 301, 311, 319, 320, 321, 322, 330, 331, 332, 341]),
   ("collection law", [96, 97, 98, 100, 101, 102, 103, 105, 106]),
   ("library", [384, 385, 386, 387, 388, 389, 390, 391, 392, 393, 394, 395, 396, 397, 398,
      399, 400, 401, 402, 403, 404, 405, 406, 407, 418, 419, 420, 421, 422, 424, 425, 426, 427, 428, 429,
      430, 431, 432, 433, 434, 435, 436, 437, 438, 439, 440, 441, 442, 443, 444, 445, 446, 447, 448, 449,
      450, 451, 452, 453, 454, 455, 456, 457, 458, 459, 461, 462, 463, 464, 465, 466, 467, 468, 469, 470,
      471, 472, 473, 474, 475, 476, 477, 478, 521, 522, 549, 550, 558, 686, 687, 733, 734, 748, 749, 788,
      793, 794, 795, 796, 797, 802, 803]),
   ("set idempotence", [104]),
   ("set-variable lemma", [379, 380, 381, 382, 383, 837]),
   ("no direction", [62, 70, 75, 79, 116, 118, 247, 345, 350, 423, 460, 496, 559, 596, 597, 598, 757, 758, 759, 760, 761,
      762, 763, 764, 765, 766, 767, 768, 769, 770, 771, 772, 773, 774, 775, 776, 777, 778, 779, 780, 781,
      782, 783, 784, 785, 786, 787, 805])]

/-- The indices of a class. -/
def classOf (n : String) : List Nat := (classes.filter (·.1 == n)).flatMap (·.2)

/-- The sentences' indices are 4 to 837. -/
theorem indices_eq : U.all.map (·.index) = List.range' 4 834 := by decide +kernel

/-- **The account**: the class lists partition the user module's sentences. Their concatenation is
a permutation of the sentences' indices, which are distinct, so each sentence is in one class and
in it once. -/
theorem account : (classes.flatMap (·.2)).isPerm (userAxioms.map (·.index)) = true ∧
    (userAxioms.map (·.index)).Nodup := by
  rw [userAxioms_eq]
  exact ⟨by rw [indices_eq]; decide +kernel, by rw [indices_eq]; exact List.nodup_range'⟩

/-- The class sizes. -/
theorem account_sizes : classes.map (fun cl => (cl.1, cl.2.length)) =
    [("function equation", 302), ("rewrite rule", 10), ("priority equation", 0), ("constructor functional", 52), ("subsort", 32), ("injectivity", 35), ("distinctness", 115), ("no junk", 28), ("function functional", 32), ("hooked functional", 62), ("collection law", 9), ("library", 102), ("set idempotence", 1), ("set-variable lemma", 6), ("no direction", 48)] := by
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
so no sentence with a direction applies a symbol Γ lacks. -/
theorem absent_closed :
    (userAxioms.filter (fun ad => !(classOf "no direction").contains ad.index)).all
      (fun ad => (symbolsOf ad.ax.pattern).all
        (fun n => n == "inj" || (kernelSyms c).any (fun k => c.symName k.name == n))) = true :=
  tieAbsent_of_account userAxioms _ _ account_absent

end KCore.TieKk

#print axioms KCore.TieKk.userAxioms_eq
#print axioms KCore.TieKk.account
#print axioms KCore.TieKk.account_sizes
#print axioms KCore.TieKk.account_classes
#print axioms KCore.TieKk.absent_closed
