/-
  The tie (C14) on `f2-examples/c3-cells-star.kompile.kore`, the kompiled text of construct fixture c3-cells-star
  (`test/constructs/fixtures/c3-cells-star`), sentence by sentence, against the translation of the text as
  written (`trS ad := trAxiom k.symbolDecls k.aliasNames ad`), on the literals `kore` and `defn`, for
  every interpretation H. Nothing here reads `Parse.parse` or `emit`. Written by
  `test/constructs/tiegen.py c3-cells-star`; run from the package root: `lake env lean -j1 test/TieC3CellsStar.lean`.

  Layer 1.
  - `wf_defn`: `wf defn = true`.
  - The account: the class lists partition the 495 sentences of the user module C, in
    `tieClasses`' order (`account`, `account_sizes`, `account_classes`); the no-direction class holds
    exactly the sentences that apply a symbol Γ lacks (`account_absent`, `absent_closed`).
  - `attrs_agree`: the attributes the translation does not read agree with `defn`.
  - `sig_origin_but_next`: each of the 298 items of `sigItems c` but one is a declaration's item
    of the text or a surplus one; the one is next's arity at the configuration sort, which Γ states
    and the text, having no `\rewrites` (`text_nextless`), does not. `decls_entailed`: Γ entails
    the item of each declaration without sort parameters of a symbol Γ has (by ranges of the lists).
  - The definition reads no confined sort (`readsConfined_c`), has no open generator (`noRaw`) and
    owes no fact (`term_named`, `total_named`, `agree_named`, `match_named`), so Γ with the step's
    closure has a model for every H (`consistent`).

  Layer 2, by class (indices are the text's axiom numbers, `AxiomDecl.index`).
  - Function equations (88): each of Γ's items is the translation of one sentence, in the
    order `fnText` lists them (`fn_shape`); `fns_entailed` (E), `fns_from_text` (the converse),
    `fn_prios` (the priorities the sentences state are the clauses').
  - Constructor sentences (98): entailed by Γ (`cons_entailed`).
  - No junk (3 of a sort without generators, `nojunk_trivial_entailed`; 30 equal to
    one of Γ's constructor items, `nojunk_items`; 1 KItem's with its disjuncts in the text's
    order, `nojunk_kitem_entailed`).
  - Set idempotence (137): Γ with it has no model (`idem_refuted`).
  - Set idempotence of the set collection of `Lbl'Unds'ThCellSet'Unds'` (141): Γ with it has no model
    (`own_idem_refuted_141`, from `setColl_idem_refuted_text`).
  - Library sample, 310 (`I -Int 0 = I`): holds at values (`lib166`, `lib166_at_values`).
  - The converse over Γ's content: each premise is a function sentence's translation, one of the
    five parts Γ defines by predicates, or definedness (`gamma_origin`, `gamma_from`).
  - Hooked functional, collection law, library: at values (no theorem here); function functional:
    owed as `FnHyp` (no theorem); no direction: `absent_closed`.

  The sentences with no counterpart in f2-examples/ens.kompile.kore are `unmapped` (255);
  the sentences of a class with a theorem that no theorem here holds of are `uncovered` (0).
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.TieC3CellsStar

open KCore ML Faithful KoreAML

kore_term kore from "f2-examples/c3-cells-star.kompile.kore"
definition_of defn from "f2-examples/c3-cells-star.kompile.kore"
user_axioms U from "f2-examples/c3-cells-star.kompile.kore" module "C"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

/-- No parameter of the definition is an open generator. -/
theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel

/-- The definition reads no confined sort: its theory is Γ. -/
theorem readsConfined_c : c.readsConfined = false := by decide +kernel

/-- The axioms of the user module, in text order. -/
noncomputable def userAxioms : List AxiomDecl := kore.axiomDecls.filter (·.module == "C")

theorem userAxioms_eq : userAxioms = U.all := by kernel_rfl
theorem userAxioms_length : U.all.length = 495 := by decide +kernel

/-- `tr s`: the item `Theory.ofDefinition kore` holds for the sentence. -/
noncomputable def trS (ad : AxiomDecl) : Item := trAxiom kore.symbolDecls kore.aliasNames ad

theorem trS_is_text : (Theory.ofDefinition kore).axioms = kore.axiomDecls.map trS := rfl

/-! ## Layer 1 -/

set_option maxHeartbeats 1000000 in
theorem coreOK : c.coreOK = true := by decide_cheap
theorem coreOKH (H : HookParams) : (cH H).coreOK = true := (Semantics.coreOK_withHooks c H).trans coreOK

set_option maxHeartbeats 1000000 in
theorem wf_defn : wf defn = true := by decide_cheap

/-! ## The account: every sentence of the user module is in exactly one class -/

/-- Per class of the tie (`tieClasses`), the indices (`AxiomDecl.index`) of its sentences. -/
def classes : List (String × List Nat) :=
  [("function equation", [299, 357, 359, 361, 363, 365, 367, 368, 369, 370, 371, 372, 373, 374, 375, 376, 377, 378,
      379, 380, 381, 382, 383, 384, 385, 386, 387, 388, 389, 390, 391, 392, 393, 394, 395, 396,
      397, 398, 399, 400, 401, 402, 403, 404, 405, 406, 407, 408, 409, 410, 411, 412, 413, 414,
      415, 416, 417, 418, 419, 420, 421, 422, 423, 424, 425, 426, 427, 428, 429, 430, 431, 432,
      433, 434, 435, 436, 437, 438, 439, 440, 441, 442, 443, 444, 445, 446, 447, 448]),
   ("rewrite rule", []),
   ("priority equation", []),
   ("constructor functional", [58, 60, 62, 64, 66, 68, 70, 72, 74, 76, 78, 80, 82, 84, 86, 88, 90, 92, 94, 96, 157, 216,
      217, 218, 219, 220, 221, 222, 223, 224]),
   ("subsort", [4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 22, 23, 24, 25, 27, 28, 29, 30,
      31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 48, 49, 50, 51, 52, 53, 54]),
   ("injectivity", [59, 61, 63, 65, 67, 69, 71, 73, 75, 77, 79, 81, 83, 85, 87, 89, 91, 93, 95, 97]),
   ("distinctness", []),
   ("no junk", [233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250,
      251, 253, 254, 255, 256, 257, 259, 260, 261, 262, 263, 265, 266, 267, 268, 269]),
   ("function functional", [102, 161, 162, 164, 166, 167, 169, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181,
      182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199,
      200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211]),
   ("hooked functional", [55, 56, 57, 98, 99, 100, 101, 103, 104, 105, 107, 108, 109, 111, 113, 114, 115, 116, 117,
      118, 119, 120, 121, 122, 126, 144, 145, 146, 147, 148, 149, 150, 151, 152, 154, 156, 158,
      159, 170, 213, 214, 215, 225, 226, 227, 228, 229, 230]),
   ("collection law", [123, 124, 125, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 138, 139, 140, 142, 143]),
   ("library", [275, 276, 277, 278, 279, 280, 281, 282, 283, 284, 285, 286, 287, 288, 289, 290, 291, 292,
      293, 294, 295, 296, 297, 298, 300, 302, 303, 304, 305, 306, 307, 308, 309, 310, 311, 312,
      313, 314, 315, 316, 317, 318, 319, 320, 321, 322, 323, 324, 325, 326, 327, 328, 329, 330,
      331, 332, 334, 335, 336, 337, 338, 339, 340, 341, 342, 343, 344, 345, 346, 347, 348, 349,
      350, 351, 352, 353, 451, 452, 453, 454, 495, 496]),
   ("set idempotence", [137, 141]),
   ("set-variable lemma", [270, 271, 272, 273, 274, 497, 498]),
   ("function law", []),
   ("open generator law", []),
   ("open generator functional", []),
   ("parameter lemma", []),
   ("user lemma", []),
   ("user lemma at values", []),
   ("no direction", [21, 26, 47, 106, 110, 112, 153, 155, 160, 163, 165, 168, 212, 231, 232, 252, 258, 264, 301,
      333, 354, 355, 356, 358, 360, 362, 364, 366, 449, 450, 455, 456, 457, 458, 459, 460, 461,
      462, 463, 464, 465, 466, 467, 468, 469, 470, 471, 472, 473, 474, 475, 476, 477, 478, 479,
      480, 481, 482, 483, 484, 485, 486, 487, 488, 489, 490, 491, 492, 493, 494])]

/-- The indices of a class. -/
def classOf (n : String) : List Nat := (classes.filter (·.1 == n)).flatMap (·.2)

/-- **The account**: the class lists partition the user module's sentences. Their concatenation is
a permutation of the sentences' indices, which are distinct, so each sentence is in one class and
in it once. -/
theorem account : (classes.flatMap (·.2)).isPerm (userAxioms.map (·.index)) = true ∧
    (userAxioms.map (·.index)).Nodup := by
  rw [userAxioms_eq]; decide +kernel

/-- The class sizes. -/
theorem account_sizes : classes.map (fun cl => (cl.1, cl.2.length)) =
    [("function equation", 88), ("rewrite rule", 0), ("priority equation", 0), ("constructor functional", 30), ("subsort", 48), ("injectivity", 20), ("distinctness", 0), ("no junk", 34), ("function functional", 48), ("hooked functional", 48), ("collection law", 18), ("library", 82), ("set idempotence", 2), ("set-variable lemma", 7), ("function law", 0), ("open generator law", 0), ("open generator functional", 0), ("parameter lemma", 0), ("user lemma", 0), ("user lemma at values", 0), ("no direction", 70)] := by
  decide +kernel

/-- The classes are the tie's (`tieClasses`, which gives each its direction), in its order. -/
theorem account_classes : classes.map (·.1) = tieClasses.map (·.1) := by decide +kernel

/-- The sentence is in the no-direction class exactly where it applies a head Γ lacks. -/
noncomputable def absentP (ad : AxiomDecl) : Bool :=
  (classOf "no direction").contains ad.index != (appHeadsOf ad.ax.pattern).all (gammaHasHead c)

theorem absentE_0 : (((U.all).drop 0).take 40).all absentP = true := by decide +kernel
theorem absentE_40 : (((U.all).drop 40).take 40).all absentP = true := by decide +kernel
theorem absentE_80 : (((U.all).drop 80).take 40).all absentP = true := by decide +kernel
theorem absentE_120 : (((U.all).drop 120).take 40).all absentP = true := by decide +kernel
theorem absentE_160 : (((U.all).drop 160).take 40).all absentP = true := by decide +kernel
theorem absentE_200 : (((U.all).drop 200).take 40).all absentP = true := by decide +kernel
theorem absentE_240 : (((U.all).drop 240).take 40).all absentP = true := by decide +kernel
theorem absentE_280 : (((U.all).drop 280).take 40).all absentP = true := by decide +kernel
theorem absentE_320 : (((U.all).drop 320).take 40).all absentP = true := by decide +kernel
theorem absentE_360 : (((U.all).drop 360).take 40).all absentP = true := by decide +kernel
theorem absentE_400 : (((U.all).drop 400).take 40).all absentP = true := by decide +kernel
theorem absentE_440 : (((U.all).drop 440).take 40).all absentP = true := by decide +kernel
theorem absentE_480 : ((U.all).drop 480).all absentP = true := by decide +kernel

/-- **A sentence outside the no-direction class applies only symbols Γ has**, each a head with its
sort arguments (`appHeadsOf`) among Γ's (`gammaHeads`), and each sentence of that class applies one
Γ lacks. -/
theorem account_absent : userAxioms.all (fun ad =>
    (classOf "no direction").contains ad.index != (appHeadsOf ad.ax.pattern).all (gammaHasHead c)) = true := by
  rw [userAxioms_eq]; exact
    tieAll_whole (l := U.all) (p := absentP) <|
      tieAll_range (l := U.all) (p := absentP) (a := 0) (n := 40) absentE_0 <|
      tieAll_range (l := U.all) (p := absentP) (a := 40) (n := 40) absentE_40 <|
      tieAll_range (l := U.all) (p := absentP) (a := 80) (n := 40) absentE_80 <|
      tieAll_range (l := U.all) (p := absentP) (a := 120) (n := 40) absentE_120 <|
      tieAll_range (l := U.all) (p := absentP) (a := 160) (n := 40) absentE_160 <|
      tieAll_range (l := U.all) (p := absentP) (a := 200) (n := 40) absentE_200 <|
      tieAll_range (l := U.all) (p := absentP) (a := 240) (n := 40) absentE_240 <|
      tieAll_range (l := U.all) (p := absentP) (a := 280) (n := 40) absentE_280 <|
      tieAll_range (l := U.all) (p := absentP) (a := 320) (n := 40) absentE_320 <|
      tieAll_range (l := U.all) (p := absentP) (a := 360) (n := 40) absentE_360 <|
      tieAll_range (l := U.all) (p := absentP) (a := 400) (n := 40) absentE_400 <|
      tieAll_range (l := U.all) (p := absentP) (a := 440) (n := 40) absentE_440 <|
      absentE_480

/-- **The no-direction class is closed**: every sentence outside it applies only symbols Γ has,
so no sentence with a direction applies a symbol Γ lacks. The injection `inj` is no member of
`kernelSyms` and is Γ's all the same at each subsort pair, where the constructor items state it
(`gammaHeads`). -/
theorem absent_closed :
    (userAxioms.filter (fun ad => !(classOf "no direction").contains ad.index)).all
      (fun ad => (appHeadsOf ad.ax.pattern).all (gammaHasHead c)) = true :=
  tieAbsent_of_account userAxioms _ _ account_absent

/-- The sentences whose text is none of f2-examples/ens.kompile.kore's user module, with their class. -/
def unmapped : List (Nat × String) :=
  [(4, "subsort"), (5, "subsort"), (6, "subsort"), (7, "subsort"), (8, "subsort"), (9, "subsort"),
   (10, "subsort"), (13, "subsort"), (17, "subsort"), (18, "subsort"), (19, "subsort"),
   (20, "subsort"), (21, "no direction"), (26, "no direction"), (27, "subsort"), (28, "subsort"),
   (29, "subsort"), (30, "subsort"), (32, "subsort"), (33, "subsort"), (34, "subsort"),
   (35, "subsort"), (36, "subsort"), (37, "subsort"), (38, "subsort"), (39, "subsort"),
   (41, "subsort"), (42, "subsort"), (43, "subsort"), (45, "subsort"), (47, "no direction"),
   (48, "subsort"), (49, "subsort"), (50, "subsort"), (51, "subsort"), (52, "subsort"),
   (53, "subsort"), (60, "constructor functional"), (61, "injectivity"),
   (62, "constructor functional"), (63, "injectivity"), (64, "constructor functional"),
   (65, "injectivity"), (68, "constructor functional"), (69, "injectivity"),
   (70, "constructor functional"), (71, "injectivity"), (72, "constructor functional"),
   (73, "injectivity"), (74, "constructor functional"), (75, "injectivity"),
   (76, "constructor functional"), (77, "injectivity"), (78, "constructor functional"),
   (79, "injectivity"), (80, "constructor functional"), (81, "injectivity"),
   (82, "constructor functional"), (83, "injectivity"), (84, "constructor functional"),
   (85, "injectivity"), (86, "constructor functional"), (87, "injectivity"),
   (88, "constructor functional"), (89, "injectivity"), (90, "constructor functional"),
   (91, "injectivity"), (92, "constructor functional"), (93, "injectivity"),
   (94, "constructor functional"), (95, "injectivity"), (96, "constructor functional"),
   (97, "injectivity"), (101, "hooked functional"), (102, "function functional"),
   (127, "collection law"), (128, "collection law"), (129, "collection law"),
   (133, "collection law"), (134, "collection law"), (135, "collection law"),
   (140, "collection law"), (141, "set idempotence"), (142, "collection law"),
   (143, "collection law"), (157, "constructor functional"), (161, "function functional"),
   (162, "function functional"), (163, "no direction"), (164, "function functional"),
   (165, "no direction"), (166, "function functional"), (167, "function functional"),
   (168, "no direction"), (169, "function functional"), (172, "function functional"),
   (177, "function functional"), (178, "function functional"), (185, "function functional"),
   (186, "function functional"), (188, "function functional"), (189, "function functional"),
   (190, "function functional"), (191, "function functional"), (192, "function functional"),
   (194, "function functional"), (195, "function functional"), (196, "function functional"),
   (197, "function functional"), (198, "function functional"), (199, "function functional"),
   (201, "function functional"), (202, "function functional"), (203, "function functional"),
   (204, "function functional"), (205, "function functional"), (206, "function functional"),
   (207, "function functional"), (208, "function functional"), (209, "function functional"),
   (210, "function functional"), (211, "function functional"), (217, "constructor functional"),
   (219, "constructor functional"), (220, "constructor functional"),
   (221, "constructor functional"), (222, "constructor functional"),
   (223, "constructor functional"), (224, "constructor functional"), (234, "no junk"),
   (237, "no junk"), (238, "no junk"), (239, "no junk"), (240, "no junk"), (245, "no junk"),
   (246, "no junk"), (247, "no junk"), (248, "no junk"), (249, "no junk"), (250, "no junk"),
   (251, "no junk"), (252, "no direction"), (253, "no junk"), (254, "no junk"), (255, "no junk"),
   (256, "no junk"), (257, "no junk"), (258, "no direction"), (259, "no junk"), (260, "no junk"),
   (261, "no junk"), (262, "no junk"), (263, "no junk"), (264, "no direction"), (265, "no junk"),
   (266, "no junk"), (267, "no junk"), (268, "no junk"), (269, "no junk"),
   (299, "function equation"), (354, "no direction"), (356, "no direction"),
   (357, "function equation"), (358, "no direction"), (359, "function equation"),
   (360, "no direction"), (361, "function equation"), (362, "no direction"),
   (363, "function equation"), (364, "no direction"), (365, "function equation"),
   (366, "no direction"), (367, "function equation"), (370, "function equation"),
   (371, "function equation"), (380, "function equation"), (381, "function equation"),
   (382, "function equation"), (383, "function equation"), (395, "function equation"),
   (396, "function equation"), (397, "function equation"), (398, "function equation"),
   (401, "function equation"), (402, "function equation"), (403, "function equation"),
   (404, "function equation"), (405, "function equation"), (406, "function equation"),
   (407, "function equation"), (408, "function equation"), (409, "function equation"),
   (410, "function equation"), (413, "function equation"), (414, "function equation"),
   (415, "function equation"), (416, "function equation"), (417, "function equation"),
   (418, "function equation"), (419, "function equation"), (420, "function equation"),
   (421, "function equation"), (422, "function equation"), (423, "function equation"),
   (424, "function equation"), (427, "function equation"), (428, "function equation"),
   (429, "function equation"), (430, "function equation"), (431, "function equation"),
   (432, "function equation"), (433, "function equation"), (434, "function equation"),
   (435, "function equation"), (436, "function equation"), (437, "function equation"),
   (438, "function equation"), (439, "function equation"), (440, "function equation"),
   (441, "function equation"), (442, "function equation"), (443, "function equation"),
   (444, "function equation"), (445, "function equation"), (446, "function equation"),
   (447, "function equation"), (448, "function equation"), (456, "no direction"),
   (461, "no direction"), (462, "no direction"), (468, "no direction"), (469, "no direction"),
   (471, "no direction"), (472, "no direction"), (473, "no direction"), (474, "no direction"),
   (475, "no direction"), (477, "no direction"), (478, "no direction"), (479, "no direction"),
   (480, "no direction"), (481, "no direction"), (482, "no direction"), (484, "no direction"),
   (485, "no direction"), (486, "no direction"), (487, "no direction"), (488, "no direction"),
   (489, "no direction"), (490, "no direction"), (491, "no direction"), (492, "no direction"),
   (493, "no direction"), (494, "no direction"), (497, "set-variable lemma")]

/-- The sentences of a class with a theorem in the tie that no theorem of this file holds of: the
tie's remainder on this text. -/
def uncovered : List (Nat × String) :=
  []

/-- Each listed sentence is in its class in the account. -/
theorem lists_in_account : (unmapped ++ uncovered).all (fun ic => (classOf ic.2).contains ic.1) = true := by
  decide +kernel

/-! ## The attributes -/

/-- **The attributes of the text agree with `defn`** (`attrsAgree`): constructors, functions,
hooks, collection symbols, priorities. -/
theorem attrs_agree : attrsAgree kore defn = true := by decide +kernel

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

theorem sigE_0 : (((sigItems c).drop 0).take 34).all sigFromN = true := by decide +kernel
theorem sigE_34 : (((sigItems c).drop 34).take 13).all sigFromN = true := by decide +kernel
theorem sigE_47 : (((sigItems c).drop 47).take 13).all sigFromN = true := by decide +kernel
theorem sigE_60 : (((sigItems c).drop 60).take 13).all sigFromN = true := by decide +kernel
theorem sigE_73 : (((sigItems c).drop 73).take 13).all sigFromN = true := by decide +kernel
theorem sigE_86 : (((sigItems c).drop 86).take 13).all sigFromN = true := by decide +kernel
theorem sigE_99 : (((sigItems c).drop 99).take 13).all sigFromN = true := by decide +kernel
theorem sigE_112 : (((sigItems c).drop 112).take 13).all sigFromN = true := by decide +kernel
theorem sigE_125 : (((sigItems c).drop 125).take 13).all sigFromN = true := by decide +kernel
theorem sigE_138 : (((sigItems c).drop 138).take 13).all sigFromN = true := by decide +kernel
theorem sigE_151 : (((sigItems c).drop 151).take 13).all sigFromN = true := by decide +kernel
theorem sigE_164 : (((sigItems c).drop 164).take 13).all sigFromN = true := by decide +kernel
theorem sigE_177 : (((sigItems c).drop 177).take 13).all sigFromN = true := by decide +kernel
theorem sigE_190 : (((sigItems c).drop 190).take 13).all sigFromN = true := by decide +kernel
theorem sigE_203 : (((sigItems c).drop 203).take 13).all sigFromN = true := by decide +kernel
theorem sigE_216 : (((sigItems c).drop 216).take 13).all sigFromN = true := by decide +kernel
theorem sigE_229 : (((sigItems c).drop 229).take 13).all sigFromN = true := by decide +kernel
theorem sigE_242 : (((sigItems c).drop 242).take 13).all sigFromN = true := by decide +kernel
theorem sigE_255 : (((sigItems c).drop 255).take 13).all sigFromN = true := by decide +kernel
theorem sigE_268 : (((sigItems c).drop 268).take 13).all sigFromN = true := by decide +kernel
theorem sigE_281 : (((sigItems c).drop 281).take 13).all sigFromN = true := by decide +kernel
theorem sigE_294 : ((sigItems c).drop 294).all sigFromN = true := by decide +kernel

theorem sig_sizes : (sigItems c).length = 298 := by decide +kernel

/-- **Every item of Γ's signature but next's arity has its origin**: the item of a declaration of
the text, or the sort constant of a registry sort or the arity of an interpreted hooked symbol that
the text does not declare at that shape. Next's arity at the configuration sort has none: the
text has no rule (`text_nextless`). -/
theorem sig_origin_but_next : (sigItems c).all (fun it =>
    (Theory.ofDefinition kore).signature.any (·.pat == it.pat) || surplusItem kore it ||
      it.pat == nextItem.pat) = true :=
  tieAllE_whole (p := sigFromN) <|
    tieAllE_range (a := 0) (n := 34) sigE_0 <|
    tieAllE_range (a := 34) (n := 13) sigE_34 <|
    tieAllE_range (a := 47) (n := 13) sigE_47 <|
    tieAllE_range (a := 60) (n := 13) sigE_60 <|
    tieAllE_range (a := 73) (n := 13) sigE_73 <|
    tieAllE_range (a := 86) (n := 13) sigE_86 <|
    tieAllE_range (a := 99) (n := 13) sigE_99 <|
    tieAllE_range (a := 112) (n := 13) sigE_112 <|
    tieAllE_range (a := 125) (n := 13) sigE_125 <|
    tieAllE_range (a := 138) (n := 13) sigE_138 <|
    tieAllE_range (a := 151) (n := 13) sigE_151 <|
    tieAllE_range (a := 164) (n := 13) sigE_164 <|
    tieAllE_range (a := 177) (n := 13) sigE_177 <|
    tieAllE_range (a := 190) (n := 13) sigE_190 <|
    tieAllE_range (a := 203) (n := 13) sigE_203 <|
    tieAllE_range (a := 216) (n := 13) sigE_216 <|
    tieAllE_range (a := 229) (n := 13) sigE_229 <|
    tieAllE_range (a := 242) (n := 13) sigE_242 <|
    tieAllE_range (a := 255) (n := 13) sigE_255 <|
    tieAllE_range (a := 268) (n := 13) sigE_268 <|
    tieAllE_range (a := 281) (n := 13) sigE_281 <|
    sigE_294

kernel_rfl sigItems_withHooks : ∀ (c : Semantics) (H : HookParams), sigItems (c.withHooks H) = sigItems c

/-- Γ has a symbol under the name `n`. -/
noncomputable def hasSym (n : String) : Bool := (kernelSyms c).any fun k => c.symName k.name == n

noncomputable def plainSorts : List SortDecl := kore.sortDecls.filter (·.params.isEmpty)
noncomputable def plainSyms : List SymbolDecl := kore.symbolDecls.filter fun sd => sd.params.isEmpty && hasSym sd.name
noncomputable def declItems : List Item := plainSorts.map sortConstantItem ++ plainSyms.map arityItem

/-- The item is one of `sigItems c`, pattern for pattern. -/
noncomputable def inSigItems (it : Item) : Bool := (sigItems c).any (·.pat == it.pat)

/-- The declarations of the text: sorts, sorts without parameters, symbols, symbols without
parameters that Γ has, symbols with parameters, symbols without parameters that Γ lacks. -/
theorem decl_counts :
    (kore.sortDecls.length, plainSorts.length, kore.symbolDecls.length, plainSyms.length,
      (kore.symbolDecls.filter fun sd => !sd.params.isEmpty).length,
      (kore.symbolDecls.filter fun sd => sd.params.isEmpty && !hasSym sd.name).length) = (42, 41, 225, 157, 5, 63) := by
  decide +kernel

theorem declsE_0 : (((declItems).drop 0).take 25).all inSigItems = true := by decide +kernel
theorem declsE_25 : (((declItems).drop 25).take 25).all inSigItems = true := by decide +kernel
theorem declsE_50 : (((declItems).drop 50).take 25).all inSigItems = true := by decide +kernel
theorem declsE_75 : (((declItems).drop 75).take 25).all inSigItems = true := by decide +kernel
theorem declsE_100 : (((declItems).drop 100).take 25).all inSigItems = true := by decide +kernel
theorem declsE_125 : (((declItems).drop 125).take 25).all inSigItems = true := by decide +kernel
theorem declsE_150 : (((declItems).drop 150).take 25).all inSigItems = true := by decide +kernel
theorem declsE_175 : ((declItems).drop 175).all inSigItems = true := by decide +kernel

theorem decls_in_sig : declItems.all inSigItems = true :=
  tieAllE_whole (p := inSigItems) <|
    tieAllE_range (a := 0) (n := 25) declsE_0 <|
    tieAllE_range (a := 25) (n := 25) declsE_25 <|
    tieAllE_range (a := 50) (n := 25) declsE_50 <|
    tieAllE_range (a := 75) (n := 25) declsE_75 <|
    tieAllE_range (a := 100) (n := 25) declsE_100 <|
    tieAllE_range (a := 125) (n := 25) declsE_125 <|
    tieAllE_range (a := 150) (n := 25) declsE_150 <|
    declsE_175

/-- **E for the declarations**: Γ entails the item of each declaration without sort parameters of
a symbol Γ has, for every H. -/
theorem decls_entailed (H : HookParams) : ∀ it ∈ declItems, Γ (cH H) ⊧ it.pat := by
  intro it hit M _ I hI
  have h1 : (sigItems c).any (·.pat == it.pat) = true := List.all_eq_true.mp decls_in_sig it hit
  obtain ⟨it', hit', he⟩ := List.any_eq_true.mp h1
  rw [← of_decide_eq_true he]
  exact sat_sigItem hI (by rw [sigItems_withHooks]; exact hit')

/-! ## Consistency for every H -/

def callOrder : List Nat := [
435,436,437,438,
441,439,440]

theorem term_named : c.rankObligations callOrder ++ c.decObligationsL = [] := by decide +kernel
theorem total_named : c.totalObligationsRP callOrder [] = [] := by decide +kernel
theorem agree_named : c.agreeObligationsI = [] := by decide +kernel
theorem match_named : c.matchObligationsL = ([] : List (Nat × Nat)) := by decide +kernel

theorem obl_nil (H : HookParams) : FnObligations (cH H) callOrder [] :=
  FnObligations.of_nil
    (by rw [Semantics.rankObligations_withHooks, Semantics.decObligationsL_withHooks]; exact term_named)
    ((Semantics.totalObligationsRP_withHooks _ H _ _).trans total_named)
    ((Det.Semantics.agreeObligationsI_withHooks _ H).trans agree_named)
    ((Det.Semantics.matchObligationsL_withHooks _ H).trans match_named)

theorem fnHypH (H : HookParams) : FnHyp (cH H) := fnHyp_withHooks coreOK (Semantics.rightHeld_of_valued (by decide +kernel)) H
  ParamsTotal.nil (obl_nil H)

/-- **Γ with the step's closure has a model, for every H.** -/
theorem consistent (H : HookParams) : Consistent (cH H) := consistent_of_fnHyp _ (coreOKH H) (fnHypH H)

/-! ## Γ under every interpretation reads the same equations and rules -/

kernel_rfl fnItems_withHooks : ∀ (c : Semantics) (H : HookParams), fnItems (c.withHooks H) = fnItems c
kernel_rfl ruleItems_withHooks : ∀ (c : Semantics) (H : HookParams), ruleItems (c.withHooks H) = ruleItems c

theorem mem_Γ_fns {c : Semantics} {φ : P} (h : ΓFns c φ) : Γ c φ := Or.inl (Or.inl (Or.inr h))

/-! ## Function equations (88 sentences) -/

/-- The axioms of Γ's equations, in `fnItems`'s order. -/
noncomputable def fnAxioms (c : Semantics) : List Kore.Axiom :=
  c.allFns.flatMap fun f => (fnEquationsK c f).filterMap fun
    | .axiom a => some a
    | _ => none

theorem fnItems_eq : fnItems c = (fnAxioms c).map fun a => trAxiom [] [] ⟨0, "kernel", a⟩ := by kernel_rfl

/-- The text sentences of Γ's 88 equations, in `fnItems`'s order. -/
noncomputable def fnText : List AxiomDecl :=
  [U.ax299, U.ax357, U.ax359, U.ax361, U.ax363, U.ax365, U.ax367, U.ax386, U.ax394, U.ax393,
   U.ax392, U.ax391, U.ax412, U.ax411, U.ax426, U.ax425, U.ax400, U.ax399, U.ax369, U.ax368,
   U.ax385, U.ax384, U.ax377, U.ax376, U.ax379, U.ax378, U.ax428, U.ax427, U.ax432, U.ax431,
   U.ax430, U.ax429, U.ax388, U.ax387, U.ax390, U.ax389, U.ax440, U.ax439, U.ax444, U.ax443,
   U.ax414, U.ax413, U.ax418, U.ax417, U.ax402, U.ax401, U.ax406, U.ax405, U.ax373, U.ax372,
   U.ax375, U.ax374, U.ax442, U.ax441, U.ax436, U.ax435, U.ax448, U.ax447, U.ax381, U.ax380,
   U.ax434, U.ax433, U.ax404, U.ax403, U.ax398, U.ax397, U.ax408, U.ax407, U.ax416, U.ax415,
   U.ax422, U.ax421, U.ax420, U.ax419, U.ax383, U.ax382, U.ax371, U.ax370, U.ax396, U.ax395,
   U.ax446, U.ax445, U.ax424, U.ax423, U.ax438, U.ax437, U.ax410, U.ax409]

set_option maxHeartbeats 1000000 in
/-- **Γ's equations are the text's sentences' translations, pattern for pattern** (one kernel
decision). -/
theorem fn_shape : (fnItems c).map (·.pat) = fnText.map (trS · |>.pat) := by
  rw [fnItems_eq, List.map_map]
  exact (by decide +kernel :
    ((fnAxioms c).map fun a => (trAxiom [] [] ⟨0, "kernel", a⟩).pat) = fnText.map (trS · |>.pat))

/-- **`fnText` is the account's function-equation class**: the same indices, each once. -/
theorem fns_account : (classOf "function equation").isPerm (fnText.map (·.index)) = true := by decide +kernel

/-- **E for the equations**: Γ entails each, for every H. -/
theorem fns_entailed (H : HookParams) : ∀ ad ∈ fnText, Γ (cH H) ⊧ (trS ad).pat := by
  intro ad had M _ I hI
  have hmem : (trS ad).pat ∈ (fnItems c).map (·.pat) := by
    rw [fn_shape]; exact List.mem_map.mpr ⟨ad, had, rfl⟩
  obtain ⟨it, hit, he⟩ := List.mem_map.mp hmem
  exact hI _ (mem_Γ_fns (Or.inl ⟨it, by rw [fnItems_withHooks]; exact hit, he⟩))

/-- **The converse for `fnItems`**: the j-th item is a consequence of `fnText[j]`. -/
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

/-- The priority each function sentence's attributes state is the priority of the clause whose
item is the sentence's translation, item by item in `fnItems`'s order. -/
theorem fn_prios : fnText.map (fun ad => AttrsAgree.prioOf ad.ax.attributes) =
    c.allFns.flatMap (fun f => f.clauses.map (·.prio)) := by decide +kernel

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

theorem nj233 : (trS U.ax233).pat = orTopBot (sym (.sort "SortBool")) := by decide +kernel
theorem nj241 : (trS U.ax241).pat = orTopBot (sym (.sort "SortInt")) := by decide +kernel
theorem nj244 : (trS U.ax244).pat = orTopBot (sym (.sort "SortKConfigVar")) := by decide +kernel

/-- **E for the no-junk sentences of the sorts without generators**: logical truths, entailed by
Γ for every H. -/
theorem nojunk_trivial_entailed (H : HookParams) :
    ∀ ad ∈ [U.ax233, U.ax241, U.ax244], Γ (cH H) ⊧ (trS ad).pat := by
  intro ad had M _ I hI
  have hD := defOK hI
  simp only [List.mem_cons, List.not_mem_nil, or_false] at had
  rcases had with rfl | rfl | rfl
  · rw [nj233]; exact orTopBot_valid hD rfl
  · rw [nj241]; exact orTopBot_valid hD rfl
  · rw [nj244]; exact orTopBot_valid hD rfl

/-- **No junk of the sorts with generators**: the translation of each sentence is the pattern of
one of Γ's constructor items. -/
theorem nojunk_items : ∀ ad ∈ [U.ax234, U.ax235, U.ax236, U.ax237, U.ax238, U.ax239, U.ax240, U.ax242, U.ax243, U.ax246,
      U.ax247, U.ax248, U.ax249, U.ax250, U.ax251, U.ax253, U.ax254, U.ax255, U.ax256, U.ax257,
      U.ax259, U.ax260, U.ax261, U.ax262, U.ax263, U.ax265, U.ax266, U.ax267, U.ax268, U.ax269],
    (consItemsK c).any (·.pat == (trS ad).pat) = true := by decide +kernel

kernel_rfl consItemsK_withHooks : ∀ (c : Semantics) (H : HookParams), consItemsK (c.withHooks H) = consItemsK c

/-- **E for those**: Γ entails each, for every H. -/
theorem nojunk_items_entailed (H : HookParams) : ∀ ad ∈ [U.ax234, U.ax235, U.ax236, U.ax237, U.ax238, U.ax239, U.ax240, U.ax242, U.ax243, U.ax246,
      U.ax247, U.ax248, U.ax249, U.ax250, U.ax251, U.ax253, U.ax254, U.ax255, U.ax256, U.ax257,
      U.ax259, U.ax260, U.ax261, U.ax262, U.ax263, U.ax265, U.ax266, U.ax267, U.ax268, U.ax269],
    Γ (cH H) ⊧ (trS ad).pat := by
  intro ad had M _ I hI
  obtain ⟨it, hit, he⟩ := List.any_eq_true.mp (nojunk_items ad had)
  rw [← of_decide_eq_true he]
  exact sat_cons hI (Or.inl ⟨it, by rw [consItemsK_withHooks]; exact hit, rfl⟩)

/-- KItem's no-junk sentence is the item over KItem's generators in the text's order, the same
generators as `Semantics.gens` lists, in another order. -/
theorem nojunk_kitem_order : (trS U.ax245).pat =
    (KoreAML.Cons.noJunkItem (c.sortName Srt.kitem) ((gensInOrder c defn.pres Srt.kitem).map (Gen.toK c))).pat := by
  decide +kernel
theorem nojunk_kitem_members :
    ((gensInOrder c defn.pres Srt.kitem).map (Gen.toK c)).isPerm ((c.gens Srt.kitem).map (Gen.toK c)) = true := by
  decide +kernel

/-- **E for KItem's no junk (245)**, for every H (`noJunkItem_of_subset`). -/
theorem nojunk_kitem_entailed (H : HookParams) : Γ (cH H) ⊧ (trS U.ax245).pat := by
  intro M _ I hI
  rw [nojunk_kitem_order]
  refine noJunkItem_of_subset (defOK hI) (gs := (c.gens Srt.kitem).map (Gen.toK c))
    (fun g hg => (List.isPerm_iff.mp nojunk_kitem_members).mem_iff.mpr hg) ?_
  exact sat_cons hI (Or.inl ⟨_, noJunkItem_mem (c := cH H) (N := Srt.kitem)
    (show Srt.kitem ∈ consSorts c by decide +kernel) (show (c.gens Srt.kitem).isEmpty = false by decide +kernel), rfl⟩)

/-! ## The constructor sentences: functional, subsort, injectivity, distinctness -/

/-- The constructor sentences `tieConsB` decides, in text order. -/
noncomputable def consText : List AxiomDecl :=
  [U.ax4, U.ax5, U.ax6, U.ax7, U.ax8, U.ax9, U.ax10, U.ax11, U.ax12, U.ax13, U.ax14, U.ax15,
   U.ax16, U.ax17, U.ax18, U.ax19, U.ax20, U.ax22, U.ax23, U.ax24, U.ax25, U.ax27, U.ax28, U.ax29,
   U.ax30, U.ax31, U.ax32, U.ax33, U.ax34, U.ax35, U.ax36, U.ax37, U.ax38, U.ax39, U.ax40, U.ax41,
   U.ax42, U.ax43, U.ax44, U.ax45, U.ax46, U.ax48, U.ax49, U.ax50, U.ax51, U.ax52, U.ax53, U.ax54,
   U.ax58, U.ax59, U.ax60, U.ax61, U.ax62, U.ax63, U.ax64, U.ax65, U.ax66, U.ax67, U.ax68, U.ax69,
   U.ax70, U.ax71, U.ax72, U.ax73, U.ax74, U.ax75, U.ax76, U.ax77, U.ax78, U.ax79, U.ax80, U.ax81,
   U.ax82, U.ax83, U.ax84, U.ax85, U.ax86, U.ax87, U.ax88, U.ax89, U.ax90, U.ax91, U.ax92, U.ax93,
   U.ax94, U.ax95, U.ax96, U.ax97, U.ax157, U.ax216, U.ax217, U.ax218, U.ax219, U.ax220, U.ax221,
   U.ax222, U.ax223, U.ax224]

theorem consE_0 : (((consText).drop 0).take 40).all (fun ad => tieConsB c ad.ax) = true := by decide +kernel
theorem consE_40 : (((consText).drop 40).take 40).all (fun ad => tieConsB c ad.ax) = true := by decide +kernel
theorem consE_80 : ((consText).drop 80).all (fun ad => tieConsB c ad.ax) = true := by decide +kernel
theorem cons_checked : consText.all (fun ad => tieConsB c ad.ax) = true :=
  tieAll_whole (l := consText) (p := (fun ad => tieConsB c ad.ax)) <|
    tieAll_range (l := consText) (p := (fun ad => tieConsB c ad.ax)) (a := 0) (n := 40) consE_0 <|
    tieAll_range (l := consText) (p := (fun ad => tieConsB c ad.ax)) (a := 40) (n := 40) consE_40 <|
    consE_80

theorem consT_0 : (((consText).drop 0).take 40).all (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat)) = true := by decide +kernel
theorem consT_40 : (((consText).drop 40).take 40).all (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat)) = true := by decide +kernel
theorem consT_80 : ((consText).drop 80).all (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat)) = true := by decide +kernel
theorem cons_trS : consText.all (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat)) = true :=
  tieAll_whole (l := consText) (p := (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat))) <|
    tieAll_range (l := consText) (p := (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat))) (a := 0) (n := 40) consT_0 <|
    tieAll_range (l := consText) (p := (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat))) (a := 40) (n := 40) consT_40 <|
    consT_80

/-- **E for the constructor sentences**: Γ entails each, for every H. -/
theorem cons_entailed (H : HookParams) : ∀ ad ∈ consText, Γ (cH H) ⊧ (trS ad).pat := by
  intro ad had M _ I hI
  rw [of_decide_eq_true (List.all_eq_true.mp cons_trS ad had)]
  haveI : OvlOK (cH H) := ovlOK_of_core (coreOKH H)
  exact tieCons_entailed (c := cH H) (a := ad.ax)
    ((tieConsB_withHooks c H ad.ax).trans (List.all_eq_true.mp cons_checked ad had)) ad.index ad.module hI

/-! ## Set idempotence (61): refuted -/

section Idem
variable (H : HookParams)

/-- The text's variable `K:SortSet{}`. -/
def kVar : Kore.Pattern := KoreAML.ev "K" (KoreAML.srt "Set")

theorem idem_pattern : U.ax137.ax.pattern = .equals (srtOf c Srt.set) KoreAML.R (symApp c setConcat [kVar, kVar]) kVar := by
  decide +kernel
theorem idem_trS : (trS U.ax137).pat = (trAxiom [] [] U.ax137).pat := by decide +kernel

/-- `0` as a KItem, and the set `SetItem(0)`. -/
def a0 : GroundTerm := .inj Srt.int Srt.kitem (.dv Srt.int (.int 0))
def s1 : GroundTerm := .set Srt.set [a0]

theorem s1_sort : (cH H).sortOf s1 = some Srt.set := by rw [Semantics.sortOf_withHooks _ _ noRaw]; decide +kernel
theorem concat_sig : (⟨setConcat, [Srt.set, Srt.set], Srt.set⟩ : CtorSig) ∈ hookSigs := by decide +kernel
theorem concat_args : (cH H).sortsOf [s1, s1] = some [Srt.set, Srt.set] := by
  rw [Semantics.sortsOf_withHooks _ _ noRaw]; decide +kernel
theorem concat_none : hook setConcat [s1, s1] = some none := by decide +kernel
theorem concat_heard : silent setConcat [s1, s1] = false := by decide +kernel
theorem set_numbered : Srt.set < nRegSorts + (cH H).sortNames.length :=
  (by decide +kernel : Srt.set < nRegSorts + c.sortNames.length)
theorem set_name : (cH H).sortName Srt.set = "Set" := (by decide +kernel : c.sortName Srt.set = "Set")
theorem idem_vars : (U.ax137.ax.sortVars.map KoreAML.sortVarKey ++ KoreAML.freeOf [] U.ax137.ax.pattern).eraseDups =
    [.sortVar "R", .evar "K" (KoreAML.srt "Set")] := by decide +kernel
theorem idem_sort : KoreAML.sortOf [] U.ax137.ax.pattern = some KoreAML.R := by decide +kernel
theorem symApp_withHooks (f : Sym) (ps : List Kore.Pattern) : symApp (cH H) f ps = symApp c f ps := rfl

/-- **Sentence 137 is refuted, for every H**: Γ with it has no model. At `K = SetItem(0)` the
sentence says `_Set_(K, K)` denotes `K`'s element, and `ΓDomains` (the hook's graph, the two sets
sharing a member) says it denotes nothing. -/
theorem idem_refuted : ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M),
    I ⊧ᴵP Γ (cH H) → ¬ (I ⊧ᴵ (trS U.ax137).pat) := by
  intro M _ I hI hax
  rw [idem_trS] at hax
  haveI : OvlOK (cH H) := ovlOK_of_core (coreOKH H)
  have hD := defOK hI
  have hc := sat_sigItem hI (sig_ceilDef (c := cH H))
  obtain ⟨σS, hσS1, hσS2⟩ := sortSing hI (set_numbered H)
  rw [set_name] at hσS1
  obtain ⟨hes, hesort⟩ := elemOf_spec hI (s1_sort H) KoreAML.val0
  rw [set_name] at hesort
  let a := elemOf (cH H) I s1
  have ha : KoreAML.Inh I σS a := (KoreAML.interp_inhOf_of (S := KoreAML.sym _) hσS1).mp hesort
  let tbl : KoreAML.VarTable := KoreAML.tableOf U.ax137.ax.sortVars U.ax137.ax.pattern
  let val : KoreAML.VarKey → M := fun
    | .sortVar _ => σS
    | _ => a
  let e' : Valuation M := valOf tbl val
  have hRmem : KoreAML.VarKey.sortVar "R" ∈ tbl := by decide +kernel
  have hKmem : KoreAML.VarKey.evar "K" (KoreAML.srt "Set") ∈ tbl := by decide +kernel
  have hRv : ∀ b, (KoreAML.trSort tbl KoreAML.R).interpret I e' b ↔ b = σS := fun b => by
    rw [trSort_R, KoreAML.interp_evar, valOf_ev hRmem]
  have hKv : e'.evalEvar (tbl.ev (.evar "K" (KoreAML.srt "Set"))) = a := valOf_ev hKmem
  have hg : ∀ k ∈ (U.ax137.ax.sortVars.map KoreAML.sortVarKey ++ KoreAML.freeOf [] U.ax137.ax.pattern).eraseDups,
      ∀ m, (KoreAML.guardOf tbl k).interpret I e' m := by
    intro k hk m
    rw [idem_vars] at hk
    rcases List.mem_cons.mp hk with rfl | hk
    · rw [KoreAML.interp_guard_sortVar hD, valOf_ev hRmem]
      exact hσS2
    · rw [List.mem_singleton.mp hk, KoreAML.interp_guard_evar hD, trSort_srt, hKv]
      exact hesort
  have hP := (KoreAML.trAxiom_at hD hax e' hg a).mpr (by
    rw [idem_sort]
    show (KoreAML.inhOf (KoreAML.trSort tbl KoreAML.R)).interpret I e' a
    rw [KoreAML.interp_inhOf_of hRv]; exact ha)
  have hP : (KoreAML.tr ⟨tbl, []⟩ (.equals (srtOf c Srt.set) KoreAML.R (symApp c setConcat [kVar, kVar]) kVar)).interpret
      I e' a := by
    have := hP; simp only [tbl] at this ⊢; rw [idem_pattern] at this ⊢; exact this
  have hS : ∀ b, (KoreAML.trSort tbl (srtOf c Srt.set)).interpret I e' b ↔ b = σS := fun b => by
    unfold srtOf; rw [show c.sortName Srt.set = "Set" from set_name H, trSort_srt]; exact hσS1 b
  rw [KoreAML.tr, KoreAML.interp_sEquals hD hc hS hRv hσS2 hσS2] at hP
  obtain ⟨-, hall⟩ := hP
  have hK : ∀ b, (KoreAML.tr ⟨tbl, []⟩ kVar).interpret I e' b ↔ b = a := fun b => by
    unfold kVar KoreAML.ev
    rw [KoreAML.tr, KoreAML.interp_evar]
    show b = e'.evalEvar (tbl.ev (.evar "K" (KoreAML.srt "Set"))) ↔ b = a
    rw [hKv]
  have happ := (hall a ha).mpr ((hK a).mpr rfl)
  rw [tr_symApp, KoreAML.trArgs_cons, KoreAML.trArgs_cons, KoreAML.trArgs_nil] at happ
  have hden : (KoreAML.den (symApp (cH H) setConcat (GroundTerm.koreList (cH H) [s1, s1]))).interpret I KoreAML.val0 a := by
    unfold KoreAML.den
    rw [symApp_withHooks, tr_symApp]
    simp only [GroundTerm.koreList]
    rw [KoreAML.trArgs_cons, KoreAML.trArgs_cons, KoreAML.trArgs_nil]
    obtain ⟨f1, b1, hf1, hb1, h1⟩ := KoreAML.interp_app.mp happ
    obtain ⟨f0, b0, hf0, hb0, h0⟩ := KoreAML.interp_app.mp hf1
    refine KoreAML.interp_app.mpr ⟨f1, b1, KoreAML.interp_app.mpr ⟨f0, b0, ?_, (hes b0).mpr ((hK b0).mp hb0), h0⟩,
      (hes b1).mpr ((hK b1).mp hb1), h1⟩
    exact (sym_congr (e := KoreAML.val0) (e' := e') _ f0).mpr hf0
  have hgraph := sat_dom hI (Or.inl ⟨_, [s1, s1], none, concat_sig, concat_args H, concat_none,
    fun _ => concat_heard, rfl⟩)
  exact ((KoreAML.interp_equal hD).mp (hgraph KoreAML.val0 default) a).mp hden

end Idem


/-! ## Set idempotence of the definition's own set collections: refuted

Each sentence is the idempotence sentence of a set collection of the definition, whose key sort
has a value the search exhibits (`setIdemTextOK`, a kernel decision). At the element `x` of a
one-member set `{w}` the sentence says `concat(x, x)` holds `x`; `ΓColls` (`setElemAtomAx`) then
makes `x` the unit's, which `setElemNotUnitAx` denies (`Faithful.setColl_idem_refuted_text`). -/

theorem own_idem_ok_141 : setIdemTextOK c "Lbl'Unds'ThCellSet'Unds'" "K" U.ax141 = true := by decide +kernel
theorem own_idem_trS_141 : (trS U.ax141).pat = (trAxiom [] [] U.ax141).pat := by decide +kernel

/-- **Sentence 141 is refuted, for every H**: Γ with it has no model. -/
theorem own_idem_refuted_141 (H : HookParams) : ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M),
    I ⊧ᴵP Γ (cH H) → ¬ (I ⊧ᴵ (trS U.ax141).pat) := by
  haveI : OvlOK (cH H) := ovlOK_of_core (coreOKH H)
  intro M hM I hI hax
  rw [own_idem_trS_141] at hax
  exact setColl_idem_refuted_text c H own_idem_ok_141 M hM I hI hax

/-! ## Library sample: sentence 310, `I -Int 0 = I` (a `simplification`), at values (Ev) -/

def vI : Kore.Pattern := KoreAML.ev "VarI" (KoreAML.srt "Int")
def kI : VarKey := .evar "VarI" (KoreAML.srt "Int")

theorem s166_trS : (trS U.ax310).pat = (trAxiom [] [] U.ax310).pat := by decide +kernel
theorem s166_pattern : U.ax310.ax.pattern = .implies KoreAML.R (.top KoreAML.R)
    (.equals (KoreAML.srt "Int") KoreAML.R (.app ⟨⟨"Lbl'Unds'-Int'Unds'"⟩⟩ [] [vI, .dv (KoreAML.srt "Int") "0"])
      (.and (KoreAML.srt "Int") [vI, .top (KoreAML.srt "Int")])) := by decide +kernel
theorem s166_free : (U.ax310.ax.sortVars.map sortVarKey ++ freeOf [] U.ax310.ax.pattern).eraseDups = [.sortVar "R", kI] := by
  decide +kernel
theorem s166_sortVars : U.ax310.ax.sortVars = [KoreAML.Rv] := by decide +kernel
theorem sub_name (H : HookParams) : (cH H).symName intSub = "Lbl'Unds'-Int'Unds'" ∧ iteSort? "Lbl'Unds'-Int'Unds'" = none :=
  (by decide +kernel : c.symName intSub = "Lbl'Unds'-Int'Unds'" ∧ iteSort? "Lbl'Unds'-Int'Unds'" = none)
theorem den_int0 (H : HookParams) : den (cH H) (KCore.int 0) = KoreAML.sym (.dv "0") ⬝ KoreAML.sym (.sort "SortInt") := by
  show den c (KCore.int 0) = _; decide +kernel
theorem int_numbered (H : HookParams) : Srt.int < nRegSorts + (cH H).sortNames.length :=
  (by decide +kernel : Srt.int < nRegSorts + c.sortNames.length)
theorem int_name (H : HookParams) : (cH H).sortName Srt.int = "Int" := (by decide +kernel : c.sortName Srt.int = "Int")

/-- **Sentence 310 holds at every value of `I`, in every model of Γ, for every H** (Ev): where `I`
denotes the element of the integer `n`, the translated sentence holds. From `ΓDomains`' graph of
`-Int` at `[n, 0]`, which is `n` for every `n`. -/
theorem lib166 (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hI : I ⊧ᴵP Γ (cH H))
    (n : Int) (e : Valuation M)
    (he : e.evalEvar ((tableOf U.ax310.ax.sortVars U.ax310.ax.pattern).ev kI) = elemOf (cH H) I (KCore.int n)) :
    Valuation.satifies I e (trS U.ax310).pat := by
  intro m
  rw [s166_trS]
  haveI : OvlOK (cH H) := ovlOK_of_core (coreOKH H)
  have hD := defOK hI
  have hc := sat_sigItem hI (sig_ceilDef (c := cH H))
  unfold trAxiom
  dsimp only
  rw [s166_free]
  generalize ht : tableOf U.ax310.ax.sortVars U.ax310.ax.pattern = t at he ⊢
  rw [s166_pattern]
  rw [interpret_impl]
  intro hg
  simp only [List.map, conjList, interpret_conj] at hg
  have hR := (interp_guard_sortVar hD).mp hg.1
  have hIg := (interp_guard_evar hD).mp hg.2
  rw [interp_equal hD]
  intro a
  obtain ⟨σI, hσI1, hσI2⟩ := sortSing hI (int_numbered H)
  rw [int_name] at hσI1
  have hS : ∀ b, (trSort t (KoreAML.srt "Int")).interpret I e b ↔ b = σI := fun b => by
    rw [trSort_srt]; exact hσI1 b
  have hRv : ∀ b, (trSort t KoreAML.R).interpret I e b ↔ b = e.evalEvar (t.ev (.sortVar "R")) := fun b => by
    rw [trSort_R, KoreAML.interp_evar]
  obtain ⟨hes, hesort⟩ := elemOf_spec hI (show (cH H).sortOf (KCore.int n) = some Srt.int from rfl) e
  obtain ⟨hes0, -⟩ := elemOf_spec hI (show (cH H).sortOf (KCore.int 0) = some Srt.int from rfl) e
  have hgraph := sat_dom hI (Or.inl ⟨⟨intSub, [Srt.int, Srt.int], Srt.int⟩, [KCore.int n, KCore.int 0], some (KCore.int (n - 0)),
    by decide +kernel, rfl, rfl, fun h => absurd h (by simp), rfl⟩)
  have hg2 := (KoreAML.interp_equal hD).mp (hgraph e default)
  simp only [Int.sub_zero] at hg2
  -- the left side at `e` is the graph's application
  have hL : ∀ b, (tr ⟨t, []⟩ (.app ⟨⟨"Lbl'Unds'-Int'Unds'"⟩⟩ [] [vI, .dv (KoreAML.srt "Int") "0"])).interpret I e b ↔
      (KoreAML.den (symApp (cH H) intSub (GroundTerm.koreList (cH H) [KCore.int n, KCore.int 0]))).interpret I e b := by
    intro b
    have h1 : tr ⟨t, []⟩ (.app ⟨⟨"Lbl'Unds'-Int'Unds'"⟩⟩ [] [vI, .dv (KoreAML.srt "Int") "0"]) =
        (KoreAML.sym (.symbol "Lbl'Unds'-Int'Unds'") ⬝ .evar (t.ev kI)) ⬝ (KoreAML.sym (.dv "0") ⬝ KoreAML.sym (.sort "SortInt")) := rfl
    have h2 : KoreAML.den (symApp (cH H) intSub (GroundTerm.koreList (cH H) [KCore.int n, KCore.int 0])) =
        (KoreAML.sym (.symbol "Lbl'Unds'-Int'Unds'") ⬝ den (cH H) (KCore.int n)) ⬝ den (cH H) (KCore.int 0) := by
      unfold symApp; rw [(sub_name H).1, (sub_name H).2]; rfl
    rw [h1, h2]
    refine interp_app_congr (fun m => interp_app_congr (fun _ => Iff.rfl) (fun m => ?_) m) (fun m => ?_) b
    · rw [interp_evar, he, hes]
    · rw [den_int0]
  simp only [sortOf]
  rw [KoreAML.tr, interp_sImp]
  constructor
  · exact fun h => h.1
  · intro ha
    refine ⟨ha, fun _ => ?_⟩
    rw [KoreAML.tr, interp_sEquals hD hc hS hRv hσI2 hR]
    refine ⟨(interp_inhOf_of hRv).mp ha, fun b hb => ?_⟩
    rw [hL b, hg2 b, hes b]
    rw [KoreAML.tr]
    show _ ↔ (sAnd (tr ⟨t, []⟩ vI) (tr ⟨t, []⟩ (.top (KoreAML.srt "Int")))).interpret I e b
    rw [interp_sAnd, KoreAML.tr]
    show _ ↔ (Pattern.evar (t.ev kI)).interpret I e b ∧ (sTop (trSort t (KoreAML.srt "Int"))).interpret I e b
    rw [interp_evar, he, interp_sTop hD (by rw [trSort_srt]; rfl), interp_inhOf_of hS]
    exact ⟨fun h => ⟨h, hb⟩, And.left⟩


theorem shapesOK_c : c.shapesOK = true := by decide +kernel

/-- The one sort named `Int` is the registry's. -/
theorem int_of_name (S : Srt) (h : KoreAML.srt (c.sortName S) = KoreAML.srt "Int") : S = Srt.int := by
  by_cases hS : S < nRegSorts + c.sortNames.length
  · exact (by decide +kernel : ∀ S ∈ List.range (nRegSorts + c.sortNames.length),
      KoreAML.srt (c.sortName S) = KoreAML.srt "Int" → S = Srt.int) S (List.mem_range.mpr hS) h
  · exfalso
    have hlt : ¬ S < nRegSorts := fun h' => hS (Nat.lt_of_lt_of_le h' (Nat.le_add_right _ _))
    have hge : c.sortNames.length ≤ S - nRegSorts :=
      Nat.le_sub_of_add_le (by rw [Nat.add_comm]; exact Nat.le_of_not_lt hS)
    have he : c.sortName S = "" := by
      unfold Semantics.sortName
      simp only [hlt, ↓reduceIte]
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge]; rfl
    rw [he] at h
    exact absurd h (by decide)
/-- **Sentence 310 is entailed at values** (`EntailsAtValues`, direction Ev), for every H: a
valuation that sends the sentence's one free variable to a value's element sends it to an
integer's, where `lib166` gives the sentence. -/
theorem lib166_at_values (H : HookParams) : EntailsAtValues (cH H) U.ax310 (trS U.ax310).pat := by
  intro M _ I hI e hat m
  obtain ⟨v, S, hS, hv, hden⟩ := hat "VarI" (KoreAML.srt "Int") (by decide +kernel)
  have hS' : S = Srt.int := int_of_name S hS
  subst hS'
  obtain ⟨n, rfl⟩ := shape_int shapesOK_c (by rw [← Semantics.sortOf_withHooks _ H noRaw]; exact hv)
  exact lib166 H hI n e (((elemOf_spec hI hv e).1 _).mp hden) m


/-! ## The converse over Γ's content -/

theorem ruleItems_nil : ruleItems c = [] := by kernel_rfl

/-- The parts of Γ that are no sentence's translation: the families. -/
def Families (H : HookParams) : Premises KoreAML.Sym :=
  ΓSig (cH H) ∪ ΓCons (cH H) ∪ ΓDomains (cH H) ∪ ΓColls (cH H) ∪ ΓFallback (cH H)

/-- The function sentences as written, with definedness, and the families. -/
def Pre (H : HookParams) : Premises KoreAML.Sym :=
  (fun φ => (∃ ad ∈ fnText, (trS ad).pat = φ) ∨ ∃ x : EVar, φ = @definedness KoreAML.Sym _ x) ∪ Families H

/-- **The origin of each premise of Γ**: a function equation is the translation of a text
sentence; the text has no rule, so Γ has no rule item; everything else is one of the five parts
defined by predicates (`Families`), or definedness. -/
theorem gamma_origin (H : HookParams) : ∀ φ, Γ (cH H) φ →
    (∃ ad ∈ fnText, (trS ad).pat = φ) ∨ Families H φ ∨ (∃ x : EVar, φ = @definedness KoreAML.Sym _ x) := by
  intro φ h
  rcases h with ((((((h | h) | h) | h) | h) | h) | h)
  · exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl h)))))
  · exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h)))))
  · exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inr h))))
  · exact Or.inr (Or.inl (Or.inl (Or.inr h)))
  · rcases h with ⟨it, hit, rfl⟩ | hx
    · rw [fnItems_withHooks] at hit
      have hmem : it.pat ∈ fnText.map (trS · |>.pat) := fn_shape ▸ List.mem_map.mpr ⟨it, hit, rfl⟩
      obtain ⟨ad, had, he⟩ := List.mem_map.mp hmem
      exact Or.inl ⟨ad, had, he⟩
    · exact Or.inr (Or.inr hx)
  · rcases h with ⟨it, hit, rfl⟩ | hx
    · rw [ruleItems_withHooks, ruleItems_nil] at hit; cases hit
    · exact Or.inr (Or.inr hx)
  · exact Or.inr (Or.inl (Or.inr h))

/-- Every premise of Γ is a consequence of `Pre`. -/
theorem gamma_from (H : HookParams) : ∀ φ, Γ (cH H) φ → Pre H ⊧ φ := by
  intro φ h M _ I hI
  rcases gamma_origin H φ h with ⟨ad, had, he⟩ | hf | hx
  · exact hI _ (Or.inl (Or.inl ⟨ad, had, he⟩))
  · exact hI _ (Or.inr hf)
  · exact hI _ (Or.inl (Or.inr hx))

end KCore.TieC3CellsStar

#check @KCore.TieC3CellsStar.noRaw
#check @KCore.TieC3CellsStar.readsConfined_c
#check @KCore.TieC3CellsStar.userAxioms_eq
#check @KCore.TieC3CellsStar.coreOK
#check @KCore.TieC3CellsStar.wf_defn
#check @KCore.TieC3CellsStar.account
#check @KCore.TieC3CellsStar.account_sizes
#check @KCore.TieC3CellsStar.account_classes
#check @KCore.TieC3CellsStar.account_absent
#check @KCore.TieC3CellsStar.absent_closed
#check @KCore.TieC3CellsStar.lists_in_account
#check @KCore.TieC3CellsStar.attrs_agree
#check @KCore.TieC3CellsStar.sig_origin_but_next
#check @KCore.TieC3CellsStar.decls_entailed
#check @KCore.TieC3CellsStar.consistent
#check @KCore.TieC3CellsStar.text_nextless
#check @KCore.TieC3CellsStar.fn_shape
#check @KCore.TieC3CellsStar.fns_account
#check @KCore.TieC3CellsStar.fns_entailed
#check @KCore.TieC3CellsStar.fns_from_text
#check @KCore.TieC3CellsStar.fn_prios
#check @KCore.TieC3CellsStar.nojunk_trivial_entailed
#check @KCore.TieC3CellsStar.nojunk_items_entailed
#check @KCore.TieC3CellsStar.nojunk_kitem_entailed
#check @KCore.TieC3CellsStar.cons_entailed
#check @KCore.TieC3CellsStar.idem_refuted
#check @KCore.TieC3CellsStar.own_idem_refuted_141
#check @KCore.TieC3CellsStar.lib166
#check @KCore.TieC3CellsStar.lib166_at_values
#check @KCore.TieC3CellsStar.gamma_origin
#check @KCore.TieC3CellsStar.gamma_from
#print axioms KCore.TieC3CellsStar.noRaw
#print axioms KCore.TieC3CellsStar.readsConfined_c
#print axioms KCore.TieC3CellsStar.userAxioms_eq
#print axioms KCore.TieC3CellsStar.coreOK
#print axioms KCore.TieC3CellsStar.wf_defn
#print axioms KCore.TieC3CellsStar.account
#print axioms KCore.TieC3CellsStar.account_sizes
#print axioms KCore.TieC3CellsStar.account_classes
#print axioms KCore.TieC3CellsStar.account_absent
#print axioms KCore.TieC3CellsStar.absent_closed
#print axioms KCore.TieC3CellsStar.lists_in_account
#print axioms KCore.TieC3CellsStar.attrs_agree
#print axioms KCore.TieC3CellsStar.sig_origin_but_next
#print axioms KCore.TieC3CellsStar.decls_entailed
#print axioms KCore.TieC3CellsStar.consistent
#print axioms KCore.TieC3CellsStar.text_nextless
#print axioms KCore.TieC3CellsStar.fn_shape
#print axioms KCore.TieC3CellsStar.fns_account
#print axioms KCore.TieC3CellsStar.fns_entailed
#print axioms KCore.TieC3CellsStar.fns_from_text
#print axioms KCore.TieC3CellsStar.fn_prios
#print axioms KCore.TieC3CellsStar.nojunk_trivial_entailed
#print axioms KCore.TieC3CellsStar.nojunk_items_entailed
#print axioms KCore.TieC3CellsStar.nojunk_kitem_entailed
#print axioms KCore.TieC3CellsStar.cons_entailed
#print axioms KCore.TieC3CellsStar.idem_refuted
#print axioms KCore.TieC3CellsStar.own_idem_refuted_141
#print axioms KCore.TieC3CellsStar.lib166
#print axioms KCore.TieC3CellsStar.lib166_at_values
#print axioms KCore.TieC3CellsStar.gamma_origin
#print axioms KCore.TieC3CellsStar.gamma_from
