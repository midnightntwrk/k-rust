/-
  The tie (C14) on `f2-examples/e2-cells.kompile.kore`, the kompiled text of construct fixture e2-cells
  (`test/constructs/fixtures/e2-cells`), sentence by sentence, against the translation of the text as
  written (`trS ad := trAxiom k.symbolDecls k.aliasNames ad`), on the literals `kore` and `defn`, for
  every interpretation H. Nothing here reads `Parse.parse` or `emit`. Written by
  `test/constructs/tiegen.py e2-cells`; run from the package root: `lake env lean -j1 test/TieE2Cells.lean`.

  Layer 1.
  - `wf_defn`: `wf defn = true`.
  - The account: the class lists partition the 553 sentences of the user module E2-CELLS, in
    `tieClasses`' order (`account`, `account_sizes`, `account_classes`); the no-direction class holds
    exactly the sentences that apply a symbol Γ lacks (`account_absent`, `absent_closed`).
  - `absent_proj_below`: the 46 no-direction sentences that are equations of a projection
    `project:X` are of sorts X that are K, KItem or below KItem in Γ (`GenEqs.projBelowB`).
  - `attrs_agree`: the attributes the translation does not read agree with `defn`.
  - `sig_origin`: each of the 318 items of `sigItems c` is a declaration's item of the text or a
    surplus one; `decls_entailed`: Γ entails the item of each declaration without sort parameters
    of a symbol Γ has (both by ranges of the lists).
  - The definition reads no confined sort (`readsConfined_c`), has no open generator (`noRaw`) and
    owes no fact (`term_named`, `total_named`, `agree_named`, `match_named`), so Γ with the step's
    closure has a model for every H (`consistent`).

  Layer 2, by class (indices are the text's axiom numbers, `AxiomDecl.index`).
  - Function equations (101): each of Γ's items is the translation of one sentence, in the
    order `fnText` lists them (`fn_shape`); `fns_entailed` (E), `fns_from_text` (the converse),
    `fn_prios` (the priorities the sentences state are the clauses').
  - Rewrite rules (1): each of Γ's rule items (with the premise `⌈rhs ∧ ens⌉`) is a consequence
    of its text sentence, `ruleText` in `ruleItems`' order (`rule_from_text`, W1, every H).
  - Constructor sentences (118): entailed by Γ (`cons_entailed`).
  - No junk (3 of a sort without generators, `nojunk_trivial_entailed`; 35 equal to
    one of Γ's constructor items, `nojunk_items`; 1 KItem's with its disjuncts in the text's
    order, `nojunk_kitem_entailed`).
  - Set idempotence (154): Γ with it has no model (`idem_refuted`).
  - Set idempotence of the set collection of `Lbl'Unds'ThCellSet'Unds'` (158): Γ with it has no model
    (`own_idem_refuted_158`, from `setColl_idem_refuted_text`).
  - Library sample, 346 (`I -Int 0 = I`): holds at values (`lib166`, `lib166_at_values`).
  - The converse over Γ's content: each premise is a function sentence's translation, one of the
    five parts Γ defines by predicates, or definedness (`gamma_origin`, `gamma_from`).
  - Function functional: at values in every model of `Γc`, from `FnHyp`, which holds for every H
    (`fnHypH`), and the sort predicates' results (`fnFun_at_values`, `fnFun_account`).
  - Hooked functional, collection law, library: at values (no theorem here); no direction:
    `absent_closed`.

  OptCell's no junk (292) is entailed (`nojunk_optcell_entailed`): its item lists OptCell's
  generators in another order than `Semantics.gens`.

  The sentences with no counterpart in f2-examples/ens.kompile.kore are `unmapped` (313);
  the sentences of a class with a theorem that no theorem here holds of are `uncovered` (0).
  Written with `--split`: this file holds the literals, the names, `wf`, the account, the
  consistency and the sections that read none of the other files' decisions; the other sections are
  in `test/TieE2CellsAttrs.lean`, `test/TieE2CellsSig.lean`, `test/TieE2CellsDecls.lean`,
  `test/TieE2CellsFns.lean`, `test/TieE2CellsNoJunk.lean`, `test/TieE2CellsCons.lean`, in this
  namespace, each of which repeats the literals and the definitions and facts it reads, as a test
  file imports no test file.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.TieE2Cells

open KCore ML Faithful KoreAML

kore_term kore from "f2-examples/e2-cells.kompile.kore"
definition_of defn from "f2-examples/e2-cells.kompile.kore"
user_axioms U from "f2-examples/e2-cells.kompile.kore" module "E2-CELLS"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

/-- No parameter of the definition is an open generator. -/
theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel

/-- The definition reads no confined sort: its theory is Γ. -/
theorem readsConfined_c : c.readsConfined = false := by decide +kernel

/-- The axioms of the user module, in text order. -/
noncomputable def userAxioms : List AxiomDecl := kore.axiomDecls.filter (·.module == "E2-CELLS")

theorem userAxioms_eq : userAxioms = U.all := by kernel_rfl
theorem userAxioms_length : U.all.length = 553 := by decide +kernel

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
  [("function equation", [335, 390, 395, 397, 399, 401, 405, 407, 408, 409, 410, 411, 412, 413, 414, 415, 416, 417,
      418, 419, 420, 421, 422, 423, 424, 425, 426, 427, 428, 429, 430, 431, 432, 433, 434, 435,
      436, 437, 438, 439, 440, 441, 442, 443, 444, 445, 446, 447, 448, 449, 450, 451, 452, 453,
      454, 455, 456, 457, 458, 459, 460, 461, 462, 463, 464, 465, 466, 467, 468, 469, 470, 471,
      472, 473, 474, 475, 476, 477, 478, 479, 480, 481, 482, 483, 484, 485, 486, 487, 488, 489,
      490, 491, 492, 493, 494, 495, 496, 497, 498, 499, 500]),
   ("rewrite rule", [334]),
   ("priority equation", []),
   ("constructor functional", [66, 69, 71, 73, 75, 77, 79, 81, 83, 85, 87, 89, 91, 93, 95, 97, 99, 101, 103, 105, 107, 109,
      111, 113, 174, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253]),
   ("subsort", [4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 25, 26, 27, 28, 29,
      31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53,
      54, 56, 57, 58, 59, 60, 61, 62, 63]),
   ("injectivity", [70, 72, 74, 76, 78, 80, 82, 84, 86, 88, 90, 92, 94, 96, 98, 100, 102, 104, 106, 108, 110,
      112, 114]),
   ("distinctness", [67]),
   ("no junk", [262, 263, 264, 265, 266, 267, 268, 269, 270, 271, 272, 273, 274, 275, 276, 277, 278, 279,
      280, 281, 282, 284, 285, 286, 287, 288, 290, 291, 292, 293, 294, 295, 296, 297, 298, 300,
      301, 302, 303, 304]),
   ("function functional", [119, 179, 180, 182, 184, 187, 189, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201,
      202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219,
      220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237]),
   ("hooked functional", [64, 65, 68, 115, 116, 117, 118, 120, 121, 122, 124, 125, 126, 128, 130, 131, 132, 133, 134,
      135, 136, 137, 138, 139, 143, 161, 162, 163, 164, 165, 166, 167, 168, 169, 171, 173, 175,
      176, 190, 239, 240, 241, 254, 255, 256, 257, 258, 259]),
   ("collection law", [140, 141, 142, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 155, 156, 157, 159, 160]),
   ("library", [310, 311, 312, 313, 314, 315, 316, 317, 318, 319, 320, 321, 322, 323, 324, 325, 326, 327,
      328, 329, 330, 331, 332, 333, 336, 338, 339, 340, 341, 342, 343, 344, 345, 346, 347, 348,
      349, 350, 351, 352, 353, 354, 355, 356, 357, 358, 359, 360, 361, 362, 363, 364, 365, 366,
      367, 368, 370, 371, 372, 373, 374, 375, 376, 377, 378, 379, 380, 381, 382, 383, 384, 385,
      386, 387, 388, 389, 503, 504, 505, 506, 553, 554]),
   ("set idempotence", [154, 158]),
   ("set-variable lemma", [305, 306, 307, 308, 309, 555, 556]),
   ("function law", []),
   ("open generator law", []),
   ("open generator functional", []),
   ("parameter functional", []),
   ("parameter lemma", []),
   ("user lemma", []),
   ("user lemma at values", []),
   ("no direction", [24, 30, 55, 123, 127, 129, 170, 172, 177, 178, 181, 183, 185, 186, 188, 238, 260, 261, 283,
      289, 299, 337, 369, 391, 392, 393, 394, 396, 398, 400, 402, 403, 404, 406, 501, 502, 507,
      508, 509, 510, 511, 512, 513, 514, 515, 516, 517, 518, 519, 520, 521, 522, 523, 524, 525,
      526, 527, 528, 529, 530, 531, 532, 533, 534, 535, 536, 537, 538, 539, 540, 541, 542, 543,
      544, 545, 546, 547, 548, 549, 550, 551, 552])]

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
    [("function equation", 101), ("rewrite rule", 1), ("priority equation", 0), ("constructor functional", 37), ("subsort", 57), ("injectivity", 23), ("distinctness", 1), ("no junk", 40), ("function functional", 54), ("hooked functional", 48), ("collection law", 18), ("library", 82), ("set idempotence", 2), ("set-variable lemma", 7), ("function law", 0), ("open generator law", 0), ("open generator functional", 0), ("parameter functional", 0), ("parameter lemma", 0), ("user lemma", 0), ("user lemma at values", 0), ("no direction", 82)] := by
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
theorem absentE_480 : (((U.all).drop 480).take 40).all absentP = true := by decide +kernel
theorem absentE_520 : ((U.all).drop 520).all absentP = true := by decide +kernel

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
      tieAll_range (l := U.all) (p := absentP) (a := 480) (n := 40) absentE_480 <|
      absentE_520

/-- **The no-direction class is closed**: every sentence outside it applies only symbols Γ has,
so no sentence with a direction applies a symbol Γ lacks. The injection `inj` is no member of
`kernelSyms` and is Γ's all the same at each subsort pair, where the constructor items state it
(`gammaHeads`). -/
theorem absent_closed :
    (userAxioms.filter (fun ad => !(classOf "no direction").contains ad.index)).all
      (fun ad => (appHeadsOf ad.ax.pattern).all (gammaHasHead c)) = true :=
  tieAbsent_of_account userAxioms _ _ account_absent

/-- The sentences of the no-direction class that are equations of a projection `project:X` (their
left side applies `Lblproject'Coln'X`), each with X. -/
def absentProj : List (Nat × String) :=
  [(507, "Bool"), (508, "ExitcodeCell"), (509, "ExitcodeCellOpt"), (510, "Exp"),
   (511, "GeneratedCounterCell"), (512, "GeneratedCounterCellOpt"), (513, "GeneratedTopCell"),
   (514, "GeneratedTopCellFragment"), (515, "IdCell"), (516, "IdCellOpt"), (517, "Int"),
   (518, "K"), (519, "KCell"), (520, "KCellOpt"), (521, "KItem"), (522, "KeyCell"),
   (523, "KeyCellOpt"), (524, "List"), (525, "LsCell"), (526, "LsCellFragment"),
   (527, "LsCellOpt"), (528, "LtCell"), (529, "LtCellList"), (530, "Map"), (531, "MsCell"),
   (532, "MsCellFragment"), (533, "MsCellOpt"), (534, "MtCell"), (535, "MtCellFragment"),
   (536, "MtCellMap"), (537, "OneCell"), (538, "OneCellOpt"), (539, "OptCell"),
   (540, "OptCellOpt"), (541, "Set"), (542, "TCell"), (543, "TCellFragment"), (544, "TCellOpt"),
   (545, "ThCell"), (546, "ThCellFragment"), (547, "ThCellSet"), (548, "TsCell"),
   (549, "TsCellFragment"), (550, "TsCellOpt"), (551, "VCell"), (552, "VCellOpt")]

/-- Each sort of `absentProj` is K, KItem or a sort below KItem of Γ, with K and KItem
constructor sorts. -/
theorem absent_proj_below_c : absentProj.all (fun p => GenEqs.projBelowB c p.2) = true := by
  decide +kernel

/-- **The projections the no-direction class defines are of sorts below KItem**: `absentProj` is
the list of the no-direction sentences whose left side applies a symbol `Lblproject'Coln'X`, each
with that X, and each such X is K, KItem or a sort below KItem of Γ, with K and KItem constructor
sorts (`GenEqs.projBelowB`). So the pattern each of these equations is at is functional and
injective on X in every model of Γ (`GenEqs.projSel_fun`, `GenEqs.projSel_inj`): what the
equation states of the pattern's symbols, Γ entails. -/
theorem absent_proj_below (H : HookParams) :
    (userAxioms.filter (fun ad => (classOf "no direction").contains ad.index &&
        ((AttrsAgree.eqnHead ad.ax.pattern).getD "").startsWith "Lblproject'Coln'")).map
      (fun ad => (ad.index, AttrsAgree.eqnHead ad.ax.pattern)) =
      absentProj.map (fun p => (p.1, some ("Lblproject'Coln'" ++ p.2))) ∧
    absentProj.all (fun p => GenEqs.projBelowB (cH H) p.2) = true :=
  ⟨by rw [userAxioms_eq]; decide +kernel, absent_proj_below_c⟩

/-- The sentences whose text is none of f2-examples/ens.kompile.kore's user module, with their class. -/
def unmapped : List (Nat × String) :=
  [(4, "subsort"), (5, "subsort"), (6, "subsort"), (7, "subsort"), (8, "subsort"), (9, "subsort"),
   (10, "subsort"), (11, "subsort"), (14, "subsort"), (18, "subsort"), (19, "subsort"),
   (20, "subsort"), (21, "subsort"), (22, "subsort"), (23, "subsort"), (24, "no direction"),
   (29, "subsort"), (30, "no direction"), (31, "subsort"), (32, "subsort"), (33, "subsort"),
   (34, "subsort"), (35, "subsort"), (37, "subsort"), (38, "subsort"), (39, "subsort"),
   (40, "subsort"), (41, "subsort"), (42, "subsort"), (43, "subsort"), (44, "subsort"),
   (45, "subsort"), (46, "subsort"), (48, "subsort"), (49, "subsort"), (50, "subsort"),
   (51, "subsort"), (53, "subsort"), (55, "no direction"), (56, "subsort"), (57, "subsort"),
   (58, "subsort"), (59, "subsort"), (60, "subsort"), (61, "subsort"), (62, "subsort"),
   (66, "constructor functional"), (67, "distinctness"), (69, "constructor functional"),
   (70, "injectivity"), (73, "constructor functional"), (74, "injectivity"),
   (75, "constructor functional"), (76, "injectivity"), (77, "constructor functional"),
   (78, "injectivity"), (81, "constructor functional"), (82, "injectivity"),
   (83, "constructor functional"), (84, "injectivity"), (85, "constructor functional"),
   (86, "injectivity"), (87, "constructor functional"), (88, "injectivity"),
   (89, "constructor functional"), (90, "injectivity"), (91, "constructor functional"),
   (92, "injectivity"), (93, "constructor functional"), (94, "injectivity"),
   (95, "constructor functional"), (96, "injectivity"), (97, "constructor functional"),
   (98, "injectivity"), (99, "constructor functional"), (100, "injectivity"),
   (101, "constructor functional"), (102, "injectivity"), (103, "constructor functional"),
   (104, "injectivity"), (105, "constructor functional"), (106, "injectivity"),
   (107, "constructor functional"), (108, "injectivity"), (109, "constructor functional"),
   (110, "injectivity"), (111, "constructor functional"), (112, "injectivity"),
   (113, "constructor functional"), (114, "injectivity"), (118, "hooked functional"),
   (119, "function functional"), (144, "collection law"), (145, "collection law"),
   (146, "collection law"), (150, "collection law"), (151, "collection law"),
   (152, "collection law"), (157, "collection law"), (158, "set idempotence"),
   (159, "collection law"), (160, "collection law"), (174, "constructor functional"),
   (177, "no direction"), (179, "function functional"), (180, "function functional"),
   (181, "no direction"), (182, "function functional"), (183, "no direction"),
   (184, "function functional"), (185, "no direction"), (186, "no direction"),
   (187, "function functional"), (188, "no direction"), (189, "function functional"),
   (192, "function functional"), (193, "function functional"), (194, "function functional"),
   (199, "function functional"), (200, "function functional"), (207, "function functional"),
   (208, "function functional"), (210, "function functional"), (211, "function functional"),
   (212, "function functional"), (213, "function functional"), (214, "function functional"),
   (216, "function functional"), (217, "function functional"), (218, "function functional"),
   (219, "function functional"), (220, "function functional"), (221, "function functional"),
   (222, "function functional"), (223, "function functional"), (224, "function functional"),
   (225, "function functional"), (227, "function functional"), (228, "function functional"),
   (229, "function functional"), (230, "function functional"), (231, "function functional"),
   (232, "function functional"), (233, "function functional"), (234, "function functional"),
   (235, "function functional"), (236, "function functional"), (237, "function functional"),
   (242, "constructor functional"), (244, "constructor functional"),
   (246, "constructor functional"), (247, "constructor functional"),
   (248, "constructor functional"), (249, "constructor functional"),
   (250, "constructor functional"), (251, "constructor functional"),
   (252, "constructor functional"), (253, "constructor functional"), (263, "no junk"),
   (264, "no junk"), (265, "no junk"), (268, "no junk"), (269, "no junk"), (270, "no junk"),
   (271, "no junk"), (276, "no junk"), (277, "no junk"), (278, "no junk"), (279, "no junk"),
   (280, "no junk"), (281, "no junk"), (282, "no junk"), (283, "no direction"), (284, "no junk"),
   (285, "no junk"), (286, "no junk"), (287, "no junk"), (288, "no junk"), (289, "no direction"),
   (290, "no junk"), (291, "no junk"), (292, "no junk"), (293, "no junk"), (294, "no junk"),
   (295, "no junk"), (296, "no junk"), (297, "no junk"), (298, "no junk"), (299, "no direction"),
   (300, "no junk"), (301, "no junk"), (302, "no junk"), (303, "no junk"), (304, "no junk"),
   (334, "rewrite rule"), (335, "function equation"), (390, "function equation"),
   (391, "no direction"), (393, "no direction"), (394, "no direction"), (395, "function equation"),
   (396, "no direction"), (397, "function equation"), (398, "no direction"),
   (399, "function equation"), (400, "no direction"), (401, "function equation"),
   (402, "no direction"), (403, "no direction"), (404, "no direction"), (405, "function equation"),
   (406, "no direction"), (407, "function equation"), (410, "function equation"),
   (411, "function equation"), (412, "function equation"), (413, "function equation"),
   (414, "function equation"), (415, "function equation"), (424, "function equation"),
   (425, "function equation"), (426, "function equation"), (427, "function equation"),
   (439, "function equation"), (440, "function equation"), (441, "function equation"),
   (442, "function equation"), (445, "function equation"), (446, "function equation"),
   (447, "function equation"), (448, "function equation"), (449, "function equation"),
   (450, "function equation"), (451, "function equation"), (452, "function equation"),
   (453, "function equation"), (454, "function equation"), (457, "function equation"),
   (458, "function equation"), (459, "function equation"), (460, "function equation"),
   (461, "function equation"), (462, "function equation"), (463, "function equation"),
   (464, "function equation"), (465, "function equation"), (466, "function equation"),
   (467, "function equation"), (468, "function equation"), (469, "function equation"),
   (470, "function equation"), (471, "function equation"), (472, "function equation"),
   (473, "function equation"), (474, "function equation"), (475, "function equation"),
   (476, "function equation"), (479, "function equation"), (480, "function equation"),
   (481, "function equation"), (482, "function equation"), (483, "function equation"),
   (484, "function equation"), (485, "function equation"), (486, "function equation"),
   (487, "function equation"), (488, "function equation"), (489, "function equation"),
   (490, "function equation"), (491, "function equation"), (492, "function equation"),
   (493, "function equation"), (494, "function equation"), (495, "function equation"),
   (496, "function equation"), (497, "function equation"), (498, "function equation"),
   (499, "function equation"), (500, "function equation"), (508, "no direction"),
   (509, "no direction"), (510, "no direction"), (515, "no direction"), (516, "no direction"),
   (522, "no direction"), (523, "no direction"), (525, "no direction"), (526, "no direction"),
   (527, "no direction"), (528, "no direction"), (529, "no direction"), (531, "no direction"),
   (532, "no direction"), (533, "no direction"), (534, "no direction"), (535, "no direction"),
   (536, "no direction"), (537, "no direction"), (538, "no direction"), (539, "no direction"),
   (540, "no direction"), (542, "no direction"), (543, "no direction"), (544, "no direction"),
   (545, "no direction"), (546, "no direction"), (547, "no direction"), (548, "no direction"),
   (549, "no direction"), (550, "no direction"), (551, "no direction"), (552, "no direction"),
   (555, "set-variable lemma")]

/-- The sentences of a class with a theorem in the tie that no theorem of this file holds of: the
tie's remainder on this text. -/
def uncovered : List (Nat × String) :=
  []

/-- Each listed sentence is in its class in the account. -/
theorem lists_in_account : (unmapped ++ uncovered).all (fun ic => (classOf ic.2).contains ic.1) = true := by
  decide +kernel

/-! ## Consistency for every H -/

def callOrder : List Nat := [
448,449,450,451,
452,455,453,454]

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

/-! ## Function functional (54): the `functional` sentences, at values in every model of Γc, from `FnHyp` -/

/- The class holds 54 `functional` sentences, `\exists{R}(Val:S, \equals{S, R}(Val:S, f(K0, …)))`:
47 of sort predicates `isX` (KCore builds them, `Semantics.sortPreds`) and 7 of functions of the
text declared total (119, 179, 180, 182, 184, 187, 189). A model of `Γc` reads the application of a
function with a value at every argument list of its sorts, at values' elements, as that value's
element (`LibEv.fnFun_evC`, under `coreOK`, the clauses' predicates `\top`, no `\exists` in a
clause, and the clauses' conditions decided where `needsWitness` holds). A sort predicate has those
values from its own clauses (`LibEv.sortPredFun_evC`); a function declared total has them from
`FnHyp` (`LibEv.fnFun_evC_withHooks`). `FnHyp`, which the tie states for every H (`fnHypH`), decides
the conditions (its `OpenDecided`). So each sentence holds in every model of `Γc`, and of `Γc` with
the step's closure, at every valuation sending its variables to values, for every H. -/

/-- The sentences' indices. -/
def fnFunIdx : List Nat := [119, 179, 180, 182, 184, 187, 189, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202,
   203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221,
   222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237]

/-- The sentences, in text order. -/
noncomputable def fnFunText : List AxiomDecl := U.all.filter fun ad => fnFunIdx.contains ad.index

theorem fnFun_indices : fnFunText.map (·.index) = fnFunIdx := by decide +kernel

/-- **`fnFunText` is the account's function functional class**: the same indices, each once. -/
theorem fnFun_account : (classOf "function functional").isPerm (fnFunText.map (·.index)) = true := by
  decide +kernel

/-- The sentence is the `functional` sentence of a sort predicate of `c`, with its variables' sorts
the registry's, or of a function of `c` declared total, with its variables' sorts sorts of `c`, over
the one sort variable `R`. -/
noncomputable def fnFunOK (ad : AxiomDecl) : Bool :=
  decide (ad.ax.sortVars = [Rv]) &&
    ((c.sortPreds.any fun fn => decide (ad.ax.pattern = LibEv.funPat c fn.sig) && LibEv.predFunReg c fn.sig) ||
      c.fns.any fun fn => fn.total && decide (ad.ax.pattern = LibEv.funPat c fn.sig) && LibEv.predFunRegS c fn.sig)

theorem fnFun_checked : fnFunText.all fnFunOK = true := by decide +kernel

/-- None of the 54 reads a declaration or an alias. -/
theorem fnFun_trS : fnFunText.all (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat)) = true := by
  decide +kernel

/-- The clauses' predicates are `\top` and no clause binds a variable by `\exists`. -/
theorem fnFun_clauses : c.clausesPreTop = true ∧
    (c.fns.all fun f => f.clauses.all fun cl => cl.exs.isEmpty) = true := by
  decide +kernel

/-- **The function functional sentences hold at values in every model of `Γc`, for every H**
(`EntailsAtValuesΓc`), from `FnHyp` (`fnHypH`). -/
theorem fnFun_at_values (H : HookParams) : ∀ ad ∈ fnFunText, EntailsAtValuesΓc (cH H) ad (trS ad).pat := by
  intro ad had
  rw [of_decide_eq_true (List.all_eq_true.mp fnFun_trS ad had)]
  have hok := List.all_eq_true.mp fnFun_checked ad had
  simp only [fnFunOK, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hok
  obtain ⟨hsv, hany | hany⟩ := hok
  · obtain ⟨fn, hfn, hfp⟩ := List.any_eq_true.mp hany
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hfp
    exact LibEv.sortPredFun_evC_withHooks H coreOK fnFun_clauses.1 (Semantics.fnsNoExs_of_all fnFun_clauses.2)
      (fnHypH H).2.2.2.2.1.2 hfn hfp.2 ad hfp.1 hsv
  · obtain ⟨fn, hfn, hfp⟩ := List.any_eq_true.mp hany
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hfp
    exact LibEv.fnFun_evC_withHooks H coreOK fnFun_clauses.1 (Semantics.fnsNoExs_of_all fnFun_clauses.2)
      (fnHypH H) hfn hfp.1.1 hfp.2 ad hfp.1.2 hsv

/-- The same in every model of `Γc` with the step's closure, the theory `Consistent` asks a model of. -/
theorem fnFun_at_values_step (H : HookParams) : ∀ ad ∈ fnFunText,
    ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M), I ⊧ᴵP (Γc (cH H) ∪ Γstep (cH H)) →
      ∀ e, AtValues (cH H) I e ad.ax → ∀ m, (trS ad).pat.interpret I e m :=
  fun ad had M hM I hI => fnFun_at_values H ad had M hM I (fun φ hφ => hI φ (Or.inl hφ))

/-! ## Set idempotence (61): refuted -/

section Idem
variable (H : HookParams)

/-- The text's variable `K:SortSet{}`. -/
def kVar : Kore.Pattern := KoreAML.ev "K" (KoreAML.srt "Set")

theorem idem_pattern : U.ax154.ax.pattern = .equals (srtOf c Srt.set) KoreAML.R (symApp c setConcat [kVar, kVar]) kVar := by
  decide +kernel
theorem idem_trS : (trS U.ax154).pat = (trAxiom [] [] U.ax154).pat := by decide +kernel

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
theorem idem_vars : (U.ax154.ax.sortVars.map KoreAML.sortVarKey ++ KoreAML.freeOf [] U.ax154.ax.pattern).eraseDups =
    [.sortVar "R", .evar "K" (KoreAML.srt "Set")] := by decide +kernel
theorem idem_sort : KoreAML.sortOf [] U.ax154.ax.pattern = some KoreAML.R := by decide +kernel
theorem symApp_withHooks (f : Sym) (ps : List Kore.Pattern) : symApp (cH H) f ps = symApp c f ps := rfl

/-- **Sentence 154 is refuted, for every H**: Γ with it has no model. At `K = SetItem(0)` the
sentence says `_Set_(K, K)` denotes `K`'s element, and `ΓDomains` (the hook's graph, the two sets
sharing a member) says it denotes nothing. -/
theorem idem_refuted : ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M),
    I ⊧ᴵP Γ (cH H) → ¬ (I ⊧ᴵ (trS U.ax154).pat) := by
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
  let tbl : KoreAML.VarTable := KoreAML.tableOf U.ax154.ax.sortVars U.ax154.ax.pattern
  let val : KoreAML.VarKey → M := fun
    | .sortVar _ => σS
    | _ => a
  let e' : Valuation M := valOf tbl val
  have hRmem : KoreAML.VarKey.sortVar "R" ∈ tbl := by decide +kernel
  have hKmem : KoreAML.VarKey.evar "K" (KoreAML.srt "Set") ∈ tbl := by decide +kernel
  have hRv : ∀ b, (KoreAML.trSort tbl KoreAML.R).interpret I e' b ↔ b = σS := fun b => by
    rw [trSort_R, KoreAML.interp_evar, valOf_ev hRmem]
  have hKv : e'.evalEvar (tbl.ev (.evar "K" (KoreAML.srt "Set"))) = a := valOf_ev hKmem
  have hg : ∀ k ∈ (U.ax154.ax.sortVars.map KoreAML.sortVarKey ++ KoreAML.freeOf [] U.ax154.ax.pattern).eraseDups,
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

theorem own_idem_ok_158 : setIdemTextOK c "Lbl'Unds'ThCellSet'Unds'" "K" U.ax158 = true := by decide +kernel
theorem own_idem_trS_158 : (trS U.ax158).pat = (trAxiom [] [] U.ax158).pat := by decide +kernel

/-- **Sentence 158 is refuted, for every H**: Γ with it has no model. -/
theorem own_idem_refuted_158 (H : HookParams) : ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M),
    I ⊧ᴵP Γ (cH H) → ¬ (I ⊧ᴵ (trS U.ax158).pat) := by
  haveI : OvlOK (cH H) := ovlOK_of_core (coreOKH H)
  intro M hM I hI hax
  rw [own_idem_trS_158] at hax
  exact setColl_idem_refuted_text c H own_idem_ok_158 M hM I hI hax

/-! ## Library sample: sentence 346, `I -Int 0 = I` (a `simplification`), at values (Ev) -/

def vI : Kore.Pattern := KoreAML.ev "VarI" (KoreAML.srt "Int")
def kI : VarKey := .evar "VarI" (KoreAML.srt "Int")

theorem s166_trS : (trS U.ax346).pat = (trAxiom [] [] U.ax346).pat := by decide +kernel
theorem s166_pattern : U.ax346.ax.pattern = .implies KoreAML.R (.top KoreAML.R)
    (.equals (KoreAML.srt "Int") KoreAML.R (.app ⟨⟨"Lbl'Unds'-Int'Unds'"⟩⟩ [] [vI, .dv (KoreAML.srt "Int") "0"])
      (.and (KoreAML.srt "Int") [vI, .top (KoreAML.srt "Int")])) := by decide +kernel
theorem s166_free : (U.ax346.ax.sortVars.map sortVarKey ++ freeOf [] U.ax346.ax.pattern).eraseDups = [.sortVar "R", kI] := by
  decide +kernel
theorem s166_sortVars : U.ax346.ax.sortVars = [KoreAML.Rv] := by decide +kernel
theorem sub_name (H : HookParams) : (cH H).symName intSub = "Lbl'Unds'-Int'Unds'" ∧ instDecode? "Lbl'Unds'-Int'Unds'" = none :=
  (by decide +kernel : c.symName intSub = "Lbl'Unds'-Int'Unds'" ∧ instDecode? "Lbl'Unds'-Int'Unds'" = none)
theorem den_int0 (H : HookParams) : den (cH H) (KCore.int 0) = KoreAML.sym (.dv "0") ⬝ KoreAML.sym (.sort "SortInt") := by
  show den c (KCore.int 0) = _; decide +kernel
theorem int_numbered (H : HookParams) : Srt.int < nRegSorts + (cH H).sortNames.length :=
  (by decide +kernel : Srt.int < nRegSorts + c.sortNames.length)
theorem int_name (H : HookParams) : (cH H).sortName Srt.int = "Int" := (by decide +kernel : c.sortName Srt.int = "Int")

/-- **Sentence 346 holds at every value of `I`, in every model of Γ, for every H** (Ev): where `I`
denotes the element of the integer `n`, the translated sentence holds. From `ΓDomains`' graph of
`-Int` at `[n, 0]`, which is `n` for every `n`. -/
theorem lib166 (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hI : I ⊧ᴵP Γ (cH H))
    (n : Int) (e : Valuation M)
    (he : e.evalEvar ((tableOf U.ax346.ax.sortVars U.ax346.ax.pattern).ev kI) = elemOf (cH H) I (KCore.int n)) :
    Valuation.satifies I e (trS U.ax346).pat := by
  intro m
  rw [s166_trS]
  haveI : OvlOK (cH H) := ovlOK_of_core (coreOKH H)
  have hD := defOK hI
  have hc := sat_sigItem hI (sig_ceilDef (c := cH H))
  unfold trAxiom
  dsimp only
  rw [s166_free]
  generalize ht : tableOf U.ax346.ax.sortVars U.ax346.ax.pattern = t at he ⊢
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
      rw [symApp_noInst (c := cH H) (f := intSub) (by rw [(sub_name H).1]; exact (sub_name H).2), (sub_name H).1]; rfl
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
/-- **Sentence 346 is entailed at values** (`EntailsAtValues`, direction Ev), for every H: a
valuation that sends the sentence's one free variable to a value's element sends it to an
integer's, where `lib166` gives the sentence. -/
theorem lib166_at_values (H : HookParams) : EntailsAtValues (cH H) U.ax346 (trS U.ax346).pat := by
  intro M _ I hI e hat m
  obtain ⟨v, S, hS, hv, hden⟩ := hat "VarI" (KoreAML.srt "Int") (by decide +kernel)
  have hS' : S = Srt.int := int_of_name S hS
  subst hS'
  obtain ⟨n, rfl⟩ := shape_int shapesOK_c (by rw [← Semantics.sortOf_withHooks _ H noRaw]; exact hv)
  exact lib166 H hI n e (((elemOf_spec hI hv e).1 _).mp hden) m


end KCore.TieE2Cells

#check @KCore.TieE2Cells.noRaw
#check @KCore.TieE2Cells.readsConfined_c
#check @KCore.TieE2Cells.userAxioms_eq
#check @KCore.TieE2Cells.coreOK
#check @KCore.TieE2Cells.wf_defn
#check @KCore.TieE2Cells.account
#check @KCore.TieE2Cells.account_sizes
#check @KCore.TieE2Cells.account_classes
#check @KCore.TieE2Cells.account_absent
#check @KCore.TieE2Cells.absent_closed
#check @KCore.TieE2Cells.absent_proj_below_c
#check @KCore.TieE2Cells.absent_proj_below
#check @KCore.TieE2Cells.lists_in_account
#check @KCore.TieE2Cells.consistent
#check @KCore.TieE2Cells.fnFun_indices
#check @KCore.TieE2Cells.fnFun_account
#check @KCore.TieE2Cells.fnFun_checked
#check @KCore.TieE2Cells.fnFun_trS
#check @KCore.TieE2Cells.fnFun_at_values
#check @KCore.TieE2Cells.fnFun_at_values_step
#check @KCore.TieE2Cells.idem_refuted
#check @KCore.TieE2Cells.own_idem_refuted_158
#check @KCore.TieE2Cells.lib166
#check @KCore.TieE2Cells.lib166_at_values
#print axioms KCore.TieE2Cells.noRaw
#print axioms KCore.TieE2Cells.readsConfined_c
#print axioms KCore.TieE2Cells.userAxioms_eq
#print axioms KCore.TieE2Cells.coreOK
#print axioms KCore.TieE2Cells.wf_defn
#print axioms KCore.TieE2Cells.account
#print axioms KCore.TieE2Cells.account_sizes
#print axioms KCore.TieE2Cells.account_classes
#print axioms KCore.TieE2Cells.account_absent
#print axioms KCore.TieE2Cells.absent_closed
#print axioms KCore.TieE2Cells.absent_proj_below_c
#print axioms KCore.TieE2Cells.absent_proj_below
#print axioms KCore.TieE2Cells.lists_in_account
#print axioms KCore.TieE2Cells.consistent
#print axioms KCore.TieE2Cells.fnFun_indices
#print axioms KCore.TieE2Cells.fnFun_account
#print axioms KCore.TieE2Cells.fnFun_checked
#print axioms KCore.TieE2Cells.fnFun_trS
#print axioms KCore.TieE2Cells.fnFun_at_values
#print axioms KCore.TieE2Cells.fnFun_at_values_step
#print axioms KCore.TieE2Cells.idem_refuted
#print axioms KCore.TieE2Cells.own_idem_refuted_158
#print axioms KCore.TieE2Cells.lib166
#print axioms KCore.TieE2Cells.lib166_at_values
