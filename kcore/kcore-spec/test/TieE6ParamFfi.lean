/-
  The tie (C14) on `f2-examples/e6-param-ffi.kompile.kore`, the kompiled text of construct fixture e6-param-ffi
  (`test/constructs/fixtures/e6-param-ffi`), sentence by sentence, against the translation of the text as
  written (`trS ad := trAxiom k.symbolDecls k.aliasNames ad`), on the literals `kore` and `defn`, for
  every interpretation H. Nothing here reads `Parse.parse` or `emit`. Written by
  `test/constructs/tiegen.py e6-param-ffi`; run from the package root: `lake env lean -j1 test/TieE6ParamFfi.lean`.

  Layer 1.
  - `wf_defn`: `wf defn = true`.
  - The account: the class lists partition the 683 sentences of the user module E6-PARAM-FFI, in
    `tieClasses`' order (`account`, `account_sizes`, `account_classes`); the no-direction class holds
    exactly the sentences that apply a symbol Γ lacks (`account_absent`, `absent_closed`).
  - `absent_proj_below`: the 19 no-direction sentences that are equations of a projection
    `project:X` are of sorts X that are K, KItem or below KItem in Γ (`GenEqs.projBelowB`).
  - `attrs_agree`: the attributes the translation does not read agree with `defn`.
  - `sig_origin`: each of the 250 items of `sigItems c` is a declaration's item of the text or a
    surplus one; `decls_entailed`: Γ entails the item of each declaration without sort parameters
    of a symbol Γ has (both by ranges of the lists).
  - The definition reads no confined sort (`readsConfined_c`), has no open generator (`noRaw`) and
    owes no fact (`term_named`, `total_named`, `agree_named`, `match_named`), so Γ with the step's
    closure has a model for every H (`consistent`).

  Layer 2, by class (indices are the text's axiom numbers, `AxiomDecl.index`).
  - Function equations (41, and two sentences of the text's prelude modules, 1 (KSEQ), 2 (KSEQ),
    which no user sentence is): each of Γ's items is the translation of one sentence, in the order
    `fnText` lists them (`fn_shape`); its user-module sentences are the class, the others those
    prelude sentences (`fns_account`, and `preludeKseq_eq`: they are the text's); `fns_entailed`
    (E), `fns_from_text` (the converse), `fn_prios` (the priorities the sentences state are the
    clauses').
  - Rewrite rules (8): each of Γ's rule items (with the premise `⌈rhs ∧ ens⌉`) is a consequence
    of its text sentence, `ruleText` in `ruleItems`' order (`rule_from_text`, W1, every H).
  - Constructor sentences (364): entailed by Γ (`cons_entailed`).
  - No junk (6 of a sort without generators, `nojunk_trivial_entailed`; 8 equal to
    one of Γ's constructor items, `nojunk_items`; 1 KItem's with its disjuncts in the text's
    order, `nojunk_kitem_entailed`).
  - Set idempotence (410): Γ with it has no model (`idem_refuted`).
  - Library sample, 556 (`I -Int 0 = I`): holds at values (`lib166`, `lib166_at_values`).
  - The converse over Γ's content: each premise is a function sentence's translation, one of the
    five parts Γ defines by predicates, or definedness (`gamma_origin`, `gamma_from`).
  - Function functional: at values in every model of `Γc`, from the sort predicates' results, not
    from `FnHyp` (`fnFun_at_values`, `fnFun_account`).
  - Hooked functional, collection law, library: at values (no theorem here); no direction:
    `absent_closed`.

  Endianness's no junk (482) is entailed (`nojunk_endianness_entailed`): its item lists Endianness's
  generators in another order than `Semantics.gens`.

  The sentences with no counterpart in f2-examples/ens.kompile.kore are `unmapped` (435);
  the sentences of a class with a theorem that no theorem here holds of are `uncovered` (0).
  Written with `--split`: this file holds the literals, the names, `wf`, the account, the
  consistency and the sections that read none of the other files' decisions; the other sections are
  in `test/TieE6ParamFfiAttrs.lean`, `test/TieE6ParamFfiSig.lean`, `test/TieE6ParamFfiDecls.lean`,
  `test/TieE6ParamFfiFns.lean`, `test/TieE6ParamFfiNoJunk.lean`, `test/TieE6ParamFfiCons.lean`, in
  this namespace, each of which repeats the literals and the definitions and facts it reads, as a
  test file imports no test file.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.TieE6ParamFfi

open KCore ML Faithful KoreAML

kore_term kore from "f2-examples/e6-param-ffi.kompile.kore"
definition_of defn from "f2-examples/e6-param-ffi.kompile.kore"
user_axioms U from "f2-examples/e6-param-ffi.kompile.kore" module "E6-PARAM-FFI"
user_axioms PreludeKseq from "f2-examples/e6-param-ffi.kompile.kore" module "KSEQ"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

/-- No parameter of the definition is an open generator. -/
theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel

/-- The definition reads no confined sort: its theory is Γ. -/
theorem readsConfined_c : c.readsConfined = false := by decide +kernel

/-- The axioms of the user module, in text order. -/
noncomputable def userAxioms : List AxiomDecl := kore.axiomDecls.filter (·.module == "E6-PARAM-FFI")

theorem userAxioms_eq : userAxioms = U.all := by kernel_rfl
theorem userAxioms_length : U.all.length = 683 := by decide +kernel

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
  [("function equation", [527, 528, 613, 614, 615, 616, 617, 618, 619, 620, 621, 622, 623, 624, 625, 626, 627, 628,
      629, 630, 631, 632, 633, 634, 635, 636, 637, 638, 639, 640, 641, 642, 643, 644, 645, 646,
      647, 648, 649, 650, 651]),
   ("rewrite rule", [529, 530, 531, 532, 533, 534, 535, 536]),
   ("priority equation", []),
   ("constructor functional", [24, 49, 73, 96, 118, 139, 159, 178, 196, 213, 229, 244, 258, 271, 283, 294, 305, 314, 322,
      329, 335, 340, 344, 347, 349, 354, 356, 358, 360, 427, 431, 460, 463, 464, 471, 477]),
   ("subsort", [4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]),
   ("injectivity", [295, 355, 357, 359, 361, 432]),
   ("distinctness", [25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47,
      48, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71,
      72, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95,
      97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115,
      116, 117, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134,
      135, 136, 137, 138, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153,
      154, 155, 156, 157, 158, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172,
      173, 174, 175, 176, 177, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191,
      192, 193, 194, 195, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210,
      211, 212, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 230,
      231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 245, 246, 247, 248, 249,
      250, 251, 252, 253, 254, 255, 256, 257, 259, 260, 261, 262, 263, 264, 265, 266, 267, 268,
      269, 270, 272, 273, 274, 275, 276, 277, 278, 279, 280, 281, 282, 284, 285, 286, 287, 288,
      289, 290, 291, 292, 293, 296, 297, 298, 299, 300, 301, 302, 303, 304, 306, 307, 308, 309,
      310, 311, 312, 313, 315, 316, 317, 318, 319, 320, 321, 323, 324, 325, 326, 327, 328, 330,
      331, 332, 333, 334, 336, 337, 338, 339, 341, 342, 343, 345, 346, 348, 428, 472]),
   ("no junk", [480, 481, 482, 483, 484, 485, 486, 487, 488, 489, 490, 491, 492, 493, 494, 495]),
   ("function functional", [435, 436, 437, 438, 439, 440, 441, 442, 443, 444, 445, 446, 447, 448, 449, 450, 451, 452,
      453, 454]),
   ("hooked functional", [350, 351, 352, 353, 362, 364, 367, 369, 370, 371, 372, 373, 374, 375, 378, 379, 380, 381,
      382, 384, 386, 387, 388, 389, 390, 391, 392, 393, 394, 395, 396, 397, 398, 399, 400, 401,
      405, 413, 414, 415, 416, 417, 418, 419, 420, 421, 423, 425, 426, 429, 430, 434, 456, 457,
      459, 461, 462, 465, 466, 467, 468, 469, 470, 473, 474, 475, 476]),
   ("collection law", [402, 403, 404, 406, 407, 408, 409, 411, 412]),
   ("library", [496, 497, 503, 504, 505, 506, 507, 508, 509, 510, 511, 512, 513, 514, 515, 516, 517, 518,
      519, 520, 521, 522, 523, 524, 525, 526, 537, 538, 544, 545, 546, 548, 549, 550, 551, 552,
      553, 554, 555, 556, 557, 558, 559, 560, 561, 562, 563, 564, 565, 566, 567, 568, 569, 570,
      571, 572, 573, 574, 575, 576, 577, 578, 579, 580, 581, 582, 583, 585, 586, 587, 588, 589,
      590, 591, 592, 593, 594, 595, 596, 597, 598, 599, 600, 601, 602, 603, 604, 605, 607, 608,
      654, 655, 656, 657, 677, 678, 679, 680, 681, 682, 683, 684, 685]),
   ("set idempotence", [410]),
   ("set-variable lemma", [498, 499, 500, 501, 502, 686]),
   ("function law", []),
   ("open generator law", []),
   ("open generator functional", []),
   ("parameter functional", []),
   ("parameter lemma", []),
   ("user lemma", []),
   ("user lemma at values", []),
   ("no direction", [363, 365, 366, 368, 376, 377, 383, 385, 422, 424, 433, 455, 458, 478, 479, 539, 540, 541,
      542, 543, 547, 584, 606, 609, 610, 611, 612, 652, 653, 658, 659, 660, 661, 662, 663, 664,
      665, 666, 667, 668, 669, 670, 671, 672, 673, 674, 675, 676])]

/-- The indices of a class. -/
def classOf (n : String) : List Nat := (classes.filter (·.1 == n)).flatMap (·.2)

/-- The indices of the user module's sentences, in text order, are 4, …, 686. -/
theorem indices_eq : U.all.map (·.index) = List.range' 4 683 := by decide +kernel

/-- The class lists, sorted (11 passes of `KoreAML.Distinct.msort`), are the same range. -/
theorem classes_sorted : KoreAML.Distinct.msort 11 (classes.flatMap (·.2)) = List.range' 4 683 := by
  decide +kernel

/-- **The account**: the class lists partition the user module's sentences. Their concatenation is
a permutation of the sentences' indices, which are distinct, so each sentence is in one class and
in it once: sorted, the class lists are the range the indices are (`tacAccount_of_msort`). -/
theorem account : (classes.flatMap (·.2)).isPerm (userAxioms.map (·.index)) = true ∧
    (userAxioms.map (·.index)).Nodup :=
  tacAccount_of_msort classes_sorted (by rw [userAxioms_eq]; exact indices_eq)

/-- The class sizes. -/
theorem account_sizes : classes.map (fun cl => (cl.1, cl.2.length)) =
    [("function equation", 41), ("rewrite rule", 8), ("priority equation", 0), ("constructor functional", 36), ("subsort", 20), ("injectivity", 6), ("distinctness", 302), ("no junk", 16), ("function functional", 20), ("hooked functional", 67), ("collection law", 9), ("library", 103), ("set idempotence", 1), ("set-variable lemma", 6), ("function law", 0), ("open generator law", 0), ("open generator functional", 0), ("parameter functional", 0), ("parameter lemma", 0), ("user lemma", 0), ("user lemma at values", 0), ("no direction", 48)] := by
  decide +kernel

/-- The classes are the tie's (`tieClasses`, which gives each its direction), in its order. -/
theorem account_classes : classes.map (·.1) = tieClasses.map (·.1) := by decide +kernel

/-- The sentence is in the no-direction class exactly where it applies a head Γ lacks. -/
noncomputable def absentP (ad : AxiomDecl) : Bool :=
  (classOf "no direction").contains ad.index != (appHeadsOf ad.ax.pattern).all (gammaHasHead c)

/-- The heads at which Γ applies its symbols (`gammaHeads c`), written out. -/
def gHeads : List (String × List Kore.KSort) :=
  [("kseq", []), ("dotk", []), ("LbllittleEndianBytes", []), ("LblbigEndianBytes", []),
   ("LblsignedBytes", []), ("LblunsignedBytes", []), ("Lbl'-LT-'generatedTop'-GT-'", []),
   ("Lbl'-LT-'generatedTop'-GT-'-fragment", []), ("Lbl'-LT-'k'-GT-'", []), ("LblnoKCell", []),
   ("Lbl'-LT-'generatedCounter'-GT-'", []), ("LblnoGeneratedCounterCell", []),
   ("Lbl'Hash'ffi'Unds'complexdouble", []), ("Lbl'Hash'ffi'Unds'complexfloat", []),
   ("Lbl'Hash'ffi'Unds'complexlongdouble", []), ("Lbl'Hash'ffi'Unds'double", []),
   ("Lbl'Hash'ffi'Unds'float", []), ("Lbl'Hash'ffi'Unds'longdouble", []),
   ("Lbl'Hash'ffi'Unds'pointer", []), ("Lbl'Hash'ffi'Unds'schar", []),
   ("Lbl'Hash'ffi'Unds'sint", []), ("Lbl'Hash'ffi'Unds'sint16", []),
   ("Lbl'Hash'ffi'Unds'sint32", []), ("Lbl'Hash'ffi'Unds'sint64", []),
   ("Lbl'Hash'ffi'Unds'sint8", []), ("Lbl'Hash'ffi'Unds'slong", []),
   ("Lbl'Hash'ffi'Unds'sshort", []), ("Lbl'Hash'ffi'Unds'struct", []),
   ("Lbl'Hash'ffi'Unds'uchar", []), ("Lbl'Hash'ffi'Unds'uint", []),
   ("Lbl'Hash'ffi'Unds'uint16", []), ("Lbl'Hash'ffi'Unds'uint32", []),
   ("Lbl'Hash'ffi'Unds'uint64", []), ("Lbl'Hash'ffi'Unds'uint8", []),
   ("Lbl'Hash'ffi'Unds'ulong", []), ("Lbl'Hash'ffi'Unds'ushort", []),
   ("Lbl'Hash'ffi'Unds'void", []), ("Lblgo", []),
   ("Lbl'Hash'ffiCall'LParUndsCommUndsCommUndsCommUndsCommUndsCommUndsRParUnds'FFI'Unds'Bytes'Unds'Bool'Unds'Int'Unds'List'Unds'List'Unds'Int'Unds'FFIType", []),
   ("append", []), ("LblisK", []), ("LblisKItem", []), ("LblisKConfigVar", []), ("LblisMap", []),
   ("LblisSet", []), ("LblisList", []), ("LblisBool", []), ("LblisInt", []), ("LblisFloat", []),
   ("LblisString", []), ("LblisBytes", []), ("LblisEndianness", []), ("LblisSignedness", []),
   ("LblisGeneratedTopCell", []), ("LblisGeneratedTopCellFragment", []), ("LblisKCell", []),
   ("LblisKCellOpt", []), ("LblisGeneratedCounterCell", []), ("LblisGeneratedCounterCellOpt", []),
   ("LblisFFIType", []), ("Lbl'Hash'address'LParUndsRParUnds'FFI'Unds'Int'Unds'Bytes", []),
   ("Lbl'Hash'alloc'LParUndsCommUndsCommUndsRParUnds'FFI'Unds'Bytes'Unds'KItem'Unds'Int'Unds'Int", []),
   ("Lbl'Hash'ffiCall'LParUndsCommUndsCommUndsCommUndsRParUnds'FFI'Unds'Bytes'Unds'Int'Unds'List'Unds'List'Unds'FFIType", []),
   ("Lbl'Hash'ffiCall'LParUndsCommUndsCommUndsCommUndsCommUndsRParUnds'FFI'Unds'Bytes'Unds'Int'Unds'List'Unds'List'Unds'List'Unds'FFIType", []),
   ("Lbl'Hash'free'LParUndsRParUnds'FFI'Unds'K'Unds'KItem", []),
   ("Lbl'Hash'functionAddress'LParUndsRParUnds'FFI'Unds'Int'Unds'String", []),
   ("Lbl'Hash'nativeRead'LParUndsCommUndsRParUnds'FFI'Unds'K'Unds'Int'Unds'Bytes", []),
   ("Lbl'Hash'nativeWrite'LParUndsCommUndsRParUnds'FFI'Unds'K'Unds'Int'Unds'Bytes", []),
   ("LblnotBool'Unds'", []), ("Lbl'Unds'andBool'Unds'", []), ("Lbl'Unds'andThenBool'Unds'", []),
   ("Lbl'Unds'orBool'Unds'", []), ("Lbl'Unds'orElseBool'Unds'", []),
   ("Lbl'Unds'xorBool'Unds'", []), ("Lbl'Unds'impliesBool'Unds'", []),
   ("Lbl'UndsEqlsEqls'Bool'Unds'", []), ("Lbl'UndsEqlsSlshEqls'Bool'Unds'", []),
   ("Lbl'UndsPlus'Int'Unds'", []), ("Lbl'Unds'-Int'Unds'", []), ("Lbl'UndsStar'Int'Unds'", []),
   ("Lbl'UndsSlsh'Int'Unds'", []), ("Lbl'UndsPerc'Int'Unds'", []), ("Lbl'Unds'divInt'Unds'", []),
   ("Lbl'Unds'modInt'Unds'", []),
   ("LblminInt'LParUndsCommUndsRParUnds'INT-COMMON'Unds'Int'Unds'Int'Unds'Int", []),
   ("LblmaxInt'LParUndsCommUndsRParUnds'INT-COMMON'Unds'Int'Unds'Int'Unds'Int", []),
   ("Lbl'Unds-LT-'Int'Unds'", []), ("Lbl'Unds-LT-Eqls'Int'Unds'", []),
   ("Lbl'Unds-GT-'Int'Unds'", []), ("Lbl'Unds-GT-Eqls'Int'Unds'", []),
   ("Lbl'UndsEqlsEqls'Int'Unds'", []), ("Lbl'UndsEqlsSlshEqls'Int'Unds'", []),
   ("LblabsInt'LParUndsRParUnds'INT-COMMON'Unds'Int'Unds'Int", []),
   ("LblfreshInt'LParUndsRParUnds'INT'Unds'Int'Unds'Int", []), ("Lbl'Unds-GT--GT-'Int'Unds'", []),
   ("Lbl'Unds-LT--LT-'Int'Unds'", []),
   ("Lbllog2Int'LParUndsRParUnds'INT-COMMON'Unds'Int'Unds'Int", []),
   ("Lbl'UndsXor-Perc'Int'UndsUnds'", []),
   ("LblbitRangeInt'LParUndsCommUndsCommUndsRParUnds'INT-COMMON'Unds'Int'Unds'Int'Unds'Int'Unds'Int", []),
   ("LblsignExtendBitRangeInt'LParUndsCommUndsCommUndsRParUnds'INT-COMMON'Unds'Int'Unds'Int'Unds'Int'Unds'Int", []),
   ("Lbl'UndsXor-'Int'Unds'", []), ("Lbl'UndsEqlsEqls'K'Unds'", []),
   ("Lbl'UndsEqlsSlshEqls'K'Unds'", []), ("Lbl'Stop'Map", []), ("Lbl'UndsPipe'-'-GT-Unds'", []),
   ("Lbl'Unds'Map'Unds'", []), ("LblMap'Coln'update", []),
   ("Lbl'UndsLSqBUnds-LT-'-undef'RSqB'", []), ("LblMap'Coln'lookup", []),
   ("LblMap'Coln'lookupOrDefault", []),
   ("Lbl'Unds'in'Unds'keys'LParUndsRParUnds'MAP'Unds'Bool'Unds'KItem'Unds'Map", []),
   ("LblsizeMap", []),
   ("LblremoveAll'LParUndsCommUndsRParUnds'MAP'Unds'Map'Unds'Map'Unds'Set", []),
   ("Lblkeys'LParUndsRParUnds'MAP'Unds'Set'Unds'Map", []), ("Lbl'Stop'Set", []),
   ("LblSetItem", []), ("Lbl'Unds'Set'Unds'", []),
   ("Lbl'UndsPipe'Set'UndsUnds'SET'Unds'Set'Unds'Set'Unds'Set", []),
   ("LblintersectSet'LParUndsCommUndsRParUnds'SET'Unds'Set'Unds'Set'Unds'Set", []),
   ("LblSet'Coln'difference", []), ("LblSet'Coln'in", []),
   ("Lbl'Unds-LT-Eqls'Set'UndsUnds'SET'Unds'Bool'Unds'Set'Unds'Set", []),
   ("Lblsize'LParUndsRParUnds'SET'Unds'Int'Unds'Set", []), ("Lbl'Unds'List'Unds'", []),
   ("Lbl'Stop'List", []), ("LblListItem", []), ("LblpushList", []), ("LblList'Coln'get", []),
   ("LblList'Coln'range", []), ("Lbl'Unds'inList'Unds'", []), ("LblsizeList", []),
   ("LblList'Coln'set", []),
   ("LblmakeList'LParUndsCommUndsRParUnds'LIST'Unds'List'Unds'Int'Unds'KItem", []),
   ("LblupdateList'LParUndsCommUndsCommUndsRParUnds'LIST'Unds'List'Unds'List'Unds'Int'Unds'List", []),
   ("LblfillList'LParUndsCommUndsCommUndsCommUndsRParUnds'LIST'Unds'List'Unds'List'Unds'Int'Unds'Int'Unds'KItem", []),
   ("Lbl'UndsPlus'Float'UndsUnds'FLOAT'Unds'Float'Unds'Float'Unds'Float", []),
   ("Lbl'Unds'-Float'UndsUnds'FLOAT'Unds'Float'Unds'Float'Unds'Float", []),
   ("Lbl'UndsStar'Float'UndsUnds'FLOAT'Unds'Float'Unds'Float'Unds'Float", []),
   ("Lbl'UndsSlsh'Float'UndsUnds'FLOAT'Unds'Float'Unds'Float'Unds'Float", []),
   ("Lbl'UndsPerc'Float'UndsUnds'FLOAT'Unds'Float'Unds'Float'Unds'Float", []),
   ("Lbl--Float'UndsUnds'FLOAT'Unds'Float'Unds'Float", []),
   ("LblabsFloat'LParUndsRParUnds'FLOAT'Unds'Float'Unds'Float", []),
   ("LblfloorFloat'LParUndsRParUnds'FLOAT'Unds'Float'Unds'Float", []),
   ("LblceilFloat'LParUndsRParUnds'FLOAT'Unds'Float'Unds'Float", []),
   ("LbltruncFloat'LParUndsRParUnds'FLOAT'Unds'Float'Unds'Float", []),
   ("LblsqrtFloat'LParUndsRParUnds'FLOAT'Unds'Float'Unds'Float", []),
   ("Lbl'Unds-LT-Eqls'Float'UndsUnds'FLOAT'Unds'Bool'Unds'Float'Unds'Float", []),
   ("Lbl'Unds-LT-'Float'UndsUnds'FLOAT'Unds'Bool'Unds'Float'Unds'Float", []),
   ("Lbl'Unds-GT-Eqls'Float'UndsUnds'FLOAT'Unds'Bool'Unds'Float'Unds'Float", []),
   ("Lbl'Unds-GT-'Float'UndsUnds'FLOAT'Unds'Bool'Unds'Float'Unds'Float", []),
   ("Lbl'UndsEqlsEqls'Float'Unds'", []),
   ("Lbl'UndsEqlsSlshEqls'Float'UndsUnds'FLOAT'Unds'Bool'Unds'Float'Unds'Float", []),
   ("LblisNaN'LParUndsRParUnds'FLOAT'Unds'Bool'Unds'Float", []),
   ("LblisInfinite'LParUndsRParUnds'FLOAT'Unds'Bool'Unds'Float", []),
   ("LblprecisionFloat'LParUndsRParUnds'FLOAT'Unds'Int'Unds'Float", []),
   ("LblexponentBitsFloat'LParUndsRParUnds'FLOAT'Unds'Int'Unds'Float", []),
   ("LblroundFloat'LParUndsCommUndsCommUndsRParUnds'FLOAT'Unds'Float'Unds'Float'Unds'Int'Unds'Int", []),
   ("LblInt2Float'LParUndsCommUndsCommUndsRParUnds'FLOAT'Unds'Float'Unds'Int'Unds'Int'Unds'Int", []),
   ("LblmaxValueFloat'LParUndsCommUndsRParUnds'FLOAT'Unds'Float'Unds'Int'Unds'Int", []),
   ("LblminValueFloat'LParUndsCommUndsRParUnds'FLOAT'Unds'Float'Unds'Int'Unds'Int", []),
   ("Lbl'UndsPlus'String'UndsUnds'STRING-COMMON'Unds'String'Unds'String'Unds'String", []),
   ("LbllengthString'LParUndsRParUnds'STRING-COMMON'Unds'Int'Unds'String", []),
   ("LblordChar'LParUndsRParUnds'STRING-COMMON'Unds'Int'Unds'String", []),
   ("LblsubstrString'LParUndsCommUndsCommUndsRParUnds'STRING-COMMON'Unds'String'Unds'String'Unds'Int'Unds'Int", []),
   ("LblfindString'LParUndsCommUndsCommUndsRParUnds'STRING-COMMON'Unds'Int'Unds'String'Unds'String'Unds'Int", []),
   ("LblrfindString'LParUndsCommUndsCommUndsRParUnds'STRING-COMMON'Unds'Int'Unds'String'Unds'String'Unds'Int", []),
   ("LblfindChar'LParUndsCommUndsCommUndsRParUnds'STRING-COMMON'Unds'Int'Unds'String'Unds'String'Unds'Int", []),
   ("LblrfindChar'LParUndsCommUndsCommUndsRParUnds'STRING-COMMON'Unds'Int'Unds'String'Unds'String'Unds'Int", []),
   ("LblString2Bool'LParUndsRParUnds'STRING-COMMON'Unds'Bool'Unds'String", []),
   ("LblString2Int'LParUndsRParUnds'STRING-COMMON'Unds'Int'Unds'String", []),
   ("LblString2Base'LParUndsCommUndsRParUnds'STRING-COMMON'Unds'Int'Unds'String'Unds'Int", []),
   ("Lblreplace'LParUndsCommUndsCommUndsCommUndsRParUnds'STRING-COMMON'Unds'String'Unds'String'Unds'String'Unds'String'Unds'Int", []),
   ("LblreplaceFirst'LParUndsCommUndsCommUndsRParUnds'STRING-COMMON'Unds'String'Unds'String'Unds'String'Unds'String", []),
   ("LblcountAllOccurrences'LParUndsCommUndsRParUnds'STRING-COMMON'Unds'Int'Unds'String'Unds'String", []),
   ("LblreplaceAll'LParUndsCommUndsCommUndsRParUnds'STRING-COMMON'Unds'String'Unds'String'Unds'String'Unds'String", []),
   ("Lbl'UndsEqlsEqls'String'UndsUnds'STRING-COMMON'Unds'Bool'Unds'String'Unds'String", []),
   ("Lbl'UndsEqlsSlshEqls'String'UndsUnds'STRING-COMMON'Unds'Bool'Unds'String'Unds'String", []),
   ("Lbl'Unds-LT-'String'UndsUnds'STRING-COMMON'Unds'Bool'Unds'String'Unds'String", []),
   ("Lbl'Unds-LT-Eqls'String'UndsUnds'STRING-COMMON'Unds'Bool'Unds'String'Unds'String", []),
   ("Lbl'Unds-GT-'String'UndsUnds'STRING-COMMON'Unds'Bool'Unds'String'Unds'String", []),
   ("Lbl'Unds-GT-Eqls'String'UndsUnds'STRING-COMMON'Unds'Bool'Unds'String'Unds'String", []),
   ("LblchrChar'LParUndsRParUnds'STRING-COMMON'Unds'String'Unds'Int", []),
   ("LblInt2String'LParUndsRParUnds'STRING-COMMON'Unds'String'Unds'Int", []),
   ("LblBool2String'LParUndsRParUnds'STRING-COMMON'Unds'String'Unds'Bool", []),
   ("LblBytes2Int'LParUndsCommUndsCommUndsRParUnds'BYTES-HOOKED'Unds'Int'Unds'Bytes'Unds'Endianness'Unds'Signedness", []),
   ("Lbl'UndsLSqBUnds-LT-'-'UndsRSqBUnds'BYTES-HOOKED'Unds'Bytes'Unds'Bytes'Unds'Int'Unds'Int", []),
   ("Lbl'UndsLSqBUndsRSqBUnds'BYTES-HOOKED'Unds'Int'Unds'Bytes'Unds'Int", []),
   ("LblsubstrBytes'LParUndsCommUndsCommUndsRParUnds'BYTES-HOOKED'Unds'Bytes'Unds'Bytes'Unds'Int'Unds'Int", []),
   ("LblreplaceAtBytes'LParUndsCommUndsCommUndsRParUnds'BYTES-HOOKED'Unds'Bytes'Unds'Bytes'Unds'Int'Unds'Bytes", []),
   ("LblmemsetBytes'LParUndsCommUndsCommUndsCommUndsRParUnds'BYTES-HOOKED'Unds'Bytes'Unds'Bytes'Unds'Int'Unds'Int'Unds'Int", []),
   ("LblpadRightBytes'LParUndsCommUndsCommUndsRParUnds'BYTES-HOOKED'Unds'Bytes'Unds'Bytes'Unds'Int'Unds'Int", []),
   ("LblpadLeftBytes'LParUndsCommUndsCommUndsRParUnds'BYTES-HOOKED'Unds'Bytes'Unds'Bytes'Unds'Int'Unds'Int", []),
   ("LblreverseBytes'LParUndsRParUnds'BYTES-HOOKED'Unds'Bytes'Unds'Bytes", []),
   ("LbllengthBytes'LParUndsRParUnds'BYTES-HOOKED'Unds'Int'Unds'Bytes", []),
   ("Lbl'UndsPlus'Bytes'UndsUnds'BYTES-HOOKED'Unds'Bytes'Unds'Bytes'Unds'Bytes", []),
   ("Lbl'Stop'Bytes'Unds'BYTES-HOOKED'Unds'Bytes", []),
   ("LblInt2Bytes'LParUndsCommUndsCommUndsRParUnds'BYTES-HOOKED'Unds'Bytes'Unds'Int'Unds'Int'Unds'Endianness", []),
   ("Lblite", []), ("Lbl'Stop'RangeMap", []), ("Lbl'Unds'r'Pipe'-'-GT-Unds'", []),
   ("Lbl'Unds'RangeMap'Unds'", []), ("LblRangeMap'Coln'lookup", []),
   ("LblRangeMap'Coln'lookupOrDefault", []), ("LblRangeMap'Coln'find'Unds'range", []),
   ("LblRangeMap'Coln'update", []), ("Lbl'Unds'r'LSqBUnds-LT-'-undef'RSqB'", []),
   ("Lbl'Unds'-RangeMap'UndsUnds'RANGEMAP'Unds'RangeMap'Unds'RangeMap'Unds'RangeMap", []),
   ("LblupdateRangeMap'LParUndsCommUndsRParUnds'RANGEMAP'Unds'RangeMap'Unds'RangeMap'Unds'RangeMap", []),
   ("LblremoveAll'LParUndsCommUndsRParUnds'RANGEMAP'Unds'RangeMap'Unds'RangeMap'Unds'Set", []),
   ("Lbl'Unds'in'Unds'keys'LParUndsRParUnds'RANGEMAP'Unds'Bool'Unds'KItem'Unds'RangeMap", []),
   ("LblsizeRangeMap", []),
   ("Lbl'Unds-LT-Eqls'RangeMap'UndsUnds'RANGEMAP'Unds'Bool'Unds'RangeMap'Unds'RangeMap", []),
   ("Lblkeys'LParUndsRParUnds'RANGEMAP'Unds'Set'Unds'RangeMap", []),
   ("inj", [.ctor ⟨⟨"SortKCell"⟩⟩ [], .ctor ⟨⟨"SortKCellOpt"⟩⟩ []]),
   ("inj", [.ctor ⟨⟨"SortGeneratedCounterCell"⟩⟩ [], .ctor ⟨⟨"SortGeneratedCounterCellOpt"⟩⟩ []]),
   ("inj", [.ctor ⟨⟨"SortKConfigVar"⟩⟩ [], .ctor ⟨⟨"SortKItem"⟩⟩ []]),
   ("inj", [.ctor ⟨⟨"SortMap"⟩⟩ [], .ctor ⟨⟨"SortKItem"⟩⟩ []]),
   ("inj", [.ctor ⟨⟨"SortSet"⟩⟩ [], .ctor ⟨⟨"SortKItem"⟩⟩ []]),
   ("inj", [.ctor ⟨⟨"SortList"⟩⟩ [], .ctor ⟨⟨"SortKItem"⟩⟩ []]),
   ("inj", [.ctor ⟨⟨"SortBool"⟩⟩ [], .ctor ⟨⟨"SortKItem"⟩⟩ []]),
   ("inj", [.ctor ⟨⟨"SortInt"⟩⟩ [], .ctor ⟨⟨"SortKItem"⟩⟩ []]),
   ("inj", [.ctor ⟨⟨"SortFloat"⟩⟩ [], .ctor ⟨⟨"SortKItem"⟩⟩ []]),
   ("inj", [.ctor ⟨⟨"SortString"⟩⟩ [], .ctor ⟨⟨"SortKItem"⟩⟩ []]),
   ("inj", [.ctor ⟨⟨"SortBytes"⟩⟩ [], .ctor ⟨⟨"SortKItem"⟩⟩ []]),
   ("inj", [.ctor ⟨⟨"SortEndianness"⟩⟩ [], .ctor ⟨⟨"SortKItem"⟩⟩ []]),
   ("inj", [.ctor ⟨⟨"SortSignedness"⟩⟩ [], .ctor ⟨⟨"SortKItem"⟩⟩ []]),
   ("inj", [.ctor ⟨⟨"SortGeneratedTopCell"⟩⟩ [], .ctor ⟨⟨"SortKItem"⟩⟩ []]),
   ("inj", [.ctor ⟨⟨"SortGeneratedTopCellFragment"⟩⟩ [], .ctor ⟨⟨"SortKItem"⟩⟩ []]),
   ("inj", [.ctor ⟨⟨"SortKCell"⟩⟩ [], .ctor ⟨⟨"SortKItem"⟩⟩ []]),
   ("inj", [.ctor ⟨⟨"SortKCellOpt"⟩⟩ [], .ctor ⟨⟨"SortKItem"⟩⟩ []]),
   ("inj", [.ctor ⟨⟨"SortGeneratedCounterCell"⟩⟩ [], .ctor ⟨⟨"SortKItem"⟩⟩ []]),
   ("inj", [.ctor ⟨⟨"SortGeneratedCounterCellOpt"⟩⟩ [], .ctor ⟨⟨"SortKItem"⟩⟩ []]),
   ("inj", [.ctor ⟨⟨"SortFFIType"⟩⟩ [], .ctor ⟨⟨"SortKItem"⟩⟩ []])]

/-- The literal is Γ's heads. -/
theorem gHeads_eq : gammaHeads c = gHeads := by decide +kernel

/-- `absentP` with Γ's heads read from the literal `gHeads`. -/
noncomputable def absentPL (ad : AxiomDecl) : Bool :=
  (classOf "no direction").contains ad.index !=
    (appHeadsOf ad.ax.pattern).all (fun h => gHeads.any fun g => decide (g = h))

/-- `absentPL` is `absentP`: `gammaHasHead c` is membership in `gammaHeads c`, which is `gHeads`. -/
theorem absentPL_eq : absentPL = absentP := by
  funext ad; unfold absentPL absentP gammaHasHead; rw [gHeads_eq]

theorem absentE_0 : (((U.all).drop 0).take 40).all absentPL = true := by decide +kernel
theorem absentE_40 : (((U.all).drop 40).take 40).all absentPL = true := by decide +kernel
theorem absentE_80 : (((U.all).drop 80).take 40).all absentPL = true := by decide +kernel
theorem absentE_120 : (((U.all).drop 120).take 40).all absentPL = true := by decide +kernel
theorem absentE_160 : (((U.all).drop 160).take 40).all absentPL = true := by decide +kernel
theorem absentE_200 : (((U.all).drop 200).take 40).all absentPL = true := by decide +kernel
theorem absentE_240 : (((U.all).drop 240).take 40).all absentPL = true := by decide +kernel
theorem absentE_280 : (((U.all).drop 280).take 40).all absentPL = true := by decide +kernel
theorem absentE_320 : (((U.all).drop 320).take 40).all absentPL = true := by decide +kernel
theorem absentE_360 : (((U.all).drop 360).take 40).all absentPL = true := by decide +kernel
theorem absentE_400 : (((U.all).drop 400).take 40).all absentPL = true := by decide +kernel
theorem absentE_440 : (((U.all).drop 440).take 40).all absentPL = true := by decide +kernel
theorem absentE_480 : (((U.all).drop 480).take 40).all absentPL = true := by decide +kernel
theorem absentE_520 : (((U.all).drop 520).take 40).all absentPL = true := by decide +kernel
theorem absentE_560 : (((U.all).drop 560).take 40).all absentPL = true := by decide +kernel
theorem absentE_600 : (((U.all).drop 600).take 40).all absentPL = true := by decide +kernel
theorem absentE_640 : (((U.all).drop 640).take 40).all absentPL = true := by decide +kernel
theorem absentE_680 : ((U.all).drop 680).all absentPL = true := by decide +kernel

/-- **A sentence outside the no-direction class applies only symbols Γ has**, each a head with its
sort arguments (`appHeadsOf`) among Γ's (`gammaHeads`), and each sentence of that class applies one
Γ lacks. -/
theorem account_absent : userAxioms.all (fun ad =>
    (classOf "no direction").contains ad.index != (appHeadsOf ad.ax.pattern).all (gammaHasHead c)) = true := by
  rw [userAxioms_eq]
  have h : (U.all).all absentPL = true :=
    tieAll_whole (l := U.all) (p := absentPL) <|
      tieAll_range (l := U.all) (p := absentPL) (a := 0) (n := 40) absentE_0 <|
      tieAll_range (l := U.all) (p := absentPL) (a := 40) (n := 40) absentE_40 <|
      tieAll_range (l := U.all) (p := absentPL) (a := 80) (n := 40) absentE_80 <|
      tieAll_range (l := U.all) (p := absentPL) (a := 120) (n := 40) absentE_120 <|
      tieAll_range (l := U.all) (p := absentPL) (a := 160) (n := 40) absentE_160 <|
      tieAll_range (l := U.all) (p := absentPL) (a := 200) (n := 40) absentE_200 <|
      tieAll_range (l := U.all) (p := absentPL) (a := 240) (n := 40) absentE_240 <|
      tieAll_range (l := U.all) (p := absentPL) (a := 280) (n := 40) absentE_280 <|
      tieAll_range (l := U.all) (p := absentPL) (a := 320) (n := 40) absentE_320 <|
      tieAll_range (l := U.all) (p := absentPL) (a := 360) (n := 40) absentE_360 <|
      tieAll_range (l := U.all) (p := absentPL) (a := 400) (n := 40) absentE_400 <|
      tieAll_range (l := U.all) (p := absentPL) (a := 440) (n := 40) absentE_440 <|
      tieAll_range (l := U.all) (p := absentPL) (a := 480) (n := 40) absentE_480 <|
      tieAll_range (l := U.all) (p := absentPL) (a := 520) (n := 40) absentE_520 <|
      tieAll_range (l := U.all) (p := absentPL) (a := 560) (n := 40) absentE_560 <|
      tieAll_range (l := U.all) (p := absentPL) (a := 600) (n := 40) absentE_600 <|
      tieAll_range (l := U.all) (p := absentPL) (a := 640) (n := 40) absentE_640 <|
      absentE_680
  rw [absentPL_eq] at h; exact h

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
  [(658, "Bool"), (659, "Bytes"), (660, "Endianness"), (661, "FFIType"), (662, "Float"),
   (663, "GeneratedCounterCell"), (664, "GeneratedCounterCellOpt"), (665, "GeneratedTopCell"),
   (666, "GeneratedTopCellFragment"), (667, "Int"), (668, "K"), (669, "KCell"), (670, "KCellOpt"),
   (671, "KItem"), (672, "List"), (673, "Map"), (674, "Set"), (675, "Signedness"), (676, "String")]

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
  [(5, "subsort"), (8, "subsort"), (16, "subsort"), (17, "subsort"), (19, "subsort"),
   (20, "subsort"), (24, "constructor functional"), (25, "distinctness"), (26, "distinctness"),
   (27, "distinctness"), (28, "distinctness"), (29, "distinctness"), (30, "distinctness"),
   (31, "distinctness"), (32, "distinctness"), (33, "distinctness"), (34, "distinctness"),
   (35, "distinctness"), (36, "distinctness"), (37, "distinctness"), (38, "distinctness"),
   (39, "distinctness"), (40, "distinctness"), (41, "distinctness"), (42, "distinctness"),
   (43, "distinctness"), (44, "distinctness"), (45, "distinctness"), (46, "distinctness"),
   (47, "distinctness"), (48, "distinctness"), (49, "constructor functional"),
   (50, "distinctness"), (51, "distinctness"), (52, "distinctness"), (53, "distinctness"),
   (54, "distinctness"), (55, "distinctness"), (56, "distinctness"), (57, "distinctness"),
   (58, "distinctness"), (59, "distinctness"), (60, "distinctness"), (61, "distinctness"),
   (62, "distinctness"), (63, "distinctness"), (64, "distinctness"), (65, "distinctness"),
   (66, "distinctness"), (67, "distinctness"), (68, "distinctness"), (69, "distinctness"),
   (70, "distinctness"), (71, "distinctness"), (72, "distinctness"),
   (73, "constructor functional"), (74, "distinctness"), (75, "distinctness"),
   (76, "distinctness"), (77, "distinctness"), (78, "distinctness"), (79, "distinctness"),
   (80, "distinctness"), (81, "distinctness"), (82, "distinctness"), (83, "distinctness"),
   (84, "distinctness"), (85, "distinctness"), (86, "distinctness"), (87, "distinctness"),
   (88, "distinctness"), (89, "distinctness"), (90, "distinctness"), (91, "distinctness"),
   (92, "distinctness"), (93, "distinctness"), (94, "distinctness"), (95, "distinctness"),
   (96, "constructor functional"), (97, "distinctness"), (98, "distinctness"),
   (99, "distinctness"), (100, "distinctness"), (101, "distinctness"), (102, "distinctness"),
   (103, "distinctness"), (104, "distinctness"), (105, "distinctness"), (106, "distinctness"),
   (107, "distinctness"), (108, "distinctness"), (109, "distinctness"), (110, "distinctness"),
   (111, "distinctness"), (112, "distinctness"), (113, "distinctness"), (114, "distinctness"),
   (115, "distinctness"), (116, "distinctness"), (117, "distinctness"),
   (118, "constructor functional"), (119, "distinctness"), (120, "distinctness"),
   (121, "distinctness"), (122, "distinctness"), (123, "distinctness"), (124, "distinctness"),
   (125, "distinctness"), (126, "distinctness"), (127, "distinctness"), (128, "distinctness"),
   (129, "distinctness"), (130, "distinctness"), (131, "distinctness"), (132, "distinctness"),
   (133, "distinctness"), (134, "distinctness"), (135, "distinctness"), (136, "distinctness"),
   (137, "distinctness"), (138, "distinctness"), (139, "constructor functional"),
   (140, "distinctness"), (141, "distinctness"), (142, "distinctness"), (143, "distinctness"),
   (144, "distinctness"), (145, "distinctness"), (146, "distinctness"), (147, "distinctness"),
   (148, "distinctness"), (149, "distinctness"), (150, "distinctness"), (151, "distinctness"),
   (152, "distinctness"), (153, "distinctness"), (154, "distinctness"), (155, "distinctness"),
   (156, "distinctness"), (157, "distinctness"), (158, "distinctness"),
   (159, "constructor functional"), (160, "distinctness"), (161, "distinctness"),
   (162, "distinctness"), (163, "distinctness"), (164, "distinctness"), (165, "distinctness"),
   (166, "distinctness"), (167, "distinctness"), (168, "distinctness"), (169, "distinctness"),
   (170, "distinctness"), (171, "distinctness"), (172, "distinctness"), (173, "distinctness"),
   (174, "distinctness"), (175, "distinctness"), (176, "distinctness"), (177, "distinctness"),
   (178, "constructor functional"), (179, "distinctness"), (180, "distinctness"),
   (181, "distinctness"), (182, "distinctness"), (183, "distinctness"), (184, "distinctness"),
   (185, "distinctness"), (186, "distinctness"), (187, "distinctness"), (188, "distinctness"),
   (189, "distinctness"), (190, "distinctness"), (191, "distinctness"), (192, "distinctness"),
   (193, "distinctness"), (194, "distinctness"), (195, "distinctness"),
   (196, "constructor functional"), (197, "distinctness"), (198, "distinctness"),
   (199, "distinctness"), (200, "distinctness"), (201, "distinctness"), (202, "distinctness"),
   (203, "distinctness"), (204, "distinctness"), (205, "distinctness"), (206, "distinctness"),
   (207, "distinctness"), (208, "distinctness"), (209, "distinctness"), (210, "distinctness"),
   (211, "distinctness"), (212, "distinctness"), (213, "constructor functional"),
   (214, "distinctness"), (215, "distinctness"), (216, "distinctness"), (217, "distinctness"),
   (218, "distinctness"), (219, "distinctness"), (220, "distinctness"), (221, "distinctness"),
   (222, "distinctness"), (223, "distinctness"), (224, "distinctness"), (225, "distinctness"),
   (226, "distinctness"), (227, "distinctness"), (228, "distinctness"),
   (229, "constructor functional"), (230, "distinctness"), (231, "distinctness"),
   (232, "distinctness"), (233, "distinctness"), (234, "distinctness"), (235, "distinctness"),
   (236, "distinctness"), (237, "distinctness"), (238, "distinctness"), (239, "distinctness"),
   (240, "distinctness"), (241, "distinctness"), (242, "distinctness"), (243, "distinctness"),
   (244, "constructor functional"), (245, "distinctness"), (246, "distinctness"),
   (247, "distinctness"), (248, "distinctness"), (249, "distinctness"), (250, "distinctness"),
   (251, "distinctness"), (252, "distinctness"), (253, "distinctness"), (254, "distinctness"),
   (255, "distinctness"), (256, "distinctness"), (257, "distinctness"),
   (258, "constructor functional"), (259, "distinctness"), (260, "distinctness"),
   (261, "distinctness"), (262, "distinctness"), (263, "distinctness"), (264, "distinctness"),
   (265, "distinctness"), (266, "distinctness"), (267, "distinctness"), (268, "distinctness"),
   (269, "distinctness"), (270, "distinctness"), (271, "constructor functional"),
   (272, "distinctness"), (273, "distinctness"), (274, "distinctness"), (275, "distinctness"),
   (276, "distinctness"), (277, "distinctness"), (278, "distinctness"), (279, "distinctness"),
   (280, "distinctness"), (281, "distinctness"), (282, "distinctness"),
   (283, "constructor functional"), (284, "distinctness"), (285, "distinctness"),
   (286, "distinctness"), (287, "distinctness"), (288, "distinctness"), (289, "distinctness"),
   (290, "distinctness"), (291, "distinctness"), (292, "distinctness"), (293, "distinctness"),
   (294, "constructor functional"), (295, "injectivity"), (296, "distinctness"),
   (297, "distinctness"), (298, "distinctness"), (299, "distinctness"), (300, "distinctness"),
   (301, "distinctness"), (302, "distinctness"), (303, "distinctness"), (304, "distinctness"),
   (305, "constructor functional"), (306, "distinctness"), (307, "distinctness"),
   (308, "distinctness"), (309, "distinctness"), (310, "distinctness"), (311, "distinctness"),
   (312, "distinctness"), (313, "distinctness"), (314, "constructor functional"),
   (315, "distinctness"), (316, "distinctness"), (317, "distinctness"), (318, "distinctness"),
   (319, "distinctness"), (320, "distinctness"), (321, "distinctness"),
   (322, "constructor functional"), (323, "distinctness"), (324, "distinctness"),
   (325, "distinctness"), (326, "distinctness"), (327, "distinctness"), (328, "distinctness"),
   (329, "constructor functional"), (330, "distinctness"), (331, "distinctness"),
   (332, "distinctness"), (333, "distinctness"), (334, "distinctness"),
   (335, "constructor functional"), (336, "distinctness"), (337, "distinctness"),
   (338, "distinctness"), (339, "distinctness"), (340, "constructor functional"),
   (341, "distinctness"), (342, "distinctness"), (343, "distinctness"),
   (344, "constructor functional"), (345, "distinctness"), (346, "distinctness"),
   (347, "constructor functional"), (348, "distinctness"), (349, "constructor functional"),
   (350, "hooked functional"), (362, "hooked functional"), (363, "no direction"),
   (364, "hooked functional"), (365, "no direction"), (366, "no direction"),
   (367, "hooked functional"), (368, "no direction"), (369, "hooked functional"),
   (376, "no direction"), (379, "hooked functional"), (381, "hooked functional"),
   (387, "hooked functional"), (389, "hooked functional"), (393, "hooked functional"),
   (397, "hooked functional"), (399, "hooked functional"), (401, "hooked functional"),
   (427, "constructor functional"), (428, "distinctness"), (429, "hooked functional"),
   (431, "constructor functional"), (432, "injectivity"), (436, "function functional"),
   (437, "function functional"), (438, "function functional"), (439, "function functional"),
   (453, "function functional"), (454, "function functional"), (457, "hooked functional"),
   (458, "no direction"), (459, "hooked functional"), (460, "constructor functional"),
   (468, "hooked functional"), (469, "hooked functional"), (470, "hooked functional"),
   (471, "constructor functional"), (472, "distinctness"), (476, "hooked functional"),
   (477, "constructor functional"), (481, "no junk"), (482, "no junk"), (483, "no junk"),
   (484, "no junk"), (493, "no junk"), (494, "no junk"), (495, "no junk"), (496, "library"),
   (497, "library"), (527, "function equation"), (528, "function equation"), (529, "rewrite rule"),
   (530, "rewrite rule"), (531, "rewrite rule"), (532, "rewrite rule"), (533, "rewrite rule"),
   (534, "rewrite rule"), (535, "rewrite rule"), (536, "rewrite rule"), (537, "library"),
   (538, "library"), (539, "no direction"), (540, "no direction"), (541, "no direction"),
   (542, "no direction"), (543, "no direction"), (544, "library"), (545, "library"),
   (563, "library"), (567, "library"), (570, "library"), (571, "library"), (574, "library"),
   (604, "library"), (605, "library"), (606, "no direction"), (607, "library"),
   (612, "no direction"), (615, "function equation"), (616, "function equation"),
   (617, "function equation"), (618, "function equation"), (619, "function equation"),
   (620, "function equation"), (621, "function equation"), (622, "function equation"),
   (648, "function equation"), (649, "function equation"), (650, "function equation"),
   (651, "function equation"), (659, "no direction"), (660, "no direction"), (661, "no direction"),
   (662, "no direction"), (675, "no direction"), (676, "no direction"), (678, "library"),
   (679, "library"), (680, "library"), (681, "library"), (682, "library"), (683, "library"),
   (684, "library")]

/-- The sentences of a class with a theorem in the tie that no theorem of this file holds of: the
tie's remainder on this text. -/
def uncovered : List (Nat × String) :=
  []

/-- Each listed sentence is in its class in the account. -/
theorem lists_in_account : (unmapped ++ uncovered).all (fun ic => (classOf ic.2).contains ic.1) = true := by
  decide +kernel

/-! ## Consistency for every H -/

def callOrder : List Nat := [
411,412]

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

/-! ## Function functional (20): the sort predicates' `functional` sentences, at values in every model of Γc -/

/- The class holds the `functional` sentences of 20 sort predicates `isX`,
`\exists{R}(Val:SortBool{}, \equals{SortBool{}, R}(Val:SortBool{}, LblisX{}(K0:SortK{})))`. KCore builds
the sort predicates (`Semantics.sortPreds`): each has a value at every K, and a model of `Γc` reads
its application at a value's element as that value's element (`LibEv.sortPredFun_evC`, under
`coreOK`, the clauses' predicates `\top`, no `\exists` in a clause, and no condition over a
variable the patterns leave open). So each sentence holds in every model of `Γc`, and of `Γc` with
the step's closure, at every valuation sending K0 to a value, for every H, from the sort predicates'
own results and without `FnHyp`. -/

/-- The sentences' indices. -/
def fnFunIdx : List Nat := [435, 436, 437, 438, 439, 440, 441, 442, 443, 444, 445, 446, 447, 448, 449, 450, 451, 452, 453,
   454]

/-- The sentences, in text order. -/
noncomputable def fnFunText : List AxiomDecl := U.all.filter fun ad => fnFunIdx.contains ad.index

theorem fnFun_indices : fnFunText.map (·.index) = fnFunIdx := by decide +kernel

/-- **`fnFunText` is the account's function functional class**: the same indices, each once. -/
theorem fnFun_account : (classOf "function functional").isPerm (fnFunText.map (·.index)) = true := by
  decide +kernel

/-- The sentence is the `functional` sentence of a sort predicate of `c`, over the one sort
variable `R`, with its variables' sorts the registry's. -/
noncomputable def fnFunOK (ad : AxiomDecl) : Bool :=
  decide (ad.ax.sortVars = [Rv]) &&
    c.sortPreds.any fun fn => decide (ad.ax.pattern = LibEv.funPat c fn.sig) && LibEv.predFunReg c fn.sig

theorem fnFun_checked : fnFunText.all fnFunOK = true := by decide +kernel

/-- None of the 20 reads a declaration or an alias. -/
theorem fnFun_trS : fnFunText.all (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat)) = true := by
  decide +kernel

/-- The clauses' predicates are `\top`, no clause binds a variable by `\exists`, and no clause has
a condition over a variable its patterns leave open. -/
theorem fnFun_clauses : c.clausesPreTop = true ∧
    (c.fns.all fun f => f.clauses.all fun cl => cl.exs.isEmpty) = true ∧
    (c.fns.all fun f => f.clauses.all fun cl => !cl.reqOpen) = true := by
  decide +kernel

theorem fnFun_noWitH (H : HookParams) : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, cl.needsWitness (cH H) = false := by
  intro fn hfn cl hcl
  have h := List.all_eq_true.mp (List.all_eq_true.mp fnFun_clauses.2.2 fn hfn) cl hcl
  simp only [Bool.not_eq_eq_eq_not, Bool.not_true] at h
  simp [Clause.needsWitness, h]

/-- **The function functional sentences hold at values in every model of `Γc`, for every H**
(`EntailsAtValuesΓc`), without `FnHyp`. -/
theorem fnFun_at_values (H : HookParams) : ∀ ad ∈ fnFunText, EntailsAtValuesΓc (cH H) ad (trS ad).pat := by
  intro ad had
  rw [of_decide_eq_true (List.all_eq_true.mp fnFun_trS ad had)]
  have hok := List.all_eq_true.mp fnFun_checked ad had
  simp only [fnFunOK, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨hsv, hany⟩ := hok
  obtain ⟨fn, hfn, hfp⟩ := List.any_eq_true.mp hany
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hfp
  exact LibEv.sortPredFun_evC_withHooks H coreOK fnFun_clauses.1 (Semantics.fnsNoExs_of_all fnFun_clauses.2.1)
    (fun fn hfn cl hcl hw => absurd hw (by rw [fnFun_noWitH H fn hfn cl hcl]; decide)) hfn hfp.2 ad hfp.1 hsv

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

theorem idem_pattern : U.ax410.ax.pattern = .equals (srtOf c Srt.set) KoreAML.R (symApp c setConcat [kVar, kVar]) kVar := by
  decide +kernel
theorem idem_trS : (trS U.ax410).pat = (trAxiom [] [] U.ax410).pat := by decide +kernel

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
theorem idem_vars : (U.ax410.ax.sortVars.map KoreAML.sortVarKey ++ KoreAML.freeOf [] U.ax410.ax.pattern).eraseDups =
    [.sortVar "R", .evar "K" (KoreAML.srt "Set")] := by decide +kernel
theorem idem_sort : KoreAML.sortOf [] U.ax410.ax.pattern = some KoreAML.R := by decide +kernel
theorem symApp_withHooks (f : Sym) (ps : List Kore.Pattern) : symApp (cH H) f ps = symApp c f ps := rfl

/-- **Sentence 410 is refuted, for every H**: Γ with it has no model. At `K = SetItem(0)` the
sentence says `_Set_(K, K)` denotes `K`'s element, and `ΓDomains` (the hook's graph, the two sets
sharing a member) says it denotes nothing. -/
theorem idem_refuted : ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M),
    I ⊧ᴵP Γ (cH H) → ¬ (I ⊧ᴵ (trS U.ax410).pat) := by
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
  let tbl : KoreAML.VarTable := KoreAML.tableOf U.ax410.ax.sortVars U.ax410.ax.pattern
  let val : KoreAML.VarKey → M := fun
    | .sortVar _ => σS
    | _ => a
  let e' : Valuation M := valOf tbl val
  have hRmem : KoreAML.VarKey.sortVar "R" ∈ tbl := by decide +kernel
  have hKmem : KoreAML.VarKey.evar "K" (KoreAML.srt "Set") ∈ tbl := by decide +kernel
  have hRv : ∀ b, (KoreAML.trSort tbl KoreAML.R).interpret I e' b ↔ b = σS := fun b => by
    rw [trSort_R, KoreAML.interp_evar, valOf_ev hRmem]
  have hKv : e'.evalEvar (tbl.ev (.evar "K" (KoreAML.srt "Set"))) = a := valOf_ev hKmem
  have hg : ∀ k ∈ (U.ax410.ax.sortVars.map KoreAML.sortVarKey ++ KoreAML.freeOf [] U.ax410.ax.pattern).eraseDups,
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


/-! ## Library sample: sentence 556, `I -Int 0 = I` (a `simplification`), at values (Ev) -/

def vI : Kore.Pattern := KoreAML.ev "VarI" (KoreAML.srt "Int")
def kI : VarKey := .evar "VarI" (KoreAML.srt "Int")

theorem s166_trS : (trS U.ax556).pat = (trAxiom [] [] U.ax556).pat := by decide +kernel
theorem s166_pattern : U.ax556.ax.pattern = .implies KoreAML.R (.top KoreAML.R)
    (.equals (KoreAML.srt "Int") KoreAML.R (.app ⟨⟨"Lbl'Unds'-Int'Unds'"⟩⟩ [] [vI, .dv (KoreAML.srt "Int") "0"])
      (.and (KoreAML.srt "Int") [vI, .top (KoreAML.srt "Int")])) := by decide +kernel
theorem s166_free : (U.ax556.ax.sortVars.map sortVarKey ++ freeOf [] U.ax556.ax.pattern).eraseDups = [.sortVar "R", kI] := by
  decide +kernel
theorem s166_sortVars : U.ax556.ax.sortVars = [KoreAML.Rv] := by decide +kernel
theorem sub_name (H : HookParams) : (cH H).symName intSub = "Lbl'Unds'-Int'Unds'" ∧ iteSort? "Lbl'Unds'-Int'Unds'" = none :=
  (by decide +kernel : c.symName intSub = "Lbl'Unds'-Int'Unds'" ∧ iteSort? "Lbl'Unds'-Int'Unds'" = none)
theorem den_int0 (H : HookParams) : den (cH H) (KCore.int 0) = KoreAML.sym (.dv "0") ⬝ KoreAML.sym (.sort "SortInt") := by
  show den c (KCore.int 0) = _; decide +kernel
theorem int_numbered (H : HookParams) : Srt.int < nRegSorts + (cH H).sortNames.length :=
  (by decide +kernel : Srt.int < nRegSorts + c.sortNames.length)
theorem int_name (H : HookParams) : (cH H).sortName Srt.int = "Int" := (by decide +kernel : c.sortName Srt.int = "Int")

/-- **Sentence 556 holds at every value of `I`, in every model of Γ, for every H** (Ev): where `I`
denotes the element of the integer `n`, the translated sentence holds. From `ΓDomains`' graph of
`-Int` at `[n, 0]`, which is `n` for every `n`. -/
theorem lib166 (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hI : I ⊧ᴵP Γ (cH H))
    (n : Int) (e : Valuation M)
    (he : e.evalEvar ((tableOf U.ax556.ax.sortVars U.ax556.ax.pattern).ev kI) = elemOf (cH H) I (KCore.int n)) :
    Valuation.satifies I e (trS U.ax556).pat := by
  intro m
  rw [s166_trS]
  haveI : OvlOK (cH H) := ovlOK_of_core (coreOKH H)
  have hD := defOK hI
  have hc := sat_sigItem hI (sig_ceilDef (c := cH H))
  unfold trAxiom
  dsimp only
  rw [s166_free]
  generalize ht : tableOf U.ax556.ax.sortVars U.ax556.ax.pattern = t at he ⊢
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
/-- **Sentence 556 is entailed at values** (`EntailsAtValues`, direction Ev), for every H: a
valuation that sends the sentence's one free variable to a value's element sends it to an
integer's, where `lib166` gives the sentence. -/
theorem lib166_at_values (H : HookParams) : EntailsAtValues (cH H) U.ax556 (trS U.ax556).pat := by
  intro M _ I hI e hat m
  obtain ⟨v, S, hS, hv, hden⟩ := hat "VarI" (KoreAML.srt "Int") (by decide +kernel)
  have hS' : S = Srt.int := int_of_name S hS
  subst hS'
  obtain ⟨n, rfl⟩ := shape_int shapesOK_c (by rw [← Semantics.sortOf_withHooks _ H noRaw]; exact hv)
  exact lib166 H hI n e (((elemOf_spec hI hv e).1 _).mp hden) m


end KCore.TieE6ParamFfi

#check @KCore.TieE6ParamFfi.noRaw
#check @KCore.TieE6ParamFfi.readsConfined_c
#check @KCore.TieE6ParamFfi.userAxioms_eq
#check @KCore.TieE6ParamFfi.coreOK
#check @KCore.TieE6ParamFfi.wf_defn
#check @KCore.TieE6ParamFfi.account
#check @KCore.TieE6ParamFfi.account_sizes
#check @KCore.TieE6ParamFfi.account_classes
#check @KCore.TieE6ParamFfi.account_absent
#check @KCore.TieE6ParamFfi.absent_closed
#check @KCore.TieE6ParamFfi.absent_proj_below_c
#check @KCore.TieE6ParamFfi.absent_proj_below
#check @KCore.TieE6ParamFfi.lists_in_account
#check @KCore.TieE6ParamFfi.consistent
#check @KCore.TieE6ParamFfi.fnFun_indices
#check @KCore.TieE6ParamFfi.fnFun_account
#check @KCore.TieE6ParamFfi.fnFun_checked
#check @KCore.TieE6ParamFfi.fnFun_trS
#check @KCore.TieE6ParamFfi.fnFun_at_values
#check @KCore.TieE6ParamFfi.fnFun_at_values_step
#check @KCore.TieE6ParamFfi.idem_refuted
#check @KCore.TieE6ParamFfi.lib166
#check @KCore.TieE6ParamFfi.lib166_at_values
#print axioms KCore.TieE6ParamFfi.noRaw
#print axioms KCore.TieE6ParamFfi.readsConfined_c
#print axioms KCore.TieE6ParamFfi.userAxioms_eq
#print axioms KCore.TieE6ParamFfi.coreOK
#print axioms KCore.TieE6ParamFfi.wf_defn
#print axioms KCore.TieE6ParamFfi.account
#print axioms KCore.TieE6ParamFfi.account_sizes
#print axioms KCore.TieE6ParamFfi.account_classes
#print axioms KCore.TieE6ParamFfi.account_absent
#print axioms KCore.TieE6ParamFfi.absent_closed
#print axioms KCore.TieE6ParamFfi.absent_proj_below_c
#print axioms KCore.TieE6ParamFfi.absent_proj_below
#print axioms KCore.TieE6ParamFfi.lists_in_account
#print axioms KCore.TieE6ParamFfi.consistent
#print axioms KCore.TieE6ParamFfi.fnFun_indices
#print axioms KCore.TieE6ParamFfi.fnFun_account
#print axioms KCore.TieE6ParamFfi.fnFun_checked
#print axioms KCore.TieE6ParamFfi.fnFun_trS
#print axioms KCore.TieE6ParamFfi.fnFun_at_values
#print axioms KCore.TieE6ParamFfi.fnFun_at_values_step
#print axioms KCore.TieE6ParamFfi.idem_refuted
#print axioms KCore.TieE6ParamFfi.lib166
#print axioms KCore.TieE6ParamFfi.lib166_at_values
