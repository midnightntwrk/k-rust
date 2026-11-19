/-
  The classes hooked functional, collection law and library on `f2-examples/silentflt.kompile.kore`
  (FLOAT, STRING, BYTES and SET imported, user module `SILENTFLT`), each sentence tied to the
  library's statement of it or listed with its reason, for every interpretation H or under the
  condition on H the statement names. Run from the package root:
  `lake env lean -j1 test/LibEvClassesFlt.lean`.

  The text has no account of all its sentences (no test/Tie file); the three classes are the tie's
  (KcoreSpec/TieDefs.lean `tieClasses`) on the library's sentences that test/LibProbe.lean puts in its
  rows 9, 15, 17 and 18:
  - hooked functional (`funIdx`, `funIntIdx`, `funSilentIdx`, 76): the `functional` sentence of an
    interpreted symbol (`hookSigs`) that applies only Γ's heads: LibProbe's 73 of row 9 over Γ, and
    the sentences of `Bool2String` (38), `freshInt` (120) and `isInfinite` (134), interpreted symbols
    the text declares without a `hook` attribute, which LibProbe's row 9 (a hooked declaration) does
    not take;
  - collection law (`lawIdx`, 9): associativity and the two units of `_List_`, `_Map_`, `_Set_`;
  - library (`libIdx`, 105): LibProbe's sentences of rows 17 (45) and 18 (66) over Γ, but for the six
    set-variable lemmas (196, 197, 198, 199, 200, 381: the `#Ceil` lemmas of `%Int`, `/Int`, `<<Int`,
    `>>Int`, `modInt` and of `_Map_`, of the class set-variable lemma, refuted at sets of values:
    test/LibEvRefutedFlt.lean).
  `classes_over`: every sentence of the three classes applies only Γ's heads (`appHeadsOf`,
  `gammaHasHead`). `absent_lacks`: the 31 other sentences of LibProbe's rows 9, 17 and 18 each apply a
  head Γ lacks, so they are of the no-direction class (`absentIdx`; the reason for each is recorded
  in test/LibEvDeclsFlt.lean, test/LibEvStrFlt.lean or below). Set idempotence (87) is its own class,
  refuted (test/LibEvRefutedFlt.lean `idem_refuted`).

  Hooked functional, `LibEv.functional_ev` (one kernel decision per list):
  - `fun_entailed`: the 63 sentences of symbols that are not partial, for every H;
  - `funInt_entailed`: `exponentBitsFloat` (117), `precisionFloat` (159), of `floatResInt`, for every
    H (`floatShapeOK`, from `coreOK`);
  - `funSilent_entailed`: the eleven sentences of symbols of `totalSilentKeys` (25, 44, 103, 108, 113, 119, 134, 143, 162, 172, 173), for
    every H meeting `silentTotal`. test/LibEvFloatFlt.lean states the seven FLOAT ones one by one too.
  Collection law: `laws_entailed`, for every H (LibEvLaw.lean).

  Library (`lib_partition`, the class's 105 in five lists):
  - `libHere` (82): test/LibEvLibFlt.lean `lib_entailed`, `set_entailed`, `lib_indices`, for every H;
  - `libStr` (17): test/LibEvStrFlt.lean, `evN` for each N, for every H;
  - `libCond` (4), under a condition on H that `HookParams.lib` meets: 254 (domains.md 1648,
    `neFloatEq`) and 321 (1673, `isInfiniteEq`), test/LibEvFloatFlt.lean `ev254`, `ev321`; 374 (1917,
    `replaceAllEq`) and 377 (1893, `rfindCharEq`), test/LibEvStrFlt.lean `ev374`, `ev377`, under
    `Semantics.libAdmitted`;
  - `libOwise` (1): 373 (1915), test/LibEvFnOwiseFlt.lean `ev373`, for every H;
  - `libLeft` (1): 294 (`countAllOccurrences`' second equation, 1898), not tied: at the empty needle
    its sides agree exactly where the interpretation gives the count no value
    (test/LibEvStrFlt.lean `count294_none`, `count294_not_holds`), so it holds under no interpretation
    meeting `silentTotal` and Γ does not refute it either.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.LibEvClassesFlt

open KCore ML Faithful KoreAML

kore_term kore from "f2-examples/silentflt.kompile.kore"
definition_of defn from "f2-examples/silentflt.kompile.kore"
user_axioms U from "f2-examples/silentflt.kompile.kore" module "SILENTFLT"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

/-- `tr s`: the item `Theory.ofDefinition kore` holds for the sentence. -/
noncomputable def trS (ad : AxiomDecl) : Item := trAxiom kore.symbolDecls kore.aliasNames ad

theorem coreOK : c.coreOK = true := by decide_cheap
theorem coreOKH (H : HookParams) : (cH H).coreOK = true := (Semantics.coreOK_withHooks c H).trans coreOK
theorem shapesOKH (H : HookParams) : (cH H).shapesOK = true := (by decide +kernel : c.shapesOK = true)
theorem floatShapeOKH (H : HookParams) : (cH H).floatShapeOK = true := floatShapeOK_of_coreOK (coreOKH H)

/-! ## The classes -/

/-- Hooked functional: the sentences of symbols that are not partial. -/
def funIdx : List Nat :=
  [26, 27, 28, 29, 38, 40, 46, 47, 48, 49, 50, 51, 52, 55, 56, 57, 58, 59, 61, 63, 64, 65, 66, 67,
   68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 82, 90, 91, 92, 93, 94, 95, 96, 97, 98, 100, 102,
   104, 120, 124, 149, 150, 152, 154, 155, 158, 160, 161, 163, 164, 169, 170, 171]

/-- Hooked functional: the sentences of symbols of `floatResInt`. -/
def funIntIdx : List Nat := [117, 159]

/-- Hooked functional: the sentences of symbols of `totalSilentKeys`. -/
def funSilentIdx : List Nat :=
  [25, 44, 103, 108, 113, 119, 134, 143, 162, 172, 173]

/-- Collection law. -/
def lawIdx : List Nat := [79, 80, 81, 83, 84, 85, 86, 88, 89]

/-- Library, in five lists by where each is tied. -/
def libHere : List Nat :=
  [201, 202, 203, 204, 205, 206, 207, 208, 213, 214, 215, 216, 219, 220, 221, 222, 235, 237, 238,
   239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 253, 255, 256, 258, 259, 262,
   263, 265, 266, 267, 268, 269, 270, 271, 272, 273, 275, 276, 277, 278, 279, 280, 281, 282, 283,
   284, 285, 286, 287, 288, 289, 290, 291, 292, 293, 298, 347, 348, 349, 350, 371, 379, 209, 210,
   211, 212, 217, 218, 223, 224]
def libStr : List Nat :=
  [194, 195, 226, 227, 233, 234, 252, 257, 260, 261, 264, 295, 297, 372, 375, 376, 378]
def libCond : List Nat := [254, 321, 374, 377]
def libOwise : List Nat := [373]
def libLeft : List Nat := [294]

/-- Library. -/
def libIdx : List Nat :=
  [194, 195, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217,
   218, 219, 220, 221, 222, 223, 224, 226, 227, 233, 234, 235, 237, 238, 239, 240, 241, 242, 243,
   244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 256, 257, 258, 259, 260, 261, 262,
   263, 264, 265, 266, 267, 268, 269, 270, 271, 272, 273, 275, 276, 277, 278, 279, 280, 281, 282,
   283, 284, 285, 286, 287, 288, 289, 290, 291, 292, 293, 294, 295, 297, 298, 321, 347, 348, 349,
   350, 371, 372, 373, 374, 375, 376, 377, 378, 379]

/-- The sentences of LibProbe's rows 9, 17 and 18 that apply a head Γ lacks. -/
def absentIdx : List Nat :=
  [39, 41, 42, 43, 53, 54, 60, 62, 99, 101, 105, 112, 116, 118, 148, 151, 165, 168, 175, 176, 228,
   229, 230, 231, 232, 236, 274, 296, 345, 346, 380]

/-- **The library class is the five lists**, each sentence in one of them once. -/
theorem lib_partition : (libHere ++ libStr ++ libCond ++ libOwise ++ libLeft).isPerm libIdx = true ∧
    libIdx.Nodup := by
  decide +kernel

/-- The class sizes. -/
theorem class_sizes : (funIdx ++ funIntIdx ++ funSilentIdx).length = 76 ∧ lawIdx.length = 9 ∧
    libIdx.length = 105 ∧ absentIdx.length = 31 ∧
    (funIdx ++ funIntIdx ++ funSilentIdx ++ lawIdx ++ libIdx ++ absentIdx).Nodup := by
  decide +kernel

/-- Γ's heads (`gammaHeads c`) as a literal, so that the decisions below compute them once. -/
def gHeads : List (String × List Kore.KSort) :=
  [("kseq", []),
   ("dotk", []),
   ("LbllittleEndianBytes", []),
   ("LblbigEndianBytes", []),
   ("LblsignedBytes", []),
   ("LblunsignedBytes", []),
   ("Lbl'-LT-'generatedTop'-GT-'", []),
   ("Lbl'-LT-'generatedTop'-GT-'-fragment", []),
   ("Lbl'-LT-'k'-GT-'", []),
   ("LblnoKCell", []),
   ("Lbl'-LT-'generatedCounter'-GT-'", []),
   ("LblnoGeneratedCounterCell", []),
   ("Lblcheck", []),
   ("Lbldone", []),
   ("Lblfv", []),
   ("LblisK", []),
   ("LblisKItem", []),
   ("LblisKConfigVar", []),
   ("LblisMap", []),
   ("LblisSet", []),
   ("LblisList", []),
   ("LblisBool", []),
   ("LblisInt", []),
   ("LblisFloat", []),
   ("LblisString", []),
   ("LblisBytes", []),
   ("LblisEndianness", []),
   ("LblisSignedness", []),
   ("LblisGeneratedTopCell", []),
   ("LblisGeneratedTopCellFragment", []),
   ("LblisKCell", []),
   ("LblisKCellOpt", []),
   ("LblisGeneratedCounterCell", []),
   ("LblisGeneratedCounterCellOpt", []),
   ("LblisVal", []),
   ("LblisCmd", []),
   ("LblnotBool'Unds'", []),
   ("Lbl'Unds'andBool'Unds'", []),
   ("Lbl'Unds'andThenBool'Unds'", []),
   ("Lbl'Unds'orBool'Unds'", []),
   ("Lbl'Unds'orElseBool'Unds'", []),
   ("Lbl'Unds'xorBool'Unds'", []),
   ("Lbl'Unds'impliesBool'Unds'", []),
   ("Lbl'UndsEqlsEqls'Bool'Unds'", []),
   ("Lbl'UndsEqlsSlshEqls'Bool'Unds'", []),
   ("Lbl'UndsPlus'Int'Unds'", []),
   ("Lbl'Unds'-Int'Unds'", []),
   ("Lbl'UndsStar'Int'Unds'", []),
   ("Lbl'UndsSlsh'Int'Unds'", []),
   ("Lbl'UndsPerc'Int'Unds'", []),
   ("Lbl'Unds'divInt'Unds'", []),
   ("Lbl'Unds'modInt'Unds'", []),
   ("LblminInt'LParUndsCommUndsRParUnds'INT-COMMON'Unds'Int'Unds'Int'Unds'Int", []),
   ("LblmaxInt'LParUndsCommUndsRParUnds'INT-COMMON'Unds'Int'Unds'Int'Unds'Int", []),
   ("Lbl'Unds-LT-'Int'Unds'", []),
   ("Lbl'Unds-LT-Eqls'Int'Unds'", []),
   ("Lbl'Unds-GT-'Int'Unds'", []),
   ("Lbl'Unds-GT-Eqls'Int'Unds'", []),
   ("Lbl'UndsEqlsEqls'Int'Unds'", []),
   ("Lbl'UndsEqlsSlshEqls'Int'Unds'", []),
   ("LblabsInt'LParUndsRParUnds'INT-COMMON'Unds'Int'Unds'Int", []),
   ("LblfreshInt'LParUndsRParUnds'INT'Unds'Int'Unds'Int", []),
   ("Lbl'Unds-GT--GT-'Int'Unds'", []),
   ("Lbl'Unds-LT--LT-'Int'Unds'", []),
   ("Lbllog2Int'LParUndsRParUnds'INT-COMMON'Unds'Int'Unds'Int", []),
   ("Lbl'UndsXor-Perc'Int'UndsUnds'", []),
   ("LblbitRangeInt'LParUndsCommUndsCommUndsRParUnds'INT-COMMON'Unds'Int'Unds'Int'Unds'Int'Unds'Int", []),
   ("LblsignExtendBitRangeInt'LParUndsCommUndsCommUndsRParUnds'INT-COMMON'Unds'Int'Unds'Int'Unds'Int'Unds'Int", []),
   ("Lbl'UndsXor-'Int'Unds'", []),
   ("Lbl'UndsEqlsEqls'K'Unds'", []),
   ("Lbl'UndsEqlsSlshEqls'K'Unds'", []),
   ("Lbl'Stop'Map", []),
   ("Lbl'UndsPipe'-'-GT-Unds'", []),
   ("Lbl'Unds'Map'Unds'", []),
   ("LblMap'Coln'update", []),
   ("Lbl'UndsLSqBUnds-LT-'-undef'RSqB'", []),
   ("LblMap'Coln'lookup", []),
   ("LblMap'Coln'lookupOrDefault", []),
   ("Lbl'Unds'in'Unds'keys'LParUndsRParUnds'MAP'Unds'Bool'Unds'KItem'Unds'Map", []),
   ("LblsizeMap", []),
   ("LblremoveAll'LParUndsCommUndsRParUnds'MAP'Unds'Map'Unds'Map'Unds'Set", []),
   ("Lblkeys'LParUndsRParUnds'MAP'Unds'Set'Unds'Map", []),
   ("Lbl'Stop'Set", []),
   ("LblSetItem", []),
   ("Lbl'Unds'Set'Unds'", []),
   ("Lbl'UndsPipe'Set'UndsUnds'SET'Unds'Set'Unds'Set'Unds'Set", []),
   ("LblintersectSet'LParUndsCommUndsRParUnds'SET'Unds'Set'Unds'Set'Unds'Set", []),
   ("LblSet'Coln'difference", []),
   ("LblSet'Coln'in", []),
   ("Lbl'Unds-LT-Eqls'Set'UndsUnds'SET'Unds'Bool'Unds'Set'Unds'Set", []),
   ("Lblsize'LParUndsRParUnds'SET'Unds'Int'Unds'Set", []),
   ("Lbl'Unds'List'Unds'", []),
   ("Lbl'Stop'List", []),
   ("LblListItem", []),
   ("LblpushList", []),
   ("LblList'Coln'get", []),
   ("LblList'Coln'range", []),
   ("Lbl'Unds'inList'Unds'", []),
   ("LblsizeList", []),
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
   ("Lblite", []),
   ("Lbl'Stop'RangeMap", []),
   ("Lbl'Unds'r'Pipe'-'-GT-Unds'", []),
   ("Lbl'Unds'RangeMap'Unds'", []),
   ("LblRangeMap'Coln'lookup", []),
   ("LblRangeMap'Coln'lookupOrDefault", []),
   ("LblRangeMap'Coln'find'Unds'range", []),
   ("LblRangeMap'Coln'update", []),
   ("Lbl'Unds'r'LSqBUnds-LT-'-undef'RSqB'", []),
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
   ("inj", [.ctor ⟨⟨"SortVal"⟩⟩ [], .ctor ⟨⟨"SortKItem"⟩⟩ []]),
   ("inj", [.ctor ⟨⟨"SortCmd"⟩⟩ [], .ctor ⟨⟨"SortKItem"⟩⟩ []])]

theorem gHeads_eq : gammaHeads c = gHeads := by decide +kernel

/-- `gammaHasHead c` read from the literal. -/
theorem gammaHasHead_eq : gammaHasHead c = fun h => gHeads.any fun g => decide (g = h) := by
  funext h; unfold gammaHasHead; rw [gHeads_eq]

/-- **Every sentence of the three classes applies only Γ's heads**, each a head with its sort
arguments among Γ's (`gammaHeads`). -/
theorem classes_over :
    (U.all.filter fun ad => (funIdx ++ funIntIdx ++ funSilentIdx ++ lawIdx ++ libIdx).contains ad.index).all
      (fun ad => (appHeadsOf ad.ax.pattern).all (gammaHasHead c)) = true := by
  rw [gammaHasHead_eq]; decide +kernel

/-- **Each sentence of `absentIdx` applies a head Γ lacks**: it is of the no-direction class. -/
theorem absent_lacks :
    (U.all.filter fun ad => absentIdx.contains ad.index).all
      (fun ad => !(appHeadsOf ad.ax.pattern).all (gammaHasHead c)) = true := by
  rw [gammaHasHead_eq]; decide +kernel

/-- The lists name sentences of the text: every index is a user axiom's. -/
theorem lists_in_text :
    (funIdx ++ funIntIdx ++ funSilentIdx ++ lawIdx ++ libIdx ++ absentIdx).all
      (fun i => U.all.any (·.index == i)) = true := by
  decide +kernel

/-! ## Hooked functional (76) -/

/-- The name of the symbol a sentence of the form `\exists{R}(Val, \equals{s, R}(Val, f(…)))`
applies. -/
def headOf : Kore.Pattern → Option String
  | .exist _ _ (.equals _ _ _ (.app h _ _)) => some h.ident.name
  | _ => none

/-- The signature of the interpreted symbol with the name of the sentence's symbol. -/
def sigOf (ad : AxiomDecl) : Option KCore.CtorSig :=
  (headOf ad.ax.pattern).bind fun n => hookSigs.find? fun k => regSymNames.getD k.name "" == n

/-- The sentence is the `functional` sentence of a symbol of `hookSigs` meeting `p`, over the one
sort variable `R`. -/
def funOKBy (p : CtorSig → Bool) (ad : AxiomDecl) : Bool :=
  match sigOf ad with
  | some k => decide (ad.ax.pattern = LibEv.funPatR k) && decide (ad.ax.sortVars = [Rv]) && LibEv.funReg k && p k
  | none => false

noncomputable def funText : List AxiomDecl := U.all.filter fun ad => funIdx.contains ad.index
noncomputable def funIntText : List AxiomDecl := U.all.filter fun ad => funIntIdx.contains ad.index
noncomputable def funSilentText : List AxiomDecl := U.all.filter fun ad => funSilentIdx.contains ad.index

theorem fun_indices : (funText ++ funIntText ++ funSilentText).map (·.index) =
    funIdx ++ funIntIdx ++ funSilentIdx := by
  decide +kernel

theorem fun_checked : funText.all (funOKBy fun k => !partialHooks.contains k.name) = true := by decide +kernel
theorem funInt_checked : funIntText.all (funOKBy fun k => floatResInt.contains k.name) = true := by decide +kernel
theorem funSilent_checked : funSilentText.all (funOKBy fun k => totalSilentKeys.contains k.name) = true := by
  decide +kernel

/-- None of the 76 reads a declaration or an alias. -/
theorem fun_trS : (funText ++ funIntText ++ funSilentText).all
    (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat)) = true := by
  decide +kernel

/-- From `funOKBy p`: the signature, the pattern, the sort variables, `funReg` and `p`. -/
theorem funOKBy_sig {p : CtorSig → Bool} {ad : AxiomDecl} (h : funOKBy p ad = true) :
    ∃ k ∈ hookSigs, ad.ax.pattern = LibEv.funPatR k ∧ ad.ax.sortVars = [Rv] ∧ LibEv.funReg k = true ∧
      p k = true := by
  unfold funOKBy at h
  cases hsig : sigOf ad with
  | none => rw [hsig] at h; cases h
  | some k =>
    rw [hsig] at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨hp, hsv⟩, hreg⟩, hk⟩ := h
    obtain ⟨n, -, hfind⟩ := Option.bind_eq_some_iff.mp hsig
    exact ⟨k, List.mem_of_find?_eq_some hfind, hp, hsv, hreg, hk⟩

theorem trS_of {ad : AxiomDecl} (had : ad ∈ funText ++ funIntText ++ funSilentText) :
    (trS ad).pat = (trAxiom [] [] ad).pat :=
  of_decide_eq_true (List.all_eq_true.mp fun_trS ad had)

/-- **Ev for the `functional` sentences of the symbols that are not partial**, for every H. -/
theorem fun_entailed (H : HookParams) : ∀ ad ∈ funText, EntailsAtValues (cH H) ad (trS ad).pat := by
  intro ad had
  rw [trS_of (List.mem_append_left _ (List.mem_append_left _ had))]
  obtain ⟨k, hk, hp, hsv, hreg, hpar⟩ := funOKBy_sig (List.all_eq_true.mp fun_checked ad had)
  exact LibEv.functional_ev (coreOKH H) (shapesOKH H) hk (Or.inl (by simpa using hpar)) hreg ad hp hsv

/-- **Ev for the `functional` sentences of `floatResInt`'s symbols**, for every H. -/
theorem funInt_entailed (H : HookParams) : ∀ ad ∈ funIntText, EntailsAtValues (cH H) ad (trS ad).pat := by
  intro ad had
  rw [trS_of (List.mem_append_left _ (List.mem_append_right _ had))]
  obtain ⟨k, hk, hp, hsv, hreg, hf⟩ := funOKBy_sig (List.all_eq_true.mp funInt_checked ad had)
  exact LibEv.functional_ev (coreOKH H) (shapesOKH H) hk
    (Or.inr (Or.inr ⟨List.contains_iff_mem.mp hf, floatShapeOKH H⟩)) hreg ad hp hsv

/-- **Ev for the `functional` sentences of `totalSilentKeys`' symbols**, for every H meeting
`silentTotal`. -/
theorem funSilent_entailed (H : HookParams) (hst : (cH H).silentTotal) :
    ∀ ad ∈ funSilentText, EntailsAtValues (cH H) ad (trS ad).pat := by
  intro ad had
  rw [trS_of (List.mem_append_right _ had)]
  obtain ⟨k, hk, hp, hsv, hreg, hs⟩ := funOKBy_sig (List.all_eq_true.mp funSilent_checked ad had)
  exact LibEv.functional_ev (coreOKH H) (shapesOKH H) hk
    (Or.inr (Or.inl ⟨List.contains_iff_mem.mp hs, hst⟩)) hreg ad hp hsv

/-! ## Collection laws (9) -/

theorem law79 (H : HookParams) : EntailsAtValues (cH H) U.ax79 (trS U.ax79).pat := by
  rw [(by decide +kernel : (trS U.ax79).pat = (trAxiom [] [] U.ax79).pat)]
  exact LibEv.listAssoc_ev (coreOKH H) (shapesOKH H) U.ax79 (by decide +kernel) (by decide +kernel)
theorem law80 (H : HookParams) : EntailsAtValues (cH H) U.ax80 (trS U.ax80).pat := by
  rw [(by decide +kernel : (trS U.ax80).pat = (trAxiom [] [] U.ax80).pat)]
  exact LibEv.listUnitR_ev (coreOKH H) (shapesOKH H) U.ax80 (by decide +kernel) (by decide +kernel)
theorem law81 (H : HookParams) : EntailsAtValues (cH H) U.ax81 (trS U.ax81).pat := by
  rw [(by decide +kernel : (trS U.ax81).pat = (trAxiom [] [] U.ax81).pat)]
  exact LibEv.listUnitL_ev (coreOKH H) (shapesOKH H) U.ax81 (by decide +kernel) (by decide +kernel)
theorem law83 (H : HookParams) : EntailsAtValues (cH H) U.ax83 (trS U.ax83).pat := by
  rw [(by decide +kernel : (trS U.ax83).pat = (trAxiom [] [] U.ax83).pat)]
  exact LibEv.mapAssoc_ev (coreOKH H) (shapesOKH H) U.ax83 (by decide +kernel) (by decide +kernel)
theorem law84 (H : HookParams) : EntailsAtValues (cH H) U.ax84 (trS U.ax84).pat := by
  rw [(by decide +kernel : (trS U.ax84).pat = (trAxiom [] [] U.ax84).pat)]
  exact LibEv.mapUnitR_ev (coreOKH H) (shapesOKH H) U.ax84 (by decide +kernel) (by decide +kernel)
theorem law85 (H : HookParams) : EntailsAtValues (cH H) U.ax85 (trS U.ax85).pat := by
  rw [(by decide +kernel : (trS U.ax85).pat = (trAxiom [] [] U.ax85).pat)]
  exact LibEv.mapUnitL_ev (coreOKH H) (shapesOKH H) U.ax85 (by decide +kernel) (by decide +kernel)
theorem law86 (H : HookParams) : EntailsAtValues (cH H) U.ax86 (trS U.ax86).pat := by
  rw [(by decide +kernel : (trS U.ax86).pat = (trAxiom [] [] U.ax86).pat)]
  exact LibEv.setAssoc_ev (coreOKH H) (shapesOKH H) U.ax86 (by decide +kernel) (by decide +kernel)
theorem law88 (H : HookParams) : EntailsAtValues (cH H) U.ax88 (trS U.ax88).pat := by
  rw [(by decide +kernel : (trS U.ax88).pat = (trAxiom [] [] U.ax88).pat)]
  exact LibEv.setUnitR_ev (coreOKH H) (shapesOKH H) U.ax88 (by decide +kernel) (by decide +kernel)
theorem law89 (H : HookParams) : EntailsAtValues (cH H) U.ax89 (trS U.ax89).pat := by
  rw [(by decide +kernel : (trS U.ax89).pat = (trAxiom [] [] U.ax89).pat)]
  exact LibEv.setUnitL_ev (coreOKH H) (shapesOKH H) U.ax89 (by decide +kernel) (by decide +kernel)

/-- The nine collection laws of the text. -/
noncomputable def lawText : List AxiomDecl :=
  [U.ax79, U.ax80, U.ax81, U.ax83, U.ax84, U.ax85, U.ax86, U.ax88, U.ax89]

theorem law_indices : lawText.map (·.index) = lawIdx := by decide +kernel

/-- **Ev for the collection laws**, for every H. -/
theorem laws_entailed (H : HookParams) : ∀ ad ∈ lawText, EntailsAtValues (cH H) ad (trS ad).pat :=
  List.forall_mem_cons.mpr ⟨law79 H, List.forall_mem_cons.mpr ⟨law80 H, List.forall_mem_cons.mpr ⟨law81 H, List.forall_mem_cons.mpr ⟨law83 H, List.forall_mem_cons.mpr ⟨law84 H, List.forall_mem_cons.mpr ⟨law85 H, List.forall_mem_cons.mpr ⟨law86 H, List.forall_mem_cons.mpr ⟨law88 H, List.forall_mem_cons.mpr ⟨law89 H, fun _ h => nomatch h⟩⟩⟩⟩⟩⟩⟩⟩⟩

end KCore.LibEvClassesFlt

/-- info: 'KCore.LibEvClassesFlt.fun_entailed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvClassesFlt.fun_entailed
/-- info: 'KCore.LibEvClassesFlt.funInt_entailed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvClassesFlt.funInt_entailed
/-- info: 'KCore.LibEvClassesFlt.funSilent_entailed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvClassesFlt.funSilent_entailed
/-- info: 'KCore.LibEvClassesFlt.laws_entailed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvClassesFlt.laws_entailed
