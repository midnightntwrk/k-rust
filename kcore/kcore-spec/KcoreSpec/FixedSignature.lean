/-
  KCore (KCORE-SPEC.md §2). The fixed vocabulary of a definition. Frozen layer; imports only the
  library's added names (BuiltinNames.lean).

  **Symbols and sorts are numbers** (ARCHITECTURE.md §8). A sort is a `Srt` and a symbol a
  `Sym`, both natural numbers: the kernel compares numbers natively and strings character by
  character (findings/R1-scale.md). The numbers below `nRegSorts` and `nRegSyms` are the
  **registry**: every sort and symbol the builtin library's modules declare (Builtins.lean), and
  the generated cells', each with a fixed number and its KORE name (`regSortNames`, `regSymNames`).
  The first 21 sorts and 173 symbols are named here, since Hooks.lean and the generic theorems
  read them; the rest are the library's (BuiltinNames.lean). A definition holds the builtins of the
  modules it imports (`Semantics.lib`, and their parameter symbols), and its own sorts and symbols
  are numbered after the registry (Core.lean). No decision and no part of `Step` reads a name;
  names are read only to print the KORE (`emit`) and to translate to matching logic
  (Statements.lean).

  Besides the registry:
  - **the builtin library a definition imports** (`Lib`): the sorts, subsorts and constructors its
    builtin modules declare. They are part of the semantics, not of the presentation: they decide
    which ground terms are values (`#EOF`, `inj{Int,IOInt}(5)`, an `Id` token) and which sorts lie
    below KItem. `wf` checks it is the union of the imported modules' (Builtins.lean).
  - **token sorts** (`Lib.tokenSorts`): sorts whose domain values are their literal strings,
    distinct literals denoting distinct elements: `Id` and `String`; and **byte sorts**
    (`Lib.byteSorts`, `Bytes`), whose values are the literals of characters below 256, one per
    byte.
  - the interpreted Set symbols and `removeAll` (Hooks.lean gives their meaning).
-/
import KcoreSpec.BuiltinNames

set_option autoImplicit false

namespace KCore

/-- A sort: a registry number, or one of the definition's own sorts (Core.lean). -/
abbrev Srt := Nat
/-- A symbol: a registry number, or one of the definition's own symbols (Core.lean). -/
abbrev Sym := Nat

/-! ## The registry's sorts -/

namespace Srt
@[match_pattern, reducible] def k : Srt := 0
@[match_pattern, reducible] def kitem : Srt := 1
@[match_pattern, reducible] def bool : Srt := 2
@[match_pattern, reducible] def int : Srt := 3
@[match_pattern, reducible] def kconfigVar : Srt := 4
@[match_pattern, reducible] def list : Srt := 5
@[match_pattern, reducible] def map : Srt := 6
@[match_pattern, reducible] def set : Srt := 7
@[match_pattern, reducible] def mint : Srt := 8
@[match_pattern, reducible] def ident : Srt := 9
@[match_pattern, reducible] def string : Srt := 10
@[match_pattern, reducible] def float : Srt := 11
@[match_pattern, reducible] def ioError : Srt := 12
@[match_pattern, reducible] def ioFile : Srt := 13
@[match_pattern, reducible] def ioInt : Srt := 14
@[match_pattern, reducible] def ioString : Srt := 15
@[match_pattern, reducible] def stream : Srt := 16
@[match_pattern, reducible] def top : Srt := 17
@[match_pattern, reducible] def topFrag : Srt := 18
@[match_pattern, reducible] def counter : Srt := 19
@[match_pattern, reducible] def counterOpt : Srt := 20
/-- BYTES' sorts: library sorts with fixed numbers (BuiltinNames.lean). -/
@[match_pattern, reducible] def bytes : Srt := 21
@[match_pattern, reducible] def endianness : Srt := 22
@[match_pattern, reducible] def signedness : Srt := 23
/-- RANGEMAP's sorts: library sorts with fixed numbers (BuiltinNames.lean). -/
@[match_pattern, reducible] def range : Srt := 28
@[match_pattern, reducible] def rangeMap : Srt := 29
end Srt

/-- The number of registry sorts; a definition's own sorts are numbered from here. -/
def nRegSorts : Nat := 21 + BuiltinNames.nNewSorts

/-- The KORE names of the registry sorts (without `Sort`), by number. -/
def regSortNames : List String :=
  ["K", "KItem", "Bool", "Int", "KConfigVar", "List", "Map", "Set", "MInt", "Id", "String", "Float", "IOError", "IOFile", "IOInt", "IOString", "Stream", "GeneratedTopCell", "GeneratedTopCellFragment", "GeneratedCounterCell", "GeneratedCounterCellOpt"] ++
  BuiltinNames.newSortNames

/-- The hooked or token sorts, with their number of sort parameters. -/
def baseSorts : List (Srt × Nat) :=
  [(Srt.bool, 0), (Srt.int, 0), (Srt.kconfigVar, 0), (Srt.list, 0), (Srt.mint, 1), (Srt.map, 0), (Srt.set, 0)]

/-- The base sorts below KItem (all but the parametric MInt). -/
def baseSortsBelowKItem : List Srt := [Srt.bool, Srt.int, Srt.kconfigVar, Srt.list, Srt.map, Srt.set]

/-- The configuration sort. -/
@[match_pattern, reducible] def topCellSort : Srt := Srt.top

/-- A constructor or a hooked symbol: symbol, argument sorts, result sort. -/
structure CtorSig where
  name : Sym
  args : List Srt
  result : Srt
  deriving Repr, DecidableEq, Inhabited

/-! ## The registry's symbols -/

@[match_pattern, reducible] def kseq : Sym := 0
@[match_pattern, reducible] def dotk : Sym := 1
@[match_pattern, reducible] def kconfigValue : Sym := 2
@[match_pattern, reducible] def boolNot : Sym := 3
@[match_pattern, reducible] def boolAnd : Sym := 4
@[match_pattern, reducible] def boolAndThen : Sym := 5
@[match_pattern, reducible] def boolOr : Sym := 6
@[match_pattern, reducible] def boolOrElse : Sym := 7
@[match_pattern, reducible] def boolXor : Sym := 8
@[match_pattern, reducible] def boolImplies : Sym := 9
@[match_pattern, reducible] def boolEq : Sym := 10
@[match_pattern, reducible] def boolNe : Sym := 11
@[match_pattern, reducible] def intAdd : Sym := 12
@[match_pattern, reducible] def intSub : Sym := 13
@[match_pattern, reducible] def intMul : Sym := 14
@[match_pattern, reducible] def intTDiv : Sym := 15
@[match_pattern, reducible] def intTMod : Sym := 16
@[match_pattern, reducible] def intEDiv : Sym := 17
@[match_pattern, reducible] def intEMod : Sym := 18
@[match_pattern, reducible] def intLt : Sym := 19
@[match_pattern, reducible] def intLe : Sym := 20
@[match_pattern, reducible] def intGt : Sym := 21
@[match_pattern, reducible] def intGe : Sym := 22
@[match_pattern, reducible] def intEq : Sym := 23
@[match_pattern, reducible] def intNe : Sym := 24
@[match_pattern, reducible] def intMin : Sym := 25
@[match_pattern, reducible] def intMax : Sym := 26
@[match_pattern, reducible] def intAbs : Sym := 27
@[match_pattern, reducible] def freshInt : Sym := 28
/-- INT's `>>Int`, `<<Int` and `log2Int`: library symbols with fixed numbers (BuiltinNames.lean). -/
@[match_pattern, reducible] def intShr : Sym := 211
@[match_pattern, reducible] def intShl : Sym := 212
@[match_pattern, reducible] def intLog2 : Sym := 216
/-- INT's `^%Int`, `bitRangeInt` and `signExtendBitRangeInt`: library symbols with fixed numbers
(BuiltinNames.lean). -/
@[match_pattern, reducible] def intPowMod : Sym := 210
@[match_pattern, reducible] def intBitRange : Sym := 217
@[match_pattern, reducible] def intSignExtBitRange : Sym := 218
/-- INT's `^Int` and LIST's `L[I <- V]`, `makeList`, `updateList`, `fillList`: library symbols with
fixed numbers (BuiltinNames.lean). -/
@[match_pattern, reducible] def intPow : Sym := 209
@[match_pattern, reducible] def listSet : Sym := 199
@[match_pattern, reducible] def listMake : Sym := 200
@[match_pattern, reducible] def listUpdateAll : Sym := 201
@[match_pattern, reducible] def listFill : Sym := 202
@[match_pattern, reducible] def kEq : Sym := 29
@[match_pattern, reducible] def kNe : Sym := 30
@[match_pattern, reducible] def mapUnit : Sym := 31
@[match_pattern, reducible] def mapElem : Sym := 32
@[match_pattern, reducible] def mapConcat : Sym := 33
@[match_pattern, reducible] def mapUpdate : Sym := 34
@[match_pattern, reducible] def mapRemove : Sym := 35
@[match_pattern, reducible] def mapLookup : Sym := 36
@[match_pattern, reducible] def mapLookupOrDefault : Sym := 37
@[match_pattern, reducible] def mapInKeys : Sym := 38
@[match_pattern, reducible] def mapSize : Sym := 39
@[match_pattern, reducible] def mapRemoveAll : Sym := 40
@[match_pattern, reducible] def mapKeys : Sym := 41
@[match_pattern, reducible] def setUnit : Sym := 42
@[match_pattern, reducible] def setElem : Sym := 43
@[match_pattern, reducible] def setConcat : Sym := 44
@[match_pattern, reducible] def setUnion : Sym := 45
@[match_pattern, reducible] def setIntersect : Sym := 46
@[match_pattern, reducible] def setDifference : Sym := 47
@[match_pattern, reducible] def setIn : Sym := 48
@[match_pattern, reducible] def setInclusion : Sym := 49
@[match_pattern, reducible] def setSize : Sym := 50
/-- LIST's interpreted symbols: library symbols with fixed numbers (BuiltinNames.lean). -/
@[match_pattern, reducible] def listConcat : Sym := 194
@[match_pattern, reducible] def listUnit : Sym := 195
@[match_pattern, reducible] def listElem : Sym := 196
@[match_pattern, reducible] def listPush : Sym := 197
@[match_pattern, reducible] def listGet : Sym := 198
@[match_pattern, reducible] def listRange : Sym := 203
@[match_pattern, reducible] def listIn : Sym := 204
@[match_pattern, reducible] def listSize : Sym := 205
/-- FLOAT's interpreted symbols: library symbols with fixed numbers (BuiltinNames.lean). -/
@[match_pattern, reducible] def floatPrecision : Sym := 222
@[match_pattern, reducible] def floatExponentBits : Sym := 223
@[match_pattern, reducible] def floatIsNaN : Sym := 226
@[match_pattern, reducible] def floatIsInfinite : Sym := 227
@[match_pattern, reducible] def floatNeg : Sym := 228
@[match_pattern, reducible] def floatMul : Sym := 230
@[match_pattern, reducible] def floatDiv : Sym := 231
@[match_pattern, reducible] def floatRem : Sym := 232
@[match_pattern, reducible] def floatAdd : Sym := 233
@[match_pattern, reducible] def floatSub : Sym := 234
@[match_pattern, reducible] def floatAbs : Sym := 236
@[match_pattern, reducible] def floatRound : Sym := 237
@[match_pattern, reducible] def floatFloor : Sym := 238
@[match_pattern, reducible] def floatCeil : Sym := 239
@[match_pattern, reducible] def floatTrunc : Sym := 240
@[match_pattern, reducible] def floatSqrt : Sym := 252
@[match_pattern, reducible] def floatMaxValue : Sym := 253
@[match_pattern, reducible] def floatMinValue : Sym := 254
@[match_pattern, reducible] def floatLe : Sym := 255
@[match_pattern, reducible] def floatLt : Sym := 256
@[match_pattern, reducible] def floatGe : Sym := 257
@[match_pattern, reducible] def floatGt : Sym := 258
@[match_pattern, reducible] def floatEq : Sym := 259
@[match_pattern, reducible] def floatNe : Sym := 260
@[match_pattern, reducible] def int2Float : Sym := 261
/-- STRING's and BYTES' interpreted symbols and BYTES' constructors of Endianness and Signedness:
library symbols with fixed numbers (BuiltinNames.lean). -/
@[match_pattern, reducible] def stringConcat : Sym := 263
@[match_pattern, reducible] def stringLength : Sym := 264
@[match_pattern, reducible] def stringOrd : Sym := 266
@[match_pattern, reducible] def stringSubstr : Sym := 267
@[match_pattern, reducible] def stringFind : Sym := 268
@[match_pattern, reducible] def stringRfind : Sym := 269
@[match_pattern, reducible] def stringFindChar : Sym := 270
@[match_pattern, reducible] def stringRfindChar : Sym := 271
@[match_pattern, reducible] def string2Bool : Sym := 273
@[match_pattern, reducible] def string2Int : Sym := 277
@[match_pattern, reducible] def string2Base : Sym := 280
@[match_pattern, reducible] def stringReplaceAll : Sym := 281
@[match_pattern, reducible] def stringReplace : Sym := 282
@[match_pattern, reducible] def stringReplaceFirst : Sym := 283
@[match_pattern, reducible] def stringCountAll : Sym := 284
@[match_pattern, reducible] def stringEq : Sym := 285
@[match_pattern, reducible] def stringNe : Sym := 286
@[match_pattern, reducible] def stringLt : Sym := 287
@[match_pattern, reducible] def stringLe : Sym := 288
@[match_pattern, reducible] def stringGt : Sym := 289
@[match_pattern, reducible] def stringGe : Sym := 290
@[match_pattern, reducible] def littleEndianBytes : Sym := 300
@[match_pattern, reducible] def bigEndianBytes : Sym := 301
@[match_pattern, reducible] def signedBytes : Sym := 302
@[match_pattern, reducible] def unsignedBytes : Sym := 303
@[match_pattern, reducible] def bytes2Int : Sym := 304
@[match_pattern, reducible] def bytesUpdate : Sym := 310
@[match_pattern, reducible] def bytesGet : Sym := 311
@[match_pattern, reducible] def bytesSubstr : Sym := 312
@[match_pattern, reducible] def bytesReplaceAt : Sym := 313
@[match_pattern, reducible] def bytesMemset : Sym := 314
@[match_pattern, reducible] def bytesPadRight : Sym := 315
@[match_pattern, reducible] def bytesPadLeft : Sym := 316
@[match_pattern, reducible] def bytesReverse : Sym := 317
@[match_pattern, reducible] def bytesLength : Sym := 318
@[match_pattern, reducible] def bytesConcat : Sym := 319
@[match_pattern, reducible] def stringChr : Sym := 265
@[match_pattern, reducible] def bool2String : Sym := 272
@[match_pattern, reducible] def int2String : Sym := 278
@[match_pattern, reducible] def bytesEmpty : Sym := 299
@[match_pattern, reducible] def int2Bytes : Sym := 305
/-- RANGEMAP's constructor `RangeMap:Range` and its hooked symbols: library symbols with fixed
numbers (BuiltinNames.lean). -/
@[match_pattern, reducible] def rangeCtor : Sym := 356
@[match_pattern, reducible] def rmUnit : Sym := 357
@[match_pattern, reducible] def rmElem : Sym := 358
@[match_pattern, reducible] def rmConcat : Sym := 359
@[match_pattern, reducible] def rmLookup : Sym := 360
@[match_pattern, reducible] def rmLookupOrDefault : Sym := 361
@[match_pattern, reducible] def rmFindRange : Sym := 362
@[match_pattern, reducible] def rmUpdate : Sym := 363
@[match_pattern, reducible] def rmRemove : Sym := 364
@[match_pattern, reducible] def rmDifference : Sym := 365
@[match_pattern, reducible] def rmUpdateAll : Sym := 366
@[match_pattern, reducible] def rmRemoveAll : Sym := 367
@[match_pattern, reducible] def rmKeys : Sym := 368
@[match_pattern, reducible] def rmInKeys : Sym := 369
@[match_pattern, reducible] def rmSize : Sym := 370
@[match_pattern, reducible] def rmInclusion : Sym := 371
@[match_pattern, reducible] def rmChoice : Sym := 372
@[match_pattern, reducible] def rmKeysList : Sym := 373
@[match_pattern, reducible] def rmValues : Sym := 374
@[match_pattern, reducible] def isK : Sym := 51
@[match_pattern, reducible] def isKItem : Sym := 52
@[match_pattern, reducible] def topLabel : Sym := 71
@[match_pattern, reducible] def topFragLabel : Sym := 72
@[match_pattern, reducible] def counterLabel : Sym := 73
@[match_pattern, reducible] def noCounter : Sym := 74

/-- `#unboxKConfigValue` and the projections `project:X` of the registry sorts: builtin functions
with no meaning here (no clause, no hook). They occur only in the cells' initial values, which
`emit` writes and `Step` does not read; a rule that applies them is not well-formed. -/
@[match_pattern, reducible] def unboxKConfigValue : Sym := 151
/-- `project:X` of the registry sort X. -/
def projectSym (X : Srt) : Sym := 152 + X

/-- `ite`, K-EQUAL's `ite{S}(C, A, B)`: if C then A else B. The library's text declares it with a
sort parameter S, so it has no number of its own there; the registry numbers it after the
library's symbols, as a hook of signature `Bool, KItem, KItem → KItem`. A definition applies it
at a sort S through an own parameter symbol `ite{S}` of signature `Bool, S, S → S` that this hook
implements (Parse.lean, `iteName`). -/
@[match_pattern, reducible] def kIte : Sym := 379

theorem kIte_eq : kIte = 173 + BuiltinNames.nNewSyms := rfl

/-- The number of registry symbols; a definition's own symbols are numbered from here. -/
def nRegSyms : Nat := 173 + BuiltinNames.nNewSyms + 1

/-- The KORE names of the registry symbols, by number. -/
def regSymNames : List String :=
  ["kseq",
   "dotk",
   "Lbl'Hash'KConfigValue",
   "LblnotBool'Unds'",
   "Lbl'Unds'andBool'Unds'",
   "Lbl'Unds'andThenBool'Unds'",
   "Lbl'Unds'orBool'Unds'",
   "Lbl'Unds'orElseBool'Unds'",
   "Lbl'Unds'xorBool'Unds'",
   "Lbl'Unds'impliesBool'Unds'",
   "Lbl'UndsEqlsEqls'Bool'Unds'",
   "Lbl'UndsEqlsSlshEqls'Bool'Unds'",
   "Lbl'UndsPlus'Int'Unds'",
   "Lbl'Unds'-Int'Unds'",
   "Lbl'UndsStar'Int'Unds'",
   "Lbl'UndsSlsh'Int'Unds'",
   "Lbl'UndsPerc'Int'Unds'",
   "Lbl'Unds'divInt'Unds'",
   "Lbl'Unds'modInt'Unds'",
   "Lbl'Unds-LT-'Int'Unds'",
   "Lbl'Unds-LT-Eqls'Int'Unds'",
   "Lbl'Unds-GT-'Int'Unds'",
   "Lbl'Unds-GT-Eqls'Int'Unds'",
   "Lbl'UndsEqlsEqls'Int'Unds'",
   "Lbl'UndsEqlsSlshEqls'Int'Unds'",
   "LblminInt'LParUndsCommUndsRParUnds'INT-COMMON'Unds'Int'Unds'Int'Unds'Int",
   "LblmaxInt'LParUndsCommUndsRParUnds'INT-COMMON'Unds'Int'Unds'Int'Unds'Int",
   "LblabsInt'LParUndsRParUnds'INT-COMMON'Unds'Int'Unds'Int",
   "LblfreshInt'LParUndsRParUnds'INT'Unds'Int'Unds'Int",
   "Lbl'UndsEqlsEqls'K'Unds'",
   "Lbl'UndsEqlsSlshEqls'K'Unds'",
   "Lbl'Stop'Map",
   "Lbl'UndsPipe'-'-GT-Unds'",
   "Lbl'Unds'Map'Unds'",
   "LblMap'Coln'update",
   "Lbl'UndsLSqBUnds-LT-'-undef'RSqB'",
   "LblMap'Coln'lookup",
   "LblMap'Coln'lookupOrDefault",
   "Lbl'Unds'in'Unds'keys'LParUndsRParUnds'MAP'Unds'Bool'Unds'KItem'Unds'Map",
   "LblsizeMap",
   "LblremoveAll'LParUndsCommUndsRParUnds'MAP'Unds'Map'Unds'Map'Unds'Set",
   "Lblkeys'LParUndsRParUnds'MAP'Unds'Set'Unds'Map",
   "Lbl'Stop'Set",
   "LblSetItem",
   "Lbl'Unds'Set'Unds'",
   "Lbl'UndsPipe'Set'UndsUnds'SET'Unds'Set'Unds'Set'Unds'Set",
   "LblintersectSet'LParUndsCommUndsRParUnds'SET'Unds'Set'Unds'Set'Unds'Set",
   "LblSet'Coln'difference",
   "LblSet'Coln'in",
   "Lbl'Unds-LT-Eqls'Set'UndsUnds'SET'Unds'Bool'Unds'Set'Unds'Set",
   "Lblsize'LParUndsRParUnds'SET'Unds'Int'Unds'Set",
   "LblisK",
   "LblisKItem",
   "LblisBool",
   "LblisInt",
   "LblisKConfigVar",
   "LblisList",
   "LblisMap",
   "LblisSet",
   "LblisId",
   "LblisString",
   "LblisFloat",
   "LblisIOError",
   "LblisIOFile",
   "LblisIOInt",
   "LblisIOString",
   "LblisStream",
   "LblisGeneratedTopCell",
   "LblisGeneratedTopCellFragment",
   "LblisGeneratedCounterCell",
   "LblisGeneratedCounterCellOpt",
   "Lbl'-LT-'generatedTop'-GT-'",
   "Lbl'-LT-'generatedTop'-GT-'-fragment",
   "Lbl'-LT-'generatedCounter'-GT-'",
   "LblnoGeneratedCounterCell",
   "Lbl'Hash'EOF",
   "Lbl'Hash'unknownIOError",
   "Lbl'Hash'E2BIG",
   "Lbl'Hash'EACCES",
   "Lbl'Hash'EAGAIN",
   "Lbl'Hash'EBADF",
   "Lbl'Hash'EBUSY",
   "Lbl'Hash'ECHILD",
   "Lbl'Hash'EDEADLK",
   "Lbl'Hash'EDOM",
   "Lbl'Hash'EEXIST",
   "Lbl'Hash'EFAULT",
   "Lbl'Hash'EFBIG",
   "Lbl'Hash'EINTR",
   "Lbl'Hash'EINVAL",
   "Lbl'Hash'EIO",
   "Lbl'Hash'EISDIR",
   "Lbl'Hash'EMFILE",
   "Lbl'Hash'EMLINK",
   "Lbl'Hash'ENAMETOOLONG",
   "Lbl'Hash'ENFILE",
   "Lbl'Hash'ENODEV",
   "Lbl'Hash'ENOENT",
   "Lbl'Hash'ENOEXEC",
   "Lbl'Hash'ENOLCK",
   "Lbl'Hash'ENOMEM",
   "Lbl'Hash'ENOSPC",
   "Lbl'Hash'ENOSYS",
   "Lbl'Hash'ENOTDIR",
   "Lbl'Hash'ENOTEMPTY",
   "Lbl'Hash'ENOTTY",
   "Lbl'Hash'ENXIO",
   "Lbl'Hash'EPERM",
   "Lbl'Hash'EPIPE",
   "Lbl'Hash'ERANGE",
   "Lbl'Hash'EROFS",
   "Lbl'Hash'ESPIPE",
   "Lbl'Hash'ESRCH",
   "Lbl'Hash'EXDEV",
   "Lbl'Hash'EWOULDBLOCK",
   "Lbl'Hash'EINPROGRESS",
   "Lbl'Hash'EALREADY",
   "Lbl'Hash'ENOTSOCK",
   "Lbl'Hash'EDESTADDRREQ",
   "Lbl'Hash'EMSGSIZE",
   "Lbl'Hash'EPROTOTYPE",
   "Lbl'Hash'ENOPROTOOPT",
   "Lbl'Hash'EPROTONOSUPPORT",
   "Lbl'Hash'ESOCKTNOSUPPORT",
   "Lbl'Hash'EOPNOTSUPP",
   "Lbl'Hash'EPFNOSUPPORT",
   "Lbl'Hash'EAFNOSUPPORT",
   "Lbl'Hash'EADDRINUSE",
   "Lbl'Hash'EADDRNOTAVAIL",
   "Lbl'Hash'ENETDOWN",
   "Lbl'Hash'ENETUNREACH",
   "Lbl'Hash'ENETRESET",
   "Lbl'Hash'ECONNABORTED",
   "Lbl'Hash'ECONNRESET",
   "Lbl'Hash'ENOBUFS",
   "Lbl'Hash'EISCONN",
   "Lbl'Hash'ENOTCONN",
   "Lbl'Hash'ESHUTDOWN",
   "Lbl'Hash'ETOOMANYREFS",
   "Lbl'Hash'ETIMEDOUT",
   "Lbl'Hash'ECONNREFUSED",
   "Lbl'Hash'EHOSTDOWN",
   "Lbl'Hash'EHOSTUNREACH",
   "Lbl'Hash'ELOOP",
   "Lbl'Hash'EOVERFLOW",
   "Lbl'Hash'systemResult",
   "Lbl'Hash'tempFile",
   "Lbl'Hash'buffer'LParUndsRParUnds'K-IO'Unds'Stream'Unds'K",
   "Lbl'Hash'istream'LParUndsRParUnds'K-IO'Unds'Stream'Unds'Int",
   "Lbl'Hash'parseInput'LParUndsCommUndsRParUnds'K-IO'Unds'Stream'Unds'String'Unds'String",
   "Lbl'Hash'ostream'LParUndsRParUnds'K-IO'Unds'Stream'Unds'Int",
   "Lbl'Hash'unboxKConfigValue",
   "Lblproject'Coln'K",
   "Lblproject'Coln'KItem",
   "Lblproject'Coln'Bool",
   "Lblproject'Coln'Int",
   "Lblproject'Coln'KConfigVar",
   "Lblproject'Coln'List",
   "Lblproject'Coln'Map",
   "Lblproject'Coln'Set",
   "Lblproject'Coln'MInt",
   "Lblproject'Coln'Id",
   "Lblproject'Coln'String",
   "Lblproject'Coln'Float",
   "Lblproject'Coln'IOError",
   "Lblproject'Coln'IOFile",
   "Lblproject'Coln'IOInt",
   "Lblproject'Coln'IOString",
   "Lblproject'Coln'Stream",
   "Lblproject'Coln'GeneratedTopCell",
   "Lblproject'Coln'GeneratedTopCellFragment",
   "Lblproject'Coln'GeneratedCounterCell",
   "Lblproject'Coln'GeneratedCounterCellOpt"] ++
  BuiltinNames.newSymNames ++ ["Lblite"]

/-- The predicate `isX` of a registry sort X below KItem (K and KItem have their own, `isK` and
`isKItem`; MInt has none). -/
def regPred (X : Srt) : Option Sym :=
  match X with
  | 2 => some 53
  | 3 => some 54
  | 4 => some 55
  | 5 => some 56
  | 6 => some 57
  | 7 => some 58
  | 9 => some 59
  | 10 => some 60
  | 11 => some 61
  | 12 => some 62
  | 13 => some 63
  | 14 => some 64
  | 15 => some 65
  | 16 => some 66
  | 17 => some 67
  | 18 => some 68
  | 19 => some 69
  | 20 => some 70
  | X => (BuiltinNames.newPreds.find? (·.1 == X)).map (·.2.1)

/-- The constructors of every definition: K's `kseq` and `dotk`. (`#KConfigValue`, which krust's
text declares and K 7.1.337's does not, is the library's when the text declares it: `libOf`.) -/
def fixedCtors : List CtorSig :=
  [⟨kseq, [Srt.kitem, Srt.k], Srt.k⟩, ⟨dotk, [], Srt.k⟩]


/-! ## The builtin library a definition imports -/

/-- The builtin signature a definition's imports bring: the union of its imported modules'
(Builtins.lean). The K prelude's Bool, Int, KConfigVar, List, MInt, Map and Set come with every
definition (krust always imports their modules). -/
structure Lib where
  /-- the library's sorts below KItem (all but the parametric MInt) -/
  sortsBelowKItem : List Srt := []
  /-- the subsorts the library declares between its own sorts (below KItem aside) -/
  subsorts : List (Srt × Srt) := []
  /-- the sorts whose domain values are tokens: any literal string, distinct literals distinct -/
  tokenSorts : List Srt := []
  /-- the sorts whose domain values are byte strings: literals of characters below 256 -/
  byteSorts : List Srt := []
  /-- the library's constructors besides `kseq` and `dotk`, in the text's order, after
  `#KConfigValue` when the text declares it -/
  ctors : List CtorSig := []
  /-- sorts hooked under their own name to a library sort with domain values: `(s, b)` -/
  carriers : List (Srt × Srt) := []
  deriving Repr, DecidableEq, Inhabited

namespace Lib

/-- The library's constructors of sort KItem, which kompile places with `#KConfigValue` (they come
from builtin modules named before `K-RUST-CONFIGURATION-VALUES`, `K-IO` for `#systemResult`). -/
def kitemCtors (l : Lib) : List CtorSig := l.ctors.filter (·.result == Srt.kitem)

/-- The sort whose literals are the values of `s`: for a sort hooked under its own name to a
library sort (`carriers`), that library sort; for a registry sort, or a sort without a carrier,
`s` itself. -/
def carrier (l : Lib) (s : Srt) : Srt :=
  if s < nRegSorts then s else match l.carriers.find? (·.1 == s) with
    | some (_, b) => if b < nRegSorts then b else s
    | none => s

/-- The carrier of a sort is its own carrier. -/
theorem carrier_carrier (l : Lib) (s : Srt) : l.carrier (l.carrier s) = l.carrier s := by
  unfold carrier
  by_cases hs : s < nRegSorts
  · simp [hs]
  · simp only [hs, if_false]
    split
    · rename_i b heq; by_cases hb : b < nRegSorts
      · simp [hb]
      · simp [hb, hs, heq]
    · rename_i heq; simp [hs, heq]

/-- A registry sort is its own carrier. -/
theorem carrier_of_lt (l : Lib) {s : Srt} (h : s < nRegSorts) : l.carrier s = s := by
  simp [carrier, h]

@[simp] theorem carrier_int (l : Lib) : l.carrier Srt.int = Srt.int := carrier_of_lt l (by decide)
@[simp] theorem carrier_bool (l : Lib) : l.carrier Srt.bool = Srt.bool := carrier_of_lt l (by decide)
@[simp] theorem carrier_float (l : Lib) : l.carrier Srt.float = Srt.float := carrier_of_lt l (by decide)
@[simp] theorem carrier_string (l : Lib) : l.carrier Srt.string = Srt.string := carrier_of_lt l (by decide)
@[simp] theorem carrier_bytes (l : Lib) : l.carrier Srt.bytes = Srt.bytes := carrier_of_lt l (by decide)
@[simp] theorem carrier_kconfigVar (l : Lib) : l.carrier Srt.kconfigVar = Srt.kconfigVar := carrier_of_lt l (by decide)

/-- Without carriers every sort is its own. -/
theorem carrier_nil (l : Lib) (h : l.carriers = []) (s : Srt) : l.carrier s = s := by
  simp [carrier, h]

/-- A sort without a pair in `carriers` is its own. -/
theorem carrier_of_not (l : Lib) {s : Srt} (h : l.carriers.all (·.1 != s) = true) : l.carrier s = s := by
  have : l.carriers.find? (·.1 == s) = none := by
    rw [List.find?_eq_none]; intro p hp; have := List.all_eq_true.mp h p hp; simpa using this
  unfold carrier; split
  · rfl
  · rw [this]

end Lib

/-! ## The interpreted hooked symbols (their registry numbers; their KORE names are `regSymNames`) -/

/-- The signatures of the interpreted hooked symbols (and `freshInt`). -/
def hookSigs : List CtorSig :=
  [⟨boolNot, [Srt.bool], Srt.bool⟩] ++
  ([boolAnd, boolAndThen, boolOr, boolOrElse, boolXor, boolImplies, boolEq, boolNe].map
    fun f => ⟨f, [Srt.bool, Srt.bool], Srt.bool⟩) ++
  ([intAdd, intSub, intMul, intTDiv, intTMod, intEDiv, intEMod, intMin, intMax].map
    fun f => ⟨f, [Srt.int, Srt.int], Srt.int⟩) ++
  ([intLt, intLe, intGt, intGe, intEq, intNe].map fun f => ⟨f, [Srt.int, Srt.int], Srt.bool⟩) ++
  [⟨intAbs, [Srt.int], Srt.int⟩, ⟨freshInt, [Srt.int], Srt.int⟩,
   ⟨intShr, [Srt.int, Srt.int], Srt.int⟩, ⟨intShl, [Srt.int, Srt.int], Srt.int⟩, ⟨intLog2, [Srt.int], Srt.int⟩,
   ⟨intPowMod, [Srt.int, Srt.int, Srt.int], Srt.int⟩, ⟨intBitRange, [Srt.int, Srt.int, Srt.int], Srt.int⟩,
   ⟨intSignExtBitRange, [Srt.int, Srt.int, Srt.int], Srt.int⟩, ⟨intPow, [Srt.int, Srt.int], Srt.int⟩,
   ⟨kEq, [Srt.k, Srt.k], Srt.bool⟩, ⟨kNe, [Srt.k, Srt.k], Srt.bool⟩,
   ⟨mapUnit, [], Srt.map⟩, ⟨mapElem, [Srt.kitem, Srt.kitem], Srt.map⟩, ⟨mapConcat, [Srt.map, Srt.map], Srt.map⟩,
   ⟨mapUpdate, [Srt.map, Srt.kitem, Srt.kitem], Srt.map⟩, ⟨mapRemove, [Srt.map, Srt.kitem], Srt.map⟩,
   ⟨mapLookup, [Srt.map, Srt.kitem], Srt.kitem⟩, ⟨mapLookupOrDefault, [Srt.map, Srt.kitem, Srt.kitem], Srt.kitem⟩,
   ⟨mapInKeys, [Srt.kitem, Srt.map], Srt.bool⟩, ⟨mapSize, [Srt.map], Srt.int⟩,
   ⟨mapRemoveAll, [Srt.map, Srt.set], Srt.map⟩, ⟨mapKeys, [Srt.map], Srt.set⟩,
   ⟨setUnit, [], Srt.set⟩, ⟨setElem, [Srt.kitem], Srt.set⟩, ⟨setConcat, [Srt.set, Srt.set], Srt.set⟩,
   ⟨setUnion, [Srt.set, Srt.set], Srt.set⟩, ⟨setIntersect, [Srt.set, Srt.set], Srt.set⟩,
   ⟨setDifference, [Srt.set, Srt.set], Srt.set⟩, ⟨setIn, [Srt.kitem, Srt.set], Srt.bool⟩,
   ⟨setInclusion, [Srt.set, Srt.set], Srt.bool⟩, ⟨setSize, [Srt.set], Srt.int⟩,
   ⟨listConcat, [Srt.list, Srt.list], Srt.list⟩, ⟨listUnit, [], Srt.list⟩,
   ⟨listElem, [Srt.kitem], Srt.list⟩, ⟨listPush, [Srt.kitem, Srt.list], Srt.list⟩,
   ⟨listGet, [Srt.list, Srt.int], Srt.kitem⟩, ⟨listRange, [Srt.list, Srt.int, Srt.int], Srt.list⟩,
   ⟨listIn, [Srt.kitem, Srt.list], Srt.bool⟩, ⟨listSize, [Srt.list], Srt.int⟩,
   ⟨listSet, [Srt.list, Srt.int, Srt.kitem], Srt.list⟩, ⟨listMake, [Srt.int, Srt.kitem], Srt.list⟩,
   ⟨listUpdateAll, [Srt.list, Srt.int, Srt.list], Srt.list⟩,
   ⟨listFill, [Srt.list, Srt.int, Srt.int, Srt.kitem], Srt.list⟩] ++
  ([floatAdd, floatSub, floatMul, floatDiv, floatRem].map fun f => ⟨f, [Srt.float, Srt.float], Srt.float⟩) ++
  ([floatNeg, floatAbs, floatFloor, floatCeil, floatTrunc, floatSqrt].map fun f => ⟨f, [Srt.float], Srt.float⟩) ++
  ([floatLe, floatLt, floatGe, floatGt, floatEq, floatNe].map fun f => ⟨f, [Srt.float, Srt.float], Srt.bool⟩) ++
  ([floatIsNaN, floatIsInfinite].map fun f => ⟨f, [Srt.float], Srt.bool⟩) ++
  ([floatPrecision, floatExponentBits].map fun f => ⟨f, [Srt.float], Srt.int⟩) ++
  [⟨floatRound, [Srt.float, Srt.int, Srt.int], Srt.float⟩, ⟨int2Float, [Srt.int, Srt.int, Srt.int], Srt.float⟩,
   ⟨floatMaxValue, [Srt.int, Srt.int], Srt.float⟩, ⟨floatMinValue, [Srt.int, Srt.int], Srt.float⟩,
   ⟨stringConcat, [Srt.string, Srt.string], Srt.string⟩, ⟨stringLength, [Srt.string], Srt.int⟩,
   ⟨stringOrd, [Srt.string], Srt.int⟩, ⟨stringSubstr, [Srt.string, Srt.int, Srt.int], Srt.string⟩,
   ⟨stringFind, [Srt.string, Srt.string, Srt.int], Srt.int⟩, ⟨stringRfind, [Srt.string, Srt.string, Srt.int], Srt.int⟩,
   ⟨stringFindChar, [Srt.string, Srt.string, Srt.int], Srt.int⟩,
   ⟨stringRfindChar, [Srt.string, Srt.string, Srt.int], Srt.int⟩,
   ⟨string2Bool, [Srt.string], Srt.bool⟩, ⟨string2Int, [Srt.string], Srt.int⟩,
   ⟨string2Base, [Srt.string, Srt.int], Srt.int⟩,
   ⟨stringReplace, [Srt.string, Srt.string, Srt.string, Srt.int], Srt.string⟩,
   ⟨stringReplaceFirst, [Srt.string, Srt.string, Srt.string], Srt.string⟩,
   ⟨stringCountAll, [Srt.string, Srt.string], Srt.int⟩,
   ⟨stringReplaceAll, [Srt.string, Srt.string, Srt.string], Srt.string⟩] ++
  ([stringEq, stringNe, stringLt, stringLe, stringGt, stringGe].map fun f => ⟨f, [Srt.string, Srt.string], Srt.bool⟩) ++
  [⟨stringChr, [Srt.int], Srt.string⟩, ⟨int2String, [Srt.int], Srt.string⟩, ⟨bool2String, [Srt.bool], Srt.string⟩] ++
  [⟨bytes2Int, [Srt.bytes, Srt.endianness, Srt.signedness], Srt.int⟩,
   ⟨bytesUpdate, [Srt.bytes, Srt.int, Srt.int], Srt.bytes⟩, ⟨bytesGet, [Srt.bytes, Srt.int], Srt.int⟩,
   ⟨bytesSubstr, [Srt.bytes, Srt.int, Srt.int], Srt.bytes⟩, ⟨bytesReplaceAt, [Srt.bytes, Srt.int, Srt.bytes], Srt.bytes⟩,
   ⟨bytesMemset, [Srt.bytes, Srt.int, Srt.int, Srt.int], Srt.bytes⟩,
   ⟨bytesPadRight, [Srt.bytes, Srt.int, Srt.int], Srt.bytes⟩, ⟨bytesPadLeft, [Srt.bytes, Srt.int, Srt.int], Srt.bytes⟩,
   ⟨bytesReverse, [Srt.bytes], Srt.bytes⟩, ⟨bytesLength, [Srt.bytes], Srt.int⟩,
   ⟨bytesConcat, [Srt.bytes, Srt.bytes], Srt.bytes⟩,
   ⟨bytesEmpty, [], Srt.bytes⟩, ⟨int2Bytes, [Srt.int, Srt.int, Srt.endianness], Srt.bytes⟩,
   ⟨kIte, [Srt.bool, Srt.kitem, Srt.kitem], Srt.kitem⟩] ++
  [⟨rmUnit, [], Srt.rangeMap⟩, ⟨rmElem, [Srt.range, Srt.kitem], Srt.rangeMap⟩,
   ⟨rmConcat, [Srt.rangeMap, Srt.rangeMap], Srt.rangeMap⟩,
   ⟨rmLookup, [Srt.rangeMap, Srt.kitem], Srt.kitem⟩,
   ⟨rmLookupOrDefault, [Srt.rangeMap, Srt.kitem, Srt.kitem], Srt.kitem⟩,
   ⟨rmFindRange, [Srt.rangeMap, Srt.kitem], Srt.range⟩,
   ⟨rmUpdate, [Srt.rangeMap, Srt.range, Srt.kitem], Srt.rangeMap⟩,
   ⟨rmRemove, [Srt.rangeMap, Srt.range], Srt.rangeMap⟩,
   ⟨rmDifference, [Srt.rangeMap, Srt.rangeMap], Srt.rangeMap⟩,
   ⟨rmUpdateAll, [Srt.rangeMap, Srt.rangeMap], Srt.rangeMap⟩,
   ⟨rmRemoveAll, [Srt.rangeMap, Srt.set], Srt.rangeMap⟩,
   ⟨rmInKeys, [Srt.kitem, Srt.rangeMap], Srt.bool⟩,
   ⟨rmSize, [Srt.rangeMap], Srt.int⟩,
   ⟨rmInclusion, [Srt.rangeMap, Srt.rangeMap], Srt.bool⟩] ++
  [⟨rmKeys, [Srt.rangeMap], Srt.set⟩]

/-- FLOAT's interpreted symbols, by the sort of their result: Float, Bool, Int. -/
def floatResFloat : List Sym :=
  [floatAdd, floatSub, floatMul, floatDiv, floatRem, floatNeg, floatAbs, floatFloor, floatCeil, floatTrunc,
   floatSqrt, floatRound, int2Float, floatMaxValue, floatMinValue]
def floatResBool : List Sym := [floatLe, floatLt, floatGe, floatGt, floatEq, floatNe, floatIsNaN, floatIsInfinite]
def floatResInt : List Sym := [floatPrecision, floatExponentBits]

/-- STRING's and BYTES' interpreted symbols that are partial: undefined off valid indices or digits,
at a negative count or length, at a byte outside 0–255, at an integer that is no code point.
`substrString` and `Int2Bytes`, declared `total` by the library's text, are among them
(findings/KN-4-string-bytes.md §1.4, §3), and so are `countAllOccurrences` and `replaceAll`, declared
`total` and without a `hook` value at the empty needle. `Bytes2Int` is not: it is undefined only at an Endianness
or Signedness value that is no constructor of BYTES, and the deciders count on its totality where
those sorts have only BYTES' constructors (`enumShapesOK`). -/
def stringPartial : List Sym :=
  [stringOrd, stringSubstr, stringFind, stringRfind, stringFindChar, stringRfindChar, string2Bool, string2Int,
   string2Base, stringReplace, stringChr, stringCountAll, stringReplaceAll]
def bytesPartial : List Sym :=
  [bytesUpdate, bytesGet, bytesSubstr, bytesReplaceAt, bytesMemset, bytesPadRight, bytesPadLeft, int2Bytes]

/-- The interpreted symbols not known total here (`hook` can be undefined): division and modulo,
the two shifts (undefined at a negative amount) and `log2Int` (undefined at a number not above 0),
`^%Int` (no value at a zero modulus, the interpretation's at a negative exponent and at a
remainder of a negative power the modulus does not divide), `bitRangeInt` and
`signExtendBitRangeInt` (undefined at a negative index or length, the second also at length 0),
`^Int` (the interpretation's at a negative exponent), `L[I <- V]`, `makeList`, `updateList` and
`fillList` (the interpretation's off the ranges the text describes),
`_Map_` and `_Set_` (undefined where the two collections share a key or a member), `Map:lookup`,
`List:get` and `List:range`, and FLOAT's (undefined on two formats or at a format without a model;
those FLOAT declares `total` are listed too, so no check counts on their totality: the seven of
`totalSilentKeys` have silent points, and `precisionFloat` and `exponentBitsFloat` have a value at
every Float literal and none at a value of sort Float that is no literal, a constructor, injection
or token of that sort, which only `floatShapeOK` excludes), and STRING's and BYTES' partial ones
(`stringPartial`, `bytesPartial`), and RANGEMAP's seven that the text does not declare `total`: the
element symbol, update and remove at a range that is no proper Int range, `removeAll` at a member
that is none, remove and `removeAll` at a range no part of which is in the map, concatenation
where two intervals meet, `lookup` and `find_range` off the keys.
The library's text declares every other one `total` (KCORE-AUDIT.md). -/
def partialHooks : List Sym :=
  [intTDiv, intTMod, intEDiv, intEMod, mapConcat, setConcat, mapLookup, listGet, listRange] ++ floatResFloat ++
    floatResBool ++ floatResInt ++ stringPartial ++ bytesPartial ++
    [rmElem, rmConcat, rmLookup, rmFindRange, rmUpdate, rmRemove, rmRemoveAll] ++ [intShr, intShl, intLog2] ++
    [intPowMod, intBitRange, intSignExtBitRange] ++ [intPow, listSet, listMake, listUpdateAll, listFill]

/-- The `hook{}` attribute of each interpreted hooked symbol, as the builtin texts declare it
(checked against them by test/Member.lean). A hooked symbol whose hook is one of these
has that symbol's meaning; one whose hook is none of these is a parameter. `freshInt` and FLOAT's
`isInfinite`, `sqrtFloat` and `=/=Float` (functions of FLOAT's text with an equation each) and
STRING's `String2Bool` (two equations) have no `hook` attribute. -/
def regHookNames : List (Sym × String) :=
  [(boolNot, "BOOL.not"),
   (boolAnd, "BOOL.and"),
   (boolAndThen, "BOOL.andThen"),
   (boolOr, "BOOL.or"),
   (boolOrElse, "BOOL.orElse"),
   (boolXor, "BOOL.xor"),
   (boolImplies, "BOOL.implies"),
   (boolEq, "BOOL.eq"),
   (boolNe, "BOOL.ne"),
   (intAdd, "INT.add"),
   (intSub, "INT.sub"),
   (intMul, "INT.mul"),
   (intTDiv, "INT.tdiv"),
   (intTMod, "INT.tmod"),
   (intEDiv, "INT.ediv"),
   (intEMod, "INT.emod"),
   (intMin, "INT.min"),
   (intMax, "INT.max"),
   (intLt, "INT.lt"),
   (intLe, "INT.le"),
   (intGt, "INT.gt"),
   (intGe, "INT.ge"),
   (intEq, "INT.eq"),
   (intNe, "INT.ne"),
   (intAbs, "INT.abs"),
   (intShr, "INT.shr"),
   (intShl, "INT.shl"),
   (intLog2, "INT.log2"),
   (intPowMod, "INT.powmod"),
   (intBitRange, "INT.bitRange"),
   (intSignExtBitRange, "INT.signExtendBitRange"),
   (intPow, "INT.pow"),
   (kEq, "KEQUAL.eq"),
   (kNe, "KEQUAL.ne"),
   (mapUnit, "MAP.unit"),
   (mapElem, "MAP.element"),
   (mapConcat, "MAP.concat"),
   (mapUpdate, "MAP.update"),
   (mapRemove, "MAP.remove"),
   (mapLookup, "MAP.lookup"),
   (mapLookupOrDefault, "MAP.lookupOrDefault"),
   (mapInKeys, "MAP.in_keys"),
   (mapSize, "MAP.size"),
   (mapRemoveAll, "MAP.removeAll"),
   (mapKeys, "MAP.keys"),
   (setUnit, "SET.unit"),
   (setElem, "SET.element"),
   (setConcat, "SET.concat"),
   (setUnion, "SET.union"),
   (setIntersect, "SET.intersection"),
   (setDifference, "SET.difference"),
   (setIn, "SET.in"),
   (setInclusion, "SET.inclusion"),
   (setSize, "SET.size"),
   (listConcat, "LIST.concat"),
   (listUnit, "LIST.unit"),
   (listElem, "LIST.element"),
   (listPush, "LIST.push"),
   (listGet, "LIST.get"),
   (listRange, "LIST.range"),
   (listIn, "LIST.in"),
   (listSize, "LIST.size"),
   (listSet, "LIST.update"),
   (listMake, "LIST.make"),
   (listUpdateAll, "LIST.updateAll"),
   (listFill, "LIST.fill"),
   (floatAdd, "FLOAT.add"),
   (floatSub, "FLOAT.sub"),
   (floatMul, "FLOAT.mul"),
   (floatDiv, "FLOAT.div"),
   (floatRem, "FLOAT.rem"),
   (floatNeg, "FLOAT.neg"),
   (floatAbs, "FLOAT.abs"),
   (floatFloor, "FLOAT.floor"),
   (floatCeil, "FLOAT.ceil"),
   (floatTrunc, "FLOAT.trunc"),
   (floatLe, "FLOAT.le"),
   (floatLt, "FLOAT.lt"),
   (floatGe, "FLOAT.ge"),
   (floatGt, "FLOAT.gt"),
   (floatEq, "FLOAT.eq"),
   (floatIsNaN, "FLOAT.isNaN"),
   (floatPrecision, "FLOAT.precision"),
   (floatExponentBits, "FLOAT.exponentBits"),
   (floatRound, "FLOAT.round"),
   (int2Float, "FLOAT.int2float"),
   (floatMaxValue, "FLOAT.maxValue"),
   (floatMinValue, "FLOAT.minValue"),
   (stringConcat, "STRING.concat"),
   (stringLength, "STRING.length"),
   (stringOrd, "STRING.ord"),
   (stringSubstr, "STRING.substr"),
   (stringFind, "STRING.find"),
   (stringRfind, "STRING.rfind"),
   (stringFindChar, "STRING.findChar"),
   (stringRfindChar, "STRING.rfindChar"),
   (string2Int, "STRING.string2int"),
   (string2Base, "STRING.string2base"),
   (stringReplace, "STRING.replace"),
   (stringReplaceFirst, "STRING.replaceFirst"),
   (stringCountAll, "STRING.countAllOccurrences"),
   (stringReplaceAll, "STRING.replaceAll"),
   (stringEq, "STRING.eq"),
   (stringNe, "STRING.ne"),
   (stringLt, "STRING.lt"),
   (stringLe, "STRING.le"),
   (stringGt, "STRING.gt"),
   (stringGe, "STRING.ge"),
   (bytes2Int, "BYTES.bytes2int"),
   (bytesUpdate, "BYTES.update"),
   (bytesGet, "BYTES.get"),
   (bytesSubstr, "BYTES.substr"),
   (bytesReplaceAt, "BYTES.replaceAt"),
   (bytesMemset, "BYTES.memset"),
   (bytesPadRight, "BYTES.padRight"),
   (bytesPadLeft, "BYTES.padLeft"),
   (bytesReverse, "BYTES.reverse"),
   (bytesLength, "BYTES.length"),
   (bytesConcat, "BYTES.concat"),
   (stringChr, "STRING.chr"),
   (int2String, "STRING.int2string"),
   (bytesEmpty, "BYTES.empty"),
   (int2Bytes, "BYTES.int2bytes"),
   (kIte, "KEQUAL.ite"),
   (rmUnit, "RANGEMAP.unit"),
   (rmElem, "RANGEMAP.elementRng"),
   (rmConcat, "RANGEMAP.concat"),
   (rmLookup, "RANGEMAP.lookup"),
   (rmLookupOrDefault, "RANGEMAP.lookupOrDefault"),
   (rmFindRange, "RANGEMAP.find_range"),
   (rmUpdate, "RANGEMAP.updateRng"),
   (rmRemove, "RANGEMAP.removeRng"),
   (rmDifference, "RANGEMAP.difference"),
   (rmUpdateAll, "RANGEMAP.updateAll"),
   (rmRemoveAll, "RANGEMAP.removeAll"),
   (rmInKeys, "RANGEMAP.in_keys"),
   (rmSize, "RANGEMAP.size"),
   (rmInclusion, "RANGEMAP.inclusion"),
   (rmKeys, "RANGEMAP.keys")]

/-- The interpreted hook of a `hook{}` attribute, if the registry has one. -/
def regHookOf (h : String) : Option Sym := (regHookNames.find? (·.2 == h)).map (·.1)

/-- The hooked symbols allowed in a left-hand side (map patterns). -/
def patternHooks : List Sym := [mapUnit, mapElem, mapConcat]

/-- The list symbols a pattern may apply (`PatVal.coll`): `.List`, `ListItem`, `_List_`. -/
def listPatternHooks : List Sym := [listUnit, listElem, listConcat]

/-- The library's collection symbols a pattern may apply as `PatVal.coll`: the set's `.Set`,
`SetItem` and `_Set_`, and the list's. `_Set_` is the union of two disjoint sets (Hooks.lean), so
`SetItem(P) S` denotes the sets `{v} ∪ s` with v not in s, of the values v and s that P and S
denote: its matches at a set are one per member that P matches, S the other members, as
`K |-> V M` matches a map once per key. -/
def collPatternHooks : List Sym := setUnit :: setElem :: setConcat :: listPatternHooks

end KCore
