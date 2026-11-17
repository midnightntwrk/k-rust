/-
  A constructor whose result sort is a sort with other values: `Faithful.genWf`, a conjunct of
  `coreOK`, excludes it. Run from the package root: `lake env lean test/H12Witnesses.lean`.

  Hand-built semantics over one frame (a `<k>` cell, the generated counter, a library), each
  decided by the kernel. `g1`, `g2`, `g3` are `genWf`'s first three conjuncts by name (`genWf_eq`):
  a constructor's result sort is a constructor sort (`consSorts`: K, KItem, the own sorts and the
  library constructors' result sorts, less own collection sorts, token sorts and carriers); a
  subsort's upper sort is one; and no constructor sort is Int, Bool, KConfigVar, Float, String,
  Bytes, a token or byte sort or a collection sort (`collOf`), each apart from the others.

  The constructor enters by the library (`Lib.ctors`, the library route) or as a constructor of
  the definition's own (`Semantics.ctors`, the own route). Each witness is beside its control, the
  same semantics without the constructor, with `coreOK = true`.

  | result sort | library route | own route | control |
  |---|---|---|---|
  | Int | `lib_int`: g3 | `own_int`: g1 | `ctl_fr` |
  | Map | `lib_map`: g3 | `own_map`: g1 | `ctl_fr_map` |
  | an own sort S with the carrier Int (`syntax S [hook(INT.Int)]`) | `lib_carrier`: g1 | `own_carrier`: g1 | `ctl_frS_carrier` |
  | an own Map collection sort S (`hook(MAP.Map)`) | `lib_coll`: g1 | `own_coll`: g1 | `ctl_ownColl` |

  By the library route into Int or Map the sort enters `consSorts` through the library
  constructor, so g1 holds and g3 fails; by the own route the sort is not in `consSorts`, and g1
  fails. A carrier and an own collection sort are filtered out of `consSorts` whichever way the
  constructor comes, so g1 fails by both. The own constructor is no defect by itself: with result
  KItem, or an own sort S with no carrier, `coreOK` holds (`ctl_own_kitem`, `ctl_ownS`,
  `ctl_libS`).

  Where the kernel gives a registry sort no values of its own, a library constructor into it keeps
  `coreOK`: MInt (`lib_mint`; no literal, no collection and no hook of the kernel reads the sort).
  RangeMap is a collection sort of the kernel (`builtinColls`' range-map row, `collOf`), so the
  library constructor into it fails g3 (`lib_rangeMap`), beside its control (`ctl_fr_rangeMap`).
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.H12Witnesses

open KCore KCore.Faithful

def cellSorts : List Srt := [Srt.top, Srt.topFrag, nRegSorts, nRegSorts + 1, Srt.counter, Srt.counterOpt]
def cellSubsorts : List (Srt × Srt) := [(nRegSorts, nRegSorts + 1), (Srt.counter, Srt.counterOpt)]
/-- The cells' constructors, the two own ones numbered from `b`. -/
def cellCtors (b : Sym) : List CtorSig :=
  [⟨topLabel, [nRegSorts, Srt.counter], Srt.top⟩, ⟨topFragLabel, [nRegSorts + 1, Srt.counterOpt], Srt.topFrag⟩,
   ⟨b, [Srt.k], nRegSorts⟩, ⟨b + 1, [], nRegSorts + 1⟩,
   ⟨counterLabel, [Srt.int], Srt.counter⟩, ⟨noCounter, [], Srt.counterOpt⟩]

/-- A `<k>` cell, the generated counter, the library `l`, nothing else. -/
def fr (l : Lib) : Semantics where
  lib := l
  sortNames := ["KCell", "KCellOpt"]
  symNames := ["LblisKCell", "LblisKCellOpt", "Lbl'-LT-'k'-GT-'", "LblnoKCell"]
  userSorts := cellSorts
  ctors := cellCtors (nRegSyms + 2)
  fns := []
  userSubsorts := cellSubsorts
  pgmSort := Srt.k
  rules := []

/-- The frame with one own constructor `k` (no argument) of result `s`. -/
def own (l : Lib) (s : Srt) : Semantics where
  lib := l
  sortNames := ["KCell", "KCellOpt"]
  symNames := ["LblisKCell", "LblisKCellOpt", "Lbl'-LT-'k'-GT-'", "LblnoKCell", "Lblk"]
  userSorts := cellSorts
  ctors := cellCtors (nRegSyms + 2) ++ [⟨nRegSyms + 4, [], s⟩]
  fns := []
  userSubsorts := cellSubsorts
  pgmSort := Srt.k
  rules := []

def S : Srt := nRegSorts + 2
/-- The frame with an own sort `S` and one own constructor `k` of result `S`. -/
def ownS (l : Lib) : Semantics where
  lib := l
  sortNames := ["KCell", "KCellOpt", "S"]
  symNames := ["LblisKCell", "LblisKCellOpt", "LblisS", "Lbl'-LT-'k'-GT-'", "LblnoKCell", "Lblk"]
  userSorts := cellSorts ++ [S]
  ctors := cellCtors (nRegSyms + 3) ++ [⟨nRegSyms + 5, [], S⟩]
  fns := []
  userSubsorts := cellSubsorts
  pgmSort := Srt.k
  rules := []

/-- An own Map collection from Int to Int at the own sort `S`, and, with `k`, an own constructor of result `S`. -/
def ownColl (k : Bool) : Semantics :=
  let uS : Sym := nRegSyms + (if k then 6 else 5)
  let eS : Sym := uS + 1
  let cS : Sym := uS + 2
  {
  lib := { sortsBelowKItem := [Srt.int, Srt.bool] }
  sortNames := ["KCell", "KCellOpt", "S"]
  symNames := ["LblisKCell", "LblisKCellOpt", "LblisS", "Lbl'-LT-'k'-GT-'", "LblnoKCell"] ++ (if k then ["Lblk"] else []) ++ ["Lbl'Stop'S", "LblSItem", "Lbl'Unds'S'Unds'"]
  userSorts := cellSorts ++ [S]
  ctors := cellCtors (nRegSyms + 3) ++ (if k then [⟨nRegSyms + 5, [], S⟩] else [])
  fns := []
  userSubsorts := cellSubsorts
  pgmSort := Srt.k
  rules := []
  params := [{ sig := ⟨uS, [], S⟩, impl := some (builtinColl .map).unit },
    { sig := ⟨eS, [Srt.int, Srt.int], S⟩, impl := some (builtinColl .map).elem },
    { sig := ⟨cS, [S, S], S⟩, impl := some (builtinColl .map).concat }]
  colls := [⟨S, .map, Srt.int, some Srt.int, uS, eS, cS⟩] }

def bI : List Srt := [Srt.int, Srt.bool]

/-- The frame with an own sort `S` and no constructor of it, the library `l`. -/
def frS (l : Lib) : Semantics where
  lib := l
  sortNames := ["KCell", "KCellOpt", "S"]
  symNames := ["LblisKCell", "LblisKCellOpt", "LblisS", "Lbl'-LT-'k'-GT-'", "LblnoKCell"]
  userSorts := cellSorts ++ [S]
  ctors := cellCtors (nRegSyms + 3)
  fns := []
  userSubsorts := cellSubsorts
  pgmSort := Srt.k
  rules := []

/-- A library constructor (the number of RANGEMAP's `Range` constructor, no argument) of result
`s`, `s` below KItem. -/
def libC (s : Srt) : Semantics :=
  fr { sortsBelowKItem := (bI ++ [s]).eraseDups, ctors := [⟨rangeCtor, [], s⟩] }

/-- The library with the own sort `S` a carrier sort of Int. -/
def carrierLib : Lib := { sortsBelowKItem := bI, carriers := [(S, Srt.int)] }

/-- `genWf`'s first three conjuncts. -/
def g1 (c : Semantics) : Bool := c.ctorSigs.all (fun k => (consSorts c).contains k.result)
def g2 (c : Semantics) : Bool := c.subsorts.all (fun p => (consSorts c).contains p.2 && p.1 != p.2)
def g3 (c : Semantics) : Bool :=
  (consSorts c).all (fun s => apartSort c s && s != Srt.int && s != Srt.bool && s != Srt.kconfigVar &&
    !c.lib.tokenSorts.contains s && !c.lib.byteSorts.contains s && (c.collOf s).isNone && s != Srt.float &&
    s != Srt.string && s != Srt.bytes)

/-- `genWf` is the three with its two conjuncts on open generators. -/
theorem genWf_eq (c : Semantics) : genWf c = (g1 c && g2 c && g3 c &&
    c.params.all (fun k => !k.raw || (consSorts c).contains k.sig.result) &&
    c.params.all (fun k => !k.raw ||
      (c.ctorSigs.all (fun g => g.name != k.sig.name && (g.result != k.sig.result || g.args.isEmpty)) &&
       c.ovlSigs.all (fun g => g.name != k.sig.name && g.result != k.sig.result) &&
       c.subsorts.all (fun p => p.2 != k.sig.result)))) := rfl

/-! ## The controls: `coreOK` holds without the constructor -/

theorem ctl_fr : (fr { sortsBelowKItem := bI }).coreOK = true := by decide_cheap
theorem ctl_fr_map : (fr { sortsBelowKItem := bI ++ [Srt.map] }).coreOK = true := by decide_cheap
theorem ctl_frS_carrier : (frS carrierLib).coreOK = true := by decide_cheap
theorem ctl_ownColl : (ownColl false).coreOK = true := by decide_cheap
theorem ctl_fr_mint : (fr { sortsBelowKItem := bI ++ [Srt.mint] }).coreOK = true := by decide_cheap
theorem ctl_fr_rangeMap : (fr { sortsBelowKItem := bI ++ [Srt.rangeMap] }).coreOK = true := by decide_cheap

/-- An own constructor of result KItem, or of an own sort with no carrier, and a library
constructor of such a sort: `coreOK` holds. -/
theorem ctl_own_kitem : (own { sortsBelowKItem := bI } Srt.kitem).coreOK = true := by decide_cheap
theorem ctl_ownS : (ownS { sortsBelowKItem := bI }).coreOK = true := by decide_cheap
theorem ctl_libS : (frS { sortsBelowKItem := bI, ctors := [⟨rangeCtor, [], S⟩] }).coreOK = true := by decide_cheap

/-! ## The library route -/

theorem lib_int : (libC Srt.int).coreOK = false ∧ g1 (libC Srt.int) = true ∧ g3 (libC Srt.int) = false ∧
    genWf (libC Srt.int) = false := by decide +kernel
theorem lib_map : (libC Srt.map).coreOK = false ∧ g1 (libC Srt.map) = true ∧ g3 (libC Srt.map) = false ∧
    genWf (libC Srt.map) = false := by decide +kernel

/-- The frame with the own carrier sort `S` and a library constructor of result `S`. -/
def libCarrier : Semantics := frS { carrierLib with ctors := [⟨rangeCtor, [], S⟩] }
theorem lib_carrier : libCarrier.coreOK = false ∧ g1 libCarrier = false ∧ genWf libCarrier = false := by
  decide +kernel

/-- The own Map collection at `S` and a library constructor of result `S`. -/
def libColl : Semantics :=
  { ownColl false with lib := { sortsBelowKItem := [Srt.int, Srt.bool], ctors := [⟨rangeCtor, [], S⟩] } }
theorem lib_coll : libColl.coreOK = false ∧ g1 libColl = false ∧ genWf libColl = false := by decide +kernel

/-! ## The own route -/

theorem own_int : (own { sortsBelowKItem := bI } Srt.int).coreOK = false ∧
    g1 (own { sortsBelowKItem := bI } Srt.int) = false ∧ genWf (own { sortsBelowKItem := bI } Srt.int) = false := by
  decide +kernel
theorem own_map : (own { sortsBelowKItem := bI ++ [Srt.map] } Srt.map).coreOK = false ∧
    g1 (own { sortsBelowKItem := bI ++ [Srt.map] } Srt.map) = false ∧
    genWf (own { sortsBelowKItem := bI ++ [Srt.map] } Srt.map) = false := by decide +kernel
theorem own_carrier : (ownS carrierLib).coreOK = false ∧ g1 (ownS carrierLib) = false ∧
    genWf (ownS carrierLib) = false := by decide +kernel
theorem own_coll : (ownColl true).coreOK = false ∧ g1 (ownColl true) = false ∧ genWf (ownColl true) = false := by
  decide +kernel

/-! ## Registry sorts the kernel gives no other values -/

/-- A library constructor into MInt keeps `coreOK`. -/
theorem lib_mint : (libC Srt.mint).coreOK = true := by decide_cheap

/-- RangeMap is a collection sort of the kernel: a library constructor into it fails `genWf`'s
third conjunct. -/
theorem lib_rangeMap : (libC Srt.rangeMap).coreOK = false ∧ ((libC Srt.rangeMap).collOf Srt.rangeMap).isSome = true ∧
    g1 (libC Srt.rangeMap) = true ∧ g3 (libC Srt.rangeMap) = false ∧ genWf (libC Srt.rangeMap) = false := by
  decide +kernel

end KCore.H12Witnesses

#print axioms KCore.H12Witnesses.ctl_fr
#print axioms KCore.H12Witnesses.ctl_fr_map
#print axioms KCore.H12Witnesses.ctl_frS_carrier
#print axioms KCore.H12Witnesses.ctl_ownColl
#print axioms KCore.H12Witnesses.ctl_fr_mint
#print axioms KCore.H12Witnesses.ctl_fr_rangeMap
#print axioms KCore.H12Witnesses.ctl_own_kitem
#print axioms KCore.H12Witnesses.ctl_ownS
#print axioms KCore.H12Witnesses.ctl_libS
#print axioms KCore.H12Witnesses.lib_int
#print axioms KCore.H12Witnesses.lib_map
#print axioms KCore.H12Witnesses.lib_carrier
#print axioms KCore.H12Witnesses.lib_coll
#print axioms KCore.H12Witnesses.own_int
#print axioms KCore.H12Witnesses.own_map
#print axioms KCore.H12Witnesses.own_carrier
#print axioms KCore.H12Witnesses.own_coll
#print axioms KCore.H12Witnesses.lib_mint
#print axioms KCore.H12Witnesses.lib_rangeMap
