/-
  The conjunct `carriersOK` of `paramsPlain` (row sortedOK.6 of test/witnesses.toml): no witness
  found in the no-model form (a semantics meeting every other condition of `coreOK` and `FnHyp`,
  failing the conjunct, whose `Γ` has no model). Run from the package root:
  `lake env lean -j1 test/WitCarriers.lean`.

  `carriersOK` says of each pair `(s, b)` of `c.lib.carriers`: `s` is an own sort (`carOwn`), a
  user sort (`carUser`), `b` is Int, Bool, Float, String or Bytes (`carLib`), `s` is no token sort
  (`carTok`), no byte sort (`carByte`), no collection sort of the definition's (`carColl`); and no
  sort is hooked twice (`carOnce`). `carriersOK_eq`: the conjunct is these seven, by `rfl`.

  Kernel-checked here.
  - Two parts are implied by other conditions of `coreOK`, for every semantics:
    `carUser_of_numbered` (an own sort hooked to a carrier is numbered, `sortsNumbered`, and the own
    sorts of `userSorts` are the numbered ones, `idsOK`'s first leaf) and `carColl_of_collSortsOK`
    (`collSortOK` asks of every collection sort that no pair hooks it).
  - The other five are not implied: for each a semantics without rule, function or parameter that
    meets every other condition of `coreOK` and `FnHyp` (`Others`) with the part false, the other
    six true except where noted. `Reg.c`: Int hooked to Int (`carOwn` false, and `carUser`, Int
    being no user sort). `Tgt.c`: the own sort MyInt hooked to K (`carLib`); `TgtVar.c`: MyInt hooked
    to KConfigVar (`carLib`). `Tok.c`, `Byte.c`: MyInt hooked to Int and a token sort, a byte sort
    (`carTok`, `carByte`). `Dup.c`, `Dup2.c`: MyInt hooked to Int twice, to Int then to Bool
    (`carOnce`).
  - `c0` (MyInt hooked to Int once) and `c00` (MyInt hooked to nothing) meet `coreOK`.
  - What the values of MyInt are in each (`vals`): in `c0`, `Reg.c` aside, `Tok.c`, `Byte.c`,
    `Dup.c`, `Dup2.c` the integers at the sort MyInt and no token; in `Tgt.c` neither; in `TgtVar.c`
    the tokens.

  The semantics have no parameter, so `paramsPlain`'s first part, over `c.params`, holds of them
  whatever it asks of a parameter; `rulesPlain` and `clausesPlain` hold of a semantics without
  rule and function.

  Argued, not kernel-checked: `Γ` of each has a model. `Γ` reads `c.lib.carriers` through
  `Lib.carrier` (the literals of a sort, `dvOK`, and the arguments a hook reads, `toLib`), through
  `consSorts` (a sort with a pair is no constructor sort), through `distinctSorts` (its distinct
  values are distinct elements) and through `litSort` at Bool (the item that Bool holds its two
  literals, present where a rule or clause reads a confined sort; no instance hooks Bool or has a
  rule or clause).
  - `Reg.c`: `Lib.carrier` ignores a pair whose first sort is a registry sort; Int is no candidate
    of `consSorts` and is in `distinctSorts` already. So `Γ` is `c00`'s up to a repeated item.
  - `Dup.c`, `Dup2.c`: `Lib.carrier` reads the first pair of a sort (`carrier_dup`), the other two
    read the first components only. So `Γ` is `c0`'s up to a repeated item.
  - `Tok.c`, `Byte.c`: `dvOK` asks the token and byte sorts at the carrier, Int, which is neither
    (`LitsApart`); `consSorts` drops MyInt for its pair already, `distinctSorts` lists it twice.
    So `Γ` is `c0`'s up to a repeated item.
  - `Tgt.c`: MyInt has no literal, is no constructor sort and no collection sort, so it has no
    value; `Γ` states of it its sort predicate's equations, the injection into KItem and the
    distinctness of its values. The value model of `c00`'s shape with no element of MyInt meets them.
  - `TgtVar.c`: the values of MyInt are the tokens at MyInt; no interpreted symbol takes or gives
    KConfigVar, and the semantics has no parameter over MyInt; the value model with MyInt holding
    its tokens, distinct, meets `Γ`.

  Not examined: a pair whose first sort is K, KItem or a generated configuration sort (then a
  candidate of `consSorts`; with a constructor or a subsort ending at it `genWf` fails too); a
  second sort that is a registry collection sort, Range, MInt or a registry token sort; any of
  the failures beside a parameter implemented by a hook over the hooked sort.

  No theorem of the library reads the conjunct: `paramsPlain` is read by `raw_of_paramsPlain`
  alone, which reads its first part. So the headline statements hold of a semantics failing
  `carriersOK` alone by the proofs they have (argued from the text of the proofs, not restated).
-/
import KcoreSpec.Tie
import KcoreSpec.Obligations
import KcoreSpec.CoreDecide

set_option autoImplicit false
set_option maxRecDepth 100000

namespace KCore.Faithful.WitCarriers

open ML Faithful.Model

/-! ## The parts of `carriersOK` -/

def carOwn (p : Srt × Srt) : Bool := decide (nRegSorts ≤ p.1)
def carUser (c : Semantics) (p : Srt × Srt) : Bool := c.userSorts.contains p.1
def carLib (p : Srt × Srt) : Bool := [Srt.int, Srt.bool, Srt.float, Srt.string, Srt.bytes].contains p.2
def carTok (c : Semantics) (p : Srt × Srt) : Bool := !c.lib.tokenSorts.contains p.1
def carByte (c : Semantics) (p : Srt × Srt) : Bool := !c.lib.byteSorts.contains p.1
def carColl (c : Semantics) (p : Srt × Srt) : Bool := !c.colls.any (·.sort == p.1)
def carOnce (c : Semantics) : Bool := nodup (c.lib.carriers.map (·.1))

/-- `carriersOK` is its seven parts. -/
theorem carriersOK_eq (c : Semantics) : c.carriersOK =
    (c.lib.carriers.all (fun p => carOwn p && carUser c p && carLib p && carTok c p && carByte c p && carColl c p) &&
      carOnce c) := rfl

/-- **`carUser` is implied**: an own sort hooked to a carrier is numbered (`sortsNumbered`), and the
own sorts of `userSorts` are the numbered ones (`idsOK`'s first leaf). -/
theorem carUser_of_numbered (c : Semantics) (hs : sortsNumbered c = true)
    (hids : (c.ownSorts == List.range' nRegSorts c.sortNames.length) = true)
    {p : Srt × Srt} (hp : p ∈ c.lib.carriers) (hown : carOwn p = true) : carUser c p = true := by
  have hlt : p.1 < nRegSorts + c.sortNames.length := by
    simp only [sortsNumbered, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hs
    exact hs.1.2 p.1 (List.mem_append_right _ (List.mem_map.mpr ⟨p, hp, rfl⟩))
  have hmem : p.1 ∈ c.ownSorts := by
    rw [eq_of_beq hids]
    exact List.mem_range'_1.mpr ⟨by simpa [carOwn] using hown, hlt⟩
  simp only [Semantics.ownSorts, List.mem_filter] at hmem
  simpa [carUser] using hmem.1

/-- **`carColl` is implied**: `collSortsOK` asks of every collection sort that no pair hooks it. -/
theorem carColl_of_collSortsOK (c : Semantics) (h : collSortsOK c = true)
    {p : Srt × Srt} (hp : p ∈ c.lib.carriers) : carColl c p = true := by
  rw [carColl, Bool.not_eq_true']
  refine Bool.eq_false_iff.mpr fun hany => ?_
  obtain ⟨k, hk, hks⟩ := List.any_eq_true.mp hany
  have hk' : k ∈ c.allColls := List.mem_append_right _ hk
  have := List.all_eq_true.mp h k hk'
  simp only [collSortOK, Bool.and_eq_true, List.all_eq_true] at this
  exact absurd (eq_of_beq hks).symm (bne_iff_ne.mp (this.2 p hp))

/-! ## The instances -/

/-- The cell sorts, their subsorts and their constructors, the own symbols numbered after three
sort predicates. -/
def cellSorts : List Srt := [Srt.top, Srt.topFrag, nRegSorts, nRegSorts + 1, Srt.counter, Srt.counterOpt]
def cellSubsorts : List (Srt × Srt) := [(nRegSorts, nRegSorts + 1), (Srt.counter, Srt.counterOpt)]
def ownCtors : List CtorSig :=
  [⟨topLabel, [nRegSorts, Srt.counter], Srt.top⟩, ⟨topFragLabel, [nRegSorts + 1, Srt.counterOpt], Srt.topFrag⟩,
   ⟨nRegSyms + 3, [Srt.k], nRegSorts⟩, ⟨nRegSyms + 4, [], nRegSorts + 1⟩,
   ⟨counterLabel, [Srt.int], Srt.counter⟩, ⟨noCounter, [], Srt.counterOpt⟩]

/-- The own sort MyInt, after the two cell sorts. -/
def myInt : Srt := nRegSorts + 2

/-- The cells and the own sort MyInt, over the library `l`: no rule, function or parameter. -/
def mk (l : Lib) : Semantics :=
  { lib := l
    sortNames := ["KCell", "KCellOpt", "MyInt"]
    symNames := ["LblisKCell", "LblisKCellOpt", "LblisMyInt", "Lbl'-LT-'k'-GT-'", "LblnoKCell"]
    userSorts := cellSorts ++ [myInt]
    ctors := ownCtors
    fns := []
    userSubsorts := cellSubsorts
    pgmSort := Srt.k
    rules := [] }

def base : Lib := { sortsBelowKItem := [Srt.int, Srt.bool] }

/-- Every condition of `coreOK` but `paramsPlain`'s `carriersOK`, and `FnHyp`, of a semantics
without rule, function or parameter. -/
def Others (c : Semantics) : Prop :=
  c.subsortsOK = true ∧ c.rules = [] ∧ c.fns = [] ∧ c.params = [] ∧ c.rulesPlain = true ∧
    c.clausesPlain = true ∧ c.predsApart = true ∧ c.idsOK = true ∧
    c.overloadsOK = true ∧ c.faithCoreOK = true ∧ FnHyp c

theorem others (l : Lib)
    (h : ((mk l).subsortsOK && (mk l).rulesPlain && (mk l).clausesPlain &&
      (mk l).predsApart && (mk l).idsOK && (mk l).overloadsOK && (mk l).faithCoreOK) = true)
    (hrc : (mk l).readsConfined = false) : Others (mk l) := by
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  exact ⟨h1, rfl, rfl, rfl, h2, h3, h5, h6, h7, h8,
    fun _ hf => absurd hf List.not_mem_nil, fun _ hf => absurd hf List.not_mem_nil,
    fun _ hf => absurd hf List.not_mem_nil, fun _ hf => absurd hf List.not_mem_nil,
    openDecided_of_readsConfined hrc, openLaws_of_plain (fun _ hk => absurd hk List.not_mem_nil)⟩

/-- The seven parts at the first pair that fails one, in the order of `carriersOK_eq`. -/
def parts (c : Semantics) (p : Srt × Srt) : List Bool :=
  [carOwn p, carUser c p, carLib p, carTok c p, carByte c p, carColl c p, carOnce c]

/-- Whether the integer `0`, the Bool `true` and the token `x` are values of MyInt. -/
def vals (c : Semantics) : List Bool :=
  [(c.sortOf (.dv myInt (.int 0))).isSome, (c.sortOf (.dv myInt (.bool true))).isSome,
   (c.sortOf (.dv myInt (.tok "x"))).isSome]

/-- MyInt hooked to Int. -/
def c0 : Semantics := mk { base with carriers := [(myInt, Srt.int)] }
/-- MyInt hooked to nothing. -/
def c00 : Semantics := mk base

theorem c0_coreOK : c0.coreOK = true := by decide_cheap
theorem c00_coreOK : c00.coreOK = true := by decide_cheap
theorem c0_vals : vals c0 = [true, false, false] := by decide +kernel

namespace Reg
/-- Int hooked to Int. -/
def l : Lib := { base with carriers := [(Srt.int, Srt.int)] }
def c : Semantics := mk l
set_option maxHeartbeats 1000000 in
theorem meets_others : Others c := others l (by decide_cheap) (by decide +kernel)
theorem not_carriersOK : c.carriersOK = false ∧
    parts c (Srt.int, Srt.int) = [false, false, true, true, true, true, true] := by decide +kernel
/-- The pair is not read: each sort is its own carrier. -/
theorem carrier_reg (s : Srt) : c.lib.carrier s = s := by
  by_cases h : s < nRegSorts
  · exact Lib.carrier_of_lt _ h
  · refine Lib.carrier_of_not _ ?_
    have : Srt.int ≠ s := fun he => h (he ▸ by decide)
    simpa [c, l, mk, base] using this
end Reg

namespace Tgt
/-- MyInt hooked to K. -/
def l : Lib := { base with carriers := [(myInt, Srt.k)] }
def c : Semantics := mk l
set_option maxHeartbeats 1000000 in
theorem meets_others : Others c := others l (by decide_cheap) (by decide +kernel)
theorem not_carriersOK : c.carriersOK = false ∧
    parts c (myInt, Srt.k) = [true, true, false, true, true, true, true] := by decide +kernel
theorem c_vals : vals c = [false, false, false] ∧ (consSorts c).contains myInt = false ∧
    (c.collOf myInt).isNone = true := by decide +kernel
end Tgt

namespace TgtVar
/-- MyInt hooked to KConfigVar. -/
def l : Lib := { base with carriers := [(myInt, Srt.kconfigVar)] }
def c : Semantics := mk l
set_option maxHeartbeats 1000000 in
theorem meets_others : Others c := others l (by decide_cheap) (by decide +kernel)
theorem not_carriersOK : c.carriersOK = false ∧
    parts c (myInt, Srt.kconfigVar) = [true, true, false, true, true, true, true] := by decide +kernel
theorem c_vals : vals c = [false, false, true] := by decide +kernel
end TgtVar

namespace Tok
/-- MyInt hooked to Int, and a token sort. -/
def l : Lib := { base with carriers := [(myInt, Srt.int)], tokenSorts := [myInt] }
def c : Semantics := mk l
set_option maxHeartbeats 1000000 in
theorem meets_others : Others c := others l (by decide_cheap) (by decide +kernel)
theorem not_carriersOK : c.carriersOK = false ∧
    parts c (myInt, Srt.int) = [true, true, true, false, true, true, true] := by decide +kernel
theorem c_vals : vals c = [true, false, false] := by decide +kernel
end Tok

namespace Byte
/-- MyInt hooked to Int, and a byte sort. -/
def l : Lib := { base with carriers := [(myInt, Srt.int)], byteSorts := [myInt] }
def c : Semantics := mk l
set_option maxHeartbeats 1000000 in
theorem meets_others : Others c := others l (by decide_cheap) (by decide +kernel)
theorem not_carriersOK : c.carriersOK = false ∧
    parts c (myInt, Srt.int) = [true, true, true, true, false, true, true] := by decide +kernel
theorem c_vals : vals c = [true, false, false] := by decide +kernel
end Byte

namespace Dup
/-- MyInt hooked to Int twice. -/
def l : Lib := { base with carriers := [(myInt, Srt.int), (myInt, Srt.int)] }
def c : Semantics := mk l
set_option maxHeartbeats 1000000 in
theorem meets_others : Others c := others l (by decide_cheap) (by decide +kernel)
theorem not_carriersOK : c.carriersOK = false ∧
    parts c (myInt, Srt.int) = [true, true, true, true, true, true, false] := by decide +kernel
theorem c_vals : vals c = [true, false, false] := by decide +kernel
end Dup

namespace Dup2
/-- MyInt hooked to Int, then to Bool. -/
def l : Lib := { base with carriers := [(myInt, Srt.int), (myInt, Srt.bool)] }
def c : Semantics := mk l
set_option maxHeartbeats 1000000 in
theorem meets_others : Others c := others l (by decide_cheap) (by decide +kernel)
theorem not_carriersOK : c.carriersOK = false ∧
    parts c (myInt, Srt.int) = [true, true, true, true, true, true, false] ∧
    parts c (myInt, Srt.bool) = [true, true, true, true, true, true, false] := by decide +kernel
theorem c_vals : vals c = [true, false, false] := by decide +kernel
/-- The second pair is not read: each sort has the carrier `c0` gives it. -/
theorem carrier_dup (s : Srt) : c.lib.carrier s = c0.lib.carrier s := by
  simp only [Lib.carrier, c, l, c0, mk, base, List.find?]
  by_cases h : myInt == s <;> simp [h]
end Dup2

/-- info: 'KCore.Faithful.WitCarriers.carUser_of_numbered' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms carUser_of_numbered

/-- info: 'KCore.Faithful.WitCarriers.carColl_of_collSortsOK' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms carColl_of_collSortsOK

/-- info: 'KCore.Faithful.WitCarriers.c0_coreOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms c0_coreOK

/-- info: 'KCore.Faithful.WitCarriers.Reg.meets_others' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Reg.meets_others

/-- info: 'KCore.Faithful.WitCarriers.Tgt.meets_others' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Tgt.meets_others

/-- info: 'KCore.Faithful.WitCarriers.TgtVar.meets_others' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TgtVar.meets_others

/-- info: 'KCore.Faithful.WitCarriers.Tok.meets_others' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Tok.meets_others

/-- info: 'KCore.Faithful.WitCarriers.Byte.meets_others' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Byte.meets_others

/-- info: 'KCore.Faithful.WitCarriers.Dup.meets_others' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Dup.meets_others

/-- info: 'KCore.Faithful.WitCarriers.Dup2.meets_others' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Dup2.meets_others

end KCore.Faithful.WitCarriers
