/-
  Totality through a set or list collection's element symbol (`setListItemHead`, TotalsG.lean) on a
  small core.
  Checked by
      lean test/SetListItem.lean   (LEAN_PATH from `lake env`)

  A set collection sort S with Int elements, built by the parameters `.S` (`setUnit`), `S.item`
  (`setElem`, `Int → S`) and `_S_` (`setConcat`), and a list collection sort L with Int elements,
  built by `.L` (`listUnit`), `L.item` (`listElem`, `Int → L`) and `_L_` (`listConcat`), as the cell
  sets and cell lists of K's `multiplicity="*"` cells of `type="Set"` and `type="List"` are; and
  three functions declared `[total]`:
  - `InitS(X) = S.item(X)` and `InitL(X) = L.item(X)`: the shape of the generated `init…Cell`
    functions. At an element of the collection's sort the element symbol's value is the one-element
    set or list of its result sort.
  - `Bad(X) = B.item(true)`, with `B.item : Bool → S` implemented by `setElem` too: its argument
    sort is not the collection's, so the set it builds has an element of the wrong sort, no sort,
    and `paramVal` keeps no value. `setListItemHead` refuses it.
  `totalObligationsRP` names Bad only (`sl_RP`); InitS and InitL are total under every
  interpretation, every function terminating and evaluation functional, given Bad's totality
  (`sl_total`).
-/
import KcoreSpec.FnObligations
import KcoreSpec.CoreDecide

set_option autoImplicit false

namespace KCore.SetListItemTest

open KCore KCore.Det

def cellSorts : List Srt := [Srt.top, Srt.topFrag, nRegSorts, nRegSorts + 1, Srt.counter, Srt.counterOpt]
def cellCtors : List CtorSig :=
  [⟨topLabel, [nRegSorts, Srt.counter], Srt.top⟩, ⟨topFragLabel, [nRegSorts + 1, Srt.counterOpt], Srt.topFrag⟩,
   ⟨nRegSyms + 50, [Srt.k], nRegSorts⟩, ⟨nRegSyms + 51, [], nRegSorts + 1⟩,
   ⟨counterLabel, [Srt.int], Srt.counter⟩, ⟨noCounter, [], Srt.counterOpt⟩]
def cellSubsorts : List (Srt × Srt) := [(nRegSorts, nRegSorts + 1), (Srt.counter, Srt.counterOpt)]

def S : Srt := nRegSorts + 2
def L : Srt := nRegSorts + 3
def uS : Sym := nRegSyms + 101
def eS : Sym := nRegSyms + 102
def cS : Sym := nRegSyms + 103
def eB : Sym := nRegSyms + 104
def uL : Sym := nRegSyms + 105
def eL : Sym := nRegSyms + 106
def cL : Sym := nRegSyms + 107
def InitS : Sym := nRegSyms + 150
def InitL : Sym := nRegSyms + 151
def Bad : Sym := nRegSyms + 152

def collS : CollSig := ⟨S, .set, Srt.int, none, uS, eS, cS⟩
def collL : CollSig := ⟨L, .list, Srt.int, none, uL, eL, cL⟩

def fnInitS : Fn := ⟨InitS, [Srt.int], S,
  [⟨[Srt.int], [.var 0], none, .app eS [.var 0], none, 50, false, [], .top, .top⟩], true⟩
def fnInitL : Fn := ⟨InitL, [Srt.int], L,
  [⟨[Srt.int], [.var 0], none, .app eL [.var 0], none, 50, false, [], .top, .top⟩], true⟩
def fnBad : Fn := ⟨Bad, [Srt.int], S,
  [⟨[Srt.int], [.var 0], none, .app eB [.dv Srt.bool (.bool true)], none, 50, false, [], .top, .top⟩], true⟩

def sl : Semantics where
  lib := { sortsBelowKItem := [Srt.int, Srt.bool] }
  sortNames := []
  symNames := []
  userSorts := cellSorts ++ [S, L]
  ctors := cellCtors
  fns := [fnInitS, fnInitL, fnBad]
  userSubsorts := cellSubsorts
  pgmSort := Srt.k
  rules := []
  params := [{ sig := ⟨uS, [], S⟩, impl := some setUnit }, { sig := ⟨eS, [Srt.int], S⟩, impl := some setElem },
    { sig := ⟨cS, [S, S], S⟩, impl := some setConcat }, { sig := ⟨eB, [Srt.bool], S⟩, impl := some setElem },
    { sig := ⟨uL, [], L⟩, impl := some listUnit }, { sig := ⟨eL, [Srt.int], L⟩, impl := some listElem },
    { sig := ⟨cL, [L, L], L⟩, impl := some listConcat }]
  colls := [collS, collL]

theorem sl_sorted : sl.sortedOK = true ∧ sl.srReady = true := by decide_cheap

/-- `S.item` and `L.item` are a set's and a list's element symbols; `B.item` is not (its argument
sort is not the collection's), and no map's element symbol is one. -/
theorem sl_heads : sl.setListItemHead eS = true ∧ sl.setListItemHead eL = true ∧
    sl.setListItemHead eB = false ∧ sl.mapItemHead eS = false := by decide +kernel

theorem sl_RP : sl.totalObligationsRP [] [] = [Bad] := by decide +kernel

/-- **InitS and InitL are total** under every interpretation, every function terminating and
evaluation functional, given Bad's totality. -/
theorem sl_total (H : HookParams) (hterm : ∀ g, Terminates (sl.withHooks H) g)
    (hco : CoherentAll (sl.withHooks H)) (hB : Total (sl.withHooks H) Bad) :
    Total (sl.withHooks H) InitS ∧ Total (sl.withHooks H) InitL := by
  have key := totals_of_rankP (hpreTop := by rw [Semantics.clausesPreTop_withHooks]; decide +kernel) (hnoEx := (Semantics.fnsNoExs_withHooks _ _).mpr (Semantics.fnsNoExs_of_all (by decide +kernel))) (c := sl.withHooks H) sl_sorted.1 sl_sorted.2
    (Semantics.ovlCase_withHooks (Semantics.ovlCase_of (by decide +kernel)) H)
    (Semantics.rightHeld_withHooks (c := sl) (Semantics.rightHeld_of_valued (by decide +kernel)) H (by decide +kernel)) hterm hco [] [] ParamsTotal.nil
    (fun g hg => by
      rw [Semantics.totalObligationsRP_withHooks, sl_RP] at hg
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      subst hg
      exact hB)
  exact ⟨key InitS fnInitS rfl rfl, key InitL fnInitL rfl rfl⟩

end KCore.SetListItemTest

#print axioms KCore.SetListItemTest.sl_total
