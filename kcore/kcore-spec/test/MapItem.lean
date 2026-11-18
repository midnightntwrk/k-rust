/-
  Totality through a map collection's element symbol (`mapItemHead`, TotalsG.lean) on a small core.
  Checked by
      lean test/MapItem.lean   (LEAN_PATH from `lake env`)

  A map collection sort S with Int keys and Int values, built by the parameters `.S` (`mapUnit`),
  `S.item` (`mapElem`, `Int, Int → S`) and `_S_` (`mapConcat`), as the cell maps of K's
  `multiplicity="*"` cells are; and two functions declared `[total]`:
  - `Init(X) = S.item(X, 0)`: the shape of the generated `init…Cell` functions. At a key and a value
    of the collection's sorts the element symbol's value is the one-entry map of sort S.
  - `Bad(X) = B.item(X, true)`, with `B.item : Int, Bool → S` implemented by `mapElem` too: its
    argument sorts are not the collection's, so the map it builds has an entry of the wrong value
    sort, no sort, and `paramVal` keeps no value. `mapItemHead` refuses it.
  `totalObligationsRP` names Bad only (`mi_RP`); Init is total under every interpretation, every
  function terminating and evaluation functional, given Bad's totality (`mi_total`).
-/
import KcoreSpec.FnObligations
import KcoreSpec.CoreDecide

set_option autoImplicit false

namespace KCore.MapItemTest

open KCore KCore.Det

def cellSorts : List Srt := [Srt.top, Srt.topFrag, nRegSorts, nRegSorts + 1, Srt.counter, Srt.counterOpt]
def cellCtors : List CtorSig :=
  [⟨topLabel, [nRegSorts, Srt.counter], Srt.top⟩, ⟨topFragLabel, [nRegSorts + 1, Srt.counterOpt], Srt.topFrag⟩,
   ⟨nRegSyms + 50, [Srt.k], nRegSorts⟩, ⟨nRegSyms + 51, [], nRegSorts + 1⟩,
   ⟨counterLabel, [Srt.int], Srt.counter⟩, ⟨noCounter, [], Srt.counterOpt⟩]
def cellSubsorts : List (Srt × Srt) := [(nRegSorts, nRegSorts + 1), (Srt.counter, Srt.counterOpt)]

def S : Srt := nRegSorts + 2
def uS : Sym := nRegSyms + 101
def eS : Sym := nRegSyms + 102
def cS : Sym := nRegSyms + 103
def eB : Sym := nRegSyms + 104
def Init : Sym := nRegSyms + 150
def Bad : Sym := nRegSyms + 151

def collS : CollSig := ⟨S, .map, Srt.int, Srt.int, uS, eS, cS⟩

def fnInit : Fn := ⟨Init, [Srt.int], S,
  [⟨[Srt.int], [.var 0], none, .app eS [.var 0, .dv Srt.int (.int 0)], none, 50, false, [], .top, .top⟩], true⟩
def fnBad : Fn := ⟨Bad, [Srt.int], S,
  [⟨[Srt.int], [.var 0], none, .app eB [.var 0, .dv Srt.bool (.bool true)], none, 50, false, [], .top, .top⟩], true⟩

def mi : Semantics where
  lib := { sortsBelowKItem := [Srt.int, Srt.bool] }
  sortNames := []
  symNames := []
  userSorts := cellSorts ++ [S]
  ctors := cellCtors
  fns := [fnInit, fnBad]
  userSubsorts := cellSubsorts
  pgmSort := Srt.k
  rules := []
  params := [{ sig := ⟨uS, [], S⟩, impl := some mapUnit }, { sig := ⟨eS, [Srt.int, Srt.int], S⟩, impl := some mapElem },
    { sig := ⟨cS, [S, S], S⟩, impl := some mapConcat }, { sig := ⟨eB, [Srt.int, Srt.bool], S⟩, impl := some mapElem }]
  colls := [collS]

theorem mi_sorted : mi.sortedOK = true ∧ mi.srReady = true := by decide_cheap

/-- `S.item` is a map collection's element symbol; `B.item` is not (its argument sorts are not the
collection's). -/
theorem mi_heads : mi.mapItemHead eS = true ∧ mi.mapItemHead eB = false := by decide +kernel

theorem mi_RP : mi.totalObligationsRP [] [] = [Bad] := by decide +kernel

/-- **Init is total** under every interpretation, every function terminating and evaluation
functional, given Bad's totality. -/
theorem mi_total (H : HookParams) (hterm : ∀ g, Terminates (mi.withHooks H) g)
    (hco : CoherentAll (mi.withHooks H)) (hB : Total (mi.withHooks H) Bad) :
    Total (mi.withHooks H) Init := by
  have key := totals_of_rankP (hpreTop := by rw [Semantics.clausesPreTop_withHooks]; decide +kernel) (hnoEx := (Semantics.fnsNoExs_withHooks _ _).mpr (Semantics.fnsNoExs_of_all (by decide +kernel))) (c := mi.withHooks H) mi_sorted.1 mi_sorted.2
    (Semantics.ovlCase_withHooks (Semantics.ovlCase_of (by decide +kernel)) H)
    (Semantics.rightHeld_withHooks (c := mi) (Semantics.rightHeld_of_valued (by decide +kernel)) H (by decide +kernel)) hterm hco [] [] ParamsTotal.nil
    (fun g hg => by
      rw [Semantics.totalObligationsRP_withHooks, mi_RP] at hg
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      subst hg
      exact hB)
  exact key Init fnInit rfl rfl

end KCore.MapItemTest

#print axioms KCore.MapItemTest.mi_total
