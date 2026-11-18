/-
  Totality from termination by induction on evaluation (TotalsG.lean) on a small core. Checked by
      lean test/TotalsG.lean   (LEAN_PATH from `lake env`)

  Seven functions `Int → Int` declared `[total]`:
  - `A(X) = 1 requires X >Int 0`, `A(X) = 0 requires notBool (X >Int 0)`: two clauses with
    complementary `requires` (`guardPair`);
  - `D(X, Y) = X /Int Y requires Y =/=Int 0`, `D(X, Y) = 0 requires Y ==Int 0`: complementary
    comparisons, and a division whose divisor the `requires` asserts non-zero (`nonzeroIn`);
  - `E(X) = X /Int 2`: a division by a non-zero literal;
  - `S(X) = S(X -Int 1) requires X >Int 0`, `S(X) = 0 requires notBool (X >Int 0)`: a self call that
    does not decrease structurally (its termination is a fact of its own);
  - `B(X) = 1 requires X >Int 0`: no clause where X ≤ 0;
  - `C(X) = 1 requires X >Int 0`, `C(X) = 2 requires X >Int 0`: the same `requires` twice, which
    leaves X ≤ 0 uncovered;
  - `N(X, Y) = X /Int Y`: a division by a variable nothing asserts non-zero.
  `totalObligationsR` (the rank, `decreasingOK`, rows without `requires`, total hooks only) names all
  seven (`tg_R`); `totalObligationsRP` names B, C and N (`tg_RP`). Under every interpretation, every
  function terminating and evaluation functional, A, D, E and S are total given B, C and N
  (`tg_total`); B's value at 0 is open (no clause applies), none under the core's interpretation
  `HookParams.none` (`AtNone.tg_B_not_total`), so it must stay named.

  Termination of S by an Int counter bounded below (`ctrOK`, DecreasingL.lean): its self call's
  argument is `X -Int 1` where its `requires` puts X above 0. `decreasingOKL` does not show it
  (`tg_S_weight`); `decObligationsL` names only `U(X) = U(X -Int 1)` (no bound) and
  `V(X) = V(X +Int 1) requires X >Int 0` (the counter grows), neither declared total (`tg_dec`).
-/
import KcoreSpec.FnObligations
import KcoreSpec.CoreDecide

set_option autoImplicit false

namespace KCore.TotalsGTest

open KCore KCore.Det

def cellSorts : List Srt := [Srt.top, Srt.topFrag, nRegSorts, nRegSorts + 1, Srt.counter, Srt.counterOpt]
def cellCtors : List CtorSig :=
  [⟨topLabel, [nRegSorts, Srt.counter], Srt.top⟩, ⟨topFragLabel, [nRegSorts + 1, Srt.counterOpt], Srt.topFrag⟩,
   ⟨nRegSyms + 50, [Srt.k], nRegSorts⟩, ⟨nRegSyms + 51, [], nRegSorts + 1⟩,
   ⟨counterLabel, [Srt.int], Srt.counter⟩, ⟨noCounter, [], Srt.counterOpt⟩]
def cellSubsorts : List (Srt × Srt) := [(nRegSorts, nRegSorts + 1), (Srt.counter, Srt.counterOpt)]

def A : Sym := nRegSyms + 130
def D : Sym := nRegSyms + 131
def E : Sym := nRegSyms + 132
def S : Sym := nRegSyms + 133
def B : Sym := nRegSyms + 134
def C : Sym := nRegSyms + 135
def N : Sym := nRegSyms + 136
def U : Sym := nRegSyms + 137
def V : Sym := nRegSyms + 138

def x0 : Term := .var 0
def x1 : Term := .var 1
def lit (k : Int) : Term := .dv Srt.int (.int k)
def pos : Term := .app intGt [x0, lit 0]

def fnA : Fn := ⟨A, [Srt.int], Srt.int,
  [⟨[Srt.int], [x0], some pos, lit 1, none, 50, false, [], .top, .top⟩, ⟨[Srt.int], [x0], some (.app boolNot [pos]), lit 0, none, 50, false, [], .top, .top⟩], true⟩
def fnD : Fn := ⟨D, [Srt.int, Srt.int], Srt.int,
  [⟨[Srt.int, Srt.int], [x0, x1], some (.app intNe [x1, lit 0]), .app intTDiv [x0, x1], none, 50, false, [], .top, .top⟩,
   ⟨[Srt.int, Srt.int], [x0, x1], some (.app intEq [x1, lit 0]), lit 0, none, 50, false, [], .top, .top⟩], true⟩
def fnE : Fn := ⟨E, [Srt.int], Srt.int, [⟨[Srt.int], [x0], none, .app intTDiv [x0, lit 2], none, 50, false, [], .top, .top⟩], true⟩
def fnS : Fn := ⟨S, [Srt.int], Srt.int,
  [⟨[Srt.int], [x0], some pos, .app S [.app intSub [x0, lit 1]], none, 50, false, [], .top, .top⟩,
   ⟨[Srt.int], [x0], some (.app boolNot [pos]), lit 0, none, 50, false, [], .top, .top⟩], true⟩
def fnB : Fn := ⟨B, [Srt.int], Srt.int, [⟨[Srt.int], [x0], some pos, lit 1, none, 50, false, [], .top, .top⟩], true⟩
def fnC : Fn := ⟨C, [Srt.int], Srt.int,
  [⟨[Srt.int], [x0], some pos, lit 1, none, 50, false, [], .top, .top⟩, ⟨[Srt.int], [x0], some pos, lit 2, none, 50, false, [], .top, .top⟩], true⟩
def fnN : Fn := ⟨N, [Srt.int, Srt.int], Srt.int,
  [⟨[Srt.int, Srt.int], [x0, x1], none, .app intTDiv [x0, x1], none, 50, false, [], .top, .top⟩], true⟩

def fnU : Fn := ⟨U, [Srt.int], Srt.int, [⟨[Srt.int], [x0], none, .app U [.app intSub [x0, lit 1]], none, 50, false, [], .top, .top⟩], false⟩
def fnV : Fn := ⟨V, [Srt.int], Srt.int,
  [⟨[Srt.int], [x0], some pos, .app V [.app intAdd [x0, lit 1]], none, 50, false, [], .top, .top⟩], false⟩

def tg : Semantics where
  lib := { sortsBelowKItem := [Srt.map, Srt.list, Srt.int, Srt.bool] }
  sortNames := []
  symNames := []
  userSorts := cellSorts
  ctors := cellCtors
  fns := [fnA, fnD, fnE, fnS, fnB, fnC, fnN, fnU, fnV]
  userSubsorts := cellSubsorts
  pgmSort := Srt.k
  rules := []

theorem tg_sorted : tg.sortedOK = true ∧ tg.srReady = true := by decide_cheap

def ord : List Sym := [A, D, E, S, B, C, N]

theorem tg_R : tg.totalObligationsR ord = [A, D, E, S, B, C, N] := by decide +kernel

theorem tg_RP : tg.totalObligationsRP ord [] = [B, C, N] := by decide +kernel

/-- Under every interpretation, every function terminating and evaluation functional, the four
functions `totalObligationsRP` confirms are total, given the totality of the three it names. -/
theorem tg_total (H : HookParams) (hterm : ∀ g, Terminates (tg.withHooks H) g)
    (hco : CoherentAll (tg.withHooks H)) (hB : Total (tg.withHooks H) B) (hC : Total (tg.withHooks H) C)
    (hN : Total (tg.withHooks H) N) :
    Total (tg.withHooks H) A ∧ Total (tg.withHooks H) D ∧ Total (tg.withHooks H) E ∧
      Total (tg.withHooks H) S := by
  have key := totals_of_rankP (hpreTop := by decide +kernel) (c := tg.withHooks H) tg_sorted.1 tg_sorted.2
    (Semantics.ovlCase_withHooks (Semantics.ovlCase_of (by decide +kernel)) H)
    (Semantics.rightHeld_withHooks (c := tg) (Semantics.rightHeld_of_valued (by decide +kernel)) H (by decide +kernel)) hterm hco ord [] ParamsTotal.nil
    (fun g hg => by
      rw [Semantics.totalObligationsRP_withHooks, tg_RP] at hg
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl
      · exact hB
      · exact hC
      · exact hN)
  exact ⟨key A fnA rfl rfl, key D fnD rfl rfl, key E fnE rfl rfl, key S fnS rfl rfl⟩

theorem tg_S_weight : tg.decreasingOKL fnS (tg.decArgL fnS) = false := by decide +kernel

theorem tg_dec : tg.decObligationsL = [U, V] := by decide +kernel

theorem tg_rank : tg.rankObligations ord = [] := by decide +kernel

/-- Every function terminates, given U's and V's termination: S by its counter. -/
theorem tg_terminates (H : HookParams) (hU : Terminates (tg.withHooks H) U)
    (hV : Terminates (tg.withHooks H) V) : ∀ f, Terminates (tg.withHooks H) f :=
  terminates_of_rankL (hpreTop := by decide +kernel) (c := tg.withHooks H) tg_sorted.1 tg_sorted.2
    (Semantics.ovlCase_withHooks (Semantics.ovlCase_of (by decide +kernel)) H)
    (Semantics.rightHeld_withHooks (c := tg) (Semantics.rightHeld_of_valued (by decide +kernel)) H (by decide +kernel)) ord fun g hg => by
    rw [Semantics.rankObligations_withHooks, Semantics.decObligationsL_withHooks, tg_rank, tg_dec] at hg
    simp only [List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl
    · exact hU
    · exact hV

theorem tg_B_lookup : tg.lookupFn B = some fnB := by rfl

-- At the interpretation that gives nothing (`HookParams.none`): no statement for every interpretation.
namespace AtNone

/-- **B has no value at 0 under `HookParams.none`**: its one clause's `requires` `0 >Int 0` is false, so
its value there is its rest, which that interpretation does not give. -/
theorem tg_B_not_total : ¬ Total tg B := by
  intro h
  obtain ⟨v, hv⟩ := h fnB tg_B_lookup [.dv Srt.int (.int 0)] (by decide +kernel)
  cases hv with
  | clauseEx hfn hmem _ _ _ _ _ hne =>
    rw [tg_B_lookup] at hfn; cases hfn
    simp only [fnB, List.mem_singleton] at hmem
    subst hmem; exact absurd rfl hne
  | @clause _ _ _ _ σ _ hfn hmem hσ hm hreq =>
    rw [tg_B_lookup] at hfn; cases hfn
    simp only [fnB, List.mem_singleton] at hmem
    subst hmem
    cases hm with
    | cons h1 _ =>
      obtain ⟨a, b, X, Y, ea, eb, hX, hY, hb⟩ := int2_inv rfl hook_intGt (hreq pos rfl)
      have ha : σ.lookup 0 = some a := by
        generalize hx : Term.var 0 = t at ea
        generalize hra : some a = r at ea
        cases ea with
        | var => cases hx; rfl
        | _ => cases hx
      have hb' : b = .dv Srt.int (.int 0) := by
        generalize hx : lit 0 = t at eb
        generalize hrb : some b = r at eb
        cases eb with
        | dv => cases hx; exact (Option.some.inj hrb)
        | _ => cases hx
      cases h1 with
      | var hl =>
        rw [hl] at ha
        cases ha
        subst hb'
        simp [asInt] at hX hY
        subst hX; subst hY
        simp at hb

end AtNone

end KCore.TotalsGTest

#print axioms KCore.TotalsGTest.tg_total
#print axioms KCore.TotalsGTest.tg_terminates
#print axioms KCore.TotalsGTest.AtNone.tg_B_not_total
