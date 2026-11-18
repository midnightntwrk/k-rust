/-
  Termination of mutually recursive functions by a weight shared across their cycle
  (CallGroups.lean) on a small core. Checked by
      lean test/CallGroups.lean   (LEAN_PATH from `lake env`)

  A sort T with constructors `c(Int, T)` and `n`, and six functions:
  - `Ev(c(X, R)) = Od(R)`, `Ev(n) = 1`; `Od(c(X, R)) = Ev(R)`, `Od(n) = 0`: a cycle in which every
    call is on a strict subterm;
  - `A(N, c(X, R)) = B(R, N)`; `B(c(X, R), N) = A(N, R)`: the same with the decreasing argument at
    different positions (A's second, B's first), which the search finds;
  - `P(c(X, R)) = Q(R)`; `Q(c(X, R)) = P(c(X, c(X, R)))`: a cycle with a call to a heavier argument.
    It does not terminate (`P(c(x, c(x, r)))` calls `Q(c(x, r))`, which calls `P(c(x, c(x, r)))`
    again). Its call from P to Q goes to a later position of the rank and to a lighter argument;
    the call back from Q is ranked below Q but heavier. So the check reads every call inside the
    cycle, the ones the rank orders included: a variant that trusted the rank for those would
    accept P and Q.
  With the rank `[Ev, Od, P, Q, A, B]` (each cycle at consecutive positions, callees first), each of
  Ev, P and A calls a function placed after it (`cg_unranked`); `rankObligations` names only P
  (`cg_rank`). With a rank that interleaves the cycles of Ev and P, their intervals merge into one,
  which P's cycle spoils: Ev is named too (`cg_rankInterleaved`), a wrong rank only names more.
  Every function terminates given P's termination (`cg_terminates`).
-/
import KcoreSpec.FnObligations
import KcoreSpec.CoreDecide

set_option autoImplicit false

namespace KCore.CallGroupsTest

open KCore KCore.Det

def cellSorts : List Srt := [Srt.top, Srt.topFrag, nRegSorts, nRegSorts + 1, Srt.counter, Srt.counterOpt]
def cellCtors : List CtorSig :=
  [⟨topLabel, [nRegSorts, Srt.counter], Srt.top⟩, ⟨topFragLabel, [nRegSorts + 1, Srt.counterOpt], Srt.topFrag⟩,
   ⟨nRegSyms + 50, [Srt.k], nRegSorts⟩, ⟨nRegSyms + 51, [], nRegSorts + 1⟩,
   ⟨counterLabel, [Srt.int], Srt.counter⟩, ⟨noCounter, [], Srt.counterOpt⟩]
def cellSubsorts : List (Srt × Srt) := [(nRegSorts, nRegSorts + 1), (Srt.counter, Srt.counterOpt)]

def T : Srt := nRegSorts + 2
def cK : Sym := nRegSyms + 52
def nK : Sym := nRegSyms + 53

def Ev : Sym := nRegSyms + 140
def Od : Sym := nRegSyms + 141
def P : Sym := nRegSyms + 142
def Q : Sym := nRegSyms + 143
def A : Sym := nRegSyms + 144
def B : Sym := nRegSyms + 145

def lit (k : Int) : Term := .dv Srt.int (.int k)
/-- `c(X, R)` with X, R the variables x, r. -/
def cXR (x r : Nat) : Term := .app cK [.var x, .var r]
def nil : Term := .app nK []

def fnEv : Fn := ⟨Ev, [T], Srt.int,
  [⟨[Srt.int, T], [cXR 0 1], none, .app Od [.var 1], none, 50, false, [], .top, .top⟩, ⟨[], [nil], none, lit 1, none, 50, false, [], .top, .top⟩], false⟩
def fnOd : Fn := ⟨Od, [T], Srt.int,
  [⟨[Srt.int, T], [cXR 0 1], none, .app Ev [.var 1], none, 50, false, [], .top, .top⟩, ⟨[], [nil], none, lit 0, none, 50, false, [], .top, .top⟩], false⟩
def fnP : Fn := ⟨P, [T], Srt.int, [⟨[Srt.int, T], [cXR 0 1], none, .app Q [.var 1], none, 50, false, [], .top, .top⟩], false⟩
def fnQ : Fn := ⟨Q, [T], Srt.int,
  [⟨[Srt.int, T], [cXR 0 1], none, .app P [.app cK [.var 0, cXR 0 1]], none, 50, false, [], .top, .top⟩], false⟩
def fnA : Fn := ⟨A, [Srt.int, T], Srt.int,
  [⟨[Srt.int, Srt.int, T], [.var 0, cXR 1 2], none, .app B [.var 2, .var 0], none, 50, false, [], .top, .top⟩], false⟩
def fnB : Fn := ⟨B, [T, Srt.int], Srt.int,
  [⟨[Srt.int, T, Srt.int], [cXR 0 1, .var 2], none, .app A [.var 2, .var 1], none, 50, false, [], .top, .top⟩], false⟩

def cg : Semantics where
  lib := { sortsBelowKItem := [Srt.int, Srt.bool] }
  sortNames := []
  symNames := []
  userSorts := cellSorts ++ [T]
  ctors := cellCtors ++ [⟨cK, [Srt.int, T], T⟩, ⟨nK, [], T⟩]
  fns := [fnEv, fnOd, fnP, fnQ, fnA, fnB]
  userSubsorts := cellSubsorts
  pgmSort := Srt.k
  rules := []

theorem cg_sorted : cg.sortedOK = true ∧ cg.srReady = true := by decide_cheap

def ord : List Sym := [Ev, Od, P, Q, A, B]

/-- Ev, P and A each call a function the rank places after them. -/
theorem cg_unranked :
    (cg.fns.filter fun f => !rankedCallees ord (cg.fns.map (·.label)) f).map (·.label) = [Ev, P, A] := by
  decide +kernel

/-- Of those, only P is named: Ev's and A's cycles decrease, the second at A's second argument and
B's first. -/
theorem cg_rank : cg.rankObligations ord = [P] ∧ cg.decObligationsL = [] := by decide +kernel

/-- Interleaving the cycles of Ev and P merges their intervals: Ev is named too. -/
theorem cg_rankInterleaved : cg.rankObligations [Ev, P, Od, Q, A, B] = [Ev, P] := by decide +kernel

/-- **Every function terminates, given P's termination.** -/
theorem cg_terminates (H : HookParams) (hP : Terminates (cg.withHooks H) P) :
    ∀ f, Terminates (cg.withHooks H) f :=
  terminates_of_rankL (hpreTop := by rw [Semantics.clausesPreTop_withHooks]; decide +kernel) (c := cg.withHooks H) cg_sorted.1 cg_sorted.2
    (Semantics.ovlCase_withHooks (Semantics.ovlCase_of (by decide +kernel)) H)
    (Semantics.rightHeld_withHooks (c := cg) (Semantics.rightHeld_of_valued (by decide +kernel)) H (by decide +kernel)) ord fun g hg => by
    rw [Semantics.rankObligations_withHooks, Semantics.decObligationsL_withHooks, cg_rank.1, cg_rank.2] at hg
    simp only [List.append_nil, List.mem_cons, List.not_mem_nil, or_false] at hg
    subst hg
    exact hP

end KCore.CallGroupsTest

#print axioms KCore.CallGroupsTest.cg_terminates
