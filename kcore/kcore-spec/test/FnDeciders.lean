/-
  The deciders `FnObligations` reads (CallRank.lean, UniqLists.lean, AgreeLists.lean) on small
  cores, each with a case they confirm that the deciders of `CoreObligations` do not, a case they
  leave named, and counter-examples for the variants considered and found unsound. Checked by
      lean test/FnDeciders.lean   (LEAN_PATH from `lake env`)

  1. `rk`: `F(X) = G(X)` declared before `G(X) = 0`, both `[total]`. Declaration order names F for
     termination and for totality; the rank `[G, F]` names nothing (`rk_rank`). A rank that puts F
     first names F (`rk_wrongRank`): a wrong rank only names more.
  2. `mt`: `F(X) = G(X)`, `G(X) = F(X)`. Every rank names one of them (`mt_rank`): the order of the
     functions must put each callee first, and a cycle has no such order. (That neither terminates
     is TerminationGaps' `gapSelf` with one more call.)
  3. `ls`: `H(ListItem(X) L) = X` (one list pattern), `K(K' |-> V M, K') = V` (a map whose key the
     second argument binds), `S(L1 L2) = L1` (two frames). `clauseFixed` refuses the first two and
     `clauseFixedL` accepts them (`ls_fixed`); both refuse the third. **Counter-example**: a variant
     that read `_List_(P, Q)` like `ListItem(P) L`, fixing both sides, would accept S; S is not match
     independent (`ls_S_not_independent`): the one-element list splits as `[e] ++ []` and as
     `[] ++ [e]`, with right-hand sides `[e]` and `[]`.
  4. `ag`: `A(.List) = 0` beside `A(ListItem(X) L) = 1` (apart: the empty list against one with a
     first element); `B(ListItem(X) L) = 0` beside `B(L ListItem(Y)) = 1` (not apart).
     `fnExclusiveOK` refuses A and `fnExclusiveL` accepts it (`ag_A`); both refuse B.
     **Counter-example**: a variant that read two list patterns as apart when their shapes differ
     (first element against last element) would accept B; B's equations disagree
     (`ag_B_disagree`): both apply at the one-element list, with 0 and 1.
     `gd`: `C(0) = 0` beside `C(I) = 1 requires I >Int 0`, `C'(1) = 2` beside `C'(I) = 3 requires
     I =/=Int 1` (a literal against a guard), `D(I) = 0 requires 0 <=Int I andBool I <Int 5`
     beside `D(I) = 1 requires notBool (0 <=Int I andBool I <Int 5)` (a negated conjunction):
     `fnExclusiveL` accepts both; `E(0) = 0` beside `E(I) = 1 requires I >=Int 0` stays named (both
     apply at 0, with different results).
  5. `dc`: `N(ListItem(X) L) = N(L)` (a list's tail), `P(c(A, c(B, R) #as V)) = P(V)` (an alias under
     a constructor), `Q(c(A, c(B, R))) = Q(c(A, R))` (the head constructor around a lighter
     argument), `M(.Map M') = M(M')` (a map's frame). The certificate (`decreasingOK`) names all four;
     `decObligationsL` names only M (`dc_dec`): a map frame can denote the whole map, so its weight
     does not decrease (TerminationGaps' `gapDec` shows M does not terminate). **Counter-example**:
     a variant that weighed a map by its entries, as a list, and read the frame of `_Map_(P, M')` as
     lighter, would accept M.
-/
import KcoreSpec.FnObligations
import KcoreSpec.CoreDecide

set_option autoImplicit false

namespace KCore.FnDeciders

open KCore KCore.Det

def cellSorts : List Srt := [Srt.top, Srt.topFrag, nRegSorts, nRegSorts + 1, Srt.counter, Srt.counterOpt]
def cellCtors : List CtorSig :=
  [⟨topLabel, [nRegSorts, Srt.counter], Srt.top⟩, ⟨topFragLabel, [nRegSorts + 1, Srt.counterOpt], Srt.topFrag⟩,
   ⟨nRegSyms + 50, [Srt.k], nRegSorts⟩, ⟨nRegSyms + 51, [], nRegSorts + 1⟩,
   ⟨counterLabel, [Srt.int], Srt.counter⟩, ⟨noCounter, [], Srt.counterOpt⟩]
def cellSubsorts : List (Srt × Srt) := [(nRegSorts, nRegSorts + 1), (Srt.counter, Srt.counterOpt)]

def core (fns : List Fn) : Semantics where
  lib := { sortsBelowKItem := [Srt.map, Srt.list, Srt.int, Srt.bool] }
  sortNames := []
  symNames := []
  userSorts := cellSorts
  ctors := cellCtors
  fns := fns
  userSubsorts := cellSubsorts
  pgmSort := Srt.k
  rules := []

def F : Sym := nRegSyms + 100
def G : Sym := nRegSyms + 101

/-! ## 1. A rank against declaration order -/

def rk : Semantics := core
  [⟨F, [Srt.int], Srt.int, [⟨[Srt.int], [.var 0], none, .app G [.var 0], none, 50, false, [], .top, .top⟩], true⟩,
   ⟨G, [Srt.int], Srt.int, [⟨[Srt.int], [.var 0], none, .dv Srt.int (.int 0), none, 50, false, [], .top, .top⟩], true⟩]

theorem rk_sorted : rk.sortedOK = true ∧ rk.srReady = true := by decide_cheap

/-- Declaration order names F, for termination and totality. -/
theorem rk_order : rk.orderObligations = [F] ∧ rk.totalObligations = [F] := by decide +kernel

/-- The rank `[G, F]` names nothing. -/
theorem rk_rank : rk.rankObligations [G, F] = [] ∧ rk.totalObligationsR [G, F] = [] := by decide +kernel

/-- A rank that puts F first names F. -/
theorem rk_wrongRank : rk.rankObligations [F, G] = [F] ∧ rk.totalObligationsR [F, G] = [F] := by decide +kernel

/-- So every function of `rk` terminates and is total, nothing named. -/
theorem rk_terminates : ∀ f, Terminates rk f :=
  terminates_of_rankL rk_sorted.1 rk_sorted.2 (Semantics.ovlCase_of (by decide +kernel))
    (Semantics.rightHeld_of_binds (by decide +kernel)) [G, F] fun g hg => by
    rw [show rk.rankObligations [G, F] ++ rk.decObligationsL = [] by decide +kernel] at hg
    exact absurd hg List.not_mem_nil

/-! ## 2. Mutual recursion: no rank -/

def mt : Semantics := core
  [⟨F, [Srt.int], Srt.int, [⟨[Srt.int], [.var 0], none, .app G [.var 0], none, 50, false, [], .top, .top⟩], false⟩,
   ⟨G, [Srt.int], Srt.int, [⟨[Srt.int], [.var 0], none, .app F [.var 0], none, 50, false, [], .top, .top⟩], false⟩]

theorem mt_rank : mt.rankObligations [F, G] = [F] ∧ mt.rankObligations [G, F] = [G] := by decide +kernel

/-! ## 3. Match independence: list patterns, a map key bound later, two frames -/

def H : Sym := nRegSyms + 102
def K : Sym := nRegSyms + 103
def S : Sym := nRegSyms + 104

/-- `H(ListItem(X) L) = X`. -/
def clH : Clause := ⟨[Srt.kitem, Srt.list], [.app listConcat [.app listElem [.var 0], .var 1]], none, .var 0, none, 50, false, [], .top, .top⟩
/-- `K(K' |-> V M, K') = V`. -/
def clK : Clause :=
  ⟨[Srt.kitem, Srt.kitem, Srt.map], [.app mapConcat [.app mapElem [.var 0, .var 1], .var 2], .var 0], none, .var 1, none, 50, false, [], .top, .top⟩
/-- `S(L1 L2) = L1`. -/
def clS : Clause := ⟨[Srt.list, Srt.list], [.app listConcat [.var 0, .var 1]], none, .var 0, none, 50, false, [], .top, .top⟩

def ls : Semantics := core
  [⟨H, [Srt.list], Srt.kitem, [clH], false⟩, ⟨K, [Srt.map, Srt.kitem], Srt.kitem, [clK], false⟩,
   ⟨S, [Srt.list], Srt.list, [clS], false⟩]

theorem ls_sorted : ls.sortedOK = true ∧ ls.matchReady = true := by decide_cheap

/-- `clauseFixed` refuses H's and K's clauses; `clauseFixedL` accepts them; both refuse S's. -/
theorem ls_fixed : ls.matchObligations = [(H, 0), (K, 0), (S, 0)] ∧ ls.matchObligationsL = [(S, 0)] := by
  decide +kernel

/-- The variant that fixed both sides of `_List_(P, Q)` would not name S's clause. -/
def uniqBoth (D : List Nat) : Term → Option (List Nat)
  | .app f [.var i, .var j] => if f == listConcat then some (j :: i :: D) else none
  | _ => none

theorem uniqBoth_S : uniqBoth [] (.app listConcat [.var 0, .var 1]) = some [1, 0] := rfl

def e : GroundTerm := .inj Srt.int Srt.kitem (.dv Srt.int (.int 1))
def l0 : GroundTerm := .list Srt.list []
def l1 : GroundTerm := .list Srt.list [e]

theorem ls_isCtor : ls.isCtor listConcat = false ∧ ls.isCtor listElem = false := by decide +kernel

theorem ls_wellSorted {a b : GroundTerm} (ha : ls.sortOf a = some Srt.list) (hb : ls.sortOf b = some Srt.list) :
    ls.WellSorted [Srt.list, Srt.list] [(0, a), (1, b)] := by
  intro i s h
  match i, h with
  | 0, h => simp only [List.getElem?_cons_zero, Option.some.injEq] at h; subst h; exact ⟨a, rfl, ha⟩
  | 1, h => simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at h
            subst h; exact ⟨b, rfl, hb⟩
  | _ + 2, h => simp at h

theorem sort_l0 : ls.sortOf l0 = some Srt.list := by decide +kernel
theorem sort_l1 : ls.sortOf l1 = some Srt.list := by decide +kernel

/-- `L1 L2` denotes the one-element list under `[e] ++ []` and under `[] ++ [e]`. -/
theorem ls_S_split (a b : GroundTerm) (h : ls.collVal listConcat [a, b] = some l1) :
    PatVals ls [(0, a), (1, b)] clS.pats [l1] :=
  .cons (.coll ls_isCtor.1 (by decide) (.cons (.var rfl) (.cons (.var rfl) .nil)) h) .nil

/-- **S's clause is not match independent**: two matches at the one-element list give `[e]` and `[]`. -/
theorem ls_S_not_independent : ¬ MatchIndependent ls clS := by
  intro h
  have ha : clS.AppliesAt ls [(0, l1), (1, l0)] [l1] :=
    ⟨(ls_wellSorted sort_l1 sort_l0).at _, ls_S_split l1 l0 rfl, (fun _ ht => by cases ht), .top⟩
  have hb : clS.AppliesAt ls [(0, l0), (1, l1)] [l1] :=
    ⟨(ls_wellSorted sort_l0 sort_l1).at _, ls_S_split l0 l1 rfl, (fun _ ht => by cases ht), .top⟩
  have hdet : HDet ls [(0, l1), (1, l0)] clS.rhs := by
    intro u hu r r' h1 h2
    have hu : u = .var 0 := by simpa [clS, subterms] using hu
    subst hu
    cases h1; cases h2; rfl
  have hlow : ∀ cl' ∈ [clS], cl'.aside = false → cl'.prio < clS.prio → Fails ls [l1] cl' :=
    fun cl' h _ hlt => absurd hlt (by simp at h; subst h; decide)
  rcases h.1 [l1] _ _ ha hb (fun _ ht => by cases ht) (fun _ _ => hdet) (fun _ _ ht => by cases ht) (fun hne => absurd rfl hne)
      ⟨S, ⟨S, [Srt.list], Srt.list, [clS], false⟩, rfl, by simp, by simp, ⟨ha, hlow⟩, ⟨hb, hlow⟩⟩ with
    ⟨-, -, -, -, hv, -⟩ | hr
  · have := hv 0 (by simp [clS, varOccs])
    simp [l1, l0] at this
  · have := hr _ _ (.inl ⟨rfl, .inl ⟨(fun _ ht => by cases ht), .top, .var⟩⟩)
      (.inl ⟨rfl, .inl ⟨(fun _ ht => by cases ht), .top, .var⟩⟩)
    simp [l1, l0] at this

/-! ## 4. Agreement: list patterns apart, and not apart -/

def A : Sym := nRegSyms + 105
def B : Sym := nRegSyms + 106

def fnA : Fn := ⟨A, [Srt.list], Srt.int,
  [⟨[], [.app listUnit []], none, .dv Srt.int (.int 0), none, 50, false, [], .top, .top⟩,
   ⟨[Srt.kitem, Srt.list], [.app listConcat [.app listElem [.var 0], .var 1]], none, .dv Srt.int (.int 1), none, 50, false, [], .top, .top⟩], false⟩

def clB0 : Clause := ⟨[Srt.kitem, Srt.list], [.app listConcat [.app listElem [.var 0], .var 1]], none, .dv Srt.int (.int 0), none, 50, false, [], .top, .top⟩
def clB1 : Clause := ⟨[Srt.list, Srt.kitem], [.app listConcat [.var 0, .app listElem [.var 1]]], none, .dv Srt.int (.int 1), none, 50, false, [], .top, .top⟩
def fnB : Fn := ⟨B, [Srt.list], Srt.int, [clB0, clB1], false⟩

def ag : Semantics := core [fnA, fnB]

theorem ag_sorted : ag.sortedOK = true ∧ ag.matchReady = true := by decide_cheap

/-- `fnExclusiveOK` refuses A and B; `fnExclusiveL` accepts A and refuses B. -/
theorem ag_A : ag.agreeObligations = [A, B] ∧ ag.agreeObligationsL = [B] := by decide +kernel

/-- The variant that read list patterns of different shapes as apart would accept B. -/
def shapesApart (p q : Term) : Bool :=
  match p, q with
  | .app f [.app e₁ [_], _], .app g [_, .app e₂ [_]] => f == listConcat && g == listConcat && e₁ == listElem && e₂ == listElem
  | _, _ => false

theorem shapesApart_B : shapesApart clB0.pats[0]! clB1.pats[0]! = true := rfl

theorem ag_isCtor : ag.isCtor listConcat = false ∧ ag.isCtor listElem = false := by decide +kernel

/-- **B's equations disagree**: at the one-element list, `ListItem(X) L` matches with X = e,
L = [], `L ListItem(Y)` with L = [], Y = e; the right-hand sides are 0 and 1. -/
theorem ag_B_disagree : ¬ ClausesAgree ag fnB := by
  intro h
  have hp : (clB0, clB1) ∈ pairs fnB.clauses := by simp [fnB, pairs]
  have hws0 : ag.WellSorted clB0.vars [(0, e), (1, l0)] := by
    intro i s hi
    match i, hi with
    | 0, hi => simp only [clB0, List.getElem?_cons_zero, Option.some.injEq] at hi; subst hi
               exact ⟨e, rfl, by decide +kernel⟩
    | 1, hi => simp only [clB0, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hi
               subst hi; exact ⟨l0, rfl, by decide +kernel⟩
    | _ + 2, hi => simp [clB0] at hi
  have hws1 : ag.WellSorted clB1.vars [(0, l0), (1, e)] := by
    intro i s hi
    match i, hi with
    | 0, hi => simp only [clB1, List.getElem?_cons_zero, Option.some.injEq] at hi; subst hi
               exact ⟨l0, rfl, by decide +kernel⟩
    | 1, hi => simp only [clB1, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hi
               subst hi; exact ⟨e, rfl, by decide +kernel⟩
    | _ + 2, hi => simp [clB1] at hi
  have hm0 : PatVals ag [(0, e), (1, l0)] clB0.pats [l1] :=
    .cons (.coll ag_isCtor.1 (by decide)
      (.cons (.coll ag_isCtor.2 (by decide) (.cons (.var rfl) .nil) rfl) (.cons (.var rfl) .nil)) rfl) .nil
  have hm1 : PatVals ag [(0, l0), (1, e)] clB1.pats [l1] :=
    .cons (.coll ag_isCtor.1 (by decide)
      (.cons (.var rfl) (.cons (.coll ag_isCtor.2 (by decide) (.cons (.var rfl) .nil) rfl) .nil)) rfl) .nil
  have hdet : HDet ag [(0, e), (1, l0)] clB0.rhs := by
    intro u hu r r' h1 h2
    have hu : u = .dv Srt.int (.int 0) := by simpa [clB0, subterms] using hu
    subst hu
    cases h1; cases h2; rfl
  have hlow : ∀ (cl : Clause), cl.prio = 50 → ∀ cl' ∈ fnB.clauses, cl'.aside = false → cl'.prio < cl.prio →
      Fails ag [l1] cl' := fun cl hc cl' h _ hlt => absurd hlt (by
    have : cl'.prio = 50 := by simp [fnB, clB0, clB1] at h ⊢; rcases h with rfl | rfl <;> rfl
    rw [hc, this]; decide)
  rcases (h clB0 clB1 hp (.inl rfl)).1 [l1] _ _ ⟨hws0.at _, hm0, (fun _ ht => by cases ht), .top⟩
      ⟨hws1.at _, hm1, (fun _ ht => by cases ht), .top⟩ (fun _ ht => by cases ht) (fun _ _ => hdet) (fun _ _ ht => by cases ht) (fun hne => absurd rfl hne)
      ⟨B, fnB, rfl, by simp [fnB], by simp [fnB], ⟨⟨hws0.at _, hm0, (fun _ ht => by cases ht), .top⟩, hlow _ rfl⟩,
        ⟨⟨hws1.at _, hm1, (fun _ ht => by cases ht), .top⟩, hlow _ rfl⟩⟩ with ⟨-, -, hr, -⟩ | hr
  · simp [clB0, clB1] at hr
  · have := hr _ _ (.inl ⟨rfl, .inl ⟨(fun _ ht => by cases ht), .top, .dv⟩⟩)
      (.inl ⟨rfl, .inl ⟨(fun _ ht => by cases ht), .top, .dv⟩⟩)
    simp at this

def Cc : Sym := nRegSyms + 111
def Dd : Sym := nRegSyms + 112
def Ee : Sym := nRegSyms + 113
def Cc' : Sym := nRegSyms + 114
def lit (k : Int) : Term := .dv Srt.int (.int k)

def gd : Semantics := core
  [⟨Cc, [Srt.int], Srt.int,
     [⟨[], [lit 0], none, lit 0, none, 50, false, [], .top, .top⟩, ⟨[Srt.int], [.var 0], some (.app intGt [.var 0, lit 0]), lit 1, none, 50, false, [], .top, .top⟩], false⟩,
   ⟨Cc', [Srt.int], Srt.int,
     [⟨[], [lit 1], none, lit 2, none, 50, false, [], .top, .top⟩, ⟨[Srt.int], [.var 0], some (.app intNe [.var 0, lit 1]), lit 3, none, 50, false, [], .top, .top⟩], false⟩,
   ⟨Dd, [Srt.int], Srt.int,
     [⟨[Srt.int], [.var 0], some (.app boolAnd [.app intLe [lit 0, .var 0], .app intLt [.var 0, lit 5]]), lit 0, none, 50, false, [], .top, .top⟩,
      ⟨[Srt.int], [.var 0], some (.app boolNot [.app boolAnd [.app intLe [lit 0, .var 0], .app intLt [.var 0, lit 5]]]),
        lit 1, none, 50, false, [], .top, .top⟩], false⟩,
   ⟨Ee, [Srt.int], Srt.int,
     [⟨[], [lit 0], none, lit 0, none, 50, false, [], .top, .top⟩, ⟨[Srt.int], [.var 0], some (.app intGe [.var 0, lit 0]), lit 1, none, 50, false, [], .top, .top⟩], false⟩]

theorem gd_sorted : gd.sortedOK = true ∧ gd.matchReady = true := by decide_cheap

/-- `fnExclusiveOK` refuses C, C', D and E; `fnExclusiveL` accepts C, C' and D. -/
theorem gd_C : gd.agreeObligations = [Cc, Cc', Dd, Ee] ∧ gd.agreeObligationsL = [Ee] := by decide +kernel

/-! ## 5. Self calls decreasing in weight -/

def Nn : Sym := nRegSyms + 107
def Pp : Sym := nRegSyms + 108
def Qq : Sym := nRegSyms + 109
def Mm : Sym := nRegSyms + 110
def cK : Sym := nRegSyms + 52
def T0 : Srt := nRegSorts + 2

def dc : Semantics := { core
  [⟨Nn, [Srt.list], Srt.int,
     [⟨[Srt.kitem, Srt.list], [.app listConcat [.app listElem [.var 0], .var 1]], none, .app Nn [.var 1], none, 50, false, [], .top, .top⟩], false⟩,
   ⟨Pp, [T0], Srt.int,
     [⟨[Srt.int, Srt.int, T0, T0], [.app cK [.var 0, .as (.app cK [.var 1, .var 2]) 3]], none, .app Pp [.var 3], none, 50, false, [], .top, .top⟩], false⟩,
   ⟨Qq, [T0], Srt.int,
     [⟨[Srt.int, Srt.int, T0], [.app cK [.var 0, .app cK [.var 1, .var 2]]], none, .app Qq [.app cK [.var 0, .var 2]], none, 50, false, [], .top, .top⟩], false⟩,
   ⟨Mm, [Srt.map], Srt.int,
     [⟨[Srt.map], [.app mapConcat [.app mapUnit [], .var 0]], none, .app Mm [.var 0], none, 50, false, [], .top, .top⟩], false⟩]
  with userSorts := cellSorts ++ [T0], ctors := cellCtors ++ [⟨cK, [Srt.int, T0], T0⟩, ⟨nRegSyms + 53, [], T0⟩] }

theorem dc_sorted : dc.sortedOK = true ∧ dc.srReady = true := by decide_cheap

/-- The certificate names all four; `decObligationsL` names only the map's frame. -/
theorem dc_dec : (Parse.certOf dc).obligations dc = [Nn, Pp, Qq, Mm] ∧ dc.decObligationsL = [Mm] := by
  decide +kernel

/-- The variant weighing the frame of `_Map_(P, M')` below the map would accept M. -/
def mapFrameLighter (p : Term) (j : Nat) : Bool :=
  match p with
  | .app f [_, .var i] => f == mapConcat && i == j
  | _ => false

theorem mapFrameLighter_M : mapFrameLighter (.app mapConcat [.app mapUnit [], .var 0]) 0 = true := rfl

end KCore.FnDeciders

#print axioms KCore.FnDeciders.ls_S_not_independent
#print axioms KCore.FnDeciders.ag_B_disagree
#print axioms KCore.FnDeciders.rk_terminates
#print axioms KCore.FnDeciders.dc_dec
