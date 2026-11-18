/-
  Cores `okAll` accepts with a function that does not terminate or is not total, and what the
  deciders say of each. Checked by
      lean test/TerminationGaps.lean   (LEAN_PATH from `lake env`)

  1. `gapDec`: `f(.Map M) = f(M)`. At the empty map the clause applies with M the empty map and
     calls f at the same argument, so `Eval` has no derivation there (`gapDec_not_terminates`).
     The variable `M` is inside the pattern `_Map_(.Map, M)` under no constructor, so the
     certificate's check (`strictlyIn`) refuses argument 0: `certDec` (which names it) is not
     `ok`, `certOf` gives no decreasing argument, and f is a named obligation
     (`Certificates.obligations`). The clause's match obligation holds (`gapDec_matchIndependent`).
  2. `gapCov`: a collection sort S of the definition (a map sort, built by parameters implemented
     by the map hooks) and `f(.S) = 0`, declared `[total]`. The pattern `.S` denotes the empty
     collection only, so at a non-empty one no clause applies: the equations leave f's value open
     there, and under the interpretation that gives nothing (`HookParams.none`, the core's) f has
     none (`AtNone.gapCov_not_total`). S is not enumerable (its values are collections, which no generator
     builds), so only variable rows cover it: `totalOK` refuses f, and f is in `totalObligations`.
  3. `gapLin`: `f(X, X) = 0`, declared `[total]`. At two different arguments no clause applies: f's
     value is open there, none under `HookParams.none` (`AtNone.gapLin_not_total`). Read as two independent variables the row `X, X` would
     cover its sorts (`gapLin_row`); a covering row's variables occur once (`coverRows`), so
     `totalOK` refuses f, and f is in `totalObligations`.
  4. `gapSelf`: `f(X) = f(X)`, declared `[total]`: no derivation at any argument
     (`gapSelf_not_total`). Its row covers and its right-hand side is total over itself; its self
     call does not decrease, so `totalOK` refuses f (and the certificate names it).
  5. `gapDv`: a user sort that is Int, with a constructor `z`, and `f(z) = 0`, declared `[total]`.
     At an Int literal no clause applies: f's value is open there, none under `HookParams.none`
     (`AtNone.gapDv_not_total`). A sort holding domain values is not
     enumerable: only variable rows cover it, and `totalOK` refuses f.
  6. `gapParam`: a parameter symbol P (no interpretation) and a function of the same number, and
     `f(X) = P(X)`, declared `[total]` after it. The application of P has the parameter's value,
     the interpretation's: none under `HookParams.none` (`AtNone.gapParam_not_total`). `totalTerm` admits a call of a function of `tot` only where
     its number is no parameter symbol's: `totalOK` refuses f.
  7. `gapHook`: a function numbered as the interpreted `_/Int_`, and `f(X) = X /Int 0`, declared
     `[total]` after it. The application is the hook's, undefined (`gapHook_not_total`).
     `totalTerm` admits a call of a function of `tot` only where its number is no interpreted
     symbol's: `totalOK` refuses f.
-/
import KcoreSpec.Totals
import KcoreSpec.CoreDecide

set_option autoImplicit false

namespace KCore.TerminationGaps

open KCore

/-- The configuration `<k> K </k>` with the generated counter, as ordinary sorts, constructors and
subsorts: the top cell's, its fragment's, the `k` cell's and the counter's. -/
def cellSorts : List Srt := [Srt.top, Srt.topFrag, nRegSorts, nRegSorts + 1, Srt.counter, Srt.counterOpt]
def cellCtors : List CtorSig :=
  [⟨topLabel, [nRegSorts, Srt.counter], Srt.top⟩, ⟨topFragLabel, [nRegSorts + 1, Srt.counterOpt], Srt.topFrag⟩,
   ⟨nRegSyms + 50, [Srt.k], nRegSorts⟩, ⟨nRegSyms + 51, [], nRegSorts + 1⟩,
   ⟨counterLabel, [Srt.int], Srt.counter⟩, ⟨noCounter, [], Srt.counterOpt⟩]
def cellSubsorts : List (Srt × Srt) := [(nRegSorts, nRegSorts + 1), (Srt.counter, Srt.counterOpt)]

/-! ## 1. A decreasing argument through a map pattern -/

def F : Sym := nRegSyms + 100

def clDec : Clause :=
  ⟨[Srt.map], [.app mapConcat [.app mapUnit [], .var 0]], none, .app F [.var 0], none, 50, false, [], .top, .top⟩

def fDec : Fn := ⟨F, [Srt.map], Srt.int, [clDec], false⟩

def gapDec : Semantics where
  lib := { sortsBelowKItem := [Srt.map, Srt.int, Srt.bool] }
  sortNames := []
  symNames := []
  userSorts := cellSorts
  ctors := cellCtors
  fns := [fDec]
  userSubsorts := cellSubsorts
  pgmSort := Srt.k
  rules := []

def certDec : Certificates := ⟨[some 0]⟩

theorem gapDec_okAll : gapDec.okAll = true := by decide_cheap
theorem gapDec_srReady : gapDec.srReady = true := by decide +kernel
/-- The certificate's check refuses the decreasing argument: f is named. -/
theorem gapDec_cert : certDec.ok gapDec = false ∧ certDec.obligations gapDec = [F] := by decide +kernel
theorem gapDec_certOf : (Parse.certOf gapDec).decreasing = [none] ∧
    (Parse.certOf gapDec).ok gapDec = true ∧ (Parse.certOf gapDec).obligations gapDec = [F] := by
  decide +kernel
theorem gapDec_named : gapDec.orderObligations = [] ∧
    gapDec.totalObligations = [] ∧ gapDec.agreeObligations = [] ∧ gapDec.lazyObligations = [] := by
  decide +kernel
theorem gapDec_match : gapDec.matchObligations = [(F, 0)] := by decide +kernel

theorem gapDec_lookup : gapDec.lookupFn F = some fDec := rfl

def m0 : GroundTerm := .map Srt.map []

theorem gapDec_sorted : gapDec.sortsOf [m0] = some [Srt.map] := by decide +kernel

theorem gapDec_ctor_false : gapDec.isCtor mapConcat = false ∧ gapDec.isCtor mapUnit = false ∧
    gapDec.isCtor F = false := by decide +kernel

theorem sortOf_map_eq {s : Srt} {es : List (GroundTerm × GroundTerm)}
    (h : gapDec.sortOf (.map s es) = some Srt.map) : s = Srt.map := by
  obtain ⟨_, _, _, _, _, _, _, h⟩ := sortOf_mapS_fwd h
  exact h.symm

theorem hook_concat_unit (w : GroundTerm) : hook mapConcat [.map Srt.map [], w] =
    some (match w with | .map _ b => some (.map Srt.map b) | _ => none) := by
  cases w <;> rfl

/-- Every well-sorted match of `_Map_(.Map, M)` binds M to the argument. -/
theorem match_dec {σ : Subst} {v : GroundTerm} (hσ : gapDec.WellSorted [Srt.map] σ)
    (hm : PatVals gapDec σ clDec.pats [v]) : σ.lookup 0 = some v := by
  cases hm with
  | cons hp hrest =>
    cases hp with
    | ctor h _ => exact absurd h (by rw [gapDec_ctor_false.1]; decide)
    | coll _ hp _ _ => exact absurd hp (by rw [gapDec.isCollPat_of_hook (by decide)]; decide)
    | ovl _ ho _ _ => exact absurd ho (by decide +kernel)
    | hook _ hs hv' =>
      cases hs with
      | cons h1 h2 =>
        cases h2 with
        | cons h2 h3 =>
          cases h3
          cases h2 with
          | var hl =>
            cases h1 with
            | ctor h _ => exact absurd h (by rw [gapDec_ctor_false.2.1]; decide)
            | coll _ hp _ _ => exact absurd hp (by rw [gapDec.isCollPat_of_hook (by decide)]; decide)
            | ovl _ ho _ _ => exact absurd ho (by decide +kernel)
            | hook _ hs1 hv1 =>
              cases hs1
              have hw1 : hook mapUnit [] = some (some (.map Srt.map [])) := rfl
              rw [hw1] at hv1
              cases hv1
              rw [hook_concat_unit] at hv'
              obtain ⟨w', hw, hsw'⟩ := hσ 0 Srt.map rfl
              rw [hl] at hw
              cases hw
              split at hv'
              · have hs := sortOf_map_eq hsw'
                subst hs
                simp only [Option.some.injEq] at hv'
                rw [hl, hv']
              · simp at hv'

/-- The clause is match independent: every match binds its one variable to the argument. -/
theorem gapDec_matchIndependent : MatchIndependent gapDec clDec := by
  refine ⟨?_, fun hne => absurd rfl hne⟩
  intro vs σ σ' ⟨hσ, hm, _⟩ ⟨hσ', hm', _⟩ _ _ _ _ _
  refine .inl ⟨rfl, rfl, rfl, rfl, ?_, fun t ht => by simp [clDec] at ht⟩
  intro i hi
  have hi0 : i = 0 := by simpa [clDec, varOccs, varOccsList] using hi
  subst hi0
  cases vs with
  | nil => cases hm
  | cons v vs =>
    cases vs with
    | cons _ _ => cases hm with | cons _ h => cases h
    | nil => rw [match_dec hσ hm, match_dec hσ' hm']

theorem wellSorted_m0 : gapDec.WellSorted [Srt.map] [(0, m0)] := by
  intro i s h
  cases i with
  | zero =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    exact ⟨m0, rfl, by decide +kernel⟩
  | succ i => simp at h

theorem match_m0 : PatVals gapDec [(0, m0)] clDec.pats [m0] :=
  .cons (.hook (by decide) (.cons (.hook (by decide) .nil rfl) (.cons (.var rfl) .nil)) rfl) .nil

/-- **f does not terminate at the empty map**: the clause applies there with M the empty map,
and calls f at the same argument; `Eval` has no derivation. -/
theorem gapDec_not_terminates : ¬ Terminates gapDec F := by
  intro h
  obtain ⟨r, hr⟩ := h fDec gapDec_lookup [m0] gapDec_sorted
  exact Eval.rec (c := gapDec)
    (motive_1 := fun f vs _ _ => f = F → vs = [m0] → False)
    (motive_2 := fun _ _ _ => True) (motive_3 := fun _ _ _ => True)
    (motive_4 := fun σ t _ _ => t = .app F [.var 0] → σ.lookup 0 = some m0 → False)
    (motive_5 := fun _ _ _ _ => True)
    (motive_6 := fun _ _ _ _ _ => True)
    (motive_7 := fun _ _ _ => True) (motive_8 := fun _ _ _ _ => True)
    (fun {_ _ _ _ _ _} hfn hmem hσ hmatch _ _ _ _ _ _ _ _ _ _ ihrhs _ _ => fun hf hvs => by
      subst hf; subst hvs
      rw [gapDec_lookup] at hfn; cases hfn
      change _ ∈ [clDec] at hmem
      obtain rfl := List.mem_singleton.mp hmem
      exact ihrhs rfl (match_dec hσ hmatch))
    (fun hfn hnone _ => fun hf hvs => by
      subst hf; subst hvs
      rw [gapDec_lookup] at hfn; cases hfn
      cases hnone clDec (by simp [fDec]) with
      | intro h =>
        cases h [(0, m0)] (fun i _ => wellSorted_m0 i) match_m0 with
        | intro ht _ _ => cases ht
        | pre h => exact absurd (Holds.top_eq h) (by simp))
    (fun {_ _ _ _ _ _ _} hfn hmem _ _ _ _ _ _ ht _ _ _ _ _ _ => fun hf hvs => by
      subst hf; subst hvs
      rw [gapDec_lookup] at hfn; cases hfn
      change _ ∈ [clDec] at hmem
      obtain rfl := List.mem_singleton.mp hmem
      cases ht)
    (fun {_ _ _ _ _ _} hfn hmem _ _ _ _ _ hne _ _ _ _ _ _ _ _ _ _ _ => fun hf hvs => by
      subst hf; subst hvs
      rw [gapDec_lookup] at hfn; cases hfn
      change _ ∈ [clDec] at hmem
      obtain rfl := List.mem_singleton.mp hmem
      exact absurd rfl hne)
    (fun {_ _ _ _ _} hfn hmem hne _ _ _ _ _ _ _ _ _ _ _ => fun hf hvs => by
      subst hf; subst hvs
      rw [gapDec_lookup] at hfn; cases hfn
      change _ ∈ [clDec] at hmem
      obtain rfl := List.mem_singleton.mp hmem
      exact absurd rfl hne)
    (fun _ _ => trivial) (fun _ _ _ _ => trivial) (fun _ _ => trivial)
    (fun h _ => by cases h) (fun h _ => by cases h) (fun _ _ => fun h _ => by cases h)
    (fun hk _ _ => fun h _ => by
      cases h; exact absurd hk (by rw [gapDec_ctor_false.2.2]; decide))
    (fun _ hhk _ _ _ _ => fun h _ => by cases h; exact absurd hhk (by decide +kernel))
    (fun _ _ hp _ _ _ => fun h _ => by cases h; exact absurd hp (by decide +kernel))
    (fun _ _ hts hvs _ _ _ ihf => fun h h0 => by
      cases h
      cases hts with
      | cons h1 h2 =>
        cases h2; cases h1
        rw [h0] at hvs
        simp only [allSome, Option.bind_some, Option.map_some, Option.some.injEq] at hvs
        exact ihf rfl hvs.symm)
    (fun _ _ hts hvs _ _ => fun h h0 => by
      cases h
      cases hts with
      | cons h1 h2 =>
        cases h2; cases h1
        rw [h0] at hvs
        simp [allSome] at hvs)
    (fun _ ho _ _ _ => fun h _ => by cases h; exact absurd ho (by decide +kernel))
    (fun _ ho _ _ _ _ _ _ _ => fun h _ => by cases h; exact absurd ho (by decide +kernel))
    trivial (fun _ _ _ _ => trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (fun _ _ _ _ => trivial) (fun _ _ => trivial) (fun _ _ => trivial)
    (fun _ _ _ _ => trivial) (fun _ _ _ _ _ _ => trivial)
    hr rfl rfl

/-! ## 2. Coverage over a collection sort of the definition -/

def S : Srt := nRegSorts + 2
def uS : Sym := nRegSyms + 101
def eS : Sym := nRegSyms + 102
def cS : Sym := nRegSyms + 103
def G : Sym := nRegSyms + 104

def collS : CollSig := ⟨S, .map, Srt.int, Srt.int, uS, eS, cS⟩

def clCov : Clause := ⟨[], [.app uS []], none, .dv Srt.int (.int 0), none, 50, false, [], .top, .top⟩

def fCov : Fn := ⟨G, [S], Srt.int, [clCov], true⟩

def gapCov : Semantics where
  lib := { sortsBelowKItem := [Srt.int, Srt.bool] }
  sortNames := []
  symNames := []
  userSorts := cellSorts ++ [S]
  ctors := cellCtors
  fns := [fCov]
  userSubsorts := cellSubsorts
  pgmSort := Srt.k
  rules := []
  params := [{ sig := ⟨uS, [], S⟩, impl := some mapUnit }, { sig := ⟨eS, [Srt.int, Srt.int], S⟩, impl := some mapElem },
    { sig := ⟨cS, [S, S], S⟩, impl := some mapConcat }]
  colls := [collS]

theorem gapCov_okAll : gapCov.okAll = true := by decide_cheap
theorem gapCov_srReady : gapCov.srReady = true := by decide +kernel
theorem gapCov_collOK : gapCov.collOK collS = true := by decide +kernel
/-- `totalOK` refuses f: G is in `totalObligations`. -/
theorem gapCov_totalOK : gapCov.totalOK fCov = false ∧ gapCov.totalObligations = [G] := by
  decide +kernel
theorem gapCov_named : gapCov.orderObligations = [] ∧ (Parse.certOf gapCov).obligations gapCov = [] ∧ gapCov.agreeObligations = [] ∧ gapCov.lazyObligations = [] := by
  decide +kernel
theorem gapCov_match : gapCov.matchObligations = [(G, 0)] := by decide +kernel

/-- The clause's obligation holds: it has no variable. -/
theorem gapCov_matchIndependent : MatchIndependent gapCov clCov :=
  ⟨fun _ _ _ _ _ _ _ _ _ _ => Or.inl ⟨rfl, rfl, rfl, rfl, fun i hi => (by simp [clCov, varOccs] at hi),
    fun t ht => (by simp [clCov] at ht)⟩, fun hne => absurd rfl hne⟩

def mS : GroundTerm := .map S [(.dv Srt.int (.int 1), .dv Srt.int (.int 1))]

theorem gapCov_sorted : gapCov.sortsOf [mS] = some [S] := by decide +kernel

theorem gapCov_unit : gapCov.collVal uS [] = some (.map S []) := rfl

-- At the interpretation that gives nothing (`HookParams.none`): no statement for every interpretation.
namespace AtNone

/-- **f, declared total and confirmed by `totalOK`, has no value at a non-empty collection under
`HookParams.none`**: its one clause's pattern `.S` denotes the empty one only, so its value there is
its rest, which that interpretation does not give; under another interpretation it may have one. -/
theorem gapCov_not_total : ¬ Total gapCov G := by
  intro h
  obtain ⟨v, hv⟩ := h fCov rfl [mS] gapCov_sorted
  have hlook : gapCov.lookupFn G = some fCov := rfl
  cases hv with
  | @clauseEx _ _ _ _ _ _ hfn hmem _ _ _ _ _ hne _ _ _ _ =>
    rw [hlook] at hfn; cases hfn
    change _ ∈ [clCov] at hmem
    obtain rfl := List.mem_singleton.mp hmem
    exact absurd rfl hne
  | @clause _ _ _ _ _ _ hfn hmem _ hmatch _ _ _ =>
    rw [hlook] at hfn; cases hfn
    change _ ∈ [clCov] at hmem
    obtain rfl := List.mem_singleton.mp hmem
    cases hmatch with
    | cons hp _ =>
      cases hp with
      | hook hp _ _ => exact absurd hp (by decide)
      | ovl _ ho _ _ => exact absurd ho (by decide +kernel)
      | coll _ _ hs hv =>
        cases hs
        rw [gapCov_unit] at hv
        cases hv

end AtNone

/-! ## 3. A clause that repeats a variable -/

def L : Sym := nRegSyms + 105

def clLin : Clause := ⟨[Srt.int], [.var 0, .var 0], none, .dv Srt.int (.int 0), none, 50, false, [], .top, .top⟩

def fLin : Fn := ⟨L, [Srt.int, Srt.int], Srt.int, [clLin], true⟩

def gapLin : Semantics where
  lib := { sortsBelowKItem := [Srt.int, Srt.bool] }
  sortNames := []
  symNames := []
  userSorts := cellSorts
  ctors := cellCtors
  fns := [fLin]
  userSubsorts := cellSubsorts
  pgmSort := Srt.k
  rules := []

theorem gapLin_okAll : gapLin.okAll = true := by decide_cheap
theorem gapLin_srReady : gapLin.srReady = true := by decide +kernel
/-- Read as independent variables, the row `X, X` covers. -/
theorem gapLin_row : gapLin.covers (Semantics.coverFuel fLin) fLin.args [clLin.pats] = true := by
  decide +kernel
/-- `totalOK` refuses f: it has no covering row. -/
theorem gapLin_totalOK : Semantics.coverRows fLin = [] ∧ gapLin.totalOK fLin = false ∧
    gapLin.totalObligations = [L] := by decide +kernel
theorem gapLin_named : gapLin.orderObligations = [] ∧ (Parse.certOf gapLin).obligations gapLin = [] ∧
    gapLin.agreeObligations = [] ∧ gapLin.matchObligations = [] ∧ gapLin.lazyObligations = [] := by
  decide +kernel

theorem gapLin_sorted : gapLin.sortsOf [.dv Srt.int (.int 0), .dv Srt.int (.int 1)] =
    some [Srt.int, Srt.int] := by decide +kernel

-- At the interpretation that gives nothing (`HookParams.none`): no statement for every interpretation.
namespace AtNone

/-- **f, declared total and confirmed by `totalOK`, has no value at two different Ints under
`HookParams.none`**: its one clause matches only equal arguments, so its value there is its rest. -/
theorem gapLin_not_total : ¬ Total gapLin L := by
  intro h
  obtain ⟨v, hv⟩ := h fLin rfl _ gapLin_sorted
  have hlook : gapLin.lookupFn L = some fLin := rfl
  cases hv with
  | @clauseEx _ _ _ _ _ _ hfn hmem _ _ _ _ _ hne _ _ _ _ =>
    rw [hlook] at hfn; cases hfn
    change _ ∈ [clLin] at hmem
    obtain rfl := List.mem_singleton.mp hmem
    exact absurd rfl hne
  | @clause _ _ _ _ _ _ hfn hmem _ hmatch _ _ _ =>
    rw [hlook] at hfn; cases hfn
    change _ ∈ [clLin] at hmem
    obtain rfl := List.mem_singleton.mp hmem
    cases hmatch with
    | cons h1 h2 =>
      cases h2 with
      | cons h2 _ =>
        cases h1 with
        | var hl1 =>
          cases h2 with
          | var hl2 =>
            rw [hl1] at hl2
            simp at hl2

end AtNone

/-! ## 4. A self call that does not decrease -/

def S4 : Sym := nRegSyms + 106

def clSelf : Clause := ⟨[Srt.int], [.var 0], none, .app S4 [.var 0], none, 50, false, [], .top, .top⟩

def fSelf : Fn := ⟨S4, [Srt.int], Srt.int, [clSelf], true⟩

def gapSelf : Semantics where
  lib := { sortsBelowKItem := [Srt.int, Srt.bool] }
  sortNames := []
  symNames := []
  userSorts := cellSorts
  ctors := cellCtors
  fns := [fSelf]
  userSubsorts := cellSubsorts
  pgmSort := Srt.k
  rules := []

theorem gapSelf_okAll : gapSelf.okAll = true ∧ gapSelf.srReady = true := by decide_cheap
/-- The row covers and the right-hand side is total over f itself; the self call does not
decrease: `totalOK` refuses f, and the certificate names it. -/
theorem gapSelf_totalOK :
    gapSelf.covers (Semantics.coverFuel fSelf) fSelf.args (Semantics.coverRows fSelf) = true ∧
    gapSelf.totalTerm [S4] clSelf.rhs = true ∧ decreasingOK gapSelf fSelf (gapSelf.decArg fSelf) = false ∧
    gapSelf.totalOK fSelf = false ∧ gapSelf.totalObligations = [S4] ∧
    (Parse.certOf gapSelf).obligations gapSelf = [S4] := by
  decide +kernel

def i1 : GroundTerm := .dv Srt.int (.int 1)

/-- **f has no result at 1**: the clause applies and calls f at 1. -/
theorem gapSelf_not_total : ¬ Total gapSelf S4 := by
  intro h
  obtain ⟨v, hv⟩ := h fSelf rfl [i1] (by decide +kernel)
  have hlook : gapSelf.lookupFn S4 = some fSelf := rfl
  have hct : gapSelf.isCtor S4 = false := by decide +kernel
  exact Eval.rec (c := gapSelf)
    (motive_1 := fun f vs _ _ => f = S4 → vs = [i1] → False)
    (motive_2 := fun _ _ _ => True) (motive_3 := fun _ _ _ => True)
    (motive_4 := fun σ t _ _ => t = .app S4 [.var 0] → σ.lookup 0 = some i1 → False)
    (motive_5 := fun _ _ _ _ => True)
    (motive_6 := fun _ _ _ _ _ => True)
    (motive_7 := fun _ _ _ => True) (motive_8 := fun _ _ _ _ => True)
    (fun {_ _ _ _ _ _} hfn hmem _ hmatch _ _ _ _ _ _ _ _ _ _ ihrhs _ _ => fun hf hvs => by
      subst hf; subst hvs
      rw [hlook] at hfn; cases hfn
      change _ ∈ [clSelf] at hmem
      obtain rfl := List.mem_singleton.mp hmem
      cases hmatch with
      | cons h1 _ => cases h1 with | var hl => exact ihrhs rfl hl)
    (fun hfn hnone _ => fun hf hvs => by
      subst hf; subst hvs
      rw [hlook] at hfn; cases hfn
      cases hnone clSelf (by simp [fSelf]) with
      | intro h =>
        have hσ : gapSelf.WellSorted [Srt.int] [(0, i1)] := by
          intro i s hi
          cases i with
          | zero =>
            simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
            subst hi
            exact ⟨i1, rfl, by decide +kernel⟩
          | succ i => simp at hi
        cases h [(0, i1)] (fun i _ => hσ i) (.cons (.var rfl) .nil) with
        | intro ht _ _ => cases ht
        | pre h => exact absurd (Holds.top_eq h) (by simp))
    (fun {_ _ _ _ _ _ _} hfn hmem _ _ _ _ _ _ ht _ _ _ _ _ _ => fun hf hvs => by
      subst hf; subst hvs
      rw [hlook] at hfn; cases hfn
      change _ ∈ [clSelf] at hmem
      obtain rfl := List.mem_singleton.mp hmem
      cases ht)
    (fun {_ _ _ _ _ _} hfn hmem _ _ _ _ _ hne _ _ _ _ _ _ _ _ _ _ _ => fun hf hvs => by
      subst hf; subst hvs
      rw [hlook] at hfn; cases hfn
      change _ ∈ [clSelf] at hmem
      obtain rfl := List.mem_singleton.mp hmem
      exact absurd rfl hne)
    (fun {_ _ _ _ _} hfn hmem hne _ _ _ _ _ _ _ _ _ _ _ => fun hf hvs => by
      subst hf; subst hvs
      rw [hlook] at hfn; cases hfn
      change _ ∈ [clSelf] at hmem
      obtain rfl := List.mem_singleton.mp hmem
      exact absurd rfl hne)
    (fun _ _ => trivial) (fun _ _ _ _ => trivial) (fun _ _ => trivial)
    (fun h _ => by cases h) (fun h _ => by cases h) (fun _ _ => fun h _ => by cases h)
    (fun hk _ _ => fun h _ => by cases h; rw [hct] at hk; cases hk)
    (fun _ hhk _ _ _ _ => fun h _ => by cases h; exact absurd hhk (by decide +kernel))
    (fun _ _ hp _ _ _ => fun h _ => by cases h; exact absurd hp (by decide +kernel))
    (fun _ _ hts hvs _ _ _ ihf => fun h h0 => by
      cases h
      cases hts with
      | cons h1 h2 =>
        cases h2; cases h1
        rw [h0] at hvs
        simp only [allSome, Option.bind_some, Option.map_some, Option.some.injEq] at hvs
        exact ihf rfl hvs.symm)
    (fun _ _ hts hvs _ _ => fun h h0 => by
      cases h
      cases hts with
      | cons h1 h2 =>
        cases h2; cases h1
        rw [h0] at hvs
        simp [allSome] at hvs)
    (fun _ ho _ _ _ => fun h _ => by cases h; exact absurd ho (by decide +kernel))
    (fun _ ho _ _ _ _ _ _ _ => fun h _ => by cases h; exact absurd ho (by decide +kernel))
    trivial (fun _ _ _ _ => trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (fun _ _ _ _ => trivial) (fun _ _ => trivial) (fun _ _ => trivial)
    (fun _ _ _ _ => trivial) (fun _ _ _ _ _ _ => trivial)
    hv rfl rfl

/-! ## 5. A user sort holding domain values -/

def Z5 : Sym := nRegSyms + 107
def F5 : Sym := nRegSyms + 108

def clDv : Clause := ⟨[], [.app Z5 []], none, .dv Srt.int (.int 0), none, 50, false, [], .top, .top⟩

def fDv : Fn := ⟨F5, [Srt.int], Srt.int, [clDv], true⟩

def gapDv : Semantics where
  lib := { sortsBelowKItem := [Srt.bool] }
  sortNames := []
  symNames := []
  userSorts := cellSorts ++ [Srt.int]
  ctors := cellCtors ++ [⟨Z5, [], Srt.int⟩]
  fns := [fDv]
  userSubsorts := cellSubsorts
  pgmSort := Srt.k
  rules := []

theorem gapDv_okAll : gapDv.okAll = true ∧ gapDv.srReady = true := by decide_cheap
/-- Int is a user sort, no collection sort, and holds the Int literals: it is not enumerable, and
`totalOK` refuses f. -/
theorem gapDv_totalOK : gapDv.userSorts.contains Srt.int = true ∧ (gapDv.collOf Srt.int).isNone = true ∧
    gapDv.enumerable Srt.int = false ∧ gapDv.totalOK fDv = false ∧ gapDv.totalObligations = [F5] := by
  decide +kernel

-- At the interpretation that gives nothing (`HookParams.none`): no statement for every interpretation.
namespace AtNone

/-- **f has no value at the Int 1 under `HookParams.none`**: its one pattern denotes the constructor
term `z`, so its value there is its rest. -/
theorem gapDv_not_total : ¬ Total gapDv F5 := by
  intro h
  obtain ⟨v, hv⟩ := h fDv rfl [i1] (by decide +kernel)
  have hlook : gapDv.lookupFn F5 = some fDv := rfl
  cases hv with
  | @clauseEx _ _ _ _ _ _ hfn hmem _ _ _ _ _ hne _ _ _ _ =>
    rw [hlook] at hfn; cases hfn
    change _ ∈ [clDv] at hmem
    obtain rfl := List.mem_singleton.mp hmem
    exact absurd rfl hne
  | @clause _ _ _ _ _ _ hfn hmem _ hmatch _ _ _ =>
    rw [hlook] at hfn; cases hfn
    change _ ∈ [clDv] at hmem
    obtain rfl := List.mem_singleton.mp hmem
    cases hmatch with
    | cons hp _ =>
      cases hp with
      | hook hp _ _ => exact absurd hp (by decide)
      | coll hc _ _ _ => exact absurd hc (by decide +kernel)
      | ovl hc _ _ _ => exact absurd hc (by decide +kernel)

end AtNone

/-! ## 6. A function numbered as a parameter symbol -/

def P6 : Sym := nRegSyms + 109
def F6 : Sym := nRegSyms + 110

def fP : Fn := ⟨P6, [Srt.int], Srt.int, [⟨[Srt.int], [.var 0], none, .var 0, none, 50, false, [], .top, .top⟩], true⟩

def clPar : Clause := ⟨[Srt.int], [.var 0], none, .app P6 [.var 0], none, 50, false, [], .top, .top⟩

def fPar : Fn := ⟨F6, [Srt.int], Srt.int, [clPar], true⟩

def gapParam : Semantics where
  lib := { sortsBelowKItem := [Srt.int, Srt.bool] }
  sortNames := []
  symNames := []
  userSorts := cellSorts
  ctors := cellCtors
  fns := [fP, fPar]
  userSubsorts := cellSubsorts
  pgmSort := Srt.k
  rules := []
  params := [{ sig := ⟨P6, [Srt.int], Srt.int⟩ }]

theorem gapParam_okAll : gapParam.okAll = true ∧ gapParam.srReady = true := by decide_cheap
/-- P is among the total functions before f and is a parameter symbol: `totalOK` refuses f. -/
theorem gapParam_totalOK : gapParam.totalBefore fPar = [P6] ∧
    gapParam.params.any (·.sig.name == P6) = true ∧ gapParam.totalOK fPar = false ∧
    gapParam.totalObligations = [F6] := by
  decide +kernel

-- At the interpretation that gives nothing (`HookParams.none`): no statement for every interpretation.
namespace AtNone

/-- **f has no value at 1 under `HookParams.none`**: `P(1)` has the parameter's value, which that
interpretation does not give; under another interpretation it may have one. -/
theorem gapParam_not_total : ¬ Total gapParam F6 := by
  intro h
  obtain ⟨v, hv⟩ := h fPar rfl [i1] (by decide +kernel)
  have hlook : gapParam.lookupFn F6 = some fPar := rfl
  have hpv : gapParam.paramVal P6 [i1] = none := rfl
  cases hv with
  | @clauseEx _ _ _ _ _ _ hfn hmem _ _ _ _ _ hne _ _ _ _ =>
    rw [hlook] at hfn; cases hfn
    change _ ∈ [clPar] at hmem
    obtain rfl := List.mem_singleton.mp hmem
    exact absurd rfl hne
  | @clause _ _ _ _ _ _ hfn hmem _ hmatch _ _ _ _ hrhs =>
    rw [hlook] at hfn; cases hfn
    change _ ∈ [clPar] at hmem
    obtain rfl := List.mem_singleton.mp hmem
    cases hmatch with
    | cons h1 _ =>
      cases h1 with
      | var hl =>
        generalize hrv : (some v : Option GroundTerm) = r at hrhs
        cases hrhs with
        | ctor hk _ => exact absurd hk (by decide +kernel)
        | ovl _ ho _ => exact absurd ho (by decide +kernel)
        | ovlFn _ ho => exact absurd ho (by decide +kernel)
        | hook _ hhk _ _ _ => exact absurd hhk (by decide +kernel)
        | param _ _ _ hts hr =>
          cases hts with
          | cons h1 h2 =>
            cases h2; cases h1
            rw [hl] at hr
            simp only [allSome, Option.bind_some, Option.map_some] at hr
            rw [hpv] at hr
            rw [hr] at hrv; cases hrv
        | call _ _ _ _ _ hp => exact absurd hp (by decide +kernel)
        | callUndef => cases hrv

end AtNone

/-! ## 7. A function numbered as an interpreted symbol -/

def F7 : Sym := nRegSyms + 111

def fDiv : Fn := ⟨intTDiv, [Srt.int, Srt.int], Srt.int, [⟨[Srt.int, Srt.int], [.var 0, .var 1], none, .var 0, none, 50, false, [], .top, .top⟩],
  true⟩

def clHook : Clause := ⟨[Srt.int], [.var 0], none, .app intTDiv [.var 0, .dv Srt.int (.int 0)], none, 50, false, [], .top, .top⟩

def fHook : Fn := ⟨F7, [Srt.int], Srt.int, [clHook], true⟩

def gapHook : Semantics where
  lib := { sortsBelowKItem := [Srt.int, Srt.bool] }
  sortNames := []
  symNames := []
  userSorts := cellSorts
  ctors := cellCtors
  fns := [fDiv, fHook]
  userSubsorts := cellSubsorts
  pgmSort := Srt.k
  rules := []

theorem gapHook_okAll : gapHook.okAll = true ∧ gapHook.srReady = true := by decide_cheap
/-- `_/Int_` is among the total functions before f and is an interpreted symbol: `totalOK`
refuses f. -/
theorem gapHook_totalOK : gapHook.totalBefore fHook = [intTDiv] ∧
    hookSigs.any (·.name == intTDiv) = true ∧ gapHook.totalOK fHook = false ∧
    gapHook.totalObligations = [F7] := by
  decide +kernel

/-- **f is undefined at 1**: `1 /Int 0` is the hook's, undefined. -/
theorem gapHook_not_total : ¬ Total gapHook F7 := by
  intro h
  obtain ⟨v, hv⟩ := h fHook rfl [i1] (by decide +kernel)
  have hlook : gapHook.lookupFn F7 = some fHook := rfl
  have hdiv : hook intTDiv [i1, .dv Srt.int (.int 0)] = some none := rfl
  cases hv with
  | @clauseEx _ _ _ _ _ _ hfn hmem _ _ _ _ _ hne _ _ _ _ =>
    rw [hlook] at hfn; cases hfn
    change _ ∈ [clHook] at hmem
    obtain rfl := List.mem_singleton.mp hmem
    exact absurd rfl hne
  | @clause _ _ _ _ _ _ hfn hmem _ hmatch _ _ _ _ hrhs =>
    rw [hlook] at hfn; cases hfn
    change _ ∈ [clHook] at hmem
    obtain rfl := List.mem_singleton.mp hmem
    cases hmatch with
    | cons h1 _ =>
      cases h1 with
      | var hl =>
        generalize hrv : (some v : Option GroundTerm) = r at hrhs
        cases hrhs with
        | ctor hk _ => exact absurd hk (by decide +kernel)
        | ovl _ ho _ => exact absurd ho (by decide +kernel)
        | ovlFn _ ho => exact absurd ho (by decide +kernel)
        | hook _ _ hts hh _ =>
          cases hts with
          | cons h1 h2 =>
            cases h2 with
            | cons h2 h3 =>
              cases h3; cases h1; cases h2
              rw [hl] at hh
              have := hh _ rfl
              rw [Semantics.hookRes_of_notKey (f := intTDiv) (by decide +kernel), hdiv] at this
              cases this
              cases hrv
        | param _ hhk _ _ _ => exact absurd hhk (by decide +kernel)
        | call _ hhk _ _ _ _ => exact absurd hhk (by decide +kernel)
        | callUndef _ hhk _ _ _ => exact absurd hhk (by decide +kernel)

#print axioms gapDec_not_terminates
#print axioms gapDec_matchIndependent
#print axioms AtNone.gapCov_not_total
#print axioms gapCov_matchIndependent
#print axioms AtNone.gapLin_not_total
#print axioms gapSelf_not_total
#print axioms AtNone.gapDv_not_total
#print axioms AtNone.gapParam_not_total
#print axioms gapHook_not_total

end KCore.TerminationGaps
